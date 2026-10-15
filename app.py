"""
HCG Form - ระบบแบบฟอร์มออนไลน์ (Flask)

รันในเครื่อง : pip install -r requirements.txt  แล้ว  python app.py
บน Vercel    : ใช้ Postgres (Neon) ผ่านตัวแปร DATABASE_URL
"""
import hashlib
import hmac
import io
import json
import os
import random
import re
import secrets
import sqlite3
import threading
import time
from datetime import datetime, timedelta, timezone
from functools import wraps

from flask import (Flask, abort, flash, g, redirect, render_template, request,
                   send_file, session, url_for)
from PIL import Image, ImageDraw, ImageFilter, ImageFont
from werkzeug.security import check_password_hash, generate_password_hash

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

try:
    from dotenv import load_dotenv
    load_dotenv(os.path.join(BASE_DIR, ".env"))
except ImportError:
    pass


def env(name, default=""):
    return (os.environ.get(name) or default).strip()


# =====================================================================
# การตั้งค่า
# =====================================================================
ON_VERCEL = bool(os.environ.get("VERCEL"))
DATABASE_URL = next((env(k) for k in ("DATABASE_URL", "POSTGRES_URL", "NEON_DATABASE_URL") if env(k)), "")
IS_PG = DATABASE_URL.startswith(("postgres://", "postgresql://"))
DB_PATH = os.path.join(BASE_DIR, "hcg.db")
CSS_PATH = os.path.join(BASE_DIR, "style.css")
CONFIG_ERRORS = []

psycopg = None
if IS_PG:
    try:
        import psycopg
    except ImportError:
        CONFIG_ERRORS.append("ไม่พบไลบรารี psycopg กรุณาตรวจสอบไฟล์ requirements.txt")
elif ON_VERCEL:
    CONFIG_ERRORS.append(
        "ยังไม่ได้เชื่อมฐานข้อมูล Postgres: เข้าโปรเจกต์ใน Vercel ไปที่ Storage "
        "สร้างฐานข้อมูล Neon แล้วกด Connect กับโปรเจกต์นี้")

STAFF_ACCOUNTS = [
    {
        "username": env("HCG_HQ_USERNAME", "headoffice"),
        "email": env("HCG_HQ_EMAIL", "headoffice@hcgform.local").lower(),
        "password": env("HCG_HQ_PASSWORD"),
        "role": "superadmin",
        "var": "HCG_HQ_PASSWORD",
    },
    {
        "username": env("HCG_ADMIN_USERNAME", "admin"),
        "email": env("HCG_ADMIN_EMAIL", "admin@hcgform.local").lower(),
        "password": env("HCG_ADMIN_PASSWORD"),
        "role": "admin",
        "var": "HCG_ADMIN_PASSWORD",
    },
]
for _acc in STAFF_ACCOUNTS:
    if not _acc["password"]:
        CONFIG_ERRORS.append(f"ยังไม่ได้ตั้งค่า {_acc['var']} (รหัสผ่านของบัญชี {_acc['username']})")

STAFF_ROLES = ("superadmin", "admin")
TH_TZ = timezone(timedelta(hours=7))
HISTORY_DAYS = 30
LOGIN_MAX_FAILS = 5
LOGIN_LOCK_MINUTES = 15
CAPTCHA_TTL = 600
CAPTCHA_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"

ROLE_LABELS = {"superadmin": "ผู้ดูแลระบบ (สำนักงานใหญ่)", "admin": "แอดมิน", "user": "ผู้ใช้งาน"}
STATUS_LABELS = {"pending": "กำลังรออนุมัติ", "approved": "อนุมัติ", "rejected": "ไม่อนุมัติ"}
QTYPE_LABELS = {"text": "แบบตอบคำถาม", "truefalse": "แบบแตะถูกผิด", "choice": "แบบเลือกตอบ"}
ACTION_LABELS = {
    "register": "สร้างบัญชี", "login": "เข้าสู่ระบบ", "login_fail": "เข้าสู่ระบบไม่สำเร็จ",
    "logout": "ออกจากระบบ", "submit": "ส่งแบบฟอร์ม", "approve": "อนุมัติ",
    "reject": "ไม่อนุมัติ", "form_create": "สร้างแบบฟอร์ม", "form_delete": "ลบแบบฟอร์ม",
}
TF_OPTIONS = ("ถูก", "ผิด")
TH_MONTHS = ["ม.ค.", "ก.พ.", "มี.ค.", "เม.ย.", "พ.ค.", "มิ.ย.",
             "ก.ค.", "ส.ค.", "ก.ย.", "ต.ค.", "พ.ย.", "ธ.ค."]

USERNAME_RE = re.compile(r"^[A-Za-z0-9_.]{4,20}$")
EMAIL_RE = re.compile(r"^[^@\s]{1,64}@[^@\s]+\.[A-Za-z]{2,}$")
URL_RE = re.compile(r"^https?://[^\s<>\"']+$", re.IGNORECASE)


def load_secret_key():
    key = env("HCG_SECRET_KEY")
    if key:
        return key
    if ON_VERCEL:
        CONFIG_ERRORS.append("ยังไม่ได้ตั้งค่า HCG_SECRET_KEY ใน Settings > Environment Variables")
        return secrets.token_hex(32)
    path = os.path.join(BASE_DIR, "secret.key")
    if not os.path.exists(path):
        with open(path, "w", encoding="utf-8") as f:
            f.write(secrets.token_hex(32))
    with open(path, encoding="utf-8") as f:
        return f.read().strip()


def file_version(path):
    try:
        with open(path, "rb") as f:
            return hashlib.sha256(f.read()).hexdigest()[:10]
    except OSError:
        return "0"


app = Flask(__name__, template_folder=BASE_DIR, static_folder=None)
app.config.update(
    SECRET_KEY=load_secret_key(),
    SESSION_COOKIE_NAME="hcg_session",
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=ON_VERCEL,
    PERMANENT_SESSION_LIFETIME=timedelta(days=7),
    MAX_CONTENT_LENGTH=1024 * 1024,
)
CSS_VERSION = file_version(CSS_PATH)

# =====================================================================
# ฐานข้อมูล (รองรับทั้ง SQLite และ Postgres)
# =====================================================================
INTEGRITY_ERRORS = (sqlite3.IntegrityError,) + ((psycopg.IntegrityError,) if psycopg else ())


def _col_name(d):
    return d.name if hasattr(d, "name") else d[0]


class Database:
    def __init__(self):
        if IS_PG:
            self.con = psycopg.connect(DATABASE_URL, connect_timeout=10)
        else:
            self.con = sqlite3.connect(DB_PATH, timeout=10)
            self.con.execute("PRAGMA foreign_keys = ON")

    @staticmethod
    def _sql(sql):
        return sql.replace("?", "%s") if IS_PG else sql

    def all(self, sql, params=()):
        cur = self.con.cursor()
        try:
            cur.execute(self._sql(sql), tuple(params))
            if cur.description is None:
                return []
            names = [_col_name(d) for d in cur.description]
            return [dict(zip(names, row)) for row in cur.fetchall()]
        finally:
            cur.close()

    def one(self, sql, params=()):
        rows = self.all(sql, params)
        return rows[0] if rows else None

    def scalar(self, sql, params=()):
        row = self.one(sql, params)
        return next(iter(row.values())) if row else None

    def run(self, sql, params=()):
        cur = self.con.cursor()
        try:
            cur.execute(self._sql(sql), tuple(params))
        finally:
            cur.close()

    def insert(self, sql, params=()):
        if IS_PG:
            return self.one(sql + " RETURNING id", params)["id"]
        cur = self.con.cursor()
        try:
            cur.execute(sql, tuple(params))
            return cur.lastrowid
        finally:
            cur.close()

    def columns(self, table):
        cur = self.con.cursor()
        try:
            cur.execute(f"SELECT * FROM {table} WHERE 1 = 0")
            return {_col_name(d) for d in cur.description}
        finally:
            cur.close()

    def commit(self):
        self.con.commit()

    def rollback(self):
        self.con.rollback()

    def close(self):
        self.con.close()


def schema_tables():
    pk = "SERIAL PRIMARY KEY" if IS_PG else "INTEGER PRIMARY KEY AUTOINCREMENT"
    return [
        f"""CREATE TABLE IF NOT EXISTS users (
            id {pk},
            username TEXT NOT NULL,
            email TEXT NOT NULL UNIQUE,
            password_hash TEXT NOT NULL,
            role TEXT NOT NULL DEFAULT 'user',
            created_at TEXT NOT NULL)""",
        f"""CREATE TABLE IF NOT EXISTS forms (
            id {pk},
            title TEXT NOT NULL,
            description TEXT NOT NULL DEFAULT '',
            created_by INTEGER REFERENCES users(id),
            created_at TEXT NOT NULL,
            is_deleted INTEGER NOT NULL DEFAULT 0)""",
        f"""CREATE TABLE IF NOT EXISTS questions (
            id {pk},
            form_id INTEGER NOT NULL REFERENCES forms(id),
            position INTEGER NOT NULL,
            qtype TEXT NOT NULL,
            text TEXT NOT NULL,
            options TEXT NOT NULL DEFAULT '[]',
            required INTEGER NOT NULL DEFAULT 1)""",
        f"""CREATE TABLE IF NOT EXISTS submissions (
            id {pk},
            form_id INTEGER NOT NULL REFERENCES forms(id),
            user_id INTEGER NOT NULL REFERENCES users(id),
            status TEXT NOT NULL DEFAULT 'pending',
            reason TEXT,
            link TEXT,
            reviewed_by INTEGER REFERENCES users(id),
            reviewed_at TEXT,
            created_at TEXT NOT NULL)""",
        f"""CREATE TABLE IF NOT EXISTS answers (
            id {pk},
            submission_id INTEGER NOT NULL REFERENCES submissions(id),
            question_id INTEGER NOT NULL REFERENCES questions(id),
            value TEXT NOT NULL DEFAULT '')""",
        f"""CREATE TABLE IF NOT EXISTS activity (
            id {pk},
            user_id INTEGER REFERENCES users(id),
            target_id INTEGER REFERENCES users(id),
            action TEXT NOT NULL,
            detail TEXT NOT NULL DEFAULT '',
            ref TEXT,
            created_at TEXT NOT NULL)""",
    ]


SCHEMA_INDEXES = [
    "CREATE UNIQUE INDEX IF NOT EXISTS ux_users_username ON users (lower(username))",
    "CREATE INDEX IF NOT EXISTS idx_sub_user_form ON submissions (user_id, form_id)",
    "CREATE INDEX IF NOT EXISTS idx_sub_status ON submissions (status)",
    "CREATE INDEX IF NOT EXISTS idx_ans_sub ON answers (submission_id)",
    "CREATE INDEX IF NOT EXISTS idx_q_form ON questions (form_id)",
    "CREATE INDEX IF NOT EXISTS idx_act_time ON activity (created_at)",
    "CREATE INDEX IF NOT EXISTS idx_act_ref ON activity (action, ref)",
]


def utcnow():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def iso_ago(minutes):
    return (datetime.now(timezone.utc) - timedelta(minutes=minutes)).isoformat(timespec="seconds")


def sync_staff(db):
    """สร้างหรืออัปเดตบัญชีผู้ดูแลตาม Environment Variables"""
    for acc in STAFF_ACCOUNTS:
        user = db.one("SELECT * FROM users WHERE lower(username) = lower(?) LIMIT 1", (acc["username"],))
        if user is None:
            user = db.one("SELECT * FROM users WHERE email = ? LIMIT 1", (acc["email"],))
        if user is None:
            db.insert(
                "INSERT INTO users (username, email, password_hash, role, created_at) VALUES (?,?,?,?,?)",
                (acc["username"], acc["email"], generate_password_hash(acc["password"]),
                 acc["role"], utcnow()))
            continue
        changes = {}
        if user["username"] != acc["username"]:
            changes["username"] = acc["username"]
        if user["email"] != acc["email"]:
            taken = db.one("SELECT id FROM users WHERE email = ? AND id <> ? LIMIT 1",
                           (acc["email"], user["id"]))
            if not taken:
                changes["email"] = acc["email"]
        if user["role"] != acc["role"]:
            changes["role"] = acc["role"]
        if not check_password_hash(user["password_hash"], acc["password"]):
            changes["password_hash"] = generate_password_hash(acc["password"])
        if changes:
            sets = ", ".join(f"{k} = ?" for k in changes)
            db.run(f"UPDATE users SET {sets} WHERE id = ?", (*changes.values(), user["id"]))

    # บัญชีที่ไม่ได้อยู่ในการตั้งค่าแล้ว จะถูกลดสิทธิ์เป็นผู้ใช้งานทั่วไป
    names = [a["username"].lower() for a in STAFF_ACCOUNTS]
    marks = ",".join("?" for _ in names)
    db.run(f"UPDATE users SET role = 'user' WHERE role IN ('superadmin', 'admin') "
           f"AND lower(username) NOT IN ({marks})", names)


_db_ready = False
_db_lock = threading.Lock()


def ensure_db():
    global _db_ready
    if _db_ready:
        return
    with _db_lock:
        if _db_ready:
            return
        db = Database()
        try:
            if IS_PG:
                db.run("SELECT pg_advisory_xact_lock(724113)")
            for stmt in schema_tables():
                db.run(stmt)
            if "ref" not in db.columns("activity"):
                db.run("ALTER TABLE activity ADD COLUMN ref TEXT")
            for stmt in SCHEMA_INDEXES:
                db.run(stmt)
            sync_staff(db)
            db.commit()
        finally:
            db.close()
        _db_ready = True


def get_db():
    if "db" not in g:
        g.db = Database()
    return g.db


@app.teardown_appcontext
def close_db(_exc=None):
    db = g.pop("db", None)
    if db is not None:
        db.close()


def log(action, detail="", user_id=None, target_id=None, ref=None):
    get_db().insert(
        "INSERT INTO activity (user_id, target_id, action, detail, ref, created_at) VALUES (?,?,?,?,?,?)",
        (user_id, target_id, action, detail, ref, utcnow()))


# =====================================================================
# เวลาไทย
# =====================================================================
def to_th(iso):
    return datetime.fromisoformat(iso).astimezone(TH_TZ)


def fmt_date(d):
    return f"{d.day} {TH_MONTHS[d.month - 1]} {d.year + 543}"


@app.template_filter("thtime")
def thtime(iso):
    if not iso:
        return "-"
    dt = to_th(iso)
    return f"{fmt_date(dt)} {dt:%H:%M} น."


@app.template_filter("thclock")
def thclock(iso):
    return f"{to_th(iso):%H:%M} น." if iso else "-"


def last_days():
    today = datetime.now(TH_TZ).date()
    return [today - timedelta(days=i) for i in range(HISTORY_DAYS - 1, -1, -1)]


def since_iso():
    start = datetime.combine(last_days()[0], datetime.min.time(), TH_TZ)
    return start.astimezone(timezone.utc).isoformat(timespec="seconds")


# =====================================================================
# ความปลอดภัย
# =====================================================================
def csrf_token():
    if "_csrf" not in session:
        session["_csrf"] = secrets.token_hex(16)
    return session["_csrf"]


def captcha_digest(code):
    return hmac.new(app.secret_key.encode(), code.encode(), hashlib.sha256).hexdigest()


_dummy_hash = None


def dummy_password_check(password):
    """ทำให้เวลาตอบสนองเท่ากัน ไม่ว่าบัญชีจะมีอยู่หรือไม่"""
    global _dummy_hash
    if _dummy_hash is None:
        _dummy_hash = generate_password_hash(secrets.token_hex(8))
    check_password_hash(_dummy_hash, password)


def is_staff(user):
    return bool(user) and user["role"] in STAFF_ROLES


def setup_page(messages):
    return render_template(
        "error.html", code=503, title="ระบบยังตั้งค่าไม่ครบ", messages=messages,
        hint="ตั้งค่าใน Vercel > Settings > Environment Variables แล้วกด Redeploy"), 503


@app.before_request
def before_request():
    g.user = None
    if request.endpoint == "stylesheet":
        return None
    if CONFIG_ERRORS:
        return setup_page(CONFIG_ERRORS)
    try:
        ensure_db()
    except Exception:
        app.logger.exception("Database initialisation failed")
        return setup_page(["เชื่อมต่อหรือเตรียมฐานข้อมูลไม่สำเร็จ ดูรายละเอียดใน Runtime Logs ของ Vercel"])

    uid = session.get("uid")
    if uid:
        g.user = get_db().one(
            "SELECT id, username, email, role, created_at FROM users WHERE id = ? LIMIT 1", (uid,))
        if g.user is None:
            session.clear()

    if request.method == "POST":
        token = request.form.get("_csrf", "")
        if not token or not hmac.compare_digest(token, session.get("_csrf", "")):
            abort(400)
    return None


@app.after_request
def security_headers(resp):
    resp.headers.setdefault("X-Content-Type-Options", "nosniff")
    resp.headers.setdefault("X-Frame-Options", "DENY")
    resp.headers.setdefault("Referrer-Policy", "same-origin")
    if request.endpoint not in ("stylesheet", "captcha"):
        resp.headers.setdefault("Cache-Control", "no-store")
    return resp


def login_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not g.user:
            flash("กรุณาเข้าสู่ระบบก่อน", "error")
            return redirect(url_for("login"))
        return view(*args, **kwargs)
    return wrapped


def staff_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not g.user:
            flash("กรุณาเข้าสู่ระบบก่อน", "error")
            return redirect(url_for("login"))
        if not is_staff(g.user):
            abort(403)
        return view(*args, **kwargs)
    return wrapped


@app.context_processor
def inject_helpers():
    user = g.get("user")
    staff = is_staff(user)
    pending = 0
    if staff:
        try:
            pending = get_db().scalar("SELECT COUNT(*) FROM submissions WHERE status = 'pending'") or 0
        except Exception:
            pending = 0
    return {
        "csrf_token": csrf_token,
        "css_version": CSS_VERSION,
        "staff": staff,
        "pending_count": pending,
        "role_label": lambda r: ROLE_LABELS.get(r, r),
        "status_label": lambda s: STATUS_LABELS.get(s, s),
        "qtype_label": lambda q: QTYPE_LABELS.get(q, q),
        "action_label": lambda a: ACTION_LABELS.get(a, a),
    }


# =====================================================================
# ไฟล์ CSS และรูปรหัสยืนยัน
# =====================================================================
@app.route("/style.css")
def stylesheet():
    return send_file(CSS_PATH, mimetype="text/css", max_age=86400)


@app.route("/captcha.png")
def captcha():
    code = "".join(random.choices(CAPTCHA_CHARS, k=5))
    session["captcha"] = {"h": captcha_digest(code), "t": int(time.time())}

    width, height = 220, 72
    img = Image.new("RGB", (width, height), (244, 239, 255))
    draw = ImageDraw.Draw(img)
    try:
        font = ImageFont.load_default(size=42)
    except TypeError:
        font = ImageFont.load_default()

    for _ in range(8):
        draw.line([(random.randint(0, width), random.randint(0, height)),
                   (random.randint(0, width), random.randint(0, height))],
                  fill=(random.randint(170, 210), random.randint(150, 200), 240), width=2)
    x = 14
    for ch in code:
        layer = Image.new("RGBA", (50, 66), (0, 0, 0, 0))
        ImageDraw.Draw(layer).text(
            (8, 6), ch, font=font,
            fill=(random.randint(70, 120), random.randint(40, 80), random.randint(150, 210), 255))
        layer = layer.rotate(random.randint(-28, 28), resample=Image.BICUBIC)
        img.paste(layer, (x, random.randint(-2, 8)), layer)
        x += 40
    for _ in range(280):
        draw.point((random.randint(0, width - 1), random.randint(0, height - 1)),
                   fill=(random.randint(120, 200), random.randint(100, 180), 230))
    img = img.filter(ImageFilter.SMOOTH)

    buf = io.BytesIO()
    img.save(buf, "PNG")
    buf.seek(0)
    resp = send_file(buf, mimetype="image/png")
    resp.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    return resp


# =====================================================================
# บัญชีผู้ใช้
# =====================================================================
@app.route("/")
def index():
    if not g.user:
        return redirect(url_for("login"))
    return redirect(url_for("admin_dashboard" if is_staff(g.user) else "home"))


@app.route("/login", methods=["GET", "POST"])
def login():
    if g.user:
        return redirect(url_for("index"))
    login_type = request.form.get("login_type", "username")
    if login_type not in ("username", "email"):
        login_type = "username"
    identifier = ""

    if request.method == "POST":
        identifier = request.form.get("identifier", "").strip()[:120]
        password = request.form.get("password", "")[:128]
        db = get_db()
        ref = f"{login_type}:{identifier.lower()}"

        fails = db.scalar(
            "SELECT COUNT(*) FROM activity WHERE action = 'login_fail' AND ref = ? AND created_at >= ?",
            (ref, iso_ago(LOGIN_LOCK_MINUTES))) or 0
        if fails >= LOGIN_MAX_FAILS:
            flash(f"เข้าสู่ระบบผิดหลายครั้งเกินไป กรุณารอ {LOGIN_LOCK_MINUTES} นาทีแล้วลองใหม่", "error")
            return render_template("login.html", login_type=login_type, identifier=identifier)

        if login_type == "email":
            user = db.one("SELECT * FROM users WHERE email = ? LIMIT 1", (identifier.lower(),))
        else:
            user = db.one("SELECT * FR
