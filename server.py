#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GTA VI 查询站 · 后端（零依赖，只用 Python 3 标准库）

功能
1. 托管网站本体（GTAVI查询站.html 及同目录静态文件）
2. 接收 BUG 反馈 / 投稿：POST /api/bug  → 写入 SQLite（data/bugs.db），可选同时发邮件到你的邮箱
3. 站长后台：/admin （HTTP Basic 认证）查看全部反馈、导出 CSV、删除垃圾提交
4. 账户系统：注册 / 登录 / 邮箱验证码 / 找回密码 / 个人资料 / 云同步收藏与彩蛋进度
5. 自带限流、蜜罐字段、长度限制、CORS（允许直接双击打开 HTML 时也能提交）

运行：python3 server.py
默认地址：http://localhost:8000    后台：http://localhost:8000/admin
"""

import base64
import hashlib
import hmac
import html
import io
import json
import os
import re
import secrets
import smtplib
import sqlite3
import ssl
import sys
import threading
import time
import traceback
import urllib.parse
from datetime import datetime, timedelta, timezone
from email.header import Header
from email.mime.text import MIMEText
from email.utils import formataddr, formatdate
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

DATABASE_URL = (os.environ.get("DATABASE_URL") or "").strip()
IS_PG = DATABASE_URL.startswith("postgres")


class PgCursor:
    """把 psycopg2 的游标包装成 sqlite3 游标的样子（fetchone / fetchall / dict 行）。"""
    def __init__(self, cur):
        self._c = cur

    def fetchone(self):
        try:
            return self._c.fetchone()
        except Exception:
            return None

    def fetchall(self):
        try:
            return self._c.fetchall()
        except Exception:
            return []

    def close(self):
        try:
            self._c.close()
        except Exception:
            pass


class PgConn:
    """Postgres 连接包装：把 ? 占位符换成 %s，行返回成 dict。"""
    def __init__(self, conn):
        self._conn = conn

    def execute(self, sql, params=()):
        from psycopg2.extras import RealDictCursor
        cur = self._conn.cursor(cursor_factory=RealDictCursor)
        cur.execute(sql.replace("?", "%s"), params if params is not None else ())
        return PgCursor(cur)

    def executescript(self, script):
        cur = self._conn.cursor()
        cur.execute(script)
        cur.close()

    def commit(self):
        self._conn.commit()

    def close(self):
        self._conn.close()


def pg_connect():
    import psycopg2
    return PgConn(psycopg2.connect(DATABASE_URL, connect_timeout=10))


def insert_id(conn, sql, params):
    """INSERT 后取自增主键，SQLite / Postgres 都能用。"""
    if IS_PG:
        cur = conn.execute(sql + " RETURNING id", params)
        row = cur.fetchone()
        cur.close()
        return int(row["id"]) if row else 0
    cur = conn.execute(sql, params)
    rid = cur.lastrowid
    cur.close()
    return rid


BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.environ.get("GTA6_DATA_DIR") or os.path.join(BASE_DIR, "data")
DB_PATH = os.path.join(DATA_DIR, "bugs.db")
ACC_DB_PATH = os.path.join(DATA_DIR, "accounts.db")
CONFIG_PATH = os.path.join(BASE_DIR, "config.json")
SITE_FILE = "GTAVI查询站.html"
LOG_PATH = os.path.join(DATA_DIR, "server.log")
TZ = timezone(timedelta(hours=8))          # 北京时间
MAX_BODY = 16 * 1024                        # 单次请求体上限
RATE_GAP = 30                               # 同一 IP 两次提交最小间隔（秒）
RATE_DAY = 20                               # 同一 IP 每天最多提交次数
PAGES = {"home": "首页", "map": "地图", "eggs": "彩蛋", "chars": "角色", "news": "资讯", "me": "个人中心"}
USERNAME_RE = re.compile(r"^[\u4e00-\u9fa5A-Za-z0-9_]{2,16}$")
EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]{2,}$")
RESERVED_NAMES = {"admin", "root", "system", "rockstar", "gta6", "gta", "staff", "moderator", "官方", "站长"}

DEFAULT_CONFIG = {
    "host": "0.0.0.0",
    "port": 8000,
    "admin_password": "",                  # 首次运行会自动生成
    "auth": {
        "allow_dev_code": False,               # 未配置 SMTP 时，把验证码直接返回给前端（仅建议本地/内网使用）
        "code_ttl": 300,                      # 验证码有效期（秒）
        "code_gap": 60,                       # 同一邮箱两次发码最小间隔（秒）
        "code_hour": 8,                       # 同一邮箱每小时最多发码次数
        "register_open": True,
    },
    "smtp": {
        "enabled": True,
        "host": "smtp.qq.com",
        "port": 465,
        "ssl": True,                       # QQ 邮箱 465 端口用 SSL
        "username": "2235774797@qq.com",
        "password": "",                    # ← 填 QQ 邮箱「授权码」，不是登录密码
        "to": "2235774797@qq.com",
        "from_name": "GTA VI 查询站",
    },
}

_lock = threading.Lock()
_rate = {}                                  # ip -> [最近提交时间戳...]


# ---------------------------------------------------------------- 配置 / 日志
def log(msg):
    line = "[%s] %s" % (datetime.now(TZ).strftime("%Y-%m-%d %H:%M:%S"), msg)
    print(line, flush=True)
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:
        pass


def load_config():
    os.makedirs(DATA_DIR, exist_ok=True)
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, encoding="utf-8") as f:
                user = json.load(f)
            for k, v in user.items():
                if isinstance(v, dict) and isinstance(cfg.get(k), dict):
                    cfg[k].update(v)
                else:
                    cfg[k] = v
        except Exception as e:
            log("config.json 读取失败，使用默认配置：%s" % e)
    # ---- 环境变量覆盖（云平台部署用，避免把授权码写进文件）----
    env = os.environ.get
    if env("PORT"): cfg["port"] = int(env("PORT"))
    if env("HOST"): cfg["host"] = env("HOST")
    if env("ADMIN_PASSWORD"): cfg["admin_password"] = env("ADMIN_PASSWORD")
    if env("AUTH_REGISTER_OPEN") is not None:
        cfg.setdefault("auth", {})["register_open"] = env("AUTH_REGISTER_OPEN").lower() not in ("0", "false", "no")
    if env("SMTP_HOST"):
        cfg.setdefault("smtp", {})
        cfg["smtp"].update({
            "host": env("SMTP_HOST"),
            "port": int(env("SMTP_PORT") or 465),
            "ssl": (env("SMTP_SSL") or "1").lower() not in ("0", "false", "no"),
            "username": env("SMTP_USER") or cfg["smtp"].get("username", ""),
            "password": env("SMTP_PASS") or "",
            "to": env("SMTP_TO") or env("SMTP_USER") or cfg["smtp"].get("to", ""),
            "from_name": env("SMTP_FROM") or cfg["smtp"].get("from_name", "GTA VI 查询站"),
        })
    if not cfg.get("admin_password"):
        cfg["admin_password"] = "gta6-" + secrets.token_hex(3)
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except Exception:
        pass          # 只读文件系统（部分免费平台）时跳过
    return cfg


def db():
    """BUG 反馈库：有 DATABASE_URL 走 Postgres，否则本地 SQLite。"""
    if IS_PG:
        conn = pg_connect()
        conn.execute("""CREATE TABLE IF NOT EXISTS bugs(
            id SERIAL PRIMARY KEY,
            created_at TEXT NOT NULL,
            page_key TEXT, page TEXT,
            device TEXT, "desc" TEXT,
            ip TEXT, ua TEXT, referer TEXT,
            mail_status TEXT
        )""")
        conn.commit()
        return conn
    os.makedirs(DATA_DIR, exist_ok=True)
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("""CREATE TABLE IF NOT EXISTS bugs(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        created_at TEXT NOT NULL,
        page_key TEXT, page TEXT,
        device TEXT, "desc" TEXT,
        ip TEXT, ua TEXT, referer TEXT,
        mail_status TEXT
    )""")
    conn.commit()
    return conn


# ---------------------------------------------------------------- 邮件通知
def send_mail(cfg, row):
    """把一条反馈发到站长邮箱；失败只记录，不影响已入库的数据。"""
    smtp_cfg = cfg.get("smtp") or {}
    if not smtp_cfg.get("enabled"):
        return "disabled"
    if not smtp_cfg.get("password"):
        return "no-password"
    subject = "[BUG反馈] %s · #%d" % (row["page"] or "未指定页面", row["id"])
    body = "\n".join([
        "页面：%s（%s）" % (row["page"] or "-", row["page_key"] or "-"),
        "设备 / 浏览器：%s" % (row["device"] or "未填写"),
        "时间：%s" % row["created_at"],
        "IP：%s" % (row["ip"] or "-"),
        "",
        "问题描述：",
        row["desc"] or "-",
        "",
        "User-Agent：%s" % (row["ua"] or "-"),
        "来源页：%s" % (row["referer"] or "-"),
        "",
        "—— 由 GTA VI 查询站后端自动发送；后台可查看：/admin",
    ])
    msg = MIMEText(body, "plain", "utf-8")
    msg["Subject"] = Header(subject, "utf-8")
    msg["From"] = formataddr((str(Header(smtp_cfg.get("from_name", "GTA VI 查询站"), "utf-8")), smtp_cfg["username"]))
    msg["To"] = smtp_cfg.get("to") or smtp_cfg["username"]
    msg["Date"] = formatdate(localtime=False)
    try:
        if smtp_cfg.get("ssl", True):
            ctx = ssl.create_default_context()
            with smtplib.SMTP_SSL(smtp_cfg["host"], int(smtp_cfg["port"]), timeout=12, context=ctx) as s:
                s.login(smtp_cfg["username"], smtp_cfg["password"])
                s.sendmail(smtp_cfg["username"], [msg["To"]], msg.as_string())
        else:
            with smtplib.SMTP(smtp_cfg["host"], int(smtp_cfg["port"]), timeout=12) as s:
                s.ehlo()
                try:
                    s.starttls(context=ssl.create_default_context())
                    s.ehlo()
                except smtplib.SMTPException:
                    pass
                if smtp_cfg.get("password"):
                    s.login(smtp_cfg["username"], smtp_cfg["password"])
                s.sendmail(smtp_cfg["username"], [msg["To"]], msg.as_string())
        log("邮件已发送 #%d → %s" % (row["id"], msg["To"]))
        return "sent"
    except Exception as e:
        log("邮件发送失败 #%d：%s" % (row["id"], e))
        return "failed: %s" % str(e)[:120]


def notify_async(cfg, row):
    def run():
        status = send_mail(cfg, row)
        try:
            with _lock:
                conn = db()
                conn.execute("UPDATE bugs SET mail_status=? WHERE id=?", (status, row["id"]))
                conn.commit()
                conn.close()
        except Exception:
            log("回写邮件状态失败\n" + traceback.format_exc())
    threading.Thread(target=run, daemon=True).start()


# ---------------------------------------------------------------- 工具
def now_str():
    return datetime.now(TZ).strftime("%Y-%m-%d %H:%M:%S")


def clean(text, limit):
    if not isinstance(text, str):
        return ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text).strip()
    return text[:limit]


def check_rate(ip):
    stamps = _rate.setdefault(ip, [])
    now = time.time()
    day_ago = now - 86400
    stamps[:] = [t for t in stamps if t > day_ago]
    if stamps and now - stamps[-1] < RATE_GAP:
        return "太快了，%d 秒后再试" % int(RATE_GAP - (now - stamps[-1]))
    if len(stamps) >= RATE_DAY:
        return "今天提交太多次了，明天再来"
    stamps.append(now)
    return None



# ---------------------------------------------------------------- 账户系统
ACC_SCHEMA_PG = """
CREATE TABLE IF NOT EXISTS users(
  id SERIAL PRIMARY KEY,
  username TEXT NOT NULL UNIQUE,
  email TEXT NOT NULL UNIQUE,
  pass_hash TEXT NOT NULL,
  pass_salt TEXT NOT NULL,
  bio TEXT NOT NULL DEFAULT '',
  avatar TEXT NOT NULL DEFAULT '',
  banner TEXT NOT NULL DEFAULT '',
  role TEXT NOT NULL DEFAULT 'user',
  created_at TEXT NOT NULL,
  last_login TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS sessions(
  token_hash TEXT PRIMARY KEY,
  user_id INTEGER NOT NULL,
  created_at TEXT NOT NULL,
  ua TEXT,
  ip TEXT
);
CREATE TABLE IF NOT EXISTS codes(
  email TEXT NOT NULL,
  purpose TEXT NOT NULL,
  code TEXT NOT NULL,
  exp REAL NOT NULL,
  tries INTEGER NOT NULL DEFAULT 0,
  created_at TEXT NOT NULL,
  PRIMARY KEY(email, purpose)
);
CREATE TABLE IF NOT EXISTS profiles(
  user_id INTEGER PRIMARY KEY,
  data TEXT NOT NULL DEFAULT '{}',
  updated_at TEXT
);
CREATE INDEX IF NOT EXISTS idx_sessions_user ON sessions(user_id);
"""


def acc_db():
    """账户库：有 DATABASE_URL 走 Postgres，否则本地 SQLite。"""
    if IS_PG:
        conn = pg_connect()
        conn.executescript(ACC_SCHEMA_PG)
        conn.commit()
        return conn
    os.makedirs(DATA_DIR, exist_ok=True)
    conn = sqlite3.connect(ACC_DB_PATH, timeout=20)
    conn.row_factory = sqlite3.Row
    try:
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA busy_timeout=15000")
    except Exception:
        pass
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS users(
      id INTEGER PRIMARY KEY AUTOINCREMENT,
      username TEXT NOT NULL UNIQUE COLLATE NOCASE,
      email TEXT NOT NULL UNIQUE COLLATE NOCASE,
      pass_hash TEXT NOT NULL,
      pass_salt TEXT NOT NULL,
      bio TEXT NOT NULL DEFAULT '',
      avatar TEXT NOT NULL DEFAULT '',
      banner TEXT NOT NULL DEFAULT '',
      role TEXT NOT NULL DEFAULT 'user',
      created_at TEXT NOT NULL,
      last_login TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS sessions(
      token_hash TEXT PRIMARY KEY,
      user_id INTEGER NOT NULL,
      created_at TEXT NOT NULL,
      ua TEXT,
      ip TEXT
    );
    CREATE TABLE IF NOT EXISTS codes(
      email TEXT NOT NULL,
      purpose TEXT NOT NULL,
      code TEXT NOT NULL,
      exp REAL NOT NULL,
      tries INTEGER NOT NULL DEFAULT 0,
      created_at TEXT NOT NULL,
      PRIMARY KEY(email, purpose)
    );
    CREATE TABLE IF NOT EXISTS profiles(
      user_id INTEGER PRIMARY KEY,
      data TEXT NOT NULL DEFAULT '{}',
      updated_at TEXT
    );
    CREATE INDEX IF NOT EXISTS idx_sessions_user ON sessions(user_id);
    """)
    conn.commit()
    return conn


def hash_password(password, salt_hex=None):
    salt = bytes.fromhex(salt_hex) if salt_hex else secrets.token_bytes(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 120000)
    return dk.hex(), salt.hex()


def verify_password(password, salt_hex, want_hex):
    try:
        dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(salt_hex), 120000)
        return hmac.compare_digest(dk.hex(), want_hex)
    except Exception:
        return False


_auth_rate = {}                                # (ip, action) -> [时间戳...]
_login_fail = {}                               # 账号 -> {"n": 次数, "until": 锁定到}


def auth_rate_ok(key, gap=0, limit=0, window=3600):
    """简单滑动窗口限流：gap 为两次操作最小间隔，limit/window 为窗口内次数上限。"""
    now = time.time()
    stamps = _auth_rate.setdefault(key, [])
    stamps[:] = [t for t in stamps if t > now - window]
    if gap and stamps and now - stamps[-1] < gap:
        return False
    if limit and len(stamps) >= limit:
        return False
    stamps.append(now)
    return True


def smtp_send(cfg, to, subject, body):
    smtp_cfg = cfg.get("smtp") or {}
    if not smtp_cfg.get("enabled"):
        return "disabled"
    if not smtp_cfg.get("password"):
        return "no-password"
    msg = MIMEText(body, "plain", "utf-8")
    msg["Subject"] = Header(subject, "utf-8")
    msg["From"] = formataddr((str(Header(smtp_cfg.get("from_name", "GTA VI 查询站"), "utf-8")), smtp_cfg["username"]))
    msg["To"] = to
    msg["Date"] = formatdate(localtime=False)
    try:
        if smtp_cfg.get("ssl", True):
            ctx = ssl.create_default_context()
            with smtplib.SMTP_SSL(smtp_cfg["host"], int(smtp_cfg["port"]), timeout=15, context=ctx) as s:
                s.login(smtp_cfg["username"], smtp_cfg["password"])
                s.sendmail(smtp_cfg["username"], [to], msg.as_string())
        else:
            with smtplib.SMTP(smtp_cfg["host"], int(smtp_cfg["port"]), timeout=15) as s:
                s.ehlo()
                try:
                    s.starttls(context=ssl.create_default_context())
                    s.ehlo()
                except smtplib.SMTPException:
                    pass
                s.login(smtp_cfg["username"], smtp_cfg["password"])
                s.sendmail(smtp_cfg["username"], [to], msg.as_string())
        return "sent"
    except Exception as e:
        log("验证码邮件发送失败 → %s：%s" % (to, e))
        return "failed: %s" % str(e)[:160]


def issue_code(cfg, email, purpose):
    """生成并投递验证码。返回 (ok, payload, http_status)。"""
    email = (email or "").strip().lower()
    if not EMAIL_RE.match(email) or len(email) > 254:
        return False, {"ok": False, "error": "邮箱格式不对"}, 400
    if purpose not in ("register", "reset"):
        return False, {"ok": False, "error": "验证码用途不对"}, 400
    if purpose == "register" and not cfg.get("auth", {}).get("register_open", True):
        return False, {"ok": False, "error": "现在暂停注册"}, 403

    conn = acc_db()
    if purpose == "register":
        exists = conn.execute("SELECT 1 FROM users WHERE email=?", (email,)).fetchone()
        if exists:
            conn.close()
            return False, {"ok": False, "error": "这个邮箱已经注册过了，直接登录吧"}, 409
    else:
        exists = conn.execute("SELECT 1 FROM users WHERE email=?", (email,)).fetchone()
        if not exists:
            conn.close()
            return False, {"ok": False, "error": "这个邮箱还没有注册"}, 404

    old = conn.execute("SELECT created_at, exp FROM codes WHERE email=? AND purpose=?", (email, purpose)).fetchone()
    conn.close()
    now = time.time()
    gap = int(cfg.get("auth", {}).get("code_gap", 60))
    if old:
        try:
            last = datetime.strptime(old["created_at"], "%Y-%m-%d %H:%M:%S").replace(tzinfo=TZ).timestamp()
        except Exception:
            last = 0
        if now - last < gap:
            wait = int(gap - (now - last)) + 1
            return False, {"ok": False, "error": "发送太频繁，%d 秒后再试" % wait, "wait": wait}, 429

    code = "%06d" % (secrets.randbelow(900000) + 100000)
    ttl = int(cfg.get("auth", {}).get("code_ttl", 300))
    mail_status = smtp_send(cfg, email, "GTA VI 查询站 · 验证码", (
        "你正在%s。\n\n验证码：%s\n\n%d 分钟内有效。如果这不是你本人的操作，忽略这封邮件即可。\n\n—— GTA VI 查询站"
        % ("注册账号" if purpose == "register" else "重置密码", code, max(1, ttl // 60))
    ))
    if mail_status not in ("sent", "disabled", "no-password"):
        return False, {"ok": False, "error": "邮件发送失败，请稍后再试或换个邮箱"}, 502

    conn = acc_db()
    conn.execute(
        "INSERT INTO codes(email,purpose,code,exp,tries,created_at) VALUES(?,?,?,?,0,?) "
        "ON CONFLICT(email,purpose) DO UPDATE SET code=excluded.code, exp=excluded.exp, tries=0, created_at=excluded.created_at",
        (email, purpose, code, now + ttl, now_str()))
    conn.commit()
    conn.close()
    log("验证码已生成 purpose=%s email=%s mail=%s" % (purpose, email, mail_status))

    if mail_status != "sent" and not cfg.get("auth", {}).get("allow_dev_code", False):
        return False, {"ok": False, "error": "邮件没发出去：后端还没配好发信邮箱，请联系站长"}, 502
    payload = {"ok": True, "sent": mail_status == "sent", "ttl": ttl}
    if mail_status != "sent" and cfg.get("auth", {}).get("allow_dev_code", False):
        payload["dev_code"] = code
    return True, payload, 200


def make_session(user_id, ua="", ip=""):
    token = secrets.token_urlsafe(32)
    conn = acc_db()
    conn.execute("INSERT INTO sessions(token_hash,user_id,created_at,ua,ip) VALUES(?,?,?,?,?)",
                 (hashlib.sha256(token.encode()).hexdigest(), user_id, now_str(), clean(ua, 300), ip))
    conn.commit()
    conn.close()
    return token


def user_by_token(token):
    if not token:
        return None
    conn = acc_db()
    row = conn.execute(
        "SELECT u.* FROM sessions s JOIN users u ON u.id=s.user_id WHERE s.token_hash=?",
        (hashlib.sha256(token.encode()).hexdigest(),)).fetchone()
    conn.close()
    return row


def public_user(row, data=None):
    d = {"id": row["id"], "username": row["username"], "bio": row["bio"],
         "avatar": row["avatar"], "banner": row["banner"], "role": row["role"],
         "created_at": row["created_at"]}
    if data is not None:
        d["stats"] = profile_stats(data)
    return d


def profile_stats(data):
    try:
        favs = data.get("favs", {}) or {}
        prog = data.get("eggProgress", {}) or {}
        hist = data.get("history", []) or []
        return {"favNews": len(favs.get("news", []) or []), "favEggs": len(favs.get("eggs", []) or []),
                "eggDone": sum(1 for v in prog.values() if v), "history": len(hist)}
    except Exception:
        return {"favNews": 0, "favEggs": 0, "eggDone": 0, "history": 0}


def read_profile_data(user_id):
    conn = acc_db()
    row = conn.execute("SELECT data FROM profiles WHERE user_id=?", (user_id,)).fetchone()
    conn.close()
    if not row:
        return {}
    try:
        return json.loads(row["data"] or "{}")
    except Exception:
        return {}


# ---------------------------------------------------------------- HTTP
class Handler(BaseHTTPRequestHandler):
    server_version = "GTA6Hub/1.0"
    protocol_version = "HTTP/1.1"

    # ---- 通用响应
    def _send(self, code, body=b"", ctype="text/plain; charset=utf-8", extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def _json(self, code, obj, extra=None):
        self._send(code, json.dumps(obj, ensure_ascii=False), "application/json; charset=utf-8", extra)

    def _cors(self):
        return {
            "Access-Control-Allow-Origin": "*",
            "Access-Control-Allow-Methods": "GET, POST, PATCH, DELETE, OPTIONS",
            "Access-Control-Allow-Headers": "Content-Type, Authorization",
            "Access-Control-Max-Age": "600",
            "Access-Control-Allow-Private-Network": "true",   # 允许 file:// 打开时访问本地后端
        }

    def log_message(self, fmt, *args):
        pass                                  # 用自有日志，避免噪音

    # ---- 认证
    def _authed(self):
        cfg = self.server.cfg
        head = self.headers.get("Authorization", "")
        if not head.startswith("Basic "):
            return False
        try:
            raw = base64.b64decode(head[6:]).decode("utf-8", "replace")
            _, _, pw = raw.partition(":")
            return secrets.compare_digest(pw, cfg["admin_password"])
        except Exception:
            return False

    def _need_auth(self):
        body = "需要站长密码".encode("utf-8")
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="GTA VI Hub Admin", charset="UTF-8"')
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    # ---- 路由
    def do_OPTIONS(self):
        path = urllib.parse.urlparse(self.path).path
        if path.startswith("/api/"):
            self._send(204, b"", "text/plain", self._cors())
        else:
            self._send(404, "404")

    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        path = urllib.parse.urlparse(self.path).path
        if path == "/api/bug":
            return self._admin_json()
        if path == "/admin":
            return self._admin_page()
        if path == "/admin/export.csv":
            return self._admin_csv()
        if path == "/health":
            return self._json(200, {"ok": True, "time": now_str(), "auth": True}, self._cors())
        if path == "/api/me":
            return self._api_me()
        if path == "/api/me/data":
            return self._api_me_data()
        if path.startswith("/api/u/"):
            return self._api_public_user(urllib.parse.unquote(path[7:]))
        return self._static(path)

    def do_POST(self):
        path = urllib.parse.urlparse(self.path).path
        if path == "/api/bug":
            return self._submit()
        if path == "/admin/delete":
            return self._admin_delete()
        if path == "/api/auth/code":
            return self._api_auth_code()
        if path == "/api/auth/register":
            return self._api_auth_register()
        if path == "/api/auth/login":
            return self._api_auth_login()
        if path == "/api/auth/logout":
            return self._api_auth_logout()
        if path == "/api/auth/reset":
            return self._api_auth_reset()
        if path == "/api/auth/password":
            return self._api_auth_password()
        if path == "/api/me/data":
            return self._api_save_data()
        self._json(404, {"ok": False, "error": "not found"}, self._cors())

    def do_PATCH(self):
        path = urllib.parse.urlparse(self.path).path
        if path == "/api/me":
            return self._api_update_me()
        self._json(404, {"ok": False, "error": "not found"}, self._cors())

    def do_DELETE(self):
        self.do_OPTIONS()

    # ---- 账户 API
    def _body(self):
        try:
            length = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            length = 0
        if length <= 0 or length > MAX_BODY:
            return None
        try:
            data = json.loads(self.rfile.read(length).decode("utf-8"))
        except Exception:
            return None
        return data if isinstance(data, dict) else None

    def _token(self):
        head = self.headers.get("Authorization", "")
        return head[7:].strip() if head.lower().startswith("bearer ") else ""

    def _me_row(self):
        return user_by_token(self._token())

    def _ip(self):
        return (self.headers.get("X-Forwarded-For", "").split(",")[0].strip() or self.client_address[0])

    def _api_me(self):
        row = self._me_row()
        if not row:
            return self._json(401, {"ok": False, "error": "未登录"}, self._cors())
        data = read_profile_data(row["id"])
        return self._json(200, {"ok": True, "user": public_user(row, data)}, self._cors())

    def _api_me_data(self):
        row = self._me_row()
        if not row:
            return self._json(401, {"ok": False, "error": "未登录"}, self._cors())
        data = read_profile_data(row["id"])
        return self._json(200, {"ok": True, "data": data, "stats": profile_stats(data)}, self._cors())

    def _api_public_user(self, name):
        name = (name or "").strip()
        if not name:
            return self._json(404, {"ok": False, "error": "用户不存在"}, self._cors())
        conn = acc_db()
        row = conn.execute("SELECT * FROM users WHERE username=?", (name,)).fetchone()
        conn.close()
        if not row:
            return self._json(404, {"ok": False, "error": "用户不存在"}, self._cors())
        data = read_profile_data(row["id"])
        return self._json(200, {"ok": True, "user": public_user(row, data)}, self._cors())

    def _api_auth_code(self):
        payload = self._body()
        if not payload:
            return self._json(400, {"ok": False, "error": "请求格式不对"}, self._cors())
        email = clean(payload.get("email"), 254).lower()
        purpose = "reset" if payload.get("purpose") == "reset" else "register"
        ip = self._ip()
        if not auth_rate_ok("code:" + ip, gap=8, limit=30, window=3600):
            return self._json(429, {"ok": False, "error": "操作太频繁，稍后再试"}, self._cors())
        ok, out, status = issue_code(self.server.cfg, email, purpose)
        self._json(status, out, self._cors())

    def _api_auth_register(self):
        payload = self._body()
        if not payload:
            return self._json(400, {"ok": False, "error": "请求格式不对"}, self._cors())
        cfg = self.server.cfg
        if not cfg.get("auth", {}).get("register_open", True):
            return self._json(403, {"ok": False, "error": "现在暂停注册"}, self._cors())
        ip = self._ip()
        if not auth_rate_ok("reg:" + ip, gap=5, limit=12, window=3600):
            return self._json(429, {"ok": False, "error": "注册太频繁，稍后再试"}, self._cors())

        username = clean(payload.get("username"), 24)
        email = clean(payload.get("email"), 254).lower()
        code = clean(payload.get("code"), 12)
        password = payload.get("password") if isinstance(payload.get("password"), str) else ""

        if not USERNAME_RE.match(username):
            return self._json(400, {"ok": False, "error": "用户名需 2–16 位，只能用中文、字母、数字或下划线"}, self._cors())
        if username.lower() in RESERVED_NAMES:
            return self._json(400, {"ok": False, "error": "这个用户名不可用"}, self._cors())
        if not EMAIL_RE.match(email):
            return self._json(400, {"ok": False, "error": "邮箱格式不对"}, self._cors())
        if not (8 <= len(password) <= 72):
            return self._json(400, {"ok": False, "error": "密码长度需在 8–72 位之间"}, self._cors())
        if not re.match(r"^\d{6}$", code):
            return self._json(400, {"ok": False, "error": "验证码是 6 位数字"}, self._cors())

        conn = acc_db()
        dup_user = conn.execute("SELECT 1 FROM users WHERE username=?", (username,)).fetchone()
        dup_mail = conn.execute("SELECT 1 FROM users WHERE email=?", (email,)).fetchone()
        if dup_user or dup_mail:
            conn.close()
            return self._json(409, {"ok": False, "error": "用户名或邮箱已被使用"}, self._cors())
        row = conn.execute("SELECT * FROM codes WHERE email=? AND purpose='register'", (email,)).fetchone()
        if not row or row["exp"] < time.time():
            conn.close()
            return self._json(400, {"ok": False, "error": "验证码已过期，请重新获取"}, self._cors())
        if row["tries"] >= 5:
            conn.close()
            return self._json(429, {"ok": False, "error": "验证码错误次数过多，请重新获取"}, self._cors())
        if not hmac.compare_digest(str(row["code"]), code):
            conn.execute("UPDATE codes SET tries=tries+1 WHERE email=? AND purpose='register'", (email,))
            conn.commit()
            conn.close()
            return self._json(400, {"ok": False, "error": "验证码不正确"}, self._cors())

        ph, ps = hash_password(password)
        now = now_str()
        uid = insert_id(conn,
            "INSERT INTO users(username,email,pass_hash,pass_salt,bio,avatar,banner,role,created_at,last_login)"
            " VALUES(?,?,?,?,?,'','','user',?,?)",
            (username, email, ph, ps, "", now, now))
        conn.execute("INSERT INTO profiles(user_id,data,updated_at) VALUES(?,?,?) "
                     "ON CONFLICT(user_id) DO UPDATE SET data=excluded.data, updated_at=excluded.updated_at",
                     (uid, "{}", now))
        conn.execute("DELETE FROM codes WHERE email=? AND purpose='register'", (email,))
        conn.commit()
        conn.close()
        token = make_session(uid, self.headers.get("User-Agent", ""), ip)
        log("新用户注册 #%d %s" % (uid, username))
        self._json(200, {"ok": True, "token": token, "user": {"id": uid, "username": username, "email": email,
                                                              "bio": "", "avatar": "", "banner": "", "role": "user",
                                                              "created_at": now}}, self._cors())

    def _api_auth_login(self):
        payload = self._body()
        if not payload:
            return self._json(400, {"ok": False, "error": "请求格式不对"}, self._cors())
        account = clean(payload.get("account"), 254)
        password = payload.get("password") if isinstance(payload.get("password"), str) else ""
        ip = self._ip()
        if not auth_rate_ok("login:" + ip, limit=60, window=600):
            return self._json(429, {"ok": False, "error": "尝试太频繁，稍后再试"}, self._cors())
        if not account or not password:
            return self._json(400, {"ok": False, "error": "请输入账号和密码"}, self._cors())
        key = account.lower()
        locked = _login_fail.get(key)
        if locked and locked["n"] >= 5 and locked["until"] > time.time():
            wait = int(locked["until"] - time.time()) + 1
            return self._json(429, {"ok": False, "error": "密码错误次数过多，%d 秒后再试" % wait}, self._cors())
        conn = acc_db()
        row = conn.execute("SELECT * FROM users WHERE username=? OR email=?", (account, account.lower())).fetchone()
        conn.close()
        if not row:
            hash_password(password)                       # 恒定时间，避免暴露账号是否存在
            return self._login_fail_now(key)
        if not verify_password(password, row["pass_salt"], row["pass_hash"]):
            return self._login_fail_now(key)
        _login_fail.pop(key, None)
        conn = acc_db()
        conn.execute("UPDATE users SET last_login=? WHERE id=?", (now_str(), row["id"]))
        conn.commit()
        conn.close()
        token = make_session(row["id"], self.headers.get("User-Agent", ""), ip)
        log("用户登录 #%d %s" % (row["id"], row["username"]))
        self._json(200, {"ok": True, "token": token, "user": {"id": row["id"], "username": row["username"],
                                                              "email": row["email"], "bio": row["bio"],
                                                              "avatar": row["avatar"], "banner": row["banner"],
                                                              "role": row["role"], "created_at": row["created_at"]}}, self._cors())

    def _login_fail_now(self, key):
        rec = _login_fail.setdefault(key, {"n": 0, "until": 0})
        rec["n"] += 1
        if rec["n"] >= 5:
            rec["until"] = time.time() + 900          # 连错 5 次，锁 15 分钟
        return self._json(401, {"ok": False, "error": "账号或密码不正确"}, self._cors())

    def _api_auth_logout(self):
        token = self._token()
        if token:
            conn = acc_db()
            conn.execute("DELETE FROM sessions WHERE token_hash=?", (hashlib.sha256(token.encode()).hexdigest(),))
            conn.commit()
            conn.close()
        self._json(200, {"ok": True}, self._cors())

    def _api_auth_reset(self):
        payload = self._body()
        if not payload:
            return self._json(400, {"ok": False, "error": "请求格式不对"}, self._cors())
        email = clean(payload.get("email"), 254).lower()
        code = clean(payload.get("code"), 12)
        password = payload.get("password") if isinstance(payload.get("password"), str) else ""
        if not EMAIL_RE.match(email):
            return self._json(400, {"ok": False, "error": "邮箱格式不对"}, self._cors())
        if not (8 <= len(password) <= 72):
            return self._json(400, {"ok": False, "error": "密码长度需在 8–72 位之间"}, self._cors())
        conn = acc_db()
        row = conn.execute("SELECT * FROM codes WHERE email=? AND purpose='reset'", (email,)).fetchone()
        user = conn.execute("SELECT * FROM users WHERE email=?", (email,)).fetchone()
        if not user:
            conn.close()
            return self._json(404, {"ok": False, "error": "这个邮箱还没有注册"}, self._cors())
        if not row or row["exp"] < time.time():
            conn.close()
            return self._json(400, {"ok": False, "error": "验证码已过期，请重新获取"}, self._cors())
        if row["tries"] >= 5 or not hmac.compare_digest(str(row["code"]), code):
            conn.execute("UPDATE codes SET tries=tries+1 WHERE email=? AND purpose='reset'", (email,))
            conn.commit()
            conn.close()
            return self._json(400, {"ok": False, "error": "验证码不正确"}, self._cors())
        ph, ps = hash_password(password)
        conn.execute("UPDATE users SET pass_hash=?, pass_salt=? WHERE id=?", (ph, ps, user["id"]))
        conn.execute("DELETE FROM codes WHERE email=? AND purpose='reset'", (email,))
        conn.execute("DELETE FROM sessions WHERE user_id=?", (user["id"],))
        conn.commit()
        conn.close()
        log("用户重置密码 #%d" % user["id"])
        self._json(200, {"ok": True}, self._cors())

    def _api_auth_password(self):
        row = self._me_row()
        if not row:
            return self._json(401, {"ok": False, "error": "未登录"}, self._cors())
        payload = self._body()
        if not payload:
            return self._json(400, {"ok": False, "error": "请求格式不对"}, self._cors())
        old = payload.get("old") if isinstance(payload.get("old"), str) else ""
        new = payload.get("new") if isinstance(payload.get("new"), str) else ""
        if not (8 <= len(new) <= 72):
            return self._json(400, {"ok": False, "error": "新密码长度需在 8–72 位之间"}, self._cors())
        if not verify_password(old, row["pass_salt"], row["pass_hash"]):
            return self._json(400, {"ok": False, "error": "当前密码不正确"}, self._cors())
        ph, ps = hash_password(new)
        conn = acc_db()
        conn.execute("UPDATE users SET pass_hash=?, pass_salt=? WHERE id=?", (ph, ps, row["id"]))
        conn.commit()
        conn.close()
        self._json(200, {"ok": True}, self._cors())

    def _api_update_me(self):
        row = self._me_row()
        if not row:
            return self._json(401, {"ok": False, "error": "未登录"}, self._cors())
        payload = self._body()
        if not payload:
            return self._json(400, {"ok": False, "error": "请求格式不对"}, self._cors())
        bio = clean(payload.get("bio"), 120)
        avatar = clean(payload.get("avatar"), 2000)
        banner = clean(payload.get("banner"), 2000)
        conn = acc_db()
        conn.execute("UPDATE users SET bio=?, avatar=?, banner=? WHERE id=?", (bio, avatar, banner, row["id"]))
        conn.commit()
        conn.close()
        log("更新资料 #%d %s" % (row["id"], row["username"]))
        self._json(200, {"ok": True, "user": {"id": row["id"], "username": row["username"], "email": row["email"],
                                              "bio": bio, "avatar": avatar, "banner": banner,
                                              "role": row["role"], "created_at": row["created_at"]}}, self._cors())

    def _api_save_data(self):
        row = self._me_row()
        if not row:
            return self._json(401, {"ok": False, "error": "未登录"}, self._cors())
        payload = self._body()
        if not payload:
            return self._json(400, {"ok": False, "error": "请求格式不对"}, self._cors())
        data = payload.get("data")
        if not isinstance(data, dict):
            return self._json(400, {"ok": False, "error": "数据格式不对"}, self._cors())
        raw = json.dumps(data, ensure_ascii=False)
        if len(raw) > 96 * 1024:
            return self._json(413, {"ok": False, "error": "数据太大了"}, self._cors())
        conn = acc_db()
        conn.execute("INSERT INTO profiles(user_id,data,updated_at) VALUES(?,?,?) "
                     "ON CONFLICT(user_id) DO UPDATE SET data=excluded.data, updated_at=excluded.updated_at",
                     (row["id"], raw, now_str()))
        conn.commit()
        conn.close()
        self._json(200, {"ok": True, "stats": profile_stats(data)}, self._cors())

    # ---- 静态文件
    def _static(self, path):
        if path in ("/", "/index.html"):
            rel = SITE_FILE
        else:
            rel = urllib.parse.unquote(path.lstrip("/"))
        full = os.path.normpath(os.path.join(BASE_DIR, rel))
        if not full.startswith(BASE_DIR) or not os.path.isfile(full):
            return self._send(404, "404 Not Found")
        ext = os.path.splitext(full)[1].lower()
        ctype = {
            ".html": "text/html; charset=utf-8",
            ".css": "text/css; charset=utf-8",
            ".js": "application/javascript; charset=utf-8",
            ".json": "application/json; charset=utf-8",
            ".webp": "image/webp", ".png": "image/png", ".jpg": "image/jpeg",
            ".jpeg": "image/jpeg", ".svg": "image/svg+xml", ".ico": "image/x-icon",
        }.get(ext, "application/octet-stream")
        try:
            with open(full, "rb") as f:
                data = f.read()
        except Exception as e:
            return self._send(500, "读取文件失败：%s" % e)
        self._send(200, data, ctype)

    # ---- 提交反馈
    def _submit(self):
        try:
            length = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            length = 0
        if length <= 0 or length > MAX_BODY:
            return self._json(413, {"ok": False, "error": "请求体过大或为空"}, self._cors())
        raw = self.rfile.read(length)
        try:
            payload = json.loads(raw.decode("utf-8"))
        except Exception:
            return self._json(400, {"ok": False, "error": "不是合法 JSON"}, self._cors())
        if not isinstance(payload, dict):
            return self._json(400, {"ok": False, "error": "格式不对"}, self._cors())

        if str(payload.get("hp") or "").strip():           # 蜜罐：机器人填了隐藏字段
            return self._json(200, {"ok": True, "id": 0, "mail": "ignored"}, self._cors())

        desc = clean(payload.get("desc"), 600)
        if len(desc) < 4:
            return self._json(400, {"ok": False, "error": "问题描述太短（至少 4 个字）"}, self._cors())

        page_key = clean(payload.get("page_key"), 12) or "home"
        page = PAGES.get(page_key) or clean(payload.get("page"), 24) or "首页"
        device = clean(payload.get("device"), 80)
        ip = (self.headers.get("X-Forwarded-For", "").split(",")[0].strip() or self.client_address[0])
        ua = clean(self.headers.get("User-Agent"), 300)
        referer = clean(payload.get("href") or self.headers.get("Referer"), 300)

        with _lock:
            wait = check_rate(ip)
        if wait:
            return self._json(429, {"ok": False, "error": wait}, self._cors())

        conn = db()
        rid = insert_id(conn,
            "INSERT INTO bugs(created_at,page_key,page,device,\"desc\",ip,ua,referer,mail_status)"
            " VALUES(?,?,?,?,?,?,?,?,?)",
            (now_str(), page_key, page, device, desc, ip, ua, referer, "pending"))
        conn.commit()
        conn.close()
        log("新反馈 #%d 页面=%s 设备=%s" % (rid, page, device or "-"))
        notify_async(self.server.cfg, {"id": rid, "page": page, "page_key": page_key,
                                       "device": device, "desc": desc, "ip": ip,
                                       "ua": ua, "referer": referer, "created_at": now_str()})
        mail_note = "邮件将发往 %s" % (self.server.cfg["smtp"].get("to") or "")
        if not self.server.cfg["smtp"].get("password"):
            mail_note = "已保存到后台（未配置 SMTP 授权码，暂不发邮件）"
        self._json(200, {"ok": True, "id": rid, "mail": mail_note}, self._cors())

    # ---- 后台
    def _rows(self, limit=200):
        conn = db()
        rows = conn.execute("SELECT * FROM bugs ORDER BY id DESC LIMIT ?", (limit,)).fetchall()
        conn.close()
        return rows

    def _admin_json(self):
        if not self._authed():
            return self._need_auth()
        rows = [dict(r) for r in self._rows()]
        self._json(200, {"ok": True, "count": len(rows), "items": rows})

    def _admin_csv(self):
        if not self._authed():
            return self._need_auth()
        import csv
        buf = io.StringIO()
        w = csv.writer(buf)
        w.writerow(["id", "时间", "页面", "设备", "描述", "IP", "UA", "来源", "邮件状态"])
        for r in self._rows(5000):
            w.writerow([r["id"], r["created_at"], r["page"], r["device"], r["desc"],
                        r["ip"], r["ua"], r["referer"], r["mail_status"]])
        data = "\ufeff" + buf.getvalue()
        self.send_response(200)
        self.send_header("Content-Type", "text/csv; charset=utf-8")
        self.send_header("Content-Disposition",
                         'attachment; filename="bugs-%s.csv"' % datetime.now(TZ).strftime("%Y%m%d-%H%M"))
        body = data.encode("utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _admin_delete(self):
        if not self._authed():
            return self._need_auth()
        try:
            length = int(self.headers.get("Content-Length") or 0)
            payload = json.loads(self.rfile.read(min(length, 4096)).decode("utf-8") or "{}")
            rid = int(payload.get("id"))
        except Exception:
            return self._json(400, {"ok": False, "error": "id 不合法"})
        conn = db()
        conn.execute("DELETE FROM bugs WHERE id=?", (rid,))
        conn.commit()
        conn.close()
        self._json(200, {"ok": True})

    def _admin_page(self):
        if not self._authed():
            return self._need_auth()
        rows = self._rows()
        cfg = self.server.cfg
        smtp_state = "已配置（%s）" % cfg["smtp"].get("to") if cfg["smtp"].get("password") else "未配置授权码，仅存本机"
        tr = []
        for r in rows:
            tr.append(
                "<tr><td>#{id}</td><td>{t}</td><td>{p}</td><td>{d}</td><td class='desc'>{desc}</td>"
                "<td>{m}</td><td><button onclick='del({id})'>删除</button></td></tr>".format(
                    id=r["id"], t=html.escape(r["created_at"]), p=html.escape(r["page"] or "-"),
                    d=html.escape(r["device"] or "-"), desc=html.escape(r["desc"] or ""),
                    m=html.escape(r["mail_status"] or "")))
        page = """<!doctype html><html lang="zh-CN"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>GTA VI 查询站 · 后台</title>
<style>
:root{--bg:#0b0b10;--s:#15151d;--l:#ffffff1a;--t:#f2f2f7;--m:#8b8b99;--p:#ff4b8c}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--t);font:14px/1.6 -apple-system,"PingFang SC","Microsoft YaHei",sans-serif}
.wrap{max-width:1180px;margin:0 auto;padding:26px 20px 60px}
h1{font-size:22px;margin:0 0 6px}p.sub{color:var(--m);margin:0 0 18px}
.bar{display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin-bottom:16px}
a.btn,button{background:#1f1f2a;color:var(--t);border:1px solid var(--l);border-radius:999px;padding:9px 16px;font-weight:700;font-size:13px;text-decoration:none;cursor:pointer}
a.btn:hover,button:hover{border-color:var(--p);color:var(--p)}
table{width:100%;border-collapse:collapse;background:var(--s);border:1px solid var(--l);border-radius:14px;overflow:hidden}
th,td{padding:10px 12px;text-align:left;border-bottom:1px solid var(--l);font-size:13px;vertical-align:top}
th{font-size:11px;letter-spacing:.1em;color:var(--m);text-transform:uppercase}
td.desc{max-width:520px;white-space:pre-wrap}
tr:last-child td{border-bottom:0}
.empty{padding:40px;text-align:center;color:var(--m)}
@media(max-width:720px){td.desc{max-width:220px}}
</style>
<div class="wrap">
<h1>BUG 反馈后台</h1>
<p class="sub">共 __COUNT__ 条 · 邮件通知：__SMTP__</p>
<div class="bar"><a class="btn" href="/">打开网站</a><a class="btn" href="/admin/export.csv">导出 CSV</a>
<a class="btn" href="/admin">刷新</a><a class="btn" href="/health">自检</a><span class="sub">数据文件：data/bugs.db</span></div>
__TABLE__
</div>
<script>
function del(id){ if(!confirm('删除 #'+id+' ？'))return;
  fetch('/admin/delete',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id})})
   .then(r=>r.json()).then(()=>location.reload()); }
</script></html>"""
        table = ("<table><tr><th>ID</th><th>时间</th><th>页面</th><th>设备</th><th>描述</th><th>邮件</th><th></th></tr>"
                 + "".join(tr) + "</table>") if rows else "<div class='empty'>还没有反馈。把你的 BUG 反馈表单发给朋友试试。</div>"
        page = (page.replace("__COUNT__", str(len(rows)))
                    .replace("__SMTP__", html.escape(smtp_state))
                    .replace("__TABLE__", table))
        self._send(200, page, "text/html; charset=utf-8")


def main():
    cfg = load_config()
    os.makedirs(DATA_DIR, exist_ok=True)
    db().close()
    acc_db().close()
    srv = ThreadingHTTPServer((cfg.get("host", "0.0.0.0"), int(cfg.get("port", 8000))), Handler)
    srv.cfg = cfg
    log("=" * 60)
    log("GTA VI 查询站后端已启动")
    log("网站： http://localhost:%d/" % int(cfg["port"]))
    log("后台： http://localhost:%d/admin   （密码：%s）" % (int(cfg["port"]), cfg["admin_password"]))
    log("SMTP：%s" % ("已配置 → " + (cfg["smtp"].get("to") or cfg["smtp"].get("username", ""))
                     if cfg["smtp"].get("password") else "未配置授权码 —— 注册时会提示「邮件没发出去」"))
    log("账户：注册%s · 数据文件 data/accounts.db" % ("开放" if cfg.get("auth", {}).get("register_open", True) else "已关闭"))
    log("=" * 60)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        log("已停止")


if __name__ == "__main__":
    main()
