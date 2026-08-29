#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import re
import json
import time
import threading
import html as html_lib
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import requests
try:
    import urllib3
    urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
except Exception:
    pass
import os
import sqlite3
from datetime import datetime, date, timedelta, timezone
from flask import Flask, jsonify, request, render_template_string, Response
from flask_cors import CORS
from werkzeug.serving import make_server

# ⭐ 时区修复：服务器是 UTC，全部时间显示用北京时间（UTC+8）
CN_TZ = timezone(timedelta(hours=8))
def now_cn():
    """返回当前北京时间（naive datetime，便于和现有 strftime 兼容）"""
    return datetime.now(CN_TZ).replace(tzinfo=None)

# ══════════════════════════════════════════════════════════════
#  全局配置
# ══════════════════════════════════════════════════════════════
# 🔀 平台切换：PLATFORM=shitoud (默认 石头岛) 或 PLATFORM=jingyu (鲸鱼)
# 启动命令示例：PLATFORM=jingyu python3 app.py
PLATFORM = os.environ.get("PLATFORM", "shitoud").strip().lower()
if PLATFORM not in ("shitoud", "jingyu"):
    print(f"⚠️ 未知 PLATFORM={PLATFORM!r}，已 fallback 到 shitoud")
    PLATFORM = "shitoud"
IS_JINGYU  = (PLATFORM == "jingyu")
IS_SHITOUD = (PLATFORM == "shitoud")
PLATFORM_NAME  = "鲸鱼"  if IS_JINGYU else "石头岛"
PLATFORM_EMOJI = "🐋"    if IS_JINGYU else "🪨"

# 🐋 鲸鱼 API 是自签名证书：全局关闭 requests 证书校验 + 静音警告。
# 石头岛证书正常，不受影响。ponytail: 全局 patch 省去逐个请求点加 verify=False；
# 若将来鲸鱼换成正规证书，删掉这段即可。
if IS_JINGYU:
    import functools, urllib3
    urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
    _req_get, _req_post = requests.get, requests.post
    def _no_verify(fn):
        @functools.wraps(fn)
        def w(*a, **k):
            k.setdefault("verify", False)
            return fn(*a, **k)
        return w
    requests.get, requests.post = _no_verify(_req_get), _no_verify(_req_post)

ADMIN_DEV_PASSWORD = "Bbin123456@"
# BASE_DIR 自动跟随 app.py 所在目录（避免硬编码路径带来的迁移坑）
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CLIENTS_FILE = f"{BASE_DIR}/clients.json"
ADMIN_ACCOUNTS_FILE = f"{BASE_DIR}/accounts.json"

SHUNZI_GROUPS = [
    "123","321","234","432","345","543","456","654",
    "567","765","678","876","789","987",
    "358","853","147","471","741","369","963",
    "579","975","479","974","468","864",
]

def build_pairs():
    pairs = set()
    for grp in SHUNZI_GROUPS:
        digits = [int(c) for c in grp]
        for i in range(len(digits)):
            for j in range(len(digits)):
                if i != j:
                    pairs.add((digits[i], digits[j]))
    return pairs

SHUNZI_PAIRS = build_pairs()
FIXED_SUMS = {1,2,3,4,5,6,7,8,9,16,17,18,19,20,21,22,23,24,25,26}

# 🔀 平台相关常量
if IS_JINGYU:
    STD_API = "https://api.nihangzhu.cn"
    STD_HEADERS_BASE = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
        "Content-Type": "application/json",
    }
    JINGYU_GAME_ID = {210: 2, 60: 3}   # 鲸鱼 game_id 映射
else:
    STD_API = "https://api.shitoudao.com"
    STD_HEADERS_BASE = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/148.0.0.0 Safari/537.36",
        "Referer": "https://shitoudao.com/",
        "Content-Type": "application/json",
    }
    JINGYU_GAME_ID = {210: 210, 60: 60}  # 石头岛直接用 style 当 game_id
JINGYU_PERIOD = {210: 210, 60: 60}
FETCH_URL = "https://www.app.com"  # 保留兼容（已不使用）
HEADERS_28 = STD_HEADERS_BASE
# ⭐ 赔率表 = 官方理论赔率 × 0.98（石头岛固定抽 2% 水），实测精确对齐
ODDS_TABLE = {
    0:979.99,1:326.66,2:163.33,3:98.00,4:65.32,5:46.65,
    6:34.99,7:27.21,8:21.77,9:17.81,10:15.55,11:14.20,
    12:13.41,13:13.03,14:13.03,15:13.41,16:14.20,17:15.55,
    18:17.81,19:21.77,20:27.21,21:34.99,22:46.65,23:65.32,
    24:98.00,25:163.33,26:326.66,27:979.99
}

# ══════════════════════════════════════════════════════════════
#  模拟下单引擎
# ══════════════════════════════════════════════════════════════
import random

def sim_calc_pnl(positions, result_sum, base_amount, multiplier):
    """计算单期模拟盈亏：中了返回净盈利（含回本），不中返回负投入"""
    bet_amount = base_amount * multiplier
    inv = {p: 1.0 / ODDS_TABLE[p] for p in positions}
    total_inv = sum(inv.values())
    alloc = {p: bet_amount * inv[p] / total_inv for p in positions}
    if result_sum in positions:
        win_return = alloc[result_sum] * ODDS_TABLE[result_sum]
        net = win_return - bet_amount
        return True, net, bet_amount
    else:
        return False, -bet_amount, bet_amount

def sim_parse_groups(text):
    """解析下注数字组，每行一组，-分隔，返回 list of list[int]"""
    groups = []
    for line in text.strip().split('\n'):
        line = line.strip()
        if not line:
            continue
        nums = []
        for part in line.split('-'):
            part = part.strip()
            if part.isdigit():
                n = int(part)
                if 0 <= n <= 27:
                    nums.append(n)
        if nums:
            groups.append(list(set(nums)))
    return groups

def sim_parse_multipliers(text):
    """解析倍数序列，-分隔"""
    muls = []
    for part in text.strip().split('-'):
        part = part.strip()
        try:
            muls.append(float(part))
        except:
            pass
    return muls if muls else [1.0]




# ══════════════════════════════════════════════════════════════
#  模拟下单历史数据库（SQLite，30天持久化）
# ══════════════════════════════════════════════════════════════
class SimHistoryDB:
    """每组结束时写入SQLite，保留30天，每小时清理过期数据"""
    DB_PATH = f"{BASE_DIR}/sim_history.db"

    def __init__(self):
        self.lock = threading.Lock()
        self._init_db()
        threading.Thread(target=self._cleanup_loop, daemon=True).start()

    def _conn(self):
        conn = sqlite3.connect(self.DB_PATH, timeout=10)
        conn.row_factory = sqlite3.Row
        return conn

    def _init_db(self):
        with self._conn() as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS sim_groups (
                    id          INTEGER PRIMARY KEY AUTOINCREMENT,
                    date        TEXT NOT NULL,
                    engine      TEXT NOT NULL,
                    style       INTEGER NOT NULL,
                    mode        TEXT NOT NULL,
                    rounds_json TEXT NOT NULL,
                    total_cost  INTEGER NOT NULL DEFAULT 0,
                    group_pnl   INTEGER NOT NULL DEFAULT 0,
                    ended       INTEGER NOT NULL DEFAULT 1,
                    exhausted   INTEGER NOT NULL DEFAULT 0,
                    created_at  TEXT NOT NULL
                )
            """)
            conn.execute("CREATE INDEX IF NOT EXISTS idx_sg_engine ON sim_groups(engine, style, mode, date)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_sg_date   ON sim_groups(date)")
            # 真实下单记录表（功能2：账号最新2期下单详情）
            conn.execute("""
                CREATE TABLE IF NOT EXISTS real_orders (
                    id          INTEGER PRIMARY KEY AUTOINCREMENT,
                    username    TEXT NOT NULL,
                    uid         TEXT NOT NULL,
                    tel         TEXT NOT NULL,
                    style       INTEGER NOT NULL,
                    qishu       TEXT NOT NULL,
                    press_str   TEXT NOT NULL,
                    bet_amount  INTEGER NOT NULL DEFAULT 0,
                    ok          INTEGER NOT NULL DEFAULT 0,
                    msg         TEXT NOT NULL DEFAULT '',
                    created_at  TEXT NOT NULL,
                    source      TEXT NOT NULL DEFAULT 'normal'
                )
            """)
            conn.execute("CREATE INDEX IF NOT EXISTS idx_ro_user ON real_orders(username, uid, style)")
            # 兼容老表：如果旧版本表没有 source 列，加上
            try:
                conn.execute("ALTER TABLE real_orders ADD COLUMN source TEXT NOT NULL DEFAULT 'normal'")
                print("[SimHistoryDB] real_orders 表新增 source 列")
            except sqlite3.OperationalError:
                pass  # 列已存在
            # 开奖结果持久化（避免每次查询都重算 + 解决"内存 history 不够 200 期"问题）
            for col_def in (
                "result INTEGER",          # 开奖号码 0-27；NULL 表示未结算
                "win_amount INTEGER",      # 中奖金额；NULL 表示未结算
                "settled_at TEXT",         # 结算时间字符串；NULL 表示未结算
            ):
                col_name = col_def.split()[0]
                try:
                    conn.execute(f"ALTER TABLE real_orders ADD COLUMN {col_def}")
                    print(f"[SimHistoryDB] real_orders 表新增 {col_name} 列")
                except sqlite3.OperationalError:
                    pass
            # 索引：未结算行扫描用
            try:
                conn.execute("CREATE INDEX IF NOT EXISTS idx_ro_pending ON real_orders(style, settled_at, qishu)")
            except Exception:
                pass
            conn.commit()

    def save_group(self, engine_name, style, mode, group_dict):
        """组结束时调用，写入一条完整组记录"""
        today = now_cn().strftime("%Y-%m-%d")
        rounds_json = json.dumps(group_dict.get("rounds", []), ensure_ascii=False)
        try:
            with self.lock:
                with self._conn() as conn:
                    conn.execute("""
                        INSERT INTO sim_groups
                            (date, engine, style, mode, rounds_json, total_cost, group_pnl, ended, exhausted, created_at)
                        VALUES (?,?,?,?,?,?,?,?,?,?)
                    """, (
                        today, engine_name, style, mode,
                        rounds_json,
                        group_dict.get("total_cost", 0),
                        group_dict.get("group_pnl", 0),
                        1 if group_dict.get("ended") else 0,
                        1 if group_dict.get("exhausted") else 0,
                        now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                    ))
                    conn.commit()
        except Exception as e:
            print(f"[SimHistoryDB.save_group] {e}")

    def query_groups(self, engine_name, style, mode, date_str=None, limit=200):
        """查询历史组记录，默认查今天"""
        if date_str is None:
            date_str = now_cn().strftime("%Y-%m-%d")
        try:
            with self.lock:
                with self._conn() as conn:
                    rows = conn.execute("""
                        SELECT * FROM sim_groups
                        WHERE engine=? AND style=? AND mode=? AND date=?
                        ORDER BY id DESC LIMIT ?
                    """, (engine_name, style, mode, date_str, limit)).fetchall()
            result = []
            for row in rows:
                g = dict(row)
                g["rounds"] = json.loads(g.pop("rounds_json", "[]"))
                g["ended"]    = bool(g["ended"])
                g["exhausted"] = bool(g["exhausted"])
                result.append(g)
            return result
        except Exception as e:
            print(f"[SimHistoryDB.query_groups] {e}")
            return []

    def get_dates(self, engine_name, style, mode):
        """获取有记录的日期列表"""
        try:
            with self.lock:
                with self._conn() as conn:
                    rows = conn.execute("""
                        SELECT DISTINCT date FROM sim_groups
                        WHERE engine=? AND style=? AND mode=?
                        ORDER BY date DESC LIMIT 30
                    """, (engine_name, style, mode)).fetchall()
            return [r["date"] for r in rows]
        except Exception as e:
            print(f"[SimHistoryDB.get_dates] {e}")
            return []

    def daily_pnl(self, engine_name, style, mode, date_str=None):
        """查指定日期的总盈亏（只统计已结束的组）"""
        if date_str is None:
            date_str = now_cn().strftime("%Y-%m-%d")
        try:
            with self.lock:
                with self._conn() as conn:
                    row = conn.execute("""
                        SELECT COALESCE(SUM(group_pnl),0) as total
                        FROM sim_groups
                        WHERE engine=? AND style=? AND mode=? AND date=? AND ended=1
                    """, (engine_name, style, mode, date_str)).fetchone()
            return row["total"] if row else 0
        except Exception as e:
            print(f"[SimHistoryDB.daily_pnl] {e}")
            return 0

    def save_real_order(self, username, uid, tel, style, qishu, press_str, bet_amount, ok, msg="", source="normal"):
        """保存真实参与记录（含来源标记 normal/miss/sim）"""
        now = now_cn().strftime("%Y-%m-%d %H:%M:%S")
        try:
            with self.lock:
                with self._conn() as conn:
                    conn.execute("""
                        INSERT INTO real_orders (username,uid,tel,style,qishu,press_str,bet_amount,ok,msg,created_at,source)
                        VALUES (?,?,?,?,?,?,?,?,?,?,?)
                    """, (username, uid, tel, int(style), str(qishu), press_str,
                          int(bet_amount), 1 if ok else 0, msg, now, source or "normal"))
                    conn.commit()
        except Exception as e:
            print(f"[SimHistoryDB.save_real_order] {e}")

    def get_recent_orders(self, username, uid, style, limit=2):
        """获取指定账号最近N期真实参与记录（含已结算的开奖号+中奖金额）"""
        try:
            with self.lock:
                with self._conn() as conn:
                    rows = conn.execute("""
                        SELECT qishu, press_str, bet_amount, ok, msg, created_at, source,
                               result, win_amount, settled_at
                        FROM real_orders
                        WHERE username=? AND uid=? AND style=?
                        ORDER BY id DESC LIMIT ?
                    """, (username, uid, int(style), limit)).fetchall()
                    return [dict(r) for r in rows]
        except Exception as e:
            print(f"[SimHistoryDB.get_recent_orders] {e}")
            return []

    def delete_real_orders(self, username, style):
        """删除指定用户 + 指定 style 的所有真实参与记录。返回删除条数。"""
        try:
            with self.lock:
                with self._conn() as conn:
                    cur = conn.execute(
                        "DELETE FROM real_orders WHERE username=? AND style=?",
                        (username, int(style)))
                    conn.commit()
                    return cur.rowcount or 0
        except Exception as e:
            print(f"[SimHistoryDB.delete_real_orders] {e}")
            return 0

    def _cleanup_loop(self):
        """每小时删除30天前的数据"""
        while True:
            try:
                cutoff = (now_cn() - timedelta(days=30)).strftime("%Y-%m-%d")
                with self.lock:
                    with self._conn() as conn:
                        conn.execute("DELETE FROM sim_groups WHERE date < ?", (cutoff,))
                        conn.commit()
            except Exception as e:
                print(f"[SimHistoryDB.cleanup] {e}")
            time.sleep(3600)

_sim_db = SimHistoryDB()


# ══════════════════════════════════════════════════════════════
# 服务端真实下单（不依赖浏览器）
# ══════════════════════════════════════════════════════════════
_REAL_ORDER_LOCK = threading.Lock()   # 全局锁，防止并发触发；锁只锁"决定下单+排日志"
_REAL_ORDER_INFLIGHT = set()          # 同一 (username, style, expect) 在执行中 → 跳过重复

# 爆仓账号：{(username, uid): {"reason":..., "ts":...}}，stop 所有下单任务
_BANNED_ACCOUNTS = {}
_BANNED_LOCK = threading.Lock()

def _is_account_banned(username, uid):
    with _BANNED_LOCK:
        return (username, str(uid)) in _BANNED_ACCOUNTS

def _ban_account(username, uid, tel, reason):
    """标记账号爆仓 → 所有下单跳过；同时检查是否该用户所有账号都爆了 → 自动停模拟。"""
    with _BANNED_LOCK:
        _BANNED_ACCOUNTS[(username, str(uid))] = {
            "reason": reason, "tel": tel,
            "ts": now_cn().strftime("%Y-%m-%d %H:%M:%S")
        }
    print(f"[BANNED] user={username} uid={uid} tel={tel} reason={reason}")
    # 检查该用户所有账号是否都爆了
    try:
        all_accs = _user_db.get_std_accounts(username) or []
        all_uids = [str(a.get("uid")) for a in all_accs if a.get("uid")]
        with _BANNED_LOCK:
            banned_uids = [k[1] for k in _BANNED_ACCOUNTS.keys() if k[0] == username]
        if all_uids and all(u in banned_uids for u in all_uids):
            print(f"[BANNED] user={username} 所有账号都爆仓 → 自动停止所有模拟")
            # 停所有 slot 的 random/map
            for slot in range(1, 5):
                try:
                    eng = _user_mgr.get_sim(username, slot)
                    with eng.lock:
                        for style in (210, 60):
                            s = eng._get_state(style)
                            s["random_running"] = False
                            s["map_running"] = False
                    eng.save()
                except Exception as e:
                    print(f"[BANNED] stop sim err: slot={slot} {e}")
    except Exception as e:
        print(f"[BANNED] check-all-banned err: {e}")

def _unban_account(username, uid):
    """解禁账号（用户重启任何模拟任务时调用）。"""
    with _BANNED_LOCK:
        k = (username, str(uid))
        if k in _BANNED_ACCOUNTS:
            _BANNED_ACCOUNTS.pop(k, None)
            print(f"[UNBAN] user={username} uid={uid}")
            return True
    return False

def _unban_all_for_user(username):
    """清除该用户所有爆仓标记（用户点任何"启动"按钮时调用）。"""
    with _BANNED_LOCK:
        keys = [k for k in _BANNED_ACCOUNTS if k[0] == username]
        for k in keys:
            _BANNED_ACCOUNTS.pop(k, None)
    if keys:
        print(f"[UNBAN] user={username} cleared {len(keys)} banned accounts")

def _get_banned_for_user(username):
    """前端 banner 用：拿到该用户当前爆仓的账号列表。"""
    with _BANNED_LOCK:
        return [{"uid": k[1], "tel": v.get("tel"), "reason": v.get("reason"), "ts": v.get("ts")}
                for k, v in _BANNED_ACCOUNTS.items() if k[0] == username]

# ══════════════════════════════════════════════════════════════
#  💳 motionpay 支付集成
# ══════════════════════════════════════════════════════════════
import hashlib as _hashlib
_PAY_CONFIG_CACHE = {"ts": 0, "data": None}
_PAY_CONFIG_LOCK = threading.Lock()

def _pay_get_config(force_refresh=False):
    """读支付配置（缓存 30s）。返回 dict。"""
    with _PAY_CONFIG_LOCK:
        if (not force_refresh) and _PAY_CONFIG_CACHE["data"] and (time.time() - _PAY_CONFIG_CACHE["ts"] < 30):
            return _PAY_CONFIG_CACHE["data"]
    try:
        with _user_db._conn() as c:
            row = c.execute("SELECT * FROM payment_config WHERE id=1").fetchone()
            if not row:
                return None
            d = dict(row)
            try: d["plans"] = json.loads(d.get("plans") or "{}")
            except Exception: d["plans"] = {}
        with _PAY_CONFIG_LOCK:
            _PAY_CONFIG_CACHE["data"] = d
            _PAY_CONFIG_CACHE["ts"] = time.time()
        return d
    except Exception as e:
        print(f"[pay_get_config] {e}")
        return None

def _pay_save_config(updates):
    """更新支付配置；updates 是 dict。"""
    cur = _pay_get_config(force_refresh=True) or {}
    cur.update(updates)
    if isinstance(cur.get("plans"), dict):
        plans_str = json.dumps(cur["plans"], ensure_ascii=False)
    else:
        plans_str = cur.get("plans", "") or ""
    with _user_db._conn() as c:
        c.execute("""INSERT OR REPLACE INTO payment_config
            (id, api_url, merchant_id, merchant_key,
             free_register_enabled, free_register_days, free_register_max_accounts,
             plans, updated_at)
            VALUES (1, ?, ?, ?, ?, ?, ?, ?, ?)""", (
            cur.get("api_url",""), cur.get("merchant_id",""), cur.get("merchant_key",""),
            int(cur.get("free_register_enabled") or 0),
            int(cur.get("free_register_days") or 3),
            int(cur.get("free_register_max_accounts") or 2),
            plans_str, now_cn().strftime("%Y-%m-%d %H:%M:%S")))
        c.commit()
    with _PAY_CONFIG_LOCK:
        _PAY_CONFIG_CACHE["ts"] = 0  # 失效缓存
    return True

def _pay_sign(params, key):
    """按 motionpay 文档算 sign：ASCII 排序，跳过 sign/sign_type/空/0，拼接 + KEY → md5 lowercase。"""
    items = []
    for k in sorted(params.keys()):
        if k in ("sign", "sign_type"): continue
        v = params[k]
        if v is None: continue
        sv = str(v).strip()
        if sv == "" or sv == "0": continue
        items.append(f"{k}={sv}")
    raw = "&".join(items) + str(key)
    return _hashlib.md5(raw.encode("utf-8")).hexdigest()

def _pay_verify_sign(params, key):
    """校验回调 sign。"""
    received = params.get("sign", "")
    expected = _pay_sign(params, key)
    return received == expected

def _pay_create_order(out_trade_no, name, money, notify_url, return_url=None, pay_type="cashier", client_ip="127.0.0.1"):
    """调 mapi.php 创建支付订单，返回 (ok, data_or_msg)。
    data_or_msg 包含 payurl / qrcode / urlscheme / trade_no。"""
    cfg = _pay_get_config()
    if not cfg or not cfg.get("api_url") or not cfg.get("merchant_id") or not cfg.get("merchant_key"):
        return False, "支付配置未完成（请到管理端配置）"
    params = {
        "pid": cfg["merchant_id"],
        "type": pay_type,
        "out_trade_no": out_trade_no,
        "notify_url": notify_url,
        "name": str(name)[:127],
        "money": str(money),
        "clientip": client_ip or "127.0.0.1",
    }
    if return_url:
        params["return_url"] = return_url
    params["sign"] = _pay_sign(params, cfg["merchant_key"])
    params["sign_type"] = "MD5"
    try:
        url = cfg["api_url"].rstrip("/") + "/mapi.php"
        r = requests.post(url, data=params, timeout=12)
        d = r.json()
        if d.get("code") == 1:
            return True, {
                "trade_no": d.get("trade_no", ""),
                "payurl":   d.get("payurl", ""),
                "qrcode":   d.get("qrcode", ""),
                "urlscheme": d.get("urlscheme", ""),
            }
        return False, d.get("msg", f"支付创建失败 code={d.get('code')}")
    except Exception as e:
        return False, f"支付接口异常: {e}"

def _pay_query_order(out_trade_no=None, trade_no=None):
    """查询单笔订单。"""
    cfg = _pay_get_config()
    if not cfg: return False, "支付配置未完成"
    params = {"act": "order", "pid": cfg["merchant_id"]}
    if trade_no: params["trade_no"] = trade_no
    elif out_trade_no: params["out_trade_no"] = out_trade_no
    else: return False, "缺少订单号"
    params["sign"] = _pay_sign(params, cfg["merchant_key"])
    params["sign_type"] = "MD5"
    try:
        url = cfg["api_url"].rstrip("/") + "/api.php"
        r = requests.get(url, params=params, timeout=10)
        d = r.json()
        if d.get("code") == 1: return True, d
        return False, d.get("msg", "查询失败")
    except Exception as e:
        return False, str(e)

def _pay_refund_order(out_trade_no, money, trade_no=None):
    """提交订单退款。"""
    cfg = _pay_get_config()
    if not cfg: return False, "支付配置未完成"
    params = {"pid": cfg["merchant_id"], "money": str(money)}
    if trade_no: params["trade_no"] = trade_no
    if out_trade_no: params["out_trade_no"] = out_trade_no
    params["sign"] = _pay_sign(params, cfg["merchant_key"])
    params["sign_type"] = "MD5"
    try:
        url = cfg["api_url"].rstrip("/") + "/api.php?act=refund"
        r = requests.post(url, data=params, timeout=10)
        d = r.json()
        if d.get("code") == 1: return True, d.get("msg", "退款成功")
        return False, d.get("msg", "退款失败")
    except Exception as e:
        return False, str(e)

def _pay_make_out_trade_no(prefix="P"):
    """生成商户订单号：P + 时间戳(秒) + 4 位随机。"""
    return f"{prefix}{int(time.time())}{random.randint(1000,9999)}"

def _pay_apply_business(order_row):
    """支付成功后执行业务动作：续费 / 加账号 / 注册新账号。
    order_row 是 dict from payment_orders。返回 (ok, msg)。
    幂等：已 paid 的订单直接跳过。"""
    plan_type = order_row.get("plan_type", "")
    plan_key  = order_row.get("plan_key", "")
    username  = order_row.get("username", "")
    days      = int(order_row.get("days") or 0)
    accounts  = int(order_row.get("accounts") or 0)
    try:
        if plan_type == "register":
            # 创建新用户
            pwd = order_row.get("register_password", "")
            if not pwd:
                return False, "注册订单缺密码"
            # 算 expires_at（now + days）
            exp_at = (now_cn() + timedelta(days=days)).strftime("%Y-%m-%d %H:%M:%S")
            try:
                _user_db.create_user(username, pwd, expires_at=exp_at, remark=f"支付注册-{plan_key}")
            except Exception as e:
                # 用户已存在 → 续费而非重建
                if "UNIQUE" in str(e) or "exists" in str(e).lower():
                    return _pay_renew_user(username, days, accounts)
                return False, f"创建用户失败: {e}"
            # 设置 max_accounts
            if accounts > 0:
                with _user_db._conn() as c:
                    c.execute("UPDATE users SET max_accounts=? WHERE username=?", (accounts, username))
                    c.commit()
            return True, f"注册成功 user={username} 有效期到 {exp_at} 账号上限 {accounts}"
        elif plan_type == "renew":
            return _pay_renew_user(username, days, accounts_override=accounts if accounts > 0 else None)
        elif plan_type == "extra_account":
            with _user_db._conn() as c:
                c.execute("UPDATE users SET max_accounts=COALESCE(max_accounts,5)+? WHERE username=?",
                          (accounts, username))
                c.commit()
            return True, f"加 {accounts} 个账号槽"
        return False, f"未知 plan_type={plan_type}"
    except Exception as e:
        return False, f"业务执行异常: {e}"

def _pay_renew_user(username, days, accounts_override=None):
    """续费：把 expires_at 延 days 天。若 accounts_override 设了，**覆盖**为更大的值。"""
    user = _user_db.get_user(username)
    if not user:
        return False, "用户不存在"
    cur_exp = user.get("expires_at") or ""
    base = now_cn()
    if cur_exp:
        try:
            cur_dt = datetime.strptime(cur_exp[:19], "%Y-%m-%d %H:%M:%S")
            if cur_dt > base: base = cur_dt
        except Exception: pass
    new_exp = (base + timedelta(days=days)).strftime("%Y-%m-%d %H:%M:%S")
    with _user_db._conn() as c:
        c.execute("UPDATE users SET expires_at=? WHERE username=?", (new_exp, username))
        if accounts_override is not None:
            # 续费套餐默认账号数：取大者（不降级）
            c.execute("""UPDATE users SET max_accounts=MAX(max_accounts, ?) WHERE username=?""",
                      (int(accounts_override), username))
        c.commit()
    return True, f"续费到 {new_exp}"

def _do_real_order_for_user(username, style, expect, press_str, source="sim"):
    """服务端版本的真实下单：用 username 拉所有 std_accounts，每个账号下一次。
    - source: "sim_random" / "sim_map" / "miss" / "miss_auto"
    - 爆仓账号跳过
    - token 失效跳过
    - 失败 0.5 秒间隔无限重试，直到成功 / 开奖时刻到来 / token 失效 / 余额不足
    - "重复投注"/"开奖中" 也重试（石头岛 bug）；每次重试前查 DB 看本期是否已成功，是则停
    - 每次成功立刻写 DB ok=True（后续 user+uid+expect 查到就跳过）
    """
    # ⭐ next_qishu 防御：None / 空 / "None" 字符串 都拒绝下单（避免前端出现"期号 None"脏卡）
    expect_str = str(expect) if expect is not None else ""
    if not expect_str or expect_str.lower() in ("none", "null", "undefined"):
        print(f"[real_order] skip invalid expect={expect!r} user={username} src={source}")
        return []
    expect = expect_str
    # ⭐ inflight 防重：同一期号+同 press_str+同 source 同时只下一次
    # 加 source：fix 和 jump 可能产生同 press_str 的真单（同数字组同倍率），各自独立下单不互相吃
    inflight_key = (username, int(style), str(expect), str(press_str), str(source))
    with _REAL_ORDER_LOCK:
        if inflight_key in _REAL_ORDER_INFLIGHT:
            print(f"[real_order] skip duplicate inflight: user={username} style={style} expect={expect}")
            return []
        _REAL_ORDER_INFLIGHT.add(inflight_key)
    try:
        accs = _user_db.get_std_accounts(username) or []
        if not accs:
            print(f"[real_order] user={username} no std_accounts")
            return []
        # 开奖时刻（重试截止时间）
        game = "jnd28" if int(style) == 210 else "btc28"
        period = 210 if int(style) == 210 else 60
        with _countdown_lock:
            c = _countdown_cache.get(game) or {}
        next_ts = float(c.get("next_ts") or 0)
        if next_ts <= 0:
            # 没倒计时缓存 → 按周期保守估计
            next_ts = time.time() + period - 5
        # 留 2 秒缓冲（避免封盘瞬间还在重试）
        deadline = next_ts - 2
        # ⭐ 修复 attempts=0 bug：石头岛 future.PreTime 推算的 next_ts 可能已经过期
        # （接口刷新比下单线程晚），导致循环一次进不去。给 3 秒宽限期保证至少尝试一次
        if deadline < time.time() + 1:
            deadline = time.time() + 3
            print(f"[real_order] deadline 已过，启用 3s 宽限期 user={username} style={style} expect={expect} src={source}")

        results = []

        def _check_db_ok(uid):
            """查 DB 看本期 user+uid+style+expect+press_str+source 是否已经 ok=True。
            ⭐ 加 press_str：遗漏检测一期可能下多组，每组（press_str 不同）独立判断已下
            ⭐ 加 source：fix 和 jump 可能产生同 press_str，各自来源独立判断（同来源去重，跨来源各下各的）"""
            try:
                with _sim_db.lock:
                    with _sim_db._conn() as conn:
                        row = conn.execute(
                            "SELECT ok FROM real_orders WHERE username=? AND uid=? AND style=? AND qishu=? AND press_str=? AND source=? AND ok=1 ORDER BY id DESC LIMIT 1",
                            (username, uid, int(style), str(expect), press_str, str(source))).fetchone()
                return bool(row)
            except Exception:
                return False

        for a in accs:
            uid = a.get("uid"); tel = a.get("tel") or ""; token = a.get("token")
            if not uid or not token:
                continue
            # 1) 爆仓账号跳过
            if _is_account_banned(username, uid):
                results.append({"uid": uid, "tel": tel, "ok": False, "msg": "账号爆仓已停止"})
                _sim_db.save_real_order(username, uid, tel, int(style), str(expect),
                                        press_str, _calc_bet_from_press(press_str),
                                        False, "账号爆仓已停止", source)
                continue
            # 2) 已经下成功过 → 跳过
            if _check_db_ok(uid):
                results.append({"uid": uid, "tel": tel, "ok": True, "msg": "本期已成功下单"})
                continue
            # 3) token 失效处理
            #    鲸鱼：可用 tel+password 自动续登（无验证码）
            #    石头岛：需要验证码，无法自动续登 → 直接跳过
            if _is_bad_token(token):
                if IS_JINGYU:
                    pwd = a.get("password") or ""
                    if pwd and tel:
                        try:
                            rr = requests.post(f"{STD_API}/pub/token", headers=std_headers(),
                                               params={"tel": tel, "password": pwd}, timeout=8)
                            dd = rr.json()
                            if dd.get("code") == 200 and dd.get("token"):
                                new_token = dd["token"]
                                acc_mgr = _user_mgr.get_acc(username)
                                if uid in acc_mgr.accounts:
                                    acc_mgr.accounts[uid]["token"] = new_token
                                    acc_mgr.save()
                                _user_db.save_std_account(username, uid, tel, new_token, password=pwd)
                                try:
                                    with _bad_token_lock:
                                        _bad_token_cache.pop(token, None)
                                except: pass
                                token = new_token
                                print(f"[real_order] user={username} tel={tel} token 自动续登成功")
                        except Exception as e:
                            print(f"[real_order auto relogin] {e}")
                if _is_bad_token(token):
                    results.append({"uid": uid, "tel": tel, "ok": False, "msg": "token失效"})
                    _sim_db.save_real_order(username, uid, tel, int(style), str(expect),
                                            press_str, _calc_bet_from_press(press_str),
                                            False, "token失效，请重新登录该账号", source)
                    continue

            # 4) 下单 + 重试循环
            ok, msg = False, ""
            attempt = 0
            while time.time() < deadline:
                attempt += 1
                if attempt > 1 and _check_db_ok(uid):
                    ok = True; msg = "本期已成功下单"; break
                try:
                    if IS_JINGYU:
                        # 🐋 鲸鱼下注：POST /pub/game/gameJoin?game_id=&game_no=&betNum=
                        gid = JINGYU_GAME_ID.get(int(style), 2)
                        r = requests.post(f"{STD_API}/pub/game/gameJoin",
                            headers=std_headers(token),
                            params={"game_id": gid, "game_no": str(expect), "betNum": press_str},
                            timeout=12)
                    else:
                        # 🪨 石头岛下注：POST /game/createGameRecord JSON body
                        r = requests.post(f"{STD_API}/game/createGameRecord",
                            headers=std_headers(token),
                            json={"expect": str(expect), "style": str(style), "press": press_str},
                            timeout=12)
                    raw = (r.text or "").strip()
                    if not raw or not raw.startswith("{"):
                        msg = f"非JSON HTTP {r.status_code}"
                        time.sleep(0.3); continue
                    d = r.json()
                    code = d.get("code"); msg = d.get("msg") or ""
                    if code == 200:
                        ok = True; break
                    # token 失效（含石头岛 code=201 "签名不正确" = JWT 过期）
                    if (code == -1 or code == 201 or "登录" in msg or "token" in msg.lower()
                            or "未登录" in msg or "失效" in msg or "签名" in msg):
                        _mark_bad_token(token); msg = f"token失效: {msg}"; break
                    # "已投"/"已下注"/"已参与" = 真成功
                    if "已投" in msg or "已下注" in msg or "已参与" in msg:
                        ok = True; msg = f"已下单（{msg}）"; break
                    # 余额不足 → 爆仓
                    if ("余额" in msg or ("金额" in msg and "不足" in msg)
                            or "不足" in msg and ("额" in msg or "金" in msg)):
                        _ban_account(username, uid, tel, msg); break
                    time.sleep(0.3); continue
                except Exception as e:
                    msg = f"网络: {e}"
                    time.sleep(0.3); continue

            # 5) 写入 DB（失败时附加重试次数，让前端能看到脚本已经尝试了多少次）
            bet_amt = _calc_bet_from_press(press_str)
            final_msg = msg
            if not ok and attempt > 1:
                final_msg = f"{msg}·已重试{attempt}次"
            _sim_db.save_real_order(username, uid, tel, int(style), str(expect),
                                    press_str, bet_amt, ok, final_msg, source)
            results.append({"uid": uid, "tel": tel, "ok": ok, "msg": final_msg})
            print(f"[real_order] user={username} uid={uid} style={style} expect={expect} "
                  f"ok={ok} attempts={attempt} src={source} msg={msg[:80]}")
        return results
    finally:
        with _REAL_ORDER_LOCK:
            _REAL_ORDER_INFLIGHT.discard(inflight_key)

def _calc_bet_from_press(press_str):
    """从 press_str 算总投入金额。"""
    try:
        return sum(int(x) for x in (press_str or "").split(",") if x.strip().lstrip("-").isdigit())
    except Exception:
        return 0

def _build_press_str(positions, base_amount, multiplier):
    """根据 positions + base*multiplier 算 press_str（28 个数字逗号分隔）。
    ⭐ 按赔率反比拆分（跟石头岛官网"等额俊哈"一致）：
       目标每号中奖返奖 ≈ bet_total * 2，
       这样不管开哪个号都是赢 ~bet_total（毛利），扣掉总押注后净赚 ~bet_total。
       平均拆分会导致低赔率号亏损（如 12 号开了返奖只有 333*13.69=4558 < 4985 净亏）。
    """
    if not positions:
        return ",".join(["0"]*28)
    bet_total = round(base_amount * multiplier)
    if bet_total <= 0:
        return ",".join(["0"]*28)
    # 先按 "目标返奖 = bet_total * 2" 算每个号的 stake，再缩放到总和 = bet_total
    target_payout = bet_total * 2
    arr = [0]*28
    rough_total = 0
    for p in positions:
        if 0 <= p < 28:
            odds = _REAL_ORDER_ODDS[p] if _REAL_ORDER_ODDS[p] > 0 else 1
            stake = max(1, round(target_payout / odds))
            arr[p] = stake
            rough_total += stake
    # 缩放到总和 = bet_total（绝对相等很难，先按比例缩放）
    if rough_total > 0:
        scale = bet_total / rough_total
        new_total = 0
        for p in positions:
            if 0 <= p < 28:
                arr[p] = max(1, round(arr[p] * scale))
                new_total += arr[p]
        # 误差补偿：把差额加到最低赔率（中奖额最低）的号上，避免暴露目标差距
        diff = bet_total - new_total
        if diff != 0 and positions:
            # 找出 positions 里赔率最低的号（中间号 13/14）调整
            mid_p = min(positions, key=lambda p: _REAL_ORDER_ODDS[p] if 0<=p<28 else 999)
            if 0 <= mid_p < 28:
                arr[mid_p] = max(1, arr[mid_p] + diff)
    return ",".join(str(x) for x in arr)


class SimEngine:
    """单个实例的模拟下单引擎（210 和 60 各一套状态）"""
    def __init__(self, save_file=None, engine_name="unknown", username=None):
        self.lock = threading.Lock()
        self.save_file = save_file or f"{BASE_DIR}/sim_state.json"
        self.engine_name = engine_name  # e.g. "admin1", "admin2_3", "client_17901"
        self.username = username        # 普通用户的引擎才有；admin 不下真单
        self.state_210 = self._empty_state()
        self.state_60  = self._empty_state()
        self._last_60_qishu = None
        self._token_getter = None
        self._groups_text_210 = ""
        self._groups_text_60  = ""
        _DEF_MULS = "1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625"
        # 兼容旧字段（按 style 一份，random/map 共用）
        self._muls_text_210 = _DEF_MULS
        self._muls_text_60  = _DEF_MULS
        # 新：按 style × mode 独立
        self._muls_text_random_210 = _DEF_MULS
        self._muls_text_random_60  = _DEF_MULS
        self._muls_text_map_210    = _DEF_MULS
        self._muls_text_map_60     = _DEF_MULS
        self._muls_text_fix_210    = _DEF_MULS
        self._muls_text_fix_60     = _DEF_MULS
        self._muls_text_jump_210   = _DEF_MULS
        self._muls_text_jump_60    = _DEF_MULS
        self._map_text_210 = ""
        self._map_text_60  = ""
        self._fix_text_210 = ""
        self._fix_text_60  = ""
        self._jump_text_210 = ""
        self._jump_text_60  = ""
        self.load()
        threading.Thread(target=self._daily_reset_loop, daemon=True).start()

    def _empty_state(self):
        return {
            # 共用配置
            "groups": [],
            "map_groups": {},
            # 兼容旧字段（load 时把旧值迁移到下面 random/map）
            "multipliers": [1.0],
            "base_amount": 10000,
            # 新：random/map/fix/jump 独立的倍率序列 + 基础金额
            "multipliers_random": [1.0],
            "multipliers_map":    [1.0],
            "multipliers_fix":    [1.0],
            "multipliers_jump":   [1.0],
            "base_amount_random": 10000,
            "base_amount_map":    10000,
            "base_amount_fix":    10000,
            "base_amount_jump":   10000,
            "pnl_date": now_cn().strftime("%Y-%m-%d"),
            # 随机模式独立状态
            "random_running": False,
            "random_group_idx": 0,
            "random_mul_idx": 0,
            "random_last_qishu": None,
            "random_current_group_log": None,
            "groups_log_random": [],
            "total_pnl_random": 0,
            # 开某投某独立状态
            "map_running": False,
            "map_mul_idx": 0,
            "map_last_qishu": None,
            "map_last_result": None,
            "map_current_group_log": None,
            "groups_log_map": [],
            "total_pnl_map": 0,
            # 固定模式独立状态：多行数字组，每行独立 mul_idx + stopped
            "fix_running": False,
            "fix_groups": [],
            "fix_row_states": [],  # [{mul_idx:0, stopped:False}, ...]
            "fix_stop_on_win": False,
            "fix_stop_on_exhaust": False,
            "fix_last_qishu": None,
            "fix_current_group_log": None,
            "groups_log_fix": [],
            "total_pnl_fix": 0,
            # 跳转模式独立状态：N 行 ↔ N 个倍率，step_idx 同步递进
            "jump_running": False,
            "jump_groups": [],
            "jump_step_idx": 0,
            "jump_last_qishu": None,
            "jump_current_group_log": None,
            "groups_log_jump": [],
            "total_pnl_jump": 0,
            # 止盈设置（0 = 不止盈）
            "stop_profit_random": 0,
            "stop_profit_map": 0,
            "stop_profit_fix": 0,
            "stop_profit_jump": 0,
            # 止盈基线：start() 时记录当前累计 pnl，止盈用 (pnl - 基线) 比较
            "stop_profit_base_random": 0,
            "stop_profit_base_map": 0,
            "stop_profit_base_fix": 0,
            "stop_profit_base_jump": 0,
            # 真实参与（服务端持久化，浏览器关了也照跑）
            "real_enabled_random": False,
            "real_enabled_map":    False,
            "real_enabled_fix":    False,
            "real_enabled_jump":   False,
            "real_mul_idx_random": 0,
            "real_mul_idx_map":    0,
            "real_last_qishu_random":    None,
            "real_last_qishu_map":       None,
            "real_last_qishu_fix":       None,
            "real_last_qishu_jump":      None,
            "real_settled_qishu_random": None,
            "real_settled_qishu_map":    None,
            "real_settled_qishu_fix":    None,
            "real_settled_qishu_jump":   None,
            # 公共记录
            "records": [],
        }

    def _daily_reset_loop(self):
        while True:
            now = now_cn()
            next_midnight = (now + timedelta(days=1)).replace(
                hour=0, minute=0, second=5, microsecond=0)
            sleep_secs = (next_midnight - now).total_seconds()
            time.sleep(max(sleep_secs, 1))
            with self.lock:
                for s in [self.state_210, self.state_60]:
                    s["groups_log_random"] = []
                    s["groups_log_map"] = []
                    s["records"] = []
                    s["random_current_group_log"] = None
                    s["map_current_group_log"] = None
                    s["total_pnl_random"] = 0
                    s["total_pnl_map"] = 0
                    s["random_mul_idx"] = 0
                    s["map_mul_idx"] = 0
                    s["map_last_result"] = None
                    s["pnl_date"] = now_cn().strftime("%Y-%m-%d")
            self.save()
            print("[SIM] 每日0点清空完成")

    def save(self):
        try:
            data = {
                "state_210": {k: v for k, v in self.state_210.items() if k != "running"},
                "state_60":  {k: v for k, v in self.state_60.items()  if k != "running"},
                "groups_text_210": self._groups_text_210,
                "groups_text_60":  self._groups_text_60,
                "muls_text_210":   self._muls_text_210,
                "muls_text_60":    self._muls_text_60,
                "muls_text_random_210": self._muls_text_random_210,
                "muls_text_random_60":  self._muls_text_random_60,
                "muls_text_map_210":    self._muls_text_map_210,
                "muls_text_map_60":     self._muls_text_map_60,
                "muls_text_fix_210":    self._muls_text_fix_210,
                "muls_text_fix_60":     self._muls_text_fix_60,
                "muls_text_jump_210":   self._muls_text_jump_210,
                "muls_text_jump_60":    self._muls_text_jump_60,
                "map_text_210":    self._map_text_210,
                "map_text_60":     self._map_text_60,
                "fix_text_210":    self._fix_text_210,
                "fix_text_60":     self._fix_text_60,
                "jump_text_210":   self._jump_text_210,
                "jump_text_60":    self._jump_text_60,
            }
            os.makedirs(os.path.dirname(self.save_file), exist_ok=True)
            with open(self.save_file, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False)
        except Exception as e:
            print(f"[SIM SAVE] {e}")

    def load(self):
        try:
            with open(self.save_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            def merge(base, saved):
                for k, v in saved.items():
                    base[k] = v
                base["running"] = False
            merge(self.state_210, data.get("state_210", {}))
            merge(self.state_60,  data.get("state_60", {}))
            self._groups_text_210 = data.get("groups_text_210", "")
            self._groups_text_60  = data.get("groups_text_60", "")
            self._muls_text_210   = data.get("muls_text_210", self._muls_text_210)
            self._muls_text_60    = data.get("muls_text_60",  self._muls_text_60)
            # 新独立字段：缺失则从旧 muls_text 迁移
            self._muls_text_random_210 = data.get("muls_text_random_210", self._muls_text_210)
            self._muls_text_random_60  = data.get("muls_text_random_60",  self._muls_text_60)
            self._muls_text_map_210    = data.get("muls_text_map_210",    self._muls_text_210)
            self._muls_text_map_60     = data.get("muls_text_map_60",     self._muls_text_60)
            self._muls_text_fix_210    = data.get("muls_text_fix_210",    self._muls_text_210)
            self._muls_text_fix_60     = data.get("muls_text_fix_60",     self._muls_text_60)
            self._muls_text_jump_210   = data.get("muls_text_jump_210",   self._muls_text_210)
            self._muls_text_jump_60    = data.get("muls_text_jump_60",    self._muls_text_60)
            self._map_text_210    = data.get("map_text_210", "")
            self._map_text_60     = data.get("map_text_60", "")
            self._fix_text_210    = data.get("fix_text_210", "")
            self._fix_text_60     = data.get("fix_text_60", "")
            self._jump_text_210   = data.get("jump_text_210", "")
            self._jump_text_60    = data.get("jump_text_60", "")
            # state 内部 multipliers/base_amount → 4 套独立（缺失时降级迁移）
            for _s in (self.state_210, self.state_60):
                _legacy_muls = list(_s.get("multipliers", [1.0]))
                _legacy_base = int(_s.get("base_amount", 10000))
                for _mode in ("random", "map", "fix", "jump"):
                    if not _s.get(f"multipliers_{_mode}"):
                        _s[f"multipliers_{_mode}"] = list(_legacy_muls)
                    if f"base_amount_{_mode}" not in _s:
                        _s[f"base_amount_{_mode}"] = _legacy_base
                # 兜底新字段，缺失则初始化
                _s.setdefault("fix_groups", [])
                _s.setdefault("fix_row_states", [])
                _s.setdefault("fix_stop_on_win", False)
                _s.setdefault("fix_stop_on_exhaust", False)
                _s.setdefault("fix_current_group_log", None)
                _s.setdefault("groups_log_fix", [])
                _s.setdefault("total_pnl_fix", 0)
                _s.setdefault("fix_running", False)
                _s.setdefault("fix_last_qishu", None)
                _s.setdefault("jump_groups", [])
                _s.setdefault("jump_step_idx", 0)
                _s.setdefault("jump_current_group_log", None)
                _s.setdefault("groups_log_jump", [])
                _s.setdefault("total_pnl_jump", 0)
                _s.setdefault("jump_running", False)
                _s.setdefault("jump_last_qishu", None)
                _s.setdefault("stop_profit_fix", 0)
                _s.setdefault("stop_profit_jump", 0)
                # 止盈基线（兼容老存档）
                for _m in ("random", "map", "fix", "jump"):
                    _s.setdefault(f"stop_profit_base_{_m}", 0)
                _s.setdefault("real_enabled_fix", False)
                _s.setdefault("real_enabled_jump", False)
                _s.setdefault("real_last_qishu_fix", None)
                _s.setdefault("real_last_qishu_jump", None)
                _s.setdefault("real_settled_qishu_fix", None)
                _s.setdefault("real_settled_qishu_jump", None)
            print("[SIM LOAD] 已恢复模拟状态")
        except FileNotFoundError:
            pass
        except Exception as e:
            print(f"[SIM LOAD] {e}")

    def _get_state(self, style):
        return self.state_210 if style == 210 else self.state_60

    def configure(self, style, groups_text, multipliers_text, base_amount):
        groups = sim_parse_groups(groups_text)
        muls = sim_parse_multipliers(multipliers_text)
        if not groups:
            return False, "下注数字组为空或格式错误"
        if not muls:
            return False, "倍数序列为空"
        with self.lock:
            s = self._get_state(style)
            s["groups"] = groups
            # random 模式独立
            s["multipliers_random"] = muls
            s["base_amount_random"] = max(100, int(base_amount))
            # 旧字段保持同步（防止外部读取拿到陈旧值）
            s["multipliers"] = muls
            s["base_amount"] = max(100, int(base_amount))
            s["random_group_idx"] = random.randint(0, len(groups) - 1)
            if style == 210:
                self._groups_text_210 = groups_text
                self._muls_text_random_210 = multipliers_text
                self._muls_text_210 = multipliers_text
            else:
                self._groups_text_60 = groups_text
                self._muls_text_random_60 = multipliers_text
                self._muls_text_60 = multipliers_text
        self.save()
        return True, "随机模式配置成功"

    def configure_map(self, style, map_text, multipliers_text, base_amount):
        lines = [l.strip() for l in map_text.strip().split("\n") if l.strip()]
        if len(lines) != 28:
            return False, f"开某投某需要恰好28行（当前{len(lines)}行），第1行对应合计0，第28行对应合计27"
        map_groups = {}
        for i, line in enumerate(lines):
            nums = []
            for part in line.split("-"):
                part = part.strip()
                if part.isdigit():
                    n = int(part)
                    if 0 <= n <= 27:
                        nums.append(n)
            if not nums:
                return False, f"第{i+1}行（对应合计{i}）数字无效"
            seen = set()
            map_groups[i] = [n for n in nums if not (n in seen or seen.add(n))]
        muls = sim_parse_multipliers(multipliers_text)
        if not muls:
            return False, "倍数序列为空"
        with self.lock:
            s = self._get_state(style)
            s["map_groups"] = map_groups
            # map 模式独立
            s["multipliers_map"] = muls
            s["base_amount_map"] = max(100, int(base_amount))
            if style == 210:
                self._map_text_210 = map_text
                self._muls_text_map_210 = multipliers_text
            else:
                self._map_text_60 = map_text
                self._muls_text_map_60 = multipliers_text
        self.save()
        return True, "开某投某模式配置成功（28行已验证）"

    def _parse_multiline_groups(self, text):
        """解析多行数字组（每行 - 分隔），返回 (groups, err_msg)。"""
        lines = [l.strip() for l in (text or "").strip().split("\n") if l.strip()]
        if not lines:
            return None, "数字组为空"
        groups = []
        for i, line in enumerate(lines):
            nums = []
            for part in line.split("-"):
                part = part.strip()
                if part.isdigit():
                    n = int(part)
                    if 0 <= n <= 27:
                        nums.append(n)
            seen = set()
            nums = [n for n in nums if not (n in seen or seen.add(n))]
            if not nums:
                return None, f"第{i+1}行数字无效"
            groups.append(nums)
        return groups, None

    def configure_fix(self, style, text, multipliers_text, base_amount):
        """固定玩法：多行数字组，每期同时下所有未停止行，每行独立倍率推进"""
        groups, err = self._parse_multiline_groups(text)
        if err:
            return False, err
        muls = sim_parse_multipliers(multipliers_text)
        if not muls:
            return False, "倍数序列为空"
        with self.lock:
            s = self._get_state(style)
            s["fix_groups"] = groups
            s["multipliers_fix"] = muls
            s["base_amount_fix"] = max(100, int(base_amount))
            # 配置变更 → 重置每行状态（行数也可能变）
            s["fix_row_states"] = [{"mul_idx": 0, "stopped": False} for _ in groups]
            if style == 210:
                self._fix_text_210 = text
                self._muls_text_fix_210 = multipliers_text
            else:
                self._fix_text_60 = text
                self._muls_text_fix_60 = multipliers_text
        self.save()
        return True, f"固定模式配置成功（{len(groups)}组）"

    def configure_jump(self, style, text, multipliers_text, base_amount):
        """跳转玩法：N 行数字组 ↔ N 个倍率，依次推进，中→回 0"""
        groups, err = self._parse_multiline_groups(text)
        if err:
            return False, err
        muls = sim_parse_multipliers(multipliers_text)
        if not muls:
            return False, "倍数序列为空"
        if len(groups) != len(muls):
            return False, f"跳转玩法要求数字组数（{len(groups)}）= 倍率个数（{len(muls)}），请检查"
        with self.lock:
            s = self._get_state(style)
            s["jump_groups"] = groups
            s["multipliers_jump"] = muls
            s["base_amount_jump"] = max(100, int(base_amount))
            s["jump_step_idx"] = 0
            if style == 210:
                self._jump_text_210 = text
                self._muls_text_jump_210 = multipliers_text
            else:
                self._jump_text_60 = text
                self._muls_text_jump_60 = multipliers_text
        self.save()
        return True, f"跳转模式配置成功（{len(groups)}组对应{len(muls)}倍率）"

    def set_fix_options(self, style, stop_on_win=None, stop_on_exhaust=None):
        """设置固定模式的两个开关"""
        with self.lock:
            s = self._get_state(style)
            if stop_on_win is not None:
                s["fix_stop_on_win"] = bool(stop_on_win)
            if stop_on_exhaust is not None:
                s["fix_stop_on_exhaust"] = bool(stop_on_exhaust)
        self.save()
        return True, "已更新固定模式开关"

    def set_stop_profit(self, style, mode, amount):
        """设置止盈金额，0=不止盈"""
        with self.lock:
            s = self._get_state(style)
            key = f"stop_profit_{mode}"
            s[key] = max(0, int(amount))
        self.save()
        return True, f"止盈设为 {amount}" if amount > 0 else "止盈已关闭"

    def start(self, style, mode="random"):
        with self.lock:
            s = self._get_state(style)
            if mode == "random":
                if not s["groups"]:
                    return False, "请先保存随机模式配置"
                s["random_running"] = True
                s["random_current_group_log"] = None
                s["random_mul_idx"] = 0
            elif mode == "map":
                if not s.get("map_groups"):
                    return False, "请先保存开某投某配置"
                s["map_running"] = True
                s["map_current_group_log"] = None
                s["map_mul_idx"] = 0
            elif mode == "fix":
                if not s.get("fix_groups"):
                    return False, "请先保存固定模式配置"
                s["fix_running"] = True
                s["fix_current_group_log"] = None
                # 重置所有行（mul_idx=0, stopped=False）
                s["fix_row_states"] = [{"mul_idx": 0, "stopped": False} for _ in s["fix_groups"]]
            elif mode == "jump":
                if not s.get("jump_groups"):
                    return False, "请先保存跳转模式配置"
                s["jump_running"] = True
                s["jump_current_group_log"] = None
                s["jump_step_idx"] = 0
            else:
                return False, f"未知模式 {mode}"
            # ⭐ 止盈基线：启动那一刻记录当前累计 pnl，止盈判断用 (pnl - 基线) 比较
            # 这样不管历史累计多少，止盈都是"本次启动以来的盈利"
            s[f"stop_profit_base_{mode}"] = int(s.get(f"total_pnl_{mode}", 0) or 0)
        return True, "已启动"

    def stop(self, style, mode="random"):
        with self.lock:
            s = self._get_state(style)
            if mode in ("random", "map", "fix", "jump"):
                s[f"{mode}_running"] = False
        return True, "已停止"

    def reset(self, style, mode="random"):
        with self.lock:
            s = self._get_state(style)
            if mode == "random":
                s["groups_log_random"] = []
                s["random_current_group_log"] = None
                s["total_pnl_random"] = 0
                s["random_mul_idx"] = 0
                s["random_last_qishu"] = None
            elif mode == "map":
                s["groups_log_map"] = []
                s["map_current_group_log"] = None
                s["total_pnl_map"] = 0
                s["map_mul_idx"] = 0
                s["map_last_qishu"] = None
                s["map_last_result"] = None
            elif mode == "fix":
                s["groups_log_fix"] = []
                s["fix_current_group_log"] = None
                s["total_pnl_fix"] = 0
                s["fix_last_qishu"] = None
                s["fix_row_states"] = [{"mul_idx": 0, "stopped": False} for _ in s.get("fix_groups", [])]
            elif mode == "jump":
                s["groups_log_jump"] = []
                s["jump_current_group_log"] = None
                s["total_pnl_jump"] = 0
                s["jump_last_qishu"] = None
                s["jump_step_idx"] = 0
        self.save()
        return True, "已重置"

    def clear_all_data(self, style):
        """删除该 slot 指定 style 的所有数据（records + 组日志 + 累计盈亏 + 倍率位置）。
        配置（groups_text、muls_text、base_amount、stop_profit）保留。"""
        with self.lock:
            s = self._get_state(style)
            for k in ("groups_log_random","groups_log_map","groups_log_fix","groups_log_jump","records"):
                s[k] = []
            for k in ("random_current_group_log","map_current_group_log","fix_current_group_log","jump_current_group_log",
                      "random_last_qishu","map_last_qishu","fix_last_qishu","jump_last_qishu","map_last_result",
                      "random_last_real_press","map_last_real_press"):
                s[k] = None
            for k in ("total_pnl_random","total_pnl_map","total_pnl_fix","total_pnl_jump",
                      "random_mul_idx","map_mul_idx","jump_step_idx"):
                s[k] = 0
            # 固定模式的行状态全部归零（保留行数对应原 fix_groups）
            s["fix_row_states"] = [{"mul_idx": 0, "stopped": False} for _ in s.get("fix_groups", [])]
        self.save()
        # 同时清 DB 里这个 engine + style 的所有 sim_groups
        try:
            with _sim_db.lock:
                with _sim_db._conn() as conn:
                    conn.execute("DELETE FROM sim_groups WHERE engine=? AND style=?",
                                 (self.engine_name, int(style)))
                    conn.commit()
        except Exception as e:
            print(f"[SimEngine.clear_all_data DB] {e}")
        return True, "已清空"

    def _miss_target_modes(self, s):
        modes = []
        if s.get("random_running"):
            modes.append("random")
        if s.get("map_running"):
            modes.append("map")
        return modes

    def inject_miss_bet(self, style, next_qishu, positions, base_amount, multiplier=1.0):
        if not next_qishu or not positions:
            return False
        # ⭐ 防御："None" 字符串也拦掉
        nq_str = str(next_qishu)
        if nq_str.lower() in ("none", "null", "undefined"):
            return False
        inserted = False
        with self.lock:
            s = self._get_state(style)
            for mode in self._miss_target_modes(s):
                cg_key = f"{mode}_current_group_log"
                if s.get(cg_key) is None:
                    s[cg_key] = {"rounds": [], "total_cost": 0, "group_pnl": 0, "ended": False}
                cg = s[cg_key]
                pos = list(positions)
                exists = any(str(r.get("qishu")) == str(next_qishu) and r.get("rec_type") == "miss_inject" and r.get("positions") == pos for r in cg.get("rounds", []))
                if exists:
                    continue
                bet_amount = round(float(base_amount) * float(multiplier))
                rec = {"qishu": str(next_qishu), "result": None, "positions": pos,
                       "multiplier": float(multiplier), "bet_amount": bet_amount, "net_pnl": None,
                       "won": None, "mul_step": 0, "label": "遗漏植入", "pending": True,
                       "rec_type": "miss_inject",
                       "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S")}
                cg["rounds"].insert(0, rec)
                cg["total_cost"] += bet_amount
                s["records"].insert(0, rec)
                s["records"] = s["records"][:50]
                inserted = True
        if inserted:
            self.save()
        return inserted

    def settle_miss_bets(self, style, qishu, result_sum):
        saved = []
        changed = False
        with self.lock:
            s = self._get_state(style)
            for mode in ("random", "map"):
                cg_key = f"{mode}_current_group_log"
                pnl_key = f"total_pnl_{mode}"
                cg = s.get(cg_key)
                if not cg:
                    continue
                for rec in cg.get("rounds", []):
                    if str(rec.get("qishu")) != str(qishu) or not rec.get("pending") or rec.get("rec_type") != "miss_inject":
                        continue
                    multiplier = float(rec.get("multiplier", 1.0))
                    bet_amount = float(rec.get("bet_amount", 0))
                    base = bet_amount / multiplier if multiplier else bet_amount
                    won, net_pnl, _ = sim_calc_pnl(rec.get("positions", []), int(result_sum), base, multiplier)
                    rec.update({"result": int(result_sum), "net_pnl": round(net_pnl), "won": won, "pending": False})
                    cg["group_pnl"] = cg.get("group_pnl", 0) + round(net_pnl)
                    s[pnl_key] = s.get(pnl_key, 0) + round(net_pnl)
                    saved.append((mode, dict(rec)))
                    changed = True
            for rec in s.get("records", []):
                if str(rec.get("qishu")) == str(qishu) and rec.get("pending") and rec.get("rec_type") == "miss_inject":
                    multiplier = float(rec.get("multiplier", 1.0))
                    bet_amount = float(rec.get("bet_amount", 0))
                    base = bet_amount / multiplier if multiplier else bet_amount
                    won, net_pnl, _ = sim_calc_pnl(rec.get("positions", []), int(result_sum), base, multiplier)
                    rec.update({"result": int(result_sum), "net_pnl": round(net_pnl), "won": won, "pending": False})
                    changed = True
        if changed:
            self.save()
        for mode, rec in saved:
            group = {"rounds": [rec], "total_cost": rec.get("bet_amount", 0),
                     "group_pnl": rec.get("net_pnl", 0), "ended": True,
                     "exhausted": False, "miss_inject": True}
            threading.Thread(target=_sim_db.save_group, args=(self.engine_name, style, mode, group), daemon=True).start()
        return changed

    def place_bet(self, style, next_qishu):
        """新期号出现（未开奖）时立即下注，记录 pending=True 的记录"""
        # ⭐ next_qishu 防御：None / "None" / 空字符串 → 拒绝下单（避免前端出现"期号 None"脏卡）
        nq_str = str(next_qishu) if next_qishu is not None else ""
        if not nq_str or nq_str.lower() in ("none", "null", "undefined"):
            return
        next_qishu = nq_str
        real_orders_to_fire = []  # 锁外触发，避免占用 self.lock
        with self.lock:
            s = self._get_state(style)

            for mode in ("random", "map"):
                # 各 mode 独立的倍率序列 + 基础金额
                muls = s.get(f"multipliers_{mode}") or s.get("multipliers") or [1.0]
                base = s.get(f"base_amount_{mode}", s.get("base_amount", 10000))
                running_key = f"{mode}_running"
                if not s.get(running_key):
                    continue
                # ⭐ 同期号同 mode 已有 pending → 跳过（避免启动+broadcast双触发导致重复下单）
                cg_chk = s.get(f"{mode}_current_group_log")
                if cg_chk:
                    dup = False
                    for r in cg_chk.get("rounds", []):
                        if str(r.get("qishu")) == str(next_qishu) and r.get("pending"):
                            dup = True; break
                    if dup:
                        continue
                    # ⭐ 关键修复（用户已反馈三次）：当前组里有别的 pending（上一期没开奖完）→ 跳过
                    # 否则会出现"35没中→34/36/37全部1x下单"的连环 bug，倍率序列形同虚设
                    has_other_pending = False
                    for r in cg_chk.get("rounds", []):
                        if (r.get("pending")
                                and r.get("rec_type") != "miss_inject"
                                and str(r.get("qishu")) != str(next_qishu)):
                            has_other_pending = True
                            print(f"[SIM place_bet] style={style} mode={mode} 跳过 qishu={next_qishu}：上一期 {r.get('qishu')} 还在 pending")
                            break
                    if has_other_pending:
                        continue
                bet_key = f"{mode}_pending_qishu"
                s[bet_key] = str(next_qishu)

                mul_key = f"{mode}_mul_idx"
                cg_key  = f"{mode}_current_group_log"

                m_idx = min(s[mul_key], len(muls) - 1)
                multiplier = muls[m_idx]

                if mode == "map":
                    map_groups = s.get("map_groups", {})
                    if not map_groups:
                        continue
                    prev_result = s.get("map_last_result")
                    if prev_result is None:
                        try:
                            hist = (state if style == 210 else state_60).get("history", [])
                            if hist:
                                prev_result = int(hist[0].get("sum"))
                                s["map_last_result"] = prev_result
                        except Exception:
                            prev_result = None
                    if prev_result is None:
                        continue
                    positions = map_groups.get(prev_result, map_groups.get(str(prev_result), []))
                    if not positions:
                        continue
                    label = f"开{prev_result}投"
                else:
                    groups = s["groups"]
                    if not groups:
                        continue
                    g_idx = s["random_group_idx"] % len(groups)
                    positions = groups[g_idx]
                    s["random_group_idx"] = (g_idx + 1) % len(groups)
                    label = f"随机组{g_idx}"

                bet_amount = base * multiplier
                rec = {
                    "qishu": str(next_qishu),
                    "result": None,
                    "positions": positions,
                    "multiplier": multiplier,
                    "bet_amount": round(bet_amount),
                    "net_pnl": None,
                    "won": None,
                    "mul_step": m_idx,
                    "label": label,
                    "pending": True,
                    "rec_type": mode,
                    "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                }

                if s[cg_key] is None:
                    s[cg_key] = {"rounds": [], "total_cost": 0, "group_pnl": 0, "ended": False}
                cg = s[cg_key]
                cg["rounds"].insert(0, rec)
                cg["total_cost"] += round(bet_amount)

                s["records"].insert(0, rec)
                s["records"] = s["records"][:50]

                # 兼容字段（旧前端可能还在读）
                press_arr = [0] * 28
                for p in positions:
                    if 0 <= p <= 27:
                        press_arr[p] = round(bet_amount / max(1, len(positions)))
                s[f"{mode}_last_real_press"] = {
                    "press": press_arr,
                    "positions": list(positions),
                    "base_amount": int(base),
                    "multipliers": list(muls),
                    "qishu": str(next_qishu),
                    "style": style,
                    "mode": mode,
                    "ts": time.time(),
                }

                # ⭐ 服务端真实下单：开关开了 + 普通用户引擎（非 admin）+ 同期未跟过
                if (self.username
                        and s.get(f"real_enabled_{mode}")
                        and str(s.get(f"real_last_qishu_{mode}", "")) != str(next_qishu)):
                    real_muls = list(muls)
                    real_idx = min(s.get(f"real_mul_idx_{mode}", 0), len(real_muls) - 1)
                    real_mul = real_muls[real_idx] if real_muls else 1.0
                    real_press = _build_press_str(positions, base, real_mul)
                    # 先写状态再下单，防止失败时重复跟单
                    s[f"real_last_qishu_{mode}"] = str(next_qishu)
                    real_orders_to_fire.append({
                        "username": self.username,
                        "style": int(style),
                        "expect": str(next_qishu),
                        "press_str": real_press,
                        "source": f"sim_{mode}",
                    })

            # ─── fix 模式（多行同时下，每行独立倍率推进） ───
            if s.get("fix_running"):
                muls_f = s.get("multipliers_fix") or [1.0]
                base_f = s.get("base_amount_fix", 10000)
                fix_groups = s.get("fix_groups") or []
                row_states = s.get("fix_row_states") or []
                if fix_groups and len(row_states) != len(fix_groups):
                    row_states = [{"mul_idx": 0, "stopped": False} for _ in fix_groups]
                    s["fix_row_states"] = row_states
                cg_f = s.get("fix_current_group_log")
                already_fix = False
                has_other_fix = False
                if cg_f:
                    for r in cg_f.get("rounds", []):
                        if r.get("rec_type") != "fix":
                            continue
                        if str(r.get("qishu")) == str(next_qishu) and r.get("pending"):
                            already_fix = True; break
                    if not already_fix:
                        for r in cg_f.get("rounds", []):
                            if (r.get("pending") and r.get("rec_type") == "fix"
                                    and str(r.get("qishu")) != str(next_qishu)):
                                has_other_fix = True
                                print(f"[SIM place_bet] style={style} mode=fix 跳过 qishu={next_qishu}：上一期 {r.get('qishu')} 还在 pending")
                                break
                if fix_groups and not already_fix and not has_other_fix:
                    placed_any_fix = False
                    for row_idx, positions in enumerate(fix_groups):
                        if row_idx >= len(row_states):
                            continue
                        rs = row_states[row_idx]
                        if rs.get("stopped"):
                            continue
                        m_idx = min(rs.get("mul_idx", 0), len(muls_f) - 1)
                        multiplier = muls_f[m_idx]
                        bet_amount = base_f * multiplier
                        rec = {
                            "qishu": str(next_qishu),
                            "result": None,
                            "positions": list(positions),
                            "multiplier": multiplier,
                            "bet_amount": round(bet_amount),
                            "net_pnl": None,
                            "won": None,
                            "mul_step": m_idx,
                            "label": f"固定·行{row_idx+1}",
                            "pending": True,
                            "rec_type": "fix",
                            "row_idx": row_idx,
                            "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                        }
                        if s["fix_current_group_log"] is None:
                            s["fix_current_group_log"] = {"rounds": [], "total_cost": 0, "group_pnl": 0, "ended": False}
                        cg = s["fix_current_group_log"]
                        cg["rounds"].insert(0, rec)
                        cg["total_cost"] += round(bet_amount)
                        s["records"].insert(0, rec)
                        s["records"] = s["records"][:50]
                        placed_any_fix = True
                        # 真单触发（fix 真单倍率跟模拟同步，不维护独立 real_mul_idx）
                        if (self.username
                                and s.get("real_enabled_fix")
                                and str(s.get("real_last_qishu_fix", "")) != str(next_qishu)):
                            real_press = _build_press_str(positions, base_f, multiplier)
                            real_orders_to_fire.append({
                                "username": self.username,
                                "style": int(style),
                                "expect": str(next_qishu),
                                "press_str": real_press,
                                "source": "sim_fix",
                            })
                    if placed_any_fix and self.username and s.get("real_enabled_fix"):
                        s["real_last_qishu_fix"] = str(next_qishu)

            # ─── jump 模式（单注，按 step_idx 同步推进倍率） ───
            if s.get("jump_running"):
                muls_j = s.get("multipliers_jump") or [1.0]
                base_j = s.get("base_amount_jump", 10000)
                jump_groups = s.get("jump_groups") or []
                if jump_groups and len(jump_groups) == len(muls_j):
                    cg_j = s.get("jump_current_group_log")
                    dup_j = False
                    has_other_j = False
                    if cg_j:
                        for r in cg_j.get("rounds", []):
                            if r.get("rec_type") != "jump":
                                continue
                            if str(r.get("qishu")) == str(next_qishu) and r.get("pending"):
                                dup_j = True; break
                        if not dup_j:
                            for r in cg_j.get("rounds", []):
                                if (r.get("pending") and r.get("rec_type") == "jump"
                                        and str(r.get("qishu")) != str(next_qishu)):
                                    has_other_j = True
                                    print(f"[SIM place_bet] style={style} mode=jump 跳过 qishu={next_qishu}：上一期 {r.get('qishu')} 还在 pending")
                                    break
                    if not dup_j and not has_other_j:
                        step_idx = s.get("jump_step_idx", 0)
                        if step_idx < 0 or step_idx >= len(jump_groups):
                            step_idx = 0
                            s["jump_step_idx"] = 0
                        positions = jump_groups[step_idx]
                        multiplier = muls_j[step_idx]
                        bet_amount = base_j * multiplier
                        rec = {
                            "qishu": str(next_qishu),
                            "result": None,
                            "positions": list(positions),
                            "multiplier": multiplier,
                            "bet_amount": round(bet_amount),
                            "net_pnl": None,
                            "won": None,
                            "mul_step": step_idx,
                            "label": f"跳转·步{step_idx+1}",
                            "pending": True,
                            "rec_type": "jump",
                            "step_idx": step_idx,
                            "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                        }
                        if s["jump_current_group_log"] is None:
                            s["jump_current_group_log"] = {"rounds": [], "total_cost": 0, "group_pnl": 0, "ended": False}
                        cg = s["jump_current_group_log"]
                        cg["rounds"].insert(0, rec)
                        cg["total_cost"] += round(bet_amount)
                        s["records"].insert(0, rec)
                        s["records"] = s["records"][:50]
                        if (self.username
                                and s.get("real_enabled_jump")
                                and str(s.get("real_last_qishu_jump", "")) != str(next_qishu)):
                            real_press = _build_press_str(positions, base_j, multiplier)
                            s["real_last_qishu_jump"] = str(next_qishu)
                            real_orders_to_fire.append({
                                "username": self.username,
                                "style": int(style),
                                "expect": str(next_qishu),
                                "press_str": real_press,
                                "source": "sim_jump",
                            })

        self.save()
        # 锁外触发真实下单（异步，不阻塞 place_bet 返回）
        for r in real_orders_to_fire:
            threading.Thread(
                target=_do_real_order_for_user,
                kwargs=r, daemon=True
            ).start()

    def process_result(self, style, qishu, result_sum):
        """开奖后结算：更新对应期号的 pending 记录，填入结果。
        ⭐ 即使模拟已停止（running=False）也照常结算 pending；
           running 只控制"是否新建 fallback 记录 + 是否触发止盈检查/倍率推进"。"""
        with self.lock:
            s = self._get_state(style)

            for mode in ("random", "map"):
                # 各 mode 独立的倍率序列 + 基础金额
                muls = s.get(f"multipliers_{mode}") or s.get("multipliers") or [1.0]
                base = s.get(f"base_amount_{mode}", s.get("base_amount", 10000))
                running_key = f"{mode}_running"
                running = bool(s.get(running_key))
                last_key = f"{mode}_last_qishu"
                # ⭐ 用后缀匹配避免短/长期号双广播导致 mul_idx 跳格
                if _qishu_match(qishu, s.get(last_key)):
                    continue

                mul_key = f"{mode}_mul_idx"
                cg_key  = f"{mode}_current_group_log"
                log_key = f"groups_log_{mode}"
                pnl_key = f"total_pnl_{mode}"

                m_idx = min(s[mul_key], len(muls) - 1)
                multiplier = muls[m_idx]

                # 查找当前组里这期的 pending 记录
                cg = s.get(cg_key)
                pending_rec = None
                if cg:
                    for r in cg["rounds"]:
                        if str(r.get("qishu")) == str(qishu) and r.get("pending") and r.get("rec_type") != "miss_inject":
                            pending_rec = r
                            break
                # 同时在 records 里找
                pending_rec_global = None
                for r in s.get("records", []):
                    if str(r.get("qishu")) == str(qishu) and r.get("pending") and r.get("rec_type") != "miss_inject" and r.get("label","").startswith("随机" if mode=="random" else "开"):
                        pending_rec_global = r
                        break

                # ⭐ 已停止 + 没有 pending → 没事可做，跳过（不要新建 fallback 也不推进倍率）
                if not running and not pending_rec and not pending_rec_global:
                    continue

                # 标记本期已处理
                s[last_key] = str(qishu)

                if mode == "map":
                    map_groups = s.get("map_groups", {})
                    if not map_groups:
                        s["map_last_result"] = int(result_sum)
                        continue
                    if pending_rec:
                        positions = pending_rec.get("positions", [])
                        label = pending_rec.get("label") or "开某投某"
                    else:
                        prev_result = s.get("map_last_result")
                        if prev_result is None:
                            s["map_last_result"] = int(result_sum)
                            continue
                        positions = map_groups.get(prev_result, map_groups.get(str(prev_result), []))
                        label = f"开{prev_result}投"
                    if not positions:
                        s["map_last_result"] = int(result_sum)
                        continue
                else:
                    groups = s["groups"]
                    if not groups:
                        continue
                    if pending_rec:
                        positions = pending_rec["positions"]
                        label = pending_rec["label"]
                    else:
                        # ⭐ 没有 pending → 这一期我们没下注，不要 fallback 新建（之前的 fallback
                        # 会创建脏数据，导致用户看到一堆"时间为空+混乱倍率"的期号）
                        continue

                won, net_pnl, bet_amount = sim_calc_pnl(positions, result_sum, base, multiplier)
                if mode == "map":
                    s["map_last_result"] = int(result_sum)

                # 更新 pending 记录（取 pending_rec 上原本的 bet_amount/multiplier，不是新算的）
                update_fields = {
                    "result": result_sum,
                    "won": won,
                    "pending": False,
                    "label": label,
                    "positions": positions,
                }
                if pending_rec:
                    # 用 pending_rec 自己的 bet_amount + multiplier 重算 net_pnl
                    rec_mul = pending_rec.get("multiplier", multiplier) or multiplier
                    rec_bet = pending_rec.get("bet_amount", round(bet_amount))
                    won2, net_pnl2, _ = sim_calc_pnl(positions, result_sum, base, rec_mul)
                    update_fields["net_pnl"] = round(net_pnl2)
                    update_fields["won"] = won2
                    pending_rec.update(update_fields)
                    bet_amount_used = rec_bet
                    won = won2
                    net_pnl = net_pnl2
                else:
                    # running + 找不到 pending → 新建 fallback
                    update_fields["net_pnl"] = round(net_pnl)
                    bet_amount_used = round(bet_amount)
                    new_rec = {
                        "qishu": str(qishu),
                        "multiplier": multiplier,
                        "bet_amount": bet_amount_used,
                        "mul_step": m_idx,
                        "pending": False,
                        "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                        **update_fields,
                    }
                    if s[cg_key] is None:
                        s[cg_key] = {"rounds": [], "total_cost": 0, "group_pnl": 0, "ended": False}
                    cg = s[cg_key]
                    cg["rounds"].insert(0, new_rec)
                    cg["total_cost"] += bet_amount_used
                    s["records"].insert(0, new_rec)
                    s["records"] = s["records"][:50]
                    pending_rec = new_rec

                if pending_rec_global:
                    pending_rec_global.update(update_fields)

                s[pnl_key] += round(net_pnl)

                # 止盈检测（从启动那一刻开始算，不含历史累计）
                if running:
                    sp = int(s.get(f"stop_profit_{mode}", 0) or 0)
                    base = int(s.get(f"stop_profit_base_{mode}", 0) or 0)
                    session_pnl = int(s[pnl_key]) - base
                    if sp > 0 and session_pnl >= sp:
                        s[f"{mode}_running"] = False
                        print(f"[SIM] 止盈触发 style={style} mode={mode} 本次盈利={session_pnl} >= {sp} (累计 pnl={s[pnl_key]}, 基线={base})")

                if s[cg_key] is None:
                    s[cg_key] = {"rounds": [], "total_cost": 0, "group_pnl": 0, "ended": False}
                cg = s[cg_key]
                cg["group_pnl"] += round(net_pnl)

                if won:
                    cg["ended"] = True
                    s[log_key].insert(0, dict(cg))
                    s[log_key] = s[log_key][:30]
                    s[cg_key] = None
                    s[mul_key] = 0
                    threading.Thread(target=_sim_db.save_group,
                        args=(self.engine_name, style, mode, dict(cg)), daemon=True).start()
                else:
                    # 倍率推进只在 running 时；停止状态下保持 mul_idx 不变（等用户重启）
                    if running:
                        if m_idx >= len(muls) - 1:
                            cg["ended"] = True
                            cg["exhausted"] = True
                            s[log_key].insert(0, dict(cg))
                            s[log_key] = s[log_key][:30]
                            s[cg_key] = None
                            s[mul_key] = 0
                            threading.Thread(target=_sim_db.save_group,
                                args=(self.engine_name, style, mode, dict(cg)), daemon=True).start()
                        else:
                            s[mul_key] = m_idx + 1
                    else:
                        # ⭐ bug 5：已停止 + 不中 + 已无 pending → 关闭这一组（"等开完奖才真正停"）
                        has_more_pending = any(
                            rr.get("pending") and rr.get("rec_type") != "miss_inject"
                            for rr in cg.get("rounds", [])
                        )
                        if not has_more_pending:
                            cg["ended"] = True
                            cg["exhausted"] = False
                            s[log_key].insert(0, dict(cg))
                            s[log_key] = s[log_key][:30]
                            s[cg_key] = None
                            print(f"[SIM] 停止后开奖完毕，关闭组 style={style} mode={mode}")
                            threading.Thread(target=_sim_db.save_group,
                                args=(self.engine_name, style, mode, dict(cg)), daemon=True).start()

                # ⭐ 推进真实参与倍率（独立于 running 状态，独立 settledQishu 去重）
                last_real_q = str(s.get(f"real_last_qishu_{mode}", "") or "")
                settled_real_q = str(s.get(f"real_settled_qishu_{mode}", "") or "")
                if last_real_q and last_real_q == str(qishu) and settled_real_q != str(qishu):
                    real_idx = s.get(f"real_mul_idx_{mode}", 0)
                    if won:
                        s[f"real_mul_idx_{mode}"] = 0
                    else:
                        if real_idx >= len(muls) - 1:
                            s[f"real_mul_idx_{mode}"] = 0
                        else:
                            s[f"real_mul_idx_{mode}"] = real_idx + 1
                    s[f"real_settled_qishu_{mode}"] = str(qishu)

            # ─── fix 模式结算（多行各自结算，每行独立推进 mul_idx / stopped） ───
            if str(qishu) != str(s.get("fix_last_qishu") or ""):
                muls_f = s.get("multipliers_fix") or [1.0]
                base_f = s.get("base_amount_fix", 10000)
                row_states_f = s.get("fix_row_states") or []
                fix_groups = s.get("fix_groups") or []
                running_f = bool(s.get("fix_running"))
                cg_f = s.get("fix_current_group_log")
                fix_settled = False
                fix_recs_this_q = []
                if cg_f:
                    for rec in cg_f.get("rounds", []):
                        if (str(rec.get("qishu")) == str(qishu)
                                and rec.get("pending")
                                and rec.get("rec_type") == "fix"):
                            fix_recs_this_q.append(rec)
                for rec in fix_recs_this_q:
                    row_idx = rec.get("row_idx")
                    if row_idx is None or row_idx >= len(row_states_f):
                        continue
                    positions = rec.get("positions", [])
                    rec_mul = float(rec.get("multiplier", 1.0))
                    won_r, net_pnl_r, _ = sim_calc_pnl(positions, int(result_sum), base_f, rec_mul)
                    rec["result"] = int(result_sum)
                    rec["won"] = won_r
                    rec["pending"] = False
                    rec["net_pnl"] = round(net_pnl_r)
                    cg_f["group_pnl"] = cg_f.get("group_pnl", 0) + round(net_pnl_r)
                    s["total_pnl_fix"] = s.get("total_pnl_fix", 0) + round(net_pnl_r)
                    fix_settled = True
                    # 推进该行状态（只在 running 时推进）
                    if running_f:
                        rs = row_states_f[row_idx]
                        if won_r:
                            if s.get("fix_stop_on_win"):
                                rs["stopped"] = True
                            else:
                                rs["mul_idx"] = 0
                        else:
                            cur_idx = rs.get("mul_idx", 0)
                            if cur_idx >= len(muls_f) - 1:
                                if s.get("fix_stop_on_exhaust"):
                                    rs["stopped"] = True
                                else:
                                    rs["mul_idx"] = 0
                            else:
                                rs["mul_idx"] = cur_idx + 1
                if fix_settled:
                    s["fix_last_qishu"] = str(qishu)
                    # 所有行都 stopped → 关闭当前 group，存档
                    if row_states_f and all(rs.get("stopped") for rs in row_states_f):
                        cg_f["ended"] = True
                        s["groups_log_fix"].insert(0, dict(cg_f))
                        s["groups_log_fix"] = s["groups_log_fix"][:30]
                        s["fix_current_group_log"] = None
                        threading.Thread(target=_sim_db.save_group,
                            args=(self.engine_name, style, "fix", dict(cg_f)), daemon=True).start()
                        # 全部停止后，关闭 running
                        s["fix_running"] = False
                    # 止盈检查（从启动那一刻开始算）
                    if running_f:
                        sp_f = int(s.get("stop_profit_fix", 0) or 0)
                        base_f = int(s.get("stop_profit_base_fix", 0) or 0)
                        session_pnl_f = int(s.get("total_pnl_fix", 0)) - base_f
                        if sp_f > 0 and session_pnl_f >= sp_f:
                            s["fix_running"] = False
                            print(f"[SIM] 止盈触发 style={style} mode=fix 本次盈利={session_pnl_f} >= {sp_f}")

            # ─── jump 模式结算（单注，按 step_idx 推进；中或耗尽都回 0） ───
            if str(qishu) != str(s.get("jump_last_qishu") or ""):
                muls_j = s.get("multipliers_jump") or [1.0]
                base_j = s.get("base_amount_jump", 10000)
                jump_groups = s.get("jump_groups") or []
                running_j = bool(s.get("jump_running"))
                cg_j = s.get("jump_current_group_log")
                target_rec = None
                if cg_j:
                    for rec in cg_j.get("rounds", []):
                        if (str(rec.get("qishu")) == str(qishu)
                                and rec.get("pending")
                                and rec.get("rec_type") == "jump"):
                            target_rec = rec
                            break
                if target_rec is not None:
                    positions = target_rec.get("positions", [])
                    rec_mul = float(target_rec.get("multiplier", 1.0))
                    won_j, net_pnl_j, _ = sim_calc_pnl(positions, int(result_sum), base_j, rec_mul)
                    target_rec["result"] = int(result_sum)
                    target_rec["won"] = won_j
                    target_rec["pending"] = False
                    target_rec["net_pnl"] = round(net_pnl_j)
                    cg_j["group_pnl"] = cg_j.get("group_pnl", 0) + round(net_pnl_j)
                    s["total_pnl_jump"] = s.get("total_pnl_jump", 0) + round(net_pnl_j)
                    s["jump_last_qishu"] = str(qishu)
                    if running_j:
                        step_idx = s.get("jump_step_idx", 0)
                        if won_j:
                            # 中 → 回 0，关闭当前 group 存档
                            s["jump_step_idx"] = 0
                            cg_j["ended"] = True
                            s["groups_log_jump"].insert(0, dict(cg_j))
                            s["groups_log_jump"] = s["groups_log_jump"][:30]
                            s["jump_current_group_log"] = None
                            threading.Thread(target=_sim_db.save_group,
                                args=(self.engine_name, style, "jump", dict(cg_j)), daemon=True).start()
                        else:
                            new_step = step_idx + 1
                            if new_step >= len(jump_groups) or new_step >= len(muls_j):
                                # 回档：归 0，cg 标记 exhausted 存档
                                s["jump_step_idx"] = 0
                                cg_j["ended"] = True
                                cg_j["exhausted"] = True
                                s["groups_log_jump"].insert(0, dict(cg_j))
                                s["groups_log_jump"] = s["groups_log_jump"][:30]
                                s["jump_current_group_log"] = None
                                threading.Thread(target=_sim_db.save_group,
                                    args=(self.engine_name, style, "jump", dict(cg_j)), daemon=True).start()
                            else:
                                s["jump_step_idx"] = new_step
                        # 止盈（从启动那一刻开始算）
                        sp_j = int(s.get("stop_profit_jump", 0) or 0)
                        base_j_sp = int(s.get("stop_profit_base_jump", 0) or 0)
                        session_pnl_j = int(s.get("total_pnl_jump", 0)) - base_j_sp
                        if sp_j > 0 and session_pnl_j >= sp_j:
                            s["jump_running"] = False
                            print(f"[SIM] 止盈触发 style={style} mode=jump 本次盈利={session_pnl_j} >= {sp_j}")

        self.save()

    def get_status(self, style):
        with self.lock:
            s = self._get_state(style)
            # 随机模式记录
            logs_random = list(s.get("groups_log_random", []))
            cg_random = s.get("random_current_group_log")
            if cg_random and cg_random["rounds"]:
                logs_random.insert(0, dict(cg_random))
            # 开某投某记录
            logs_map = list(s.get("groups_log_map", []))
            cg_map = s.get("map_current_group_log")
            if cg_map and cg_map["rounds"]:
                logs_map.insert(0, dict(cg_map))
            # 固定模式记录
            logs_fix = list(s.get("groups_log_fix", []))
            cg_fix = s.get("fix_current_group_log")
            if cg_fix and cg_fix.get("rounds"):
                logs_fix.insert(0, dict(cg_fix))
            # 跳转模式记录
            logs_jump = list(s.get("groups_log_jump", []))
            cg_jump = s.get("jump_current_group_log")
            if cg_jump and cg_jump.get("rounds"):
                logs_jump.insert(0, dict(cg_jump))
            groups_text = self._groups_text_210 if style == 210 else self._groups_text_60
            map_text    = self._map_text_210     if style == 210 else self._map_text_60
            fix_text    = self._fix_text_210     if style == 210 else self._fix_text_60
            jump_text   = self._jump_text_210    if style == 210 else self._jump_text_60
            muls_text_random = self._muls_text_random_210 if style == 210 else self._muls_text_random_60
            muls_text_map    = self._muls_text_map_210    if style == 210 else self._muls_text_map_60
            muls_text_fix    = self._muls_text_fix_210    if style == 210 else self._muls_text_fix_60
            muls_text_jump   = self._muls_text_jump_210   if style == 210 else self._muls_text_jump_60
            # 旧字段（向后兼容前端老代码）
            muls_text_legacy = self._muls_text_210 if style == 210 else self._muls_text_60
            pnl_random  = s.get("total_pnl_random", 0)
            pnl_map     = s.get("total_pnl_map", 0)
            pnl_fix     = s.get("total_pnl_fix", 0)
            pnl_jump    = s.get("total_pnl_jump", 0)
            base_random = int(s.get("base_amount_random", s.get("base_amount", 10000)))
            base_map    = int(s.get("base_amount_map",    s.get("base_amount", 10000)))
            base_fix    = int(s.get("base_amount_fix",    s.get("base_amount", 10000)))
            base_jump   = int(s.get("base_amount_jump",   s.get("base_amount", 10000)))
            muls_random = list(s.get("multipliers_random") or s.get("multipliers") or [1.0])
            muls_map    = list(s.get("multipliers_map")    or s.get("multipliers") or [1.0])
            muls_fix    = list(s.get("multipliers_fix")    or s.get("multipliers") or [1.0])
            muls_jump   = list(s.get("multipliers_jump")   or s.get("multipliers") or [1.0])
            return {
                "random_running": s.get("random_running", False),
                "map_running":    s.get("map_running", False),
                "fix_running":    s.get("fix_running", False),
                "jump_running":   s.get("jump_running", False),
                # 旧字段（兼容老前端，等同 random 那套）
                "base_amount": base_random,
                "multipliers": muls_random,
                "muls_text": muls_text_legacy,
                # 新：独立的四套
                "base_amount_random": base_random,
                "base_amount_map":    base_map,
                "base_amount_fix":    base_fix,
                "base_amount_jump":   base_jump,
                "multipliers_random": muls_random,
                "multipliers_map":    muls_map,
                "multipliers_fix":    muls_fix,
                "multipliers_jump":   muls_jump,
                "muls_text_random":   muls_text_random,
                "muls_text_map":      muls_text_map,
                "muls_text_fix":      muls_text_fix,
                "muls_text_jump":     muls_text_jump,
                "total_pnl": pnl_random + pnl_map + pnl_fix + pnl_jump,
                "total_pnl_random": pnl_random,
                "total_pnl_map":    pnl_map,
                "total_pnl_fix":    pnl_fix,
                "total_pnl_jump":   pnl_jump,
                "pnl_date": s.get("pnl_date", now_cn().strftime("%Y-%m-%d")),
                "records": s.get("records", []),
                "groups_log_random": logs_random[:30],
                "groups_log_map":    logs_map[:30],
                "groups_log_fix":    logs_fix[:30],
                "groups_log_jump":   logs_jump[:30],
                "groups_count": len(s["groups"]),
                "last_qishu": s.get("random_last_qishu") or s.get("map_last_qishu"),
                "groups_text": groups_text,
                "map_text": map_text,
                "fix_text":  fix_text,
                "jump_text": jump_text,
                "stop_profit_random": s.get("stop_profit_random", 0),
                "stop_profit_map":    s.get("stop_profit_map", 0),
                "stop_profit_fix":    s.get("stop_profit_fix", 0),
                "stop_profit_jump":   s.get("stop_profit_jump", 0),
                # 固定模式：行状态 + 两个开关
                "fix_row_states":      list(s.get("fix_row_states", [])),
                "fix_stop_on_win":     bool(s.get("fix_stop_on_win")),
                "fix_stop_on_exhaust": bool(s.get("fix_stop_on_exhaust")),
                "fix_groups_count":    len(s.get("fix_groups") or []),
                # 跳转模式：当前 step
                "jump_step_idx":       int(s.get("jump_step_idx", 0)),
                "jump_groups_count":   len(s.get("jump_groups") or []),
                # 真实参与（服务端持久化的开关状态，前端读这个回显开关亮灭）
                "real_enabled_random": bool(s.get("real_enabled_random")),
                "real_enabled_map":    bool(s.get("real_enabled_map")),
                "real_enabled_fix":    bool(s.get("real_enabled_fix")),
                "real_enabled_jump":   bool(s.get("real_enabled_jump")),
                # 真实参与：最新一次 place_bet 的 press 信息（仅作兼容回显，新逻辑不依赖）
                "real_press_random": s.get("random_last_real_press"),
                "real_press_map":    s.get("map_last_real_press"),
            }



# ══════════════════════════════════════════════════════════════
#  遗漏检测引擎
# ══════════════════════════════════════════════════════════════
class MissEngine:
    def __init__(self, save_file=None, username=None):
        self.lock = threading.Lock()
        self.save_file = save_file or f"{BASE_DIR}/miss_state.json"
        self.username = username  # 普通用户的 miss 引擎才下真单
        self.state = {
            "groups": [],          # 解析后的数字组
            "miss_n": 5,           # 查前几期
            "multipliers": [1.0],
            "base_amount": 10000,
            # ⭐ bug 7：mul_idx / cur_phase / locked_missed 全部按 style 分开
            "mul_idx_210": 0,
            "mul_idx_60": 0,
            "cur_phase_210": "idle",   # "idle"(待命) / "miss"(遗漏序列追单中)
            "cur_phase_60":  "idle",
            "locked_missed_210": [],   # 进入miss阶段时锁定的遗漏组（不中就按序列继续下）
            "locked_missed_60":  [],
            # 兼容字段（旧逻辑可能还在读，过渡期保留）
            "active": False,
            "miss_groups": {"210": [], "60": []},
            "cur_phase": "idle",
            "mul_idx": 0,
            "random_groups": [],
            "random_group_idx": 0,
            "last_qishu_210": None,
            "last_qishu_60": None,
            "auto_enabled_210": False,
            "auto_enabled_60": False,
            "auto_last_qishu_210": None,
            "auto_last_qishu_60": None,
            "real_enabled_210": False,
            "real_enabled_60": False,
            "records_210": [],
            "records_60": [],
            "total_pnl_210": 0,
            "total_pnl_60": 0,
            "pnl_date": now_cn().strftime("%Y-%m-%d"),
        }
        self._groups_text = ""
        self._random_text = ""
        self._muls_text = "1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625"
        self.load()
        for k, v in {
            "auto_enabled_210": False, "auto_enabled_60": False,
            "auto_last_qishu_210": None, "auto_last_qishu_60": None,
            "real_enabled_210": False, "real_enabled_60": False,
            "mul_idx_210": 0, "mul_idx_60": 0,
            "cur_phase_210": "idle", "cur_phase_60": "idle",
            "locked_missed_210": [], "locked_missed_60": [],
        }.items():
            self.state.setdefault(k, v)
        threading.Thread(target=self._daily_reset_loop, daemon=True).start()

    def _daily_reset_loop(self):
        while True:
            now = now_cn()
            next_midnight = (now + timedelta(days=1)).replace(hour=0, minute=0, second=5, microsecond=0)
            time.sleep(max((next_midnight - now).total_seconds(), 1))
            with self.lock:
                s = self.state
                s["records_210"] = []
                s["records_60"] = []
                s["total_pnl_210"] = 0
                s["total_pnl_60"] = 0
                # 新字段（按 style 分开）
                s["mul_idx_210"] = 0
                s["mul_idx_60"]  = 0
                s["cur_phase_210"] = "idle"
                s["cur_phase_60"]  = "idle"
                s["locked_missed_210"] = []
                s["locked_missed_60"]  = []
                # 兼容字段
                s["active"] = False
                s["miss_groups"] = {"210": [], "60": []}
                s["mul_idx"] = 0
                s["cur_phase"] = "idle"
                s["pnl_date"] = now_cn().strftime("%Y-%m-%d")
            self.save()

    def save(self):
        try:
            with open(self.save_file, "w", encoding="utf-8") as f:
                json.dump({
                    "state": self.state,
                    "groups_text": self._groups_text,
                    "random_text": self._random_text,
                    "muls_text": self._muls_text,
                }, f, ensure_ascii=False)
        except Exception as e:
            print(f"[MISS SAVE] {e}")

    def load(self):
        try:
            with open(self.save_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            s = data.get("state", {})
            for k, v in s.items():
                self.state[k] = v
            self.state["active"] = False
            self._groups_text = data.get("groups_text", "")
            self._random_text = data.get("random_text", "")
            self._muls_text   = data.get("muls_text", self._muls_text)
            print("[MISS LOAD] 已恢复遗漏状态")
        except FileNotFoundError:
            pass
        except Exception as e:
            print(f"[MISS LOAD] {e}")

    def configure(self, groups_text, random_text, muls_text, base_amount, miss_n):
        groups = sim_parse_groups(groups_text)
        random_groups = sim_parse_groups(random_text) if random_text.strip() else []
        muls = sim_parse_multipliers(muls_text)
        if not groups:
            return False, "遗漏数字组为空"
        with self.lock:
            self.state["groups"] = groups
            self.state["random_groups"] = random_groups
            self.state["multipliers"] = muls
            self.state["base_amount"] = max(100, int(base_amount))
            self.state["miss_n"] = max(1, int(miss_n))
            self._groups_text = groups_text
            self._random_text = random_text
            self._muls_text = muls_text
        self.save()
        return True, "配置已保存"

    def execute(self, history_210, history_60, next_qishu_210=None, next_qishu_60=None, inject_cb=None):
        """点"执行检测"按钮：检测遗漏组，立即模拟下单（手动一次）。
        每个 style 独立判断：如果当前 phase_X 已是 miss，沿用 locked + 当前 mul_idx；
        否则按 idle 处理（检测遗漏 → 锁定 → mul_idx=0 起步）。"""
        with self.lock:
            s = self.state
            groups = s["groups"]
            n = s["miss_n"]
            base = s["base_amount"]
            muls = s.get("multipliers") or [1.0]
            if not groups:
                return False, "请先保存配置", {}

            # 同期号未结算前不允许重复
            for st, nq, hk in [("210", next_qishu_210, "records_210"),
                               ("60",  next_qishu_60,  "records_60")]:
                if not nq:
                    continue
                for rec in s.get(hk, []):
                    if str(rec.get("qishu")) == str(nq) and rec.get("pending"):
                        print(f"[MISS execute] 拒绝重复：style={st} qishu={nq} 已有 pending 记录")
                        return False, f"{st}期号 {nq} 上一笔未结算，不能重复执行", {}

            def get_miss(history, game_groups):
                if not history: return []
                recent_sums = [int(h["sum"] if "sum" in h else h["sum_num"]) for h in history[:n]]
                return [g for g in game_groups if not any(r in g for r in recent_sums)]

            results = {"miss_210": [], "miss_60": []}
            real_orders_to_fire = []

            for style_str, history, hist_key in [
                ("210", history_210, "records_210"),
                ("60",  history_60,  "records_60")]:
                style = int(style_str)
                qishu = str(next_qishu_210 if style == 210 else next_qishu_60 or "")
                if not qishu:
                    continue
                phase_key  = f"cur_phase_{style}"
                mul_key    = f"mul_idx_{style}"
                locked_key = f"locked_missed_{style}"
                phase = s.get(phase_key, "idle")
                if phase == "miss" and s.get(locked_key):
                    # 继续追单：用 locked + 当前 mul_idx
                    missed = s[locked_key]
                    m_idx = min(s.get(mul_key, 0), len(muls)-1)
                else:
                    missed = get_miss(history, groups)
                    if missed:
                        s[phase_key]  = "miss"
                        s[locked_key] = missed
                        s[mul_key]    = 0
                        m_idx = 0
                    else:
                        continue
                multiplier = muls[m_idx]
                pnl_key = f"total_pnl_{style_str}"
                for positions in missed:
                    won, net_pnl, bet_amount = sim_calc_pnl(positions, -1, base, multiplier)
                    rec = {
                        "type": "miss", "qishu": qishu,
                        "label": f"遗漏植入·{m_idx+1}倍位",
                        "positions": positions,
                        "multiplier": multiplier,
                        "bet_amount": round(bet_amount),
                        "net_pnl": None, "won": None, "pending": True,
                        "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                        "mul_step": m_idx,
                    }
                    s[hist_key].insert(0, rec)
                    results[f"miss_{style_str}"].append({"qishu": qishu, "positions": positions,
                                                         "bet": round(bet_amount), "multiplier": multiplier})
                    if inject_cb:
                        try:
                            inject_cb(style, qishu, positions, base, multiplier)
                        except Exception as e:
                            print(f"[MISS inject] {e}")
                    if (self.username and s.get(f"real_enabled_{style_str}") and qishu):
                        real_orders_to_fire.append({
                            "username": self.username,
                            "style": style,
                            "expect": qishu,
                            "press_str": _build_press_str(positions, base, multiplier),
                            "source": f"miss_seq_{m_idx+1}",
                        })
                s[hist_key] = s[hist_key][:100]
                # 兼容字段
                if not isinstance(s.get("miss_groups"), dict):
                    s["miss_groups"] = {}
                s["miss_groups"][style_str] = missed

            s["active"] = bool(s.get("locked_missed_210") or s.get("locked_missed_60"))

        self.save()
        for r in real_orders_to_fire:
            threading.Thread(target=_do_real_order_for_user, kwargs=r, daemon=True).start()
        n210 = len(results["miss_210"]); n60 = len(results["miss_60"])
        return True, f"检测完成：欢乐210植入{n210}组，比特60植入{n60}组", results

    def set_auto(self, style, enabled):
        key = f"auto_enabled_{int(style)}"
        last_key = f"auto_last_qishu_{int(style)}"
        with self.lock:
            self.state[key] = bool(enabled)
            self.state[last_key] = None
        self.save()
        return True, "auto on" if enabled else "auto off"

    def auto_execute(self, style, history, next_qishu, inject_cb=None):
        """每期新期号到达时调用：
        - 若 cur_phase_{style} == 'idle'：检测遗漏，有则锁定 missed 进入 'miss' 阶段，按 mul_idx_{style}=0 下注
        - 若 cur_phase_{style} == 'miss'：直接用 locked_missed_{style} 按当前 mul_idx_{style} 下注（不重新检测）
        ⭐ bug 4+6：phase=miss 时，必须等上一期 pending 结算完才能下下一期，
        否则倍率永远没机会推进（石头岛接口在上期还没开奖时 next_qishu 就已暴露）
        倍率推进 / 退出在 process_result 里做"""
        style = int(style)
        qishu = str(next_qishu or "")
        if not qishu:
            return False, []
        with self.lock:
            s = self.state
            if not s.get(f"auto_enabled_{style}"):
                return False, []
            # ⭐ 用后缀匹配避免短/长期号双广播
            if _qishu_match(s.get(f"auto_last_qishu_{style}"), qishu):
                return False, []
            groups = s.get("groups", [])
            n = s.get("miss_n", 5)
            if not groups or not history:
                print(f"[MISS auto] style={style} skip: groups={len(groups)} hist={len(history) if history else 0}")
                return False, []
            # 同期号已有 pending → 跳过
            hist_key = f"records_{style}"
            for rec in s.get(hist_key, []):
                if str(rec.get("qishu")) == qishu and rec.get("pending"):
                    print(f"[MISS auto] style={style} qishu={qishu} skip: 已有 pending")
                    s[f"auto_last_qishu_{style}"] = qishu
                    return False, []

            phase_key  = f"cur_phase_{style}"
            mul_key    = f"mul_idx_{style}"
            locked_key = f"locked_missed_{style}"
            phase = s.get(phase_key, "idle")

            # ⭐ bug 4+6：miss 阶段，本游戏的上一期 pending 还没结算 → 等待，不下新单
            # （避免在上一期开奖前就下了下一期，导致倍率没机会推进）
            if phase == "miss":
                has_pending_prev = False
                for rec in s.get(hist_key, []):
                    if rec.get("pending") and str(rec.get("qishu")) != qishu:
                        has_pending_prev = True
                        prev_q = rec.get("qishu")
                        break
                if has_pending_prev:
                    print(f"[MISS auto] style={style} 跳过qishu={qishu}：上一期 {prev_q} 还在 pending，等其开奖后再下")
                    return False, []

            base = s.get("base_amount", 10000)
            muls = s.get("multipliers") or [1.0]

            if phase == "miss":
                # 已在追单序列中：直接用锁定的 missed 组 + 当前 mul_idx 下注
                locked = s.get(locked_key) or []
                if not locked:
                    # 异常状态：phase=miss 但 locked 空，重置回 idle
                    s[phase_key] = "idle"
                    s[mul_key] = 0
                    print(f"[MISS auto] style={style} phase=miss 但 locked 空，重置为 idle")
                    self.save()
                    return False, []
                m_idx = min(s.get(mul_key, 0), len(muls)-1)
                multiplier = muls[m_idx]
                missed = locked
                src_tag = f"miss_seq_{m_idx+1}"
                print(f"[MISS auto] style={style} qishu={qishu} 序列追单 #{m_idx+1}/{len(muls)} mul={multiplier}x 组数={len(missed)}")
            else:
                # idle 状态：检测遗漏
                recent_sums = []
                for h in history[:n]:
                    try:
                        recent_sums.append(int(h["sum"] if "sum" in h else h["sum_num"]))
                    except Exception:
                        pass
                missed = [g for g in groups if not any(r in g for r in recent_sums)]
                s[f"auto_last_qishu_{style}"] = qishu
                if not missed:
                    print(f"[MISS auto] style={style} qishu={qishu} 无遗漏 recent={recent_sums}")
                    self.save()
                    return True, []
                # 进入 miss 阶段：锁定 missed，mul_idx 从 0 开始
                s[phase_key]  = "miss"
                s[locked_key] = missed
                s[mul_key]    = 0
                m_idx = 0
                multiplier = muls[0]
                src_tag = "miss_seq_1"
                print(f"[MISS auto] style={style} qishu={qishu} 进入miss阶段 锁定{len(missed)}组 mul={multiplier}x recent={recent_sums}")

            s[f"auto_last_qishu_{style}"] = qishu

            results = []
            real_orders_to_fire = []
            real_on = bool(s.get(f"real_enabled_{style}"))
            for positions in missed:
                bet_amount = round(base * multiplier)
                rec = {"type": "miss", "qishu": qishu, "result": None, "positions": positions,
                       "multiplier": multiplier, "bet_amount": bet_amount, "net_pnl": None,
                       "won": None, "pending": True, "label": f"遗漏植入·{m_idx+1}倍位",
                       "auto": True, "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                       "mul_step": m_idx}
                s[hist_key].insert(0, rec)
                results.append({"qishu": qishu, "positions": positions, "bet": bet_amount, "multiplier": multiplier})
                if inject_cb:
                    try:
                        inject_cb(style, qishu, positions, base, multiplier)
                    except Exception as e:
                        print(f"[MISS auto inject] {e}")
                if self.username and real_on and qishu:
                    real_orders_to_fire.append({
                        "username": self.username,
                        "style": int(style),
                        "expect": qishu,
                        "press_str": _build_press_str(positions, base, multiplier),
                        "source": src_tag,
                    })
            s[hist_key] = s[hist_key][:100]
            # 兼容旧字段
            s["active"] = True
            if not isinstance(s.get("miss_groups"), dict):
                s["miss_groups"] = {}
            s["miss_groups"][str(style)] = missed
        self.save()
        for r in real_orders_to_fire:
            threading.Thread(target=_do_real_order_for_user, kwargs=r, daemon=True).start()
        return True, results

    def process_result(self, style, qishu, result_sum, history_getter=None):
        """每期开奖后调用：结算 pending + 按 style 推进 mul_idx / 退出 miss 阶段。"""
        style = int(style)
        with self.lock:
            s = self.state
            last_key = f"last_qishu_{style}"
            # ⭐ 用后缀匹配避免短/长期号双广播
            if _qishu_match(qishu, s.get(last_key)):
                return
            s[last_key] = str(qishu)

            muls = s.get("multipliers") or [1.0]
            hist_key = f"records_{style}"
            pnl_key  = f"total_pnl_{style}"
            phase_key  = f"cur_phase_{style}"
            mul_key    = f"mul_idx_{style}"
            locked_key = f"locked_missed_{style}"

            # 先结算所有 pending 的遗漏记录（无论 phase 都结算）
            for rec in s.get(hist_key, []):
                if rec.get("pending") and rec.get("qishu") and str(rec["qishu"]) == str(qishu):
                    rec_mul = float(rec.get("multiplier", 1.0))
                    rec_bet = float(rec.get("bet_amount", 0))
                    rec_base = rec_bet / rec_mul if rec_mul else rec_bet
                    won, net_pnl, _ = sim_calc_pnl(rec.get("positions", []), result_sum, rec_base, rec_mul)
                    rec.update({"result": result_sum, "net_pnl": round(net_pnl), "won": won, "pending": False})
                    s[pnl_key] += round(net_pnl)

            # 只在 miss 阶段推进倍率
            phase = s.get(phase_key, "idle")
            if phase != "miss":
                self.save()
                return

            locked = s.get(locked_key) or []
            m_idx = min(s.get(mul_key, 0), len(muls)-1)
            # 判断是否任一锁定组命中
            won_any = any(result_sum in positions for positions in locked)
            if won_any:
                # 命中：退出 miss，mul_idx 归零，清 locked
                s[phase_key]  = "idle"
                s[mul_key]    = 0
                s[locked_key] = []
                print(f"[MISS process] style={style} qishu={qishu} 命中 → 退出miss阶段")
            else:
                if m_idx >= len(muls)-1:
                    # 倍率序列耗尽：爆档，退出
                    s[phase_key]  = "idle"
                    s[mul_key]    = 0
                    s[locked_key] = []
                    print(f"[MISS process] style={style} qishu={qishu} 不中且倍率序列耗尽 → 退出miss阶段（爆档）")
                else:
                    s[mul_key] = m_idx + 1
                    print(f"[MISS process] style={style} qishu={qishu} 不中 → 推进 mul_idx {m_idx} → {m_idx+1} (下一期mul={muls[m_idx+1]}x)")

        self.save()

    def get_status(self):
        with self.lock:
            s = self.state
            return {
                "active": s["active"],
                "cur_phase": s.get("cur_phase","idle"),
                # ⭐ 新：按 style 拆分
                "cur_phase_210": s.get("cur_phase_210","idle"),
                "cur_phase_60":  s.get("cur_phase_60","idle"),
                "mul_idx_210":   s.get("mul_idx_210", 0),
                "mul_idx_60":    s.get("mul_idx_60", 0),
                "locked_missed_210": s.get("locked_missed_210", []),
                "locked_missed_60":  s.get("locked_missed_60",  []),
                "miss_n": s["miss_n"],
                "base_amount": s["base_amount"],
                "multipliers": s["multipliers"],
                "mul_idx": s.get("mul_idx", 0),
                "total_pnl_210": s["total_pnl_210"],
                "total_pnl_60": s["total_pnl_60"],
                "pnl_date": s.get("pnl_date", now_cn().strftime("%Y-%m-%d")),
                "records_210": s["records_210"][:50],
                "records_60": s["records_60"][:50],
                "miss_groups": s.get("miss_groups", {}),
                "auto_enabled_210": s.get("auto_enabled_210", False),
                "auto_enabled_60": s.get("auto_enabled_60", False),
                "real_enabled_210": bool(s.get("real_enabled_210")),
                "real_enabled_60":  bool(s.get("real_enabled_60")),
                "groups_text": self._groups_text,
                "groups_text_210": self._groups_text,
                "groups_text_60": self._groups_text,
                "random_text": self._random_text,
                "muls_text": self._muls_text,
                "muls_text_210": self._muls_text,
                "muls_text_60": self._muls_text,
                "miss_n_210": self.state["miss_n"],
                "miss_n_60": self.state["miss_n"],
                "base_amount_210": self.state["base_amount"],
                "base_amount_60": self.state["base_amount"],
            }

    def reset(self, style=None):
        with self.lock:
            s = self.state
            if style is None or style == 210:
                s["records_210"] = []
                s["total_pnl_210"] = 0
                s["cur_phase_210"] = "idle"
                s["mul_idx_210"] = 0
                s["locked_missed_210"] = []
            if style is None or style == 60:
                s["records_60"] = []
                s["total_pnl_60"] = 0
                s["cur_phase_60"] = "idle"
                s["mul_idx_60"] = 0
                s["locked_missed_60"] = []
            if style is None:
                s["active"] = False
                s["miss_groups"] = {"210": [], "60": []}
                s["mul_idx"] = 0
                s["cur_phase"] = "idle"
        self.save()
        return True, "已重置"


# ══════════════════════════════════════════════════════════════
#  📋 计划跟投（杀5余）：读 wanjia28 的 8 个杀5余预测专家，
#  挑连对≥4 的、连对最多的专家的预测，跟着下注。仅欢乐210。
# ══════════════════════════════════════════════════════════════
# 杀5余N → 要杀掉（不下）的尾数：{N, N+5}。
#   5余0 杀尾0/5、5余1 杀尾1/6、5余2 杀尾2/7、5余3 杀尾3/8、5余4 杀尾4/9
# 多个计划合并 = 并集要杀的尾数（杀的越多、下注号越少）；下注 = 尾数不在杀集里的号。
PLAN_KILL_TAILS = {
    "5余0": [0, 5],
    "5余1": [1, 6],
    "5余2": [2, 7],
    "5余3": [3, 8],
    "5余4": [4, 9],
}
def _plan_positions_from_kills(killed_tails):
    """尾数不在 killed_tails 里的 0~27 号即为下注号"""
    ks = set(killed_tails)
    return [n for n in range(28) if (n % 10) not in ks]
# 兼容：单计划下注号（尾数不含 {N,N+5} 的号）
PLAN_KILL5_MAP = {p: _plan_positions_from_kills(t) for p, t in PLAN_KILL_TAILS.items()}
WANJIA_BASE = "https://www.wanjia28.com/jnd28/7"  # /1.html ~ /8.html = 8 个杀5余专家
_PLAN_CACHE = {"ts": 0, "experts": None, "pending_qishu": None,
               "last_ok_experts": None, "last_ok_pending": None, "last_ok_ts": 0}
_PLAN_CACHE_LOCK = threading.Lock()
_PLAN_INFLIGHT = {"on": False}  # 同一时刻只允许一个抓取，避免多请求并发打爆 wanjia28
# ⭐ 预测每期才变（210 约 3.5 分钟一期），缓存放长到 90 秒，避免频繁抓触发 wanjia28
#    的 Cloudflare 反爬把服务器 IP 拉黑（2026-07-07 踩过：抓太狠被封，全站超时/403）
_PLAN_CACHE_TTL = 90  # 秒
_WANJIA_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "zh-CN,zh;q=0.9",
    "Referer": "https://www.wanjia28.com/jnd28/",
    "Connection": "keep-alive",
}

def _wanjia_parse_expert(raw):
    """解析一个专家页面 → [(qishu, '5余N'|None, '对'|'错'|'？'), ...] 最新在前"""
    m = re.search(r"<table.*?</table>", raw, re.S)
    if not m:
        return []
    out = []
    for r in re.findall(r"<tr.*?</tr>", m.group(0), re.S):
        cells = re.findall(r"<t[dh][^>]*>(.*?)</t[dh]>", r, re.S)
        c = [html_lib.unescape(re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", x)).strip()) for x in cells]
        if len(c) == 5 and c[0].isdigit():
            pm = re.search(r"5余(\d)", c[3])
            pred = f"5余{pm.group(1)}" if pm else None
            out.append((c[0], pred, c[4]))
    return out

def _fetch_wanjia_plans():
    """抓 8 个杀5余专家（带 90s 缓存 + 失败兜底旧数据）。返回 (experts_list, pending_qishu)。
    - 缓存新鲜 → 直接返回，不打 wanjia28
    - 需要刷新 → 用一个 session（keep-alive）串行抓 8 个
    - 抓取失败（Cloudflare 挡/超时）→ 返回上次成功的旧数据，避免预览空白"""
    now = time.time()
    with _PLAN_CACHE_LOCK:
        if _PLAN_CACHE["experts"] and (now - _PLAN_CACHE["ts"]) < _PLAN_CACHE_TTL:
            return _PLAN_CACHE["experts"], _PLAN_CACHE["pending_qishu"]
        # 已有别的线程在抓 → 不重复打，直接返回现有缓存（新鲜/旧/last_ok/空）
        if _PLAN_INFLIGHT["on"]:
            if _PLAN_CACHE["experts"]:
                return _PLAN_CACHE["experts"], _PLAN_CACHE["pending_qishu"]
            if _PLAN_CACHE["last_ok_experts"]:
                return _PLAN_CACHE["last_ok_experts"], _PLAN_CACHE["last_ok_pending"]
            return [], None
        _PLAN_INFLIGHT["on"] = True
    experts = []
    ok_count = 0
    try:
        sess = requests.Session()
        sess.headers.update(_WANJIA_HEADERS)
        for i in range(1, 9):
            try:
                r = sess.get(f"{WANJIA_BASE}/{i}.html", timeout=6, verify=False)
                parsed = _wanjia_parse_expert(r.text)
                experts.append(parsed)
                if parsed:
                    ok_count += 1
            except Exception as e:
                print(f"[wanjia] expert {i} 抓取失败: {e}")
                experts.append([])
    except Exception as e:
        print(f"[wanjia] session 异常: {e}")
    # 待开奖期号：任一专家第一行（对错=？）的期号
    pending_qishu = None
    for rows in experts:
        if rows and rows[0][2] not in ("对", "错"):
            pending_qishu = rows[0][0]
            break
    if not pending_qishu:
        for rows in experts:
            if rows:
                pending_qishu = rows[0][0]
                break
    with _PLAN_CACHE_LOCK:
        _PLAN_INFLIGHT["on"] = False
        if ok_count >= 1:
            # 抓到有效数据 → 更新缓存 + 记为 last_ok
            _PLAN_CACHE.update({"ts": time.time(), "experts": experts, "pending_qishu": pending_qishu,
                                "last_ok_experts": experts, "last_ok_pending": pending_qishu,
                                "last_ok_ts": time.time()})
            return experts, pending_qishu
        # 全部失败（被 Cloudflare 挡）→ 用上次成功的旧数据兜底，且把 ts 前推一点避免立刻再抓
        _PLAN_CACHE["ts"] = time.time() - _PLAN_CACHE_TTL + 20  # 20 秒后才允许重试，别猛打
        if _PLAN_CACHE["last_ok_experts"]:
            print(f"[wanjia] 本次全失败，用上次成功数据兜底（{int(time.time() - _PLAN_CACHE['last_ok_ts'])}s 前）")
            return _PLAN_CACHE["last_ok_experts"], _PLAN_CACHE["last_ok_pending"]
        return experts, pending_qishu

def _plan_lianzhong(rows):
    """从最近已开奖往前数连续'对'的数量，遇'错'即断（'？'跳过）"""
    cnt = 0
    for _q, _pred, dc in rows:
        if dc == "对":
            cnt += 1
        elif dc == "错":
            break
        # '？' 未开奖 → 跳过继续
    return cnt

# ── 冷号：算 8-19 里遗漏≥20 的号（剔除不下）──
# ⭐ 优先用系统自己的 210 开奖历史（新鲜、期号对齐），避免 28vp 滞后 1 期
#   导致"刚开过的号还被当冷号"（如 3454059 开了10，3454060 却把10当冷号剔了）。
_COLD_CACHE = {"ts": 0, "cold": None, "miss": None}
_COLD_CACHE_LOCK = threading.Lock()
_COLD_CACHE_TTL = 20  # 秒（仅 28vp 兜底路径用）
COLD_CHECK_RANGE = range(8, 20)   # 只检查 8~19
COLD_MISS_THRESHOLD = 20          # 遗漏≥20 期视为冷号

def _cold_from_sums(sums):
    """sums: 和值列表（最新在前）。返回 (cold_set, miss_dict)。"""
    if not sums:
        return set(), {}
    miss = {}
    for n in range(28):
        c = 0
        for s in sums:
            if s == n:
                break
            c += 1
        else:
            c = len(sums)  # 全程未出现
        miss[n] = c
    cold = {n for n in COLD_CHECK_RANGE if miss.get(n, 0) >= COLD_MISS_THRESHOLD}
    return cold, miss

def _fetch_cold_numbers(history=None):
    """返回 (cold_set, miss_dict)。cold_set = 8~19 里遗漏≥20 的号。
    - history: 系统 210 历史 [{"sum":..,"qishu":..}, ...] 最新在前 → 优先用（新鲜对齐）
    - 无 history → 兜底走 28vp（带缓存），可能滞后 1 期
    抓取失败 → 空集合（保守：不误剔号）。"""
    # 优先：系统 210 历史（最新最准）
    if history:
        sums = []
        for h in history:
            try:
                v = h.get("sum") if isinstance(h, dict) else h
                if v is not None:
                    sums.append(int(v))
            except Exception:
                pass
        if len(sums) >= COLD_MISS_THRESHOLD:  # 至少要有阈值那么多期才判得准
            return _cold_from_sums(sums)
    # 兜底：28vp（带缓存）
    with _COLD_CACHE_LOCK:
        if _COLD_CACHE["cold"] is not None and (time.time() - _COLD_CACHE["ts"]) < _COLD_CACHE_TTL:
            return _COLD_CACHE["cold"], _COLD_CACHE["miss"]
    sums = []
    try:
        r = requests.get("https://28vp.com/data/get/checkData",
                         params={"type": "jnd28"}, headers=VP28_HEADERS,
                         timeout=8, verify=False)
        d = r.json()
        lst = d.get("issue") or d.get("data") or []
        for it in lst:
            try:
                sums.append(int(it.get("sum")))
            except Exception:
                pass
    except Exception as e:
        print(f"[cold] 28vp 抓取失败: {e}")
        return set(), {}
    if not sums:
        return set(), {}
    cold, miss = _cold_from_sums(sums)
    with _COLD_CACHE_LOCK:
        _COLD_CACHE.update({"ts": time.time(), "cold": cold, "miss": miss})
    return cold, miss

def _plan_select(experts, min_lianzhong=4, cold_set=None):
    """选号：连对≥min 的专家里，**必须凑到两个不一样的预测**才下单。
    取连对最高的当第 1 个，再找连对最高且预测不同的当第 2 个。
    只有一种预测（都一样）→ 空仓（返回 None）。
    合并 = 并集两个预测要杀的尾数；下注 = 尾数不在杀集里的号，再剔冷号。"""
    cands = []  # (expert_id, lianzhong, pred)
    for idx, rows in enumerate(experts, 1):
        if not rows:
            continue
        lz = _plan_lianzhong(rows)
        pending_pred = rows[0][1]  # 第一行 = 待开奖预测
        if lz >= min_lianzhong and pending_pred in PLAN_KILL_TAILS:
            cands.append((idx, lz, pending_pred))
    if not cands:
        return None
    # 连对降序、专家号升序
    cands.sort(key=lambda c: (-c[1], c[0]))
    first = cands[0]
    # 找第一个跟 first 预测不同的
    second = None
    for c in cands[1:]:
        if c[2] != first[2]:
            second = c
            break
    if second is None:
        return None  # 只有一种预测 → 空仓（必须两个不同预测才下）
    chosen = [first, second]
    preds = [first[2], second[2]]
    killed_tails = set(PLAN_KILL_TAILS[first[2]]) | set(PLAN_KILL_TAILS[second[2]])
    # 下注号 = 尾数不在杀集里的号
    posset = set(_plan_positions_from_kills(killed_tails))
    # 剔除冷号
    removed = []
    if cold_set:
        removed = sorted(posset & set(cold_set))
        posset -= set(cold_set)
    return {
        "preds": preds,                        # 两个不同预测
        "lianzhong": first[1],                 # 最高连对
        "expert_ids": [c[0] for c in chosen],  # 参与的两个专家号
        "detail": [{"expert": c[0], "lianzhong": c[1], "pred": c[2]} for c in chosen],
        "killed_tails": sorted(killed_tails),  # 被杀掉的尾数
        "positions": sorted(posset),           # 下注号 - 冷号
        "removed_cold": removed,               # 被剔除的冷号
    }


class DaweiEngine:
    """打尾引擎：自动读最近 N 期开奖号，按出现顺序提取 K 个不重复尾数，下注这些尾数位置（0-9）。
    每期都重算尾数。倍率阶梯：不中→下个倍率（爆档归零）；中了→归零。
    可选连续不中暂停 K 期，恢复后第一期再不中→再暂停 K 期。
    每个用户每个 slot 一个实例，state_210 / state_60 独立。"""
    def __init__(self, save_file=None, engine_name="unknown", username=None):
        self.lock = threading.Lock()
        self.save_file = save_file or f"{BASE_DIR}/dawei_state.json"
        self.engine_name = engine_name
        self.username = username
        self.state_210 = self._empty_state()
        self.state_60  = self._empty_state()
        self.load()
        threading.Thread(target=self._daily_reset_loop, daemon=True).start()

    def _empty_state(self):
        return {
            "tail_count": 5,
            "detect_n": 30,
            "base_amount": 1000,
            "multipliers": [1.0],
            "pause_periods": 0,
            "running": False,
            "real_enabled": False,
            "mul_idx": 0,
            "pause_remaining": 0,
            "consecutive_losses": 0,  # 连续不中计数；1=只第1次不中不触发；>=2 才暂停+倍投
            "auto_last_qishu": None,
            "last_qishu": None,
            "locked_tails": [],
            "records": [],
            "total_pnl": 0,
            "pnl_date": now_cn().strftime("%Y-%m-%d"),
        }

    def _get_state(self, style):
        return self.state_210 if int(style) == 210 else self.state_60

    def _daily_reset_loop(self):
        """每日 0 点：
        - records 改成 3 天滚动保留：删超过 3 天的，保留近 3 天
        - total_pnl 跟随 records 重算（保留 records 内已结算行的 net_pnl 求和）
        - 运行态（mul_idx / pause_remaining / consecutive_losses / locked_tails）按天清零，
          算每天 0 点开新庄，跟 sim/miss 引擎一致
        """
        while True:
            now = now_cn()
            next_midnight = (now + timedelta(days=1)).replace(hour=0, minute=0, second=5, microsecond=0)
            time.sleep(max((next_midnight - now).total_seconds(), 1))
            with self.lock:
                cutoff = (now_cn() - timedelta(days=3)).strftime("%Y-%m-%d %H:%M:%S")
                for s in (self.state_210, self.state_60):
                    kept = [r for r in s.get("records", []) if (r.get("created_at") or "") >= cutoff]
                    s["records"] = kept
                    s["total_pnl"] = sum(int(r.get("net_pnl") or 0) for r in kept if r.get("won") is not None)
                    s["mul_idx"] = 0
                    s["pause_remaining"] = 0
                    s["consecutive_losses"] = 0
                    s["locked_tails"] = []
                    s["pnl_date"] = now_cn().strftime("%Y-%m-%d")
            self.save()
            print(f"[DAWEI] 每日0点：records 3天滚动清理完成（cutoff={cutoff}）")

    def save(self):
        try:
            with open(self.save_file, "w", encoding="utf-8") as f:
                json.dump({"state_210": self.state_210, "state_60": self.state_60},
                          f, ensure_ascii=False)
        except Exception as e:
            print(f"[DAWEI SAVE] {e}")

    def load(self):
        try:
            with open(self.save_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            for k, v in data.get("state_210", {}).items():
                self.state_210[k] = v
            for k, v in data.get("state_60", {}).items():
                self.state_60[k] = v
            # 重启后**保留** running / real_enabled / mul_idx / pause_remaining / cl 等运行态：
            # broadcast 一恢复就继续按原节奏跑，跟 sim/miss 引擎一致（用户体感"重启不丢参与"）
        except FileNotFoundError:
            pass
        except Exception as e:
            print(f"[DAWEI LOAD] {e}")

    def configure(self, style, tail_count, detect_n, base_amount, muls_text, pause_periods):
        style = int(style)
        if isinstance(muls_text, str):
            muls = sim_parse_multipliers(muls_text)
        else:
            muls = list(muls_text or [1.0])
        with self.lock:
            s = self._get_state(style)
            s["tail_count"]    = max(1, min(10, int(tail_count or 5)))
            s["detect_n"]      = max(1, min(200, int(detect_n or 30)))
            s["base_amount"]   = max(100, int(base_amount or 1000))
            s["multipliers"]   = muls if muls else [1.0]
            s["pause_periods"] = max(0, int(pause_periods or 0))
        self.save()
        return True, "配置已保存"

    def set_running(self, style, on):
        with self.lock:
            s = self._get_state(int(style))
            s["running"] = bool(on)
            if on:
                s["mul_idx"] = 0
                s["pause_remaining"] = 0
                s["consecutive_losses"] = 0
                s["locked_tails"] = []
                s["auto_last_qishu"] = None
        self.save()
        return True, "started" if on else "stopped"

    def set_real(self, style, on):
        with self.lock:
            s = self._get_state(int(style))
            s["real_enabled"] = bool(on)
        self.save()
        return True, "on" if on else "off"

    @staticmethod
    def _extract_tails(history, n, tail_count):
        """从 history 最近 n 期取尾数，按出现顺序去重，最多 tail_count 个。"""
        recent = []
        for h in (history or [])[:int(n)]:
            try:
                v = h.get("sum") if "sum" in h else h.get("sum_num", -1)
                v = int(v)
                if 0 <= v <= 27:
                    t = v % 10
                    if t not in recent:
                        recent.append(t)
                        if len(recent) >= int(tail_count):
                            break
            except Exception:
                pass
        return recent

    def auto_execute(self, style, history, next_qishu):
        """每期新期号触发：算尾数 + 下单/记 sim 记录 + 触发真实下单。
        暂停期内只递减 pause_remaining 不下注；上一期 pending 未结算时跳过等待。"""
        style = int(style)
        qishu = str(next_qishu or "")
        if not qishu:
            return False, []
        real_on = False
        positions = []
        base = 0
        multiplier = 1.0
        m_idx = 0
        with self.lock:
            s = self._get_state(style)
            if not s.get("running"):
                return False, []
            if _qishu_match(s.get("auto_last_qishu"), qishu):
                return False, []
            # 上一期 pending 还在 → 等结算后再下下一期
            for rec in s.get("records", []):
                if rec.get("pending") and str(rec.get("qishu")) != qishu:
                    return False, []
            # 已经在本期下过 → 跳过
            for rec in s.get("records", []):
                if str(rec.get("qishu")) == qishu and rec.get("pending"):
                    s["auto_last_qishu"] = qishu
                    return False, []
            # 暂停中：递减并记 skip 行
            if int(s.get("pause_remaining", 0)) > 0:
                s["pause_remaining"] = int(s["pause_remaining"]) - 1
                s["auto_last_qishu"] = qishu
                left = s["pause_remaining"]
                rec = {
                    "type": "dawei", "qishu": qishu, "result": None,
                    "positions": [], "tails": [], "multiplier": 0,
                    "bet_amount": 0, "net_pnl": 0,
                    "won": None, "pending": False, "skipped": True,
                    "label": f"⏸ 暂停中（剩 {left} 期）",
                    "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                    "mul_step": int(s.get("mul_idx", 0)),
                }
                s["records"].insert(0, rec)
                s["records"] = s["records"][:200]
                self.save()
                return True, [{"qishu": qishu, "skipped": True, "pause_left": left}]
            # 算尾数
            tail_count = int(s.get("tail_count", 5))
            detect_n   = int(s.get("detect_n", 30))
            tails = self._extract_tails(history or [], detect_n, tail_count)
            if not tails:
                s["auto_last_qishu"] = qishu
                print(f"[DAWEI auto] style={style} qishu={qishu} 无尾数样本，跳过")
                return False, []
            base = int(s.get("base_amount", 1000))
            muls = s.get("multipliers") or [1.0]
            m_idx = min(int(s.get("mul_idx", 0)), len(muls)-1)
            multiplier = float(muls[m_idx])
            # 尾数 → 所有 0-27 中尾数 ∈ 集合 的位置（如尾数{1,5,9,7,6} → 1,5,6,7,9, 11,15,16,17,19, 21,25,26,27）
            tail_set = set(tails)
            positions = sorted([n for n in range(28) if (n % 10) in tail_set])
            bet_amount = round(base * multiplier)
            rec = {
                "type": "dawei", "qishu": qishu, "result": None,
                "positions": positions, "tails": tails,
                "multiplier": multiplier,
                "bet_amount": bet_amount, "net_pnl": None,
                "won": None, "pending": True,
                "label": f"打尾·{m_idx+1}倍位",
                "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                "mul_step": m_idx,
            }
            s["records"].insert(0, rec)
            s["records"] = s["records"][:200]
            s["locked_tails"] = list(positions)
            s["auto_last_qishu"] = qishu
            real_on = bool(s.get("real_enabled"))
            print(f"[DAWEI auto] style={style} qishu={qishu} tails={tails} mul={multiplier}x bet={bet_amount}")
        self.save()
        if self.username and real_on and positions:
            try:
                threading.Thread(
                    target=_do_real_order_for_user,
                    kwargs={
                        "username": self.username,
                        "style": style,
                        "expect": qishu,
                        "press_str": _build_press_str(positions, base, multiplier),
                        "source": f"dawei_seq_{m_idx+1}",
                    },
                    daemon=True).start()
            except Exception as e:
                print(f"[DAWEI real_order] {e}")
        return True, [{"qishu": qishu, "positions": positions, "tails": tails,
                       "bet": round(base * multiplier), "multiplier": multiplier}]

    def process_result(self, style, qishu, result_sum):
        """开奖后结算 + 推进倍率 + 触发暂停。中清暂停，不中按设定暂停 K 期。"""
        style = int(style)
        with self.lock:
            s = self._get_state(style)
            if _qishu_match(qishu, s.get("last_qishu")):
                return
            s["last_qishu"] = str(qishu)
            muls = s.get("multipliers") or [1.0]
            settled_won  = False
            settled_lost = False
            for rec in s.get("records", []):
                if rec.get("pending") and str(rec.get("qishu")) == str(qishu):
                    positions = rec.get("positions", []) or []
                    rec_mul = float(rec.get("multiplier", 1.0))
                    rec_bet = float(rec.get("bet_amount", 0))
                    rec_base = rec_bet / rec_mul if rec_mul else rec_bet
                    won, net_pnl, _ = sim_calc_pnl(positions, result_sum, rec_base, rec_mul)
                    rec.update({"result": result_sum, "net_pnl": round(net_pnl),
                                "won": won, "pending": False})
                    s["total_pnl"] += round(net_pnl)
                    if won: settled_won = True
                    else:   settled_lost = True
            if settled_won:
                s["mul_idx"] = 0
                s["pause_remaining"] = 0
                s["consecutive_losses"] = 0
                print(f"[DAWEI process] style={style} qishu={qishu} 命中 → 倍率归零，连不中清零")
            elif settled_lost:
                cl = int(s.get("consecutive_losses", 0)) + 1
                pp = int(s.get("pause_periods", 0))
                # 规则（解耦）：
                #   1) 每次不中 → 倍率 ++（爆档保持最高，不归零；直到中才归零）
                #   2) 连续 cl 次不中累计到 pp 次 → 触发暂停 pp 期，连不中计数清零
                #      （暂停只是冷却，不再额外推倍率——倍率已经在 pp 次不中过程中累计了 pp 次）
                m_idx = int(s.get("mul_idx", 0))
                if m_idx < len(muls) - 1:
                    s["mul_idx"] = m_idx + 1
                    bump_txt = f"倍率 {m_idx}→{m_idx+1}"
                else:
                    # 爆档归零，跟 sim/miss 引擎一致
                    s["mul_idx"] = 0
                    bump_txt = f"爆档归零（{m_idx}→0）"
                if pp > 0 and cl >= pp:
                    s["pause_remaining"] = pp
                    s["consecutive_losses"] = 0
                    print(f"[DAWEI process] style={style} qishu={qishu} 不中 → {bump_txt}；连续{cl}/{pp} 触发暂停 {pp} 期 + 连不中清零")
                else:
                    s["consecutive_losses"] = cl
                    cl_show = f"{cl}/{pp}" if pp > 0 else f"{cl}"
                    print(f"[DAWEI process] style={style} qishu={qishu} 不中 → {bump_txt}；连不中 {cl_show}")
        self.save()

    def reset(self, style=None):
        with self.lock:
            for st_int, s in ((210, self.state_210), (60, self.state_60)):
                if style is None or int(style) == st_int:
                    s["records"] = []
                    s["total_pnl"] = 0
                    s["mul_idx"] = 0
                    s["pause_remaining"] = 0
                    s["consecutive_losses"] = 0
                    s["locked_tails"] = []
                    s["auto_last_qishu"] = None
                    s["last_qishu"] = None
        self.save()
        return True, "已重置"

    def get_status(self):
        with self.lock:
            def snap(s):
                return {
                    "tail_count":         s.get("tail_count", 5),
                    "detect_n":           s.get("detect_n", 30),
                    "base_amount":        s.get("base_amount", 1000),
                    "multipliers":        s.get("multipliers", [1.0]),
                    "pause_periods":      s.get("pause_periods", 0),
                    "running":            bool(s.get("running")),
                    "real_enabled":       bool(s.get("real_enabled")),
                    "mul_idx":            s.get("mul_idx", 0),
                    "pause_remaining":    s.get("pause_remaining", 0),
                    "consecutive_losses": s.get("consecutive_losses", 0),
                    "locked_tails":       s.get("locked_tails", []),
                    "records":            s.get("records", [])[:50],
                    "total_pnl":          s.get("total_pnl", 0),
                    "pnl_date":           s.get("pnl_date", now_cn().strftime("%Y-%m-%d")),
                }
            muls_text = "-".join(str(x) for x in (self.state_210.get("multipliers") or [1.0]))
            return {
                "210": snap(self.state_210),
                "60":  snap(self.state_60),
                "muls_text_210": "-".join(str(x) for x in (self.state_210.get("multipliers") or [1.0])),
                "muls_text_60":  "-".join(str(x) for x in (self.state_60.get("multipliers")  or [1.0])),
            }


class PlanEngine:
    """📋 计划跟投引擎（杀5余，仅欢乐210）：
    每期读 wanjia28 的 8 个杀5余专家，挑连对≥4 且连对最多的（并列取众数），
    跟着下注该杀5余对应的号码位置。无倍率（恒 1 倍基础金额）。
    止盈：total_pnl 达到 stop_profit 自动停（0=不止盈）。"""
    STYLE = 210

    def __init__(self, save_file=None, username=None):
        self.lock = threading.Lock()
        self.save_file = save_file or f"{BASE_DIR}/plan_state.json"
        self.username = username
        self.state = self._empty_state()
        self.load()
        threading.Thread(target=self._daily_reset_loop, daemon=True).start()

    def _empty_state(self):
        return {
            "base_amount": 1000,
            "stop_profit": 0,          # 0 = 不止盈
            "min_lianzhong": 4,        # 连对阈值
            "multipliers": [1.0],      # 倍率序列（不中→下个，爆档归零；中了→归零）
            "mul_idx": 0,              # 当前倍率位
            "running": False,
            "real_enabled": False,
            "auto_last_qishu": None,
            "last_qishu": None,
            "cur_pred": None,          # 兼容旧字段（取 preds[0]）
            "cur_preds": [],           # 当前选中预测（1~2 个）
            "cur_lianzhong": 0,
            "cur_expert_ids": [],
            "cur_removed_cold": [],    # 本期剔除的冷号
            "cur_killed_tails": [],    # 本期杀掉的尾数
            "records": [],
            "total_pnl": 0,
            "pnl_date": now_cn().strftime("%Y-%m-%d"),
        }

    def _daily_reset_loop(self):
        while True:
            now = now_cn()
            nxt = (now + timedelta(days=1)).replace(hour=0, minute=0, second=5, microsecond=0)
            time.sleep(max((nxt - now).total_seconds(), 1))
            with self.lock:
                s = self.state
                s["records"] = []
                s["total_pnl"] = 0
                s["cur_pred"] = None
                s["cur_lianzhong"] = 0
                s["cur_expert_ids"] = []
                s["mul_idx"] = 0
                s["pnl_date"] = now_cn().strftime("%Y-%m-%d")
            self.save()
            print("[PLAN] 每日0点清空完成")

    def save(self):
        try:
            with open(self.save_file, "w", encoding="utf-8") as f:
                json.dump({"state": self.state}, f, ensure_ascii=False)
        except Exception as e:
            print(f"[PLAN SAVE] {e}")

    def load(self):
        try:
            with open(self.save_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            for k, v in (data.get("state") or {}).items():
                self.state[k] = v
            # 重启保留 running/real（跟 sim/dawei 一致，不丢参与）
        except FileNotFoundError:
            pass
        except Exception as e:
            print(f"[PLAN LOAD] {e}")

    def configure(self, base_amount, stop_profit, min_lianzhong=4, muls_text=None):
        with self.lock:
            s = self.state
            s["base_amount"] = max(100, int(base_amount or 1000))
            s["stop_profit"] = max(0, int(stop_profit or 0))
            s["min_lianzhong"] = max(1, min(20, int(min_lianzhong or 4)))
            if muls_text is not None:
                muls = sim_parse_multipliers(muls_text)
                s["multipliers"] = muls if muls else [1.0]
        self.save()
        return True, "配置已保存"

    def set_running(self, on):
        with self.lock:
            self.state["running"] = bool(on)
            if on:
                self.state["auto_last_qishu"] = None
                self.state["mul_idx"] = 0
        self.save()
        return True, "started" if on else "stopped"

    def set_real(self, on):
        with self.lock:
            self.state["real_enabled"] = bool(on)
        self.save()
        return True, "on" if on else "off"

    def auto_execute(self, next_qishu, history=None):
        """新期号触发：抓 wanjia28 选号，命中就下注（sim 记录 + 真实下单）。
        history: 系统 210 开奖历史（最新在前），用于算冷号（新鲜对齐，避免 28vp 滞后）。"""
        qishu = str(next_qishu or "")
        if not qishu:
            return False, None
        with self.lock:
            s = self.state
            if not s.get("running"):
                return False, None
            if _qishu_match(s.get("auto_last_qishu"), qishu):
                return False, None
            # 上一期 pending 未结算 → 等
            for rec in s.get("records", []):
                if rec.get("pending") and str(rec.get("qishu")) != qishu:
                    return False, None
            for rec in s.get("records", []):
                if str(rec.get("qishu")) == qishu and rec.get("pending"):
                    s["auto_last_qishu"] = qishu
                    return False, None
            base = int(s.get("base_amount", 1000))
            min_lz = int(s.get("min_lianzhong", 4))
        # 抓取放锁外（HTTP 慢）
        try:
            experts, pending_qishu = _fetch_wanjia_plans()
        except Exception as e:
            print(f"[PLAN auto] 抓取失败 {e}")
            return False, None
        # ⭐ 安全防呆：wanjia28 数据的待开期号必须跟本期一致才用来下注。
        #   若被 Cloudflare 封 / 抓不到（数据是旧的或空），期号对不上 → 空仓，
        #   绝不拿上一期的旧预测去下这一期的单（尤其真实下单）。
        if not pending_qishu or not _qishu_match(pending_qishu, qishu):
            with self.lock:
                s = self.state
                s["auto_last_qishu"] = qishu
                s["cur_pred"] = None; s["cur_preds"] = []; s["cur_lianzhong"] = 0
                s["cur_expert_ids"] = []; s["cur_removed_cold"] = []; s["cur_killed_tails"] = []
                rec = {
                    "type": "plan", "qishu": qishu, "result": None,
                    "pred": None, "preds": [], "positions": [], "bet_amount": 0,
                    "net_pnl": 0, "won": None, "pending": False, "skipped": True,
                    "label": "空仓·预测源暂不可用(期号不匹配)",
                    "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                }
                s["records"].insert(0, rec)
                s["records"] = s["records"][:200]
                self.save()
            print(f"[PLAN auto] qishu={qishu} 预测源期号={pending_qishu} 不匹配 → 空仓")
            return True, {"qishu": qishu, "skipped": True}
        cold_set, _miss = _fetch_cold_numbers(history)
        sel = _plan_select(experts, min_lz, cold_set)
        real_on = False
        positions = []
        with self.lock:
            s = self.state
            s["auto_last_qishu"] = qishu
            # 空仓：无专家达标，或剔除冷号后没号可下
            if (not sel) or (not sel.get("positions")):
                s["cur_pred"] = None
                s["cur_preds"] = []
                s["cur_lianzhong"] = 0
                s["cur_expert_ids"] = []
                s["cur_removed_cold"] = (sel or {}).get("removed_cold", [])
                s["cur_killed_tails"] = (sel or {}).get("killed_tails", [])
                reason = "未凑到两个不同预测" if not sel else "剔冷号后无号可下"
                rec = {
                    "type": "plan", "qishu": qishu, "result": None,
                    "pred": None, "preds": [], "positions": [], "bet_amount": 0,
                    "net_pnl": 0, "won": None, "pending": False, "skipped": True,
                    "label": f"空仓·{reason}",
                    "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                }
                s["records"].insert(0, rec)
                s["records"] = s["records"][:200]
                self.save()
                return True, {"qishu": qishu, "skipped": True}
            preds = sel["preds"]
            positions = sel["positions"]
            removed_cold = sel.get("removed_cold", [])
            killed_tails = sel.get("killed_tails", [])
            preds_txt = "+".join(preds)
            s["cur_pred"] = preds[0]
            s["cur_preds"] = preds
            s["cur_lianzhong"] = sel["lianzhong"]
            s["cur_expert_ids"] = sel["expert_ids"]
            s["cur_removed_cold"] = removed_cold
            s["cur_killed_tails"] = killed_tails
            # 倍率：按当前倍率位下注
            muls = s.get("multipliers") or [1.0]
            m_idx = min(int(s.get("mul_idx", 0)), len(muls) - 1)
            multiplier = float(muls[m_idx])
            bet_amount = round(base * multiplier)
            cold_txt = f"·剔冷{removed_cold}" if removed_cold else ""
            mul_txt = f"·{m_idx+1}倍位({multiplier}x)" if len(muls) > 1 else ""
            rec = {
                "type": "plan", "qishu": qishu, "result": None,
                "pred": preds_txt, "preds": preds, "positions": positions,
                "lianzhong": sel["lianzhong"], "expert_ids": sel["expert_ids"],
                "removed_cold": removed_cold, "killed_tails": killed_tails,
                "multiplier": multiplier, "mul_step": m_idx,
                "bet_amount": bet_amount, "net_pnl": None,
                "won": None, "pending": True,
                "label": f"跟投·{preds_txt}(连对{sel['lianzhong']}){mul_txt}{cold_txt}",
                "created_at": now_cn().strftime("%Y-%m-%d %H:%M:%S"),
            }
            s["records"].insert(0, rec)
            s["records"] = s["records"][:200]
            real_on = bool(s.get("real_enabled"))
            print(f"[PLAN auto] qishu={qishu} 选中 {preds_txt} 连对{sel['lianzhong']} 专家{sel['expert_ids']} mul={multiplier}x 剔冷{removed_cold} 下{len(positions)}号 bet={bet_amount}")
        self.save()
        if self.username and real_on and positions:
            try:
                threading.Thread(
                    target=_do_real_order_for_user,
                    kwargs={
                        "username": self.username,
                        "style": self.STYLE,
                        "expect": qishu,
                        "press_str": _build_press_str(positions, base, multiplier),
                        "source": "plan",
                    }, daemon=True).start()
            except Exception as e:
                print(f"[PLAN real_order] {e}")
        return True, {"qishu": qishu, "preds": preds, "positions": positions}

    def process_result(self, qishu, result_sum):
        """开奖后结算 pending + 累计盈亏 + 止盈检查。"""
        with self.lock:
            s = self.state
            if _qishu_match(qishu, s.get("last_qishu")):
                return
            s["last_qishu"] = str(qishu)
            muls = s.get("multipliers") or [1.0]
            settled = False
            settled_won = False
            for rec in s.get("records", []):
                if rec.get("pending") and str(rec.get("qishu")) == str(qishu):
                    positions = rec.get("positions", []) or []
                    bet = float(rec.get("bet_amount", 0))
                    _, net_pnl, _ = sim_calc_pnl(positions, result_sum, bet, 1.0)
                    won = result_sum in positions
                    rec.update({"result": result_sum, "net_pnl": round(net_pnl),
                                "won": won, "pending": False})
                    s["total_pnl"] += round(net_pnl)
                    settled = True
                    if won:
                        settled_won = True
            if settled:
                # 倍率推进：中了归零；不中→下个倍率位（爆档归零）
                m_idx = int(s.get("mul_idx", 0))
                if settled_won:
                    s["mul_idx"] = 0
                    print(f"[PLAN process] qishu={qishu} 命中 → 倍率归零")
                else:
                    if m_idx < len(muls) - 1:
                        s["mul_idx"] = m_idx + 1
                        print(f"[PLAN process] qishu={qishu} 不中 → 倍率 {m_idx}→{m_idx+1}")
                    else:
                        s["mul_idx"] = 0
                        print(f"[PLAN process] qishu={qishu} 不中且爆档 → 归零")
                sp = int(s.get("stop_profit", 0))
                if sp > 0 and s["total_pnl"] >= sp and s.get("running"):
                    s["running"] = False
                    print(f"[PLAN process] qishu={qishu} 达到止盈 {sp}（当前 {s['total_pnl']}）→ 自动停止")
        self.save()

    def reset(self):
        with self.lock:
            s = self.state
            s["records"] = []
            s["total_pnl"] = 0
            s["cur_pred"] = None
            s["cur_preds"] = []
            s["cur_lianzhong"] = 0
            s["cur_expert_ids"] = []
            s["cur_removed_cold"] = []
            s["mul_idx"] = 0
            s["auto_last_qishu"] = None
            s["last_qishu"] = None
        self.save()
        return True, "已重置"

    def get_status(self):
        with self.lock:
            s = self.state
            muls = s.get("multipliers") or [1.0]
            return {
                "base_amount": s.get("base_amount", 1000),
                "stop_profit": s.get("stop_profit", 0),
                "min_lianzhong": s.get("min_lianzhong", 4),
                "multipliers": muls,
                "muls_text": "-".join(str(x) for x in muls),
                "mul_idx": s.get("mul_idx", 0),
                "running": bool(s.get("running")),
                "real_enabled": bool(s.get("real_enabled")),
                "cur_pred": s.get("cur_pred"),
                "cur_preds": s.get("cur_preds", []),
                "cur_lianzhong": s.get("cur_lianzhong", 0),
                "cur_expert_ids": s.get("cur_expert_ids", []),
                "cur_removed_cold": s.get("cur_removed_cold", []),
                "cur_killed_tails": s.get("cur_killed_tails", []),
                "records": s.get("records", [])[:50],
                "total_pnl": s.get("total_pnl", 0),
                "pnl_date": s.get("pnl_date", now_cn().strftime("%Y-%m-%d")),
            }


_admin_miss = MissEngine()
# 管理端4套独立模拟引擎（模拟下单1）
_admin_sims = [
    SimEngine(save_file=f"{BASE_DIR}/sim_state_admin_{i}.json", engine_name=f"admin1_{i}")
    for i in range(1, 5)
]
# 管理端4套独立模拟引擎（模拟下单2）
_admin_sims2 = [
    SimEngine(save_file=f"{BASE_DIR}/sim_state_admin2_{i}.json", engine_name=f"admin2_{i}")
    for i in range(1, 5)
]

def get_admin_sim(slot, group=1):
    """slot: 1~4, group: 1 or 2"""
    idx = max(0, min(3, int(slot) - 1))
    return _admin_sims[idx] if int(group) == 1 else _admin_sims2[idx]

def _deprecated_inject_noop(style, qishu, positions, base_amount, multiplier):
    """已废弃：遗漏检测与模拟参与现完全独立，不再注入。"""
    pass

# ── 开奖数据源：动态切换（石头岛优先，28vp 兜底）──
# 1) 优先：石头岛 api.shitoudao.com（已实测服务器能访问，与官网完全同步）
#    - GET /game{60|210}/index  → 拿 current 已开奖（Id, SumNum, TheTime）+ future 下期（Id, PreTime）
#    - POST /game{60|210}/getHisList {page,page_size}  → 拉 200 期历史种子
#    - 需要任意一个有效 X-Token（用户登录后即可用）
# 2) 兜底：28vp.com checkData 接口（未登录账号时用）
#    - GET https://28vp.com/data/get/checkData?type=jnd28|btc28
#    - 返回 issue[]: qishu, time, num1/num2/num3, sum, next(下期开奖 Unix 秒)
#    - 期号有差异（jnd28 数字累加；btc28 是 yyyymmdd+序号格式，跟石头岛不同）但合计/时间 OK
# 3) 已废弃：28xiaomi（跟石头岛严重不同步，禁用）
VP28_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "application/json, text/plain, */*",
    "Referer": "https://28vp.com/",
}
# game 标识 → (28vp type 字符串, 周期秒)
XIAOMI_GAME = {
    "jnd28": ("jnd28", 210),   # 欢乐210
    "btc28": ("btc28", 60),    # 比特60
}
# 兼容旧调用点
VP28_URL_60  = "btc28"   # 比特60
VP28_URL_210 = "jnd28"   # 欢乐210

# 石头岛 history 种子缓存：{60: [...], 210: [...]}，避免每次轮询都拉 200 期
_std_seed_done = {60: False, 210: False}
_std_seed_lock = threading.Lock()

# 比特60共享状态
state_60 = {
    "history": [], "last_qishu": None,
}

# 精确倒计时缓存：{ game: {"next_ts":开奖时间戳, "next_qishu":下期期号, "fetch_at":datetime} }
_countdown_cache = {}
_countdown_lock = threading.Lock()

def _bj_str_to_unix(s):
    """把北京时间字符串 'YYYY-MM-DD HH:MM:SS' 转 Unix 秒。
    不依赖服务器系统时区（避免服务器 TZ=UTC 时 datetime.timestamp() 多/少 8 小时）。"""
    from datetime import timezone, timedelta as _td
    try:
        dt = datetime.strptime(str(s)[:19], "%Y-%m-%d %H:%M:%S")
        return dt.replace(tzinfo=timezone(_td(hours=8))).timestamp()
    except Exception:
        return None

def _qishu_match(a, b):
    """期号匹配：兼容 28vp 短期号 vs 石头岛长期号（'05240918' 与 '202605240918' 视为相等）。
    用于 process_result / place_bet 的同期去重，避免双广播导致 mul_idx 跳 2 格的 bug。"""
    if not a or not b: return False
    sa, sb = str(a), str(b)
    if sa == sb: return True
    if len(sa) > len(sb): sa, sb = sb, sa
    # 短的必须 >=3 位才能匹配（避免 '8' endswith 都匹配）
    return len(sa) >= 3 and sb.endswith(sa)

# 兼容保留：旧代码可能引用 _qishu_seen_at（本地推算用，现已不需要但留着防 NameError）
_qishu_seen_at = {}
_qishu_seen_lock = threading.Lock()

def _record_qishu_seen(game, qishu):
    """兼容保留：记录期号首见时间（28xiaomi 有真实时间戳后已不用于倒计时）"""
    key = f"{game}:{qishu}"
    now = now_cn()
    with _qishu_seen_lock:
        if key not in _qishu_seen_at:
            _qishu_seen_at[key] = now
            if len(_qishu_seen_at) > 500:
                for k in sorted(_qishu_seen_at,
                                key=lambda x: _qishu_seen_at[x])[:-200]:
                    _qishu_seen_at.pop(k, None)
        return _qishu_seen_at[key]

def _xiaomi_game_key(game_or_url):
    """把旧的 URL/标识统一成 jnd28 / btc28"""
    g = str(game_or_url)
    if "btc28" in g or "btc" in g:
        return "btc28"
    if "jnd28" in g or "jnd" in g:
        return "jnd28"
    return g if g in XIAOMI_GAME else "jnd28"

def _countdown_from_seen(game, next_qishu, period_sec):
    """精确倒计时：用 28xiaomi 最新开奖时刻 + 周期 推算下期开奖时间，
    再减当前时间。零累积误差。被 fetch_28vp 写入缓存后这里直接读缓存。
    """
    game = _xiaomi_game_key(game)
    with _countdown_lock:
        c = _countdown_cache.get(game)
    if c and c.get("next_ts"):
        remaining = int(c["next_ts"] - time.time())
        # 若已过开奖时刻（接口还没更新到新一期），滚动补周期，避免显示卡 0/负
        guard = 0
        while remaining < 0 and guard < 5:
            remaining += period_sec
            guard += 1
        return max(0, min(remaining, period_sec))
    return 0

# 坏 token 黑名单：石头岛返回 code != 200 的 token 在 60 秒内不再尝试
_bad_token_cache = {}  # {token: expire_ts}
_bad_token_lock = threading.Lock()

def _mark_bad_token(token, ttl=60):
    if not token:
        return
    with _bad_token_lock:
        _bad_token_cache[token] = time.time() + ttl
        # 顺手清掉过期项
        now = time.time()
        for k in list(_bad_token_cache):
            if _bad_token_cache[k] < now:
                _bad_token_cache.pop(k, None)

def _is_bad_token(token):
    if not token:
        return True
    with _bad_token_lock:
        exp = _bad_token_cache.get(token)
        return bool(exp and exp > time.time())

def _find_any_valid_token():
    """遍历所有用户 + 管理员账号，找一个能用的 X-Token。
    跳过短期标记为坏的 token，避免反复用同一个失效 token 撞墙。"""
    try:
        for a in admin_acc_mgr.accounts.values():
            t = a.get("token")
            if t and not _is_bad_token(t):
                return t
    except Exception:
        pass
    try:
        for u in _user_db.list_users():
            uname = u.get("username")
            if not uname:
                continue
            try:
                accs = _user_db.get_std_accounts(uname)
                for a in accs:
                    tok = a.get("token")
                    if tok and not _is_bad_token(tok):
                        return tok
            except Exception:
                continue
    except Exception:
        pass
    return None

# 石头岛 getHisList 缓存：避免轮询线程每秒打爆 api.shitoudao.com（拖慢下单）
# 实测 getHisList 单次响应 ~3s，必须长缓存 + 防并发 race
_SHITOUD_HIS_CACHE = {60: {"ts": 0, "results": [], "next_qishu": None},
                      210: {"ts": 0, "results": [], "next_qishu": None}}
_SHITOUD_HIS_LOCK = threading.Lock()
_SHITOUD_HIS_INFLIGHT = {60: False, 210: False}   # 防止两个线程同时去拉
_SHITOUD_HIS_TTL = 5.0   # 秒；比单次响应还长，确保不会重复请求

def _fetch_shitoud_index(style, token):
    """🔀 拿历史 + 下期期号 + 倒计时。两平台实现不同：
    - 石头岛：POST /game{X}/getHisList 一次性拿历史+下期（带 2.5s 缓存避免打爆接口）
    - 鲸鱼：/pub/game/list 一次性返回历史 + 下期 open_time
    失败返回 ([], None) 让上层 fallback。"""
    game = "jnd28" if int(style) == 210 else "btc28"
    # ⭐ 缓存 + 并发去重：避免多个轮询线程同时打爆 api.shitoudao.com（拖慢下单）
    if not IS_JINGYU:
        with _SHITOUD_HIS_LOCK:
            c = _SHITOUD_HIS_CACHE.get(int(style)) or {}
            cache_age = time.time() - c.get("ts", 0)
            cache_valid = c.get("results") and cache_age < _SHITOUD_HIS_TTL
            inflight = _SHITOUD_HIS_INFLIGHT.get(int(style), False)
        # 缓存还新 → 直接返回
        if cache_valid:
            return c["results"], c.get("next_qishu")
        # 缓存过期但有别的线程在拉 → 等 1 秒后用旧缓存（避免雪崩）
        if inflight and c.get("results"):
            time.sleep(0.3)
            return c["results"], c.get("next_qishu")
        # 占位 inflight 标志，自己去拉
        with _SHITOUD_HIS_LOCK:
            _SHITOUD_HIS_INFLIGHT[int(style)] = True
    period = 210 if int(style) == 210 else 60

    if IS_JINGYU:
        # ── 鲸鱼版：单一 /pub/game/list 接口 ──
        gid = JINGYU_GAME_ID.get(int(style), 2)
        try:
            rh = requests.get(
                f"{STD_API}/pub/game/list",
                headers=std_headers(token),
                params={"game_id": gid},
                timeout=8,
            )
            if rh.status_code != 200:
                _mark_bad_token(token); return [], None
            dh = rh.json()
            code = dh.get("code")
            if code != 200:
                if code == -1 or "登录过期" in (dh.get("msg") or ""):
                    _mark_bad_token(token)
                print(f"[jingyu list] style={style} code={code} msg={dh.get('msg','')}")
                return [], None
            lst = dh.get("list") or []
            if not isinstance(lst, list) or not lst:
                return [], None
            results = []
            for it in lst:
                if it.get("status") != 1: continue
                qid = it.get("game_no"); sn = it.get("num")
                arr = it.get("num_arr") or []
                if qid is None or sn is None: continue
                try: sn_i = int(sn)
                except: continue
                nums = []
                for x in arr:
                    try: nums.append(int(x))
                    except: pass
                results.append({"qishu": str(qid), "sum": sn_i,
                                "nums": nums, "time": ""})
            if not results: return [], None
            # 未开奖找下期
            upcoming = [x for x in lst if x.get("status") in (0, 2)]
            upcoming.sort(key=lambda x: int(x.get("open_time") or 999999))
            next_qishu = None; next_ts = None
            if upcoming:
                nxt = upcoming[0]
                next_qishu = str(nxt.get("game_no"))
                rem = int(nxt.get("open_time") or 0)
                if rem > 0: next_ts = time.time() + rem
            if not next_qishu:
                try:
                    next_qishu = str(int(results[0]["qishu"]) + 1)
                    next_ts = time.time() + period
                except: pass
            if next_ts:
                with _countdown_lock:
                    _countdown_cache[game] = {
                        "next_ts": next_ts, "next_qishu": next_qishu,
                        "fetch_at": now_cn(), "source": "jingyu"}
            if int(style) == 60: state_60["history"] = results[:200]
            else: state["history"] = results[:200]
            with _std_seed_lock: _std_seed_done[int(style)] = True
            return results, next_qishu
        except Exception as e:
            print(f"[jingyu list] style={style} err={e}")
            return [], None

    # ── 石头岛版：POST /game{X}/getHisList 拿历史 + 下期期号 + 下期开奖时间 ──
    # 完全不再用 28vp。期号统一长格式（Id），避免双广播 mul_idx 跳格 bug。
    # page_size=50：石头岛实际只返回 ~45 条，但响应仍 ~3s，必须靠缓存抵消
    try:
        try:
            rh = requests.post(
                f"{STD_API}/game{int(style)}/getHisList",
                headers=std_headers(token),
                json={"page": 1, "page_size": 50},
                timeout=10,
            )
        except Exception as e:
            print(f"[shitoud getHisList] style={style} 网络异常: {e}")
            return [], None
        if rh.status_code != 200:
            _mark_bad_token(token); return [], None
        dh = rh.json()
        code = dh.get("code")
        if code != 200:
            _msg = dh.get("msg") or ""
            # token 失效判定：code=-1 / 含"登录" / code=201 签名不正确（JWT 过期）
            # 签名/JWT 过期是永久失效（token 本身到期），用长 TTL 止血，避免每分钟撞墙刷屏
            if code == 201 or "签名" in _msg:
                _mark_bad_token(token, ttl=86400)
            elif code == -1 or "登录" in _msg:
                _mark_bad_token(token)
            print(f"[shitoud getHisList] style={style} code={code} msg={_msg}")
            return [], None
        lst = dh.get("data") or []
        if not isinstance(lst, list) or not lst:
            return [], None

        # 分离已开奖（SumNum 非空）和未开奖（SumNum=null，待开期）
        results  = []
        upcoming = []
        for it in lst:
            qid = it.get("Id")
            sn  = it.get("SumNum")
            if qid is None: continue
            if sn is None:
                upcoming.append(it)
                continue
            try: sn_i = int(sn)
            except: continue
            nums = []
            for k in ("Num1", "Num2", "Num3"):
                v = it.get(k)
                try: nums.append(int(v))
                except: pass
            results.append({
                "qishu": str(qid),
                "sum": sn_i,
                "nums": nums,
                "time": it.get("TheTime", "") or "",
            })
        if not results:
            return [], None

        # 下一期：取未开奖里 openTime 最小的那条（最早要开奖的）
        next_qishu = None
        next_ts = None
        if upcoming:
            upcoming.sort(key=lambda x: int(x.get("openTime") or 9999999999))
            nxt = upcoming[0]
            next_qishu = str(nxt.get("Id"))
            ot = int(nxt.get("openTime") or 0)
            if ot > 0:
                next_ts = float(ot)
        if not next_qishu:
            try:
                next_qishu = str(int(results[0]["qishu"]) + 1)
                next_ts = time.time() + period
            except Exception:
                pass

        if next_qishu and next_ts:
            with _countdown_lock:
                _countdown_cache[game] = {
                    "next_ts": next_ts,
                    "next_qishu": next_qishu,
                    "fetch_at": now_cn(),
                    "source": "shitoud",
                }
        if int(style) == 60: state_60["history"] = results[:200]
        else: state["history"] = results[:200]
        with _std_seed_lock: _std_seed_done[int(style)] = True
        # ⭐ 写入缓存：下次 _SHITOUD_HIS_TTL 秒内不再打接口
        with _SHITOUD_HIS_LOCK:
            _SHITOUD_HIS_CACHE[int(style)] = {
                "ts": time.time(), "results": results, "next_qishu": next_qishu,
            }
        return results, next_qishu
    except Exception as e:
        print(f"[shitoud getHisList] style={style} err={e}")
        return [], None
    finally:
        # 无论成功失败都清 inflight 标志
        with _SHITOUD_HIS_LOCK:
            _SHITOUD_HIS_INFLIGHT[int(style)] = False

def _fetch_28vp_checkdata(style):
    """⚠️ 已废弃：数据源完全切换到石头岛 /game{X}/getHisList。
    保留空壳避免老调用点 NameError。"""
    return [], None

def _annotate_dx_ds(results):
    """给每条历史记录按 sum 算大小/单双（fetch_28vp 出口统一调用）。
    规则：sum >= 14 大，< 14 小；sum 奇数 单，偶数 双。"""
    for r in results or []:
        try:
            s = int(r.get("sum"))
            r["dx"] = "大" if s >= 14 else "小"
            r["ds"] = "单" if (s % 2) == 1 else "双"
        except Exception:
            r["dx"] = ""
            r["ds"] = ""
    return results

def fetch_28vp(game_or_url, referer=None):
    """开奖数据源统一入口：每次轮询都重新选择源。
    - 有可用 token → 优先石头岛 getHisList；失败标记坏 token + fallback 28vp
    - 无可用 token → 直接 28vp
    btc28 在 28vp 路径里期号会补全成石头岛 12 位格式（避免重复下单），
    所以 fallback 是安全的。
    出口统一按 sum 算 dx/ds。
    """
    game = _xiaomi_game_key(game_or_url)
    style = 210 if game == "jnd28" else 60
    token = _find_any_valid_token()
    if token:
        results, nq = _fetch_shitoud_index(style, token)
        if results:
            return _annotate_dx_ds(results), nq
        # 石头岛失败 → fallback 28vp（坏 token 已被标记，下一轮 _find 跳过）
        print(f"[fetch_28vp] style={style} 石头岛失败，fallback 28vp")
    else:
        # 没有可用 token（未登录 或 全部 token 在坏 token 黑名单）
        pass
    results, nq = _fetch_28vp_checkdata(style)
    return _annotate_dx_ds(results), nq

def central_poll_60():
    """中央比特60轮询线程，广播给所有引擎。
    数据源 fetch_28vp 内部自适应：登录态用石头岛，未登录用 28vp。
    自适应轮询频率：≤3s/0.5s，≤10s/2s，否则 8s。
    """
    last_qishu = None
    last_next_qishu = None
    while True:
        try:
            results, next_qishu = fetch_28vp(VP28_URL_60, "https://28vp.com/btc28.html")
            if results:
                # 更新共享历史（保留 200 期）
                state_60["history"] = results[:200]
                # 最新已开奖的一期
                latest = results[0]
                qishu = latest["qishu"]
                sum_num = latest["sum"]
                if str(qishu) != str(last_qishu):
                    last_qishu = str(qishu)
                    state_60["last_qishu"] = str(qishu)
                    # ⭐ 回填本期所有 real_orders（开奖号 + 中奖金额持久化到 DB）
                    try: _settle_real_orders_for(60, qishu, sum_num)
                    except Exception as _e: print(f"[settle real 60] {_e}")
                    # 广播结算给所有模拟引擎
                    for eng in _admin_sims + _admin_sims2:
                        try: eng.process_result(60, qishu, sum_num)
                        except: pass
                    # 广播给遗漏引擎
                    try: _admin_miss.process_result(60, qishu, sum_num)
                    except: pass
                    for eng in _admin_sims + _admin_sims2:
                        try: eng.settle_miss_bets(60, qishu, sum_num)
                        except: pass
                    # 广播给所有用户引擎
                    try: _user_mgr.broadcast_result(60, qishu, sum_num)
                    except: pass
                    # ⭐ bug 4+6：开奖结果到达后立即触发一次 miss_auto + place_bet，让前面被
                    # "上一期未结算"挡住的下一期单子能下出去（倍率已经在 process_result 推进）
                    if next_qishu:
                        try: _admin_miss.auto_execute(60, fetch_60_history(None, 50), next_qishu, None)
                        except Exception as e: print(f"[MISS auto 60 post-settle] {e}")
                        try: _user_mgr.broadcast_miss_auto(60, fetch_60_history(None, 50), next_qishu)
                        except Exception as e: print(f"[MISS auto user 60 post-settle] {e}")
                        try: _user_mgr.broadcast_dawei_auto(60, fetch_60_history(None, 50), next_qishu)
                        except Exception as e: print(f"[DAWEI auto user 60 post-settle] {e}")
                        # ⭐ 关键：开奖后立即让 SimEngine 下下一期单（赔率已在 process_result 推进）
                        try:
                            for eng in _admin_sims + _admin_sims2:
                                eng.place_bet(60, next_qishu)
                        except Exception as e: print(f"[SIM place_bet 60 post-settle] {e}")
                        try: _user_mgr.broadcast_place_bet(60, next_qishu)
                        except Exception as e: print(f"[SIM broadcast_place_bet 60 post-settle] {e}")
            # 推算比特60剩余倒计时
            try:
                state_60["countdown"] = _countdown_from_seen("btc28", next_qishu, 60)
            except Exception:
                state_60["countdown"] = 0
            if next_qishu and str(next_qishu) != str(last_next_qishu):
                last_next_qishu = str(next_qishu)
                state_60["next_qishu"] = str(next_qishu)
                for eng in _admin_sims + _admin_sims2:
                    try: eng.place_bet(60, next_qishu)
                    except: pass
                try:
                    _admin_miss.auto_execute(60, fetch_60_history(None, 50), next_qishu, None)
                except Exception as e:
                    print(f"[MISS auto 60] {e}")
                try: _user_mgr.broadcast_place_bet(60, next_qishu)
                except: pass
                # ⭐ 普通用户 miss 自动检测
                try: _user_mgr.broadcast_miss_auto(60, fetch_60_history(None, 50), next_qishu)
                except Exception as e: print(f"[MISS auto user 60] {e}")
                try: _user_mgr.broadcast_dawei_auto(60, fetch_60_history(None, 50), next_qishu)
                except Exception as e: print(f"[DAWEI auto user 60] {e}")
        except Exception as e:
            print(f"[central_poll_60] {e}")
        # 比特60 周期短（60秒），缩短轮询间隔保证开奖瞬间能及时拿到新数据：
        # 倒计时 ≤5 或开奖后等期窗口（cd >= 55）→ 1秒；其它 2秒
        cd = state_60.get("countdown", 30)
        if cd <= 5 or cd >= 55:
            time.sleep(1)
        else:
            time.sleep(2)

_client_sims = {}  # {port: SimEngine}

def sim_poll_60(sim_engine, token_getter):
    """兼容旧接口，实际不再使用（由central_poll_60代替）"""
    pass

def fetch_60_history(token_getter=None, limit=50):
    """从28vp共享历史缓存获取比特60历史记录（central_poll_60已维护）"""
    history = state_60.get("history", [])
    if history:
        return [{"sum_num": r["sum"], "qishu": r["qishu"]} for r in history[:limit]]
    # 缓存为空时直接拉一次
    results, _ = fetch_28vp(VP28_URL_60, "https://28vp.com/btc28.html")
    return [{"sum_num": r["sum"], "qishu": r["qishu"]} for r in results[:limit]]





# ══════════════════════════════════════════════════════════════
#  app 共享状态（所有实例共享）
# ══════════════════════════════════════════════════════════════
state = {
    "history": [], "last_qishu": None, "countdown": 0,
    "fetch_time": None, "notifications": [], "fast_mode": False,
}

def _parse_draw_time(t_str):
    """解析28vp返回的时间字段，支持 HH:MM 和完整日期时间格式"""
    if not t_str:
        return None
    t_str = str(t_str).strip()
    try:
        return datetime.strptime(t_str[:19], "%Y-%m-%d %H:%M:%S")
    except:
        pass
    try:
        hm = t_str[:5]
        now = now_cn()
        kt = now.replace(hour=int(hm[:2]), minute=int(hm[3:5]), second=0, microsecond=0)
        if (now - kt).total_seconds() > 1800:
            kt += timedelta(days=1)
        return kt
    except:
        return None


def fetch_data():
    try:
        results, next_qishu_210 = fetch_28vp(VP28_URL_210, "https://28vp.com/btc28.html")
        valid = [
            {"qishu": r["qishu"], "time": r.get("time", ""), "sum": r["sum"],
             "nums": r.get("nums") or [],   # ⭐ bug 2：保留 nums 字段，让欢乐210 lottery-bar 能显示三数相加
             "dx": r.get("dx",""), "ds": r.get("ds","")}
            for r in results
        ]
        state["history"] = valid[:200]
        state["fetch_time"] = now_cn().strftime("%H:%M:%S")
        state["fast_mode"] = True
        # 推算欢乐210剩余倒计时
        try:
            state["countdown"] = _countdown_from_seen("jnd28", next_qishu_210, 210)
        except Exception:
            state["countdown"] = 0
        if valid:
            latest = valid[0]
            if latest["qishu"] != state.get("last_qishu"):
                state["last_qishu"] = latest["qishu"]
                # ⭐ 回填本期所有 real_orders（开奖号 + 中奖金额持久化到 DB）
                try: _settle_real_orders_for(210, latest["qishu"], int(latest["sum"]))
                except Exception as _e: print(f"[settle real 210] {_e}")
                check_and_notify(latest, valid[1] if len(valid) > 1 else None)
                try:
                    for _eng in _admin_sims + _admin_sims2:
                        _eng.process_result(210, latest["qishu"], int(latest["sum"]))
                    _admin_miss.process_result(210, latest["qishu"], int(latest["sum"]))
                    for _eng in _admin_sims + _admin_sims2:
                        _eng.settle_miss_bets(210, latest["qishu"], int(latest["sum"]))
                    try: _user_mgr.broadcast_result(210, latest["qishu"], int(latest["sum"]))
                    except: pass
                except Exception as _se:
                    print(f"[SIM210] {_se}")
                # ⭐ bug 4+6：开奖结算后立即触发 miss_auto + place_bet，让之前被"等上一期"挡住的下单出去
                if next_qishu_210:
                    try:
                        history_210 = [{"sum": h["sum"], "qishu": h.get("qishu")} for h in state.get("history", []) if h.get("sum") is not None]
                        _admin_miss.auto_execute(210, history_210, next_qishu_210, None)
                    except Exception as e: print(f"[MISS auto 210 post-settle] {e}")
                    try: _user_mgr.broadcast_miss_auto(210, history_210, next_qishu_210)
                    except Exception as e: print(f"[MISS auto user 210 post-settle] {e}")
                    try: _user_mgr.broadcast_dawei_auto(210, history_210, next_qishu_210)
                    except Exception as e: print(f"[DAWEI auto user 210 post-settle] {e}")
                    try: _user_mgr.broadcast_plan_auto(next_qishu_210, history_210)
                    except Exception as e: print(f"[PLAN auto user 210 post-settle] {e}")
                    # ⭐ 关键：开奖后立即让 SimEngine 下下一期单（赔率已在 process_result 推进）
                    try:
                        for _eng in _admin_sims + _admin_sims2:
                            _eng.place_bet(210, next_qishu_210)
                    except Exception as e: print(f"[SIM place_bet 210 post-settle] {e}")
                    try: _user_mgr.broadcast_place_bet(210, next_qishu_210)
                    except Exception as e: print(f"[SIM broadcast_place_bet 210 post-settle] {e}")
        if next_qishu_210 and str(next_qishu_210) != str(state.get("next_qishu_210")):
            state["next_qishu_210"] = str(next_qishu_210)
            try:
                for _eng in _admin_sims + _admin_sims2:
                    _eng.place_bet(210, next_qishu_210)
                try: _user_mgr.broadcast_place_bet(210, next_qishu_210)
                except: pass
                history_210 = [{"sum": h["sum"], "qishu": h.get("qishu")} for h in state.get("history", []) if h.get("sum") is not None]
                _admin_miss.auto_execute(210, history_210, next_qishu_210, None)
                # ⭐ 普通用户 miss 自动检测
                try: _user_mgr.broadcast_miss_auto(210, history_210, next_qishu_210)
                except Exception as e: print(f"[MISS auto user 210] {e}")
                try: _user_mgr.broadcast_dawei_auto(210, history_210, next_qishu_210)
                except Exception as e: print(f"[DAWEI auto user 210] {e}")
                try: _user_mgr.broadcast_plan_auto(next_qishu_210, history_210)
                except Exception as e: print(f"[PLAN auto user 210] {e}")
            except Exception as _se:
                print(f"[SIM210 place_bet] {_se}")
        return True
    except Exception as e:
        print(f"[ERROR] fetch_data: {e}")
        return False

def check_and_notify(latest, prev):
    try:
        cur_sum = int(latest["sum"])
        cur_tail = cur_sum % 10
    except:
        return
    reasons = []
    if cur_sum in FIXED_SUMS:
        reasons.append(f"固定提醒 [{cur_sum}]")
    if prev:
        try:
            prev_tail = int(prev["sum"]) % 10
            if (prev_tail, cur_tail) in SHUNZI_PAIRS:
                reasons.append(f"顺子组合 [{prev_tail}→{cur_tail}]")
        except:
            pass
    if not reasons:
        return
    reason_str = " | ".join(reasons)
    prev_sum_str = prev['sum'] if prev else '-'
    prev_line = f"上期 第{prev['qishu']}期  合计: {prev['sum']}\n" if prev else ""
    short_time = latest['time'][5:] if len(latest['time']) > 5 else latest['time']
    msg = (f"🎯 本期（{latest['sum']}）上期（{prev_sum_str}）\n"
           f"本期 第{latest['qishu']}期  合计: {latest['sum']}  {latest['dx']}{latest['ds']}\n"
           f"{prev_line}"
           f"{'─'*16}\n"
           f"触发: {reason_str}\n"
           f"时间: {short_time}")
    state["notifications"].insert(0, {
        "qishu": latest["qishu"], "sum": latest["sum"], "reason": reason_str,
        "time": latest["time"], "ts": now_cn().strftime("%H:%M:%S"),
        "prev_sum": prev["sum"] if prev else "-",
        "prev_qishu": prev["qishu"] if prev else "-",
    })
    state["notifications"] = state["notifications"][:30]
    print(f"[NOTIFY] {reason_str}  期:{latest['qishu']}  合计:{latest['sum']}")

def poll_loop():
    while True:
        fetch_data()
        cd = state.get("countdown", 30)
        # 欢乐210 周期 210 秒，开奖瞬间敏感度优先：
        # 倒计时 ≤5 或开奖后等期窗口（cd >= 200）→ 1秒；中段 ≤30 → 2秒；其它 5秒
        if cd <= 5 or cd >= 200:
            time.sleep(1)
        elif cd <= 30:
            time.sleep(2)
        else:
            time.sleep(5)

# ══════════════════════════════════════════════════════════════
#  石头岛 公共函数
# ══════════════════════════════════════════════════════════════
def std_headers(token=None):
    h = dict(STD_HEADERS_BASE)
    if token:
        if IS_JINGYU:
            h["Authorization"] = token   # 🐋 鲸鱼鉴权
        else:
            h["X-Token"] = token         # 🪨 石头岛鉴权
    return h

def std_get_user_info(token):
    """🔀 拿用户信息。石头岛 /user/getUserInfo  vs  鲸鱼 /pub/user/info。
    返回归一化后的 dict（两套字段名都有，下游怎么读都行）。"""
    try:
        if IS_JINGYU:
            r = requests.get(f"{STD_API}/pub/user/info",
                             headers=std_headers(token), timeout=8)
            d = r.json()
            if d.get("code") == 200:
                data = d.get("data") or {}
                return {
                    "Id": data.get("user_id"),
                    "MyMoney": data.get("balance", 0),
                    "NickName": data.get("nick_name", ""),
                    "silver": data.get("balance", 0),
                    "nickname": data.get("nick_name", ""),
                    "balance": data.get("balance", 0),
                    "nick_name": data.get("nick_name", ""),
                    "user_id": data.get("user_id"),
                }
        else:
            r = requests.get(f"{STD_API}/user/getUserInfo",
                             headers=std_headers(token), timeout=8)
            d = r.json()
            if d.get("code") == 200:
                data = d.get("data") or {}
                out = dict(data)
                out.setdefault("balance", data.get("silver", 0))
                out.setdefault("MyMoney", data.get("silver", 0))
                out.setdefault("nick_name", data.get("nickname", ""))
                out.setdefault("NickName", data.get("nickname", ""))
                out.setdefault("user_id", data.get("Id") or data.get("id"))
                return out
    except Exception as e:
        print(f"[std_get_user_info] {e}")
    return None

def std_get_records(token, limit=50, style=210):
    """🔀 拿账号最近 N 期下单+开奖记录。两边接口差异较大，统一归一化输出。"""
    try:
        if IS_JINGYU:
            gid = JINGYU_GAME_ID.get(int(style), 2)
            r = requests.get(f"{STD_API}/pub/game/list",
                             params={"game_id": gid},
                             headers=std_headers(token), timeout=8)
            d = r.json()
            if d.get("code") == 200:
                lst = d.get("list") or []
                out = []
                for it in lst[:limit]:
                    if it.get("status") == 1 and (it.get("bet") or 0) > 0:
                        out.append({
                            "Periods": it.get("game_no"),
                            "output": it.get("bet", 0),
                            "income": it.get("prize", 0),
                            "Num": it.get("num", 0),
                            "OpenTime": "",
                            "CountBA": it.get("bet", 0),
                            "WinAmount": it.get("prize", 0),
                            "game_no": it.get("game_no"),
                            "bet": it.get("bet", 0),
                            "prize": it.get("prize", 0),
                        })
                return out
            if d.get("code") == -1 or "登录" in (d.get("msg") or ""):
                _mark_bad_token(token)
        else:
            r = requests.post(f"{STD_API}/game/getJoinRecordListNew",
                              headers=std_headers(token),
                              json={"page": 1, "limit": limit, "style": int(style)}, timeout=8)
            d = r.json()
            if d.get("code") == 200:
                lst = (d.get("data") or {}).get("list", []) or []
                for it in lst:
                    it.setdefault("output", it.get("CountBA", 0))
                    it.setdefault("income", it.get("WinAmount", 0))
                    it.setdefault("game_no", it.get("Periods"))
                    it.setdefault("bet", it.get("CountBA", 0))
                    it.setdefault("prize", it.get("WinAmount", 0))
                return lst
            if d.get("code") == -1 or "登录" in (d.get("msg") or ""):
                _mark_bad_token(token)
    except Exception as e:
        print(f"[std_get_records] {e}")
    return []

def std_get_expect(token=None, style=210):
    # ① 优先从倒计时缓存读期号
    game = "jnd28" if int(style) == 210 else "btc28"
    with _countdown_lock:
        c = _countdown_cache.get(game)
    if c and c.get("next_qishu"):
        return str(c["next_qishu"])
    tk = token or _find_any_valid_token()
    # ② 拉一次官方接口（鲸鱼用 /pub/game/list，石头岛用 /game{X}/index）
    if tk:
        try:
            results, nq = _fetch_shitoud_index(int(style), tk)
            if nq:
                return str(nq)
        except Exception as e:
            print(f"[std_get_expect] fetch_index err={e}")
    # ③ 最后回退：28vp
    try:
        results, nq = _fetch_28vp_checkdata(style)
        if nq:
            return str(nq)
    except Exception as e:
        print(f"[std_get_expect] 28vp fallback err={e}")
    return None

def std_get_stats(token, style):
    """🔀 今日盈亏 + 胜率。石头岛走 /game/stats；鲸鱼用 records 自算。"""
    try:
        if IS_JINGYU:
            recs = std_get_records(token, limit=50, style=style)
            if not recs:
                return {"today": 0, "win_rate": 0}
            total_bet = sum((r.get("output") or 0) for r in recs)
            total_win = sum((r.get("income") or 0) for r in recs)
            n = len(recs); won = sum(1 for r in recs if (r.get("income") or 0) > 0)
            return {
                "today": (total_win - total_bet),
                "win_rate": (round(won * 100.0 / n, 1) if n else 0),
            }
        else:
            r = requests.post(f"{STD_API}/game/stats",
                              headers=std_headers(token),
                              json={"style": str(style)}, timeout=8)
            d = r.json()
            if d.get("code") == 200:
                def parse_num(s):
                    try: return int(str(s).replace(",","").replace(" ",""))
                    except: return 0
                data = d.get("data") or {}
                return {
                    "today": parse_num(data.get("myScore", 0)),
                    "win_rate": float(str(data.get("myScoreS","0")).replace(",","")),
                }
            if d.get("code") == -1 or "登录" in (d.get("msg") or ""):
                _mark_bad_token(token)
    except Exception as e:
        print(f"[std_get_stats] {e}")
    return {"today": 0, "win_rate": 0}

def calc_press(tails_str, total_amount):
    tail_digits = list(set(int(ch) for ch in tails_str if ch.isdigit()))
    if not tail_digits:
        return None, "尾数无效"
    positions = [p for p in range(28) if p % 10 in tail_digits]
    inv = {p: 1.0 / ODDS_TABLE[p] for p in positions}
    total_inv = sum(inv.values())
    alloc = {p: round(total_amount * inv[p] / total_inv) for p in positions}
    if min(alloc.values()) < 1:
        return None, "总金额不足，请加大金额"
    press_arr = [0] * 28
    for p, v in alloc.items():
        press_arr[p] = v
    return ",".join(str(v) for v in press_arr), None

def calc_stats(records):
    today = date.today().strftime("%Y-%m-%d")
    today_recs = [r for r in records if r.get("OpenTime", "").startswith(today)]
    total_in  = sum(r.get("CountBA", 0) for r in today_recs)
    total_win = sum(r.get("WinAmount", 0) for r in today_recs)
    pnl = total_win - total_in
    win_count = sum(1 for r in today_recs if r.get("WinAmount", 0) > 0)
    total_count = len(today_recs)
    win_rate = round(win_count / total_count * 100, 2) if total_count else 0
    return {"pnl": pnl, "win_rate": win_rate, "today_count": total_count,
            "total_in": total_in, "total_win": total_win}

# ══════════════════════════════════════════════════════════════
#  账号管理器（每个实例独立）
# ══════════════════════════════════════════════════════════════
class AccountManager:
    def __init__(self, accounts_file):
        self.accounts_file = accounts_file
        self.accounts = {}
        self.lock = threading.Lock()
        self.load()

    def save(self):
        try:
            data = {}
            with self.lock:
                for uid, acc in self.accounts.items():
                    data[uid] = {"uid": uid, "tel": acc["tel"], "token": acc["token"], "remark": acc.get("remark","")}
            os.makedirs(os.path.dirname(self.accounts_file), exist_ok=True)
            with open(self.accounts_file, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False)
        except Exception as e:
            print(f"[SAVE] {self.accounts_file}: {e}")

    def load(self):
        try:
            with open(self.accounts_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            for uid, acc in data.items():
                self.accounts[uid] = {
                    "uid": uid, "tel": acc["tel"], "token": acc["token"],
                    "info": None, "records": [], "records60": [], 
                    "stats": {}, "stats60": {}, "total_today": 0,
                    "online": False, "remark": acc.get("remark",""),
                    "last_check": "--",
                }
            print(f"[LOAD] {self.accounts_file} 恢复 {len(self.accounts)} 个账号")
            for uid in list(self.accounts.keys()):
                threading.Thread(target=self.refresh, args=(uid,), daemon=True).start()
        except FileNotFoundError:
            pass
        except Exception as e:
            print(f"[LOAD] {self.accounts_file}: {e}")

    def refresh(self, uid):
        with self.lock:
            acc = self.accounts.get(uid)
        if not acc or not acc.get("token"):
            return
        info = std_get_user_info(acc["token"])
        records210 = std_get_records(acc["token"], 50, 210)
        records60  = std_get_records(acc["token"], 50, 60)
        stats210 = std_get_stats(acc["token"], 210)
        stats60  = std_get_stats(acc["token"], 60)
        total_today = stats210.get("today", 0) + stats60.get("today", 0)
        with self.lock:
            if uid in self.accounts:
                self.accounts[uid]["info"] = info
                self.accounts[uid]["records"] = records210[:20]
                self.accounts[uid]["records60"] = records60[:20]
                self.accounts[uid]["stats"] = stats210
                self.accounts[uid]["stats60"] = stats60
                self.accounts[uid]["total_today"] = total_today
                self.accounts[uid]["online"] = info is not None
                self.accounts[uid]["last_check"] = now_cn().strftime("%H:%M:%S")

    def poll_loop(self):
        while True:
            with self.lock:
                uids = list(self.accounts.keys())
            for uid in uids:
                try:
                    self.refresh(uid)
                except Exception as e:
                    print(f"[ACC] {uid}: {e}")
            time.sleep(30)

    def add(self, uid, tel, token, info):
        with self.lock:
            existing = self.accounts.get(uid, {})
            self.accounts[uid] = {
                "uid": uid, "tel": tel, "token": token, "info": info,
                "records": [], "records60": [], "stats": {}, "stats60": {},
                "total_today": 0, "online": True,
                "remark": existing.get("remark", ""),
                "last_check": now_cn().strftime("%H:%M:%S"),
            }
        threading.Thread(target=self.refresh, args=(uid,), daemon=True).start()
        self.save()

    def remove(self, uid):
        found = False
        with self.lock:
            if uid in self.accounts:
                del self.accounts[uid]
                found = True
        if found:
            self.save()
        return found

    def get_list(self):
        with self.lock:
            result = []
            for uid, acc in self.accounts.items():
                info = acc.get("info") or {}
                result.append({
                    "uid": uid, "tel": acc["tel"],
                    "online": acc.get("online", False),
                    "last_check": acc.get("last_check", "--"),
                    "silver": info.get("silver", 0),
                    "nickname": info.get("nickname", acc["tel"]),
                    "remark": acc.get("remark", ""),
                    "stats": acc.get("stats", {}),
                    "records": acc.get("records", []),
                    "stats60": acc.get("stats60", {}),
                    "records60": acc.get("records60", []),
                    "total_today": acc.get("total_today", 0),
                })
        return result

    def get_token(self, uid=None):
        with self.lock:
            if uid:
                acc = self.accounts.get(uid)
                return acc["token"] if acc else None
            tokens = [a["token"] for a in self.accounts.values() if a.get("token")]
            return tokens[0] if tokens else None

# ══════════════════════════════════════════════════════════════
#  客户端管理（管理员专用）
# ══════════════════════════════════════════════════════════════
clients_lock = threading.Lock()
running_clients = {}  # port -> {"name": ..., "server": ..., "thread": ...}

def load_clients_config():
    try:
        with open(CLIENTS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except:
        return []

def save_clients_config(clients):
    os.makedirs(BASE_DIR, exist_ok=True)
    with open(CLIENTS_FILE, "w", encoding="utf-8") as f:
        json.dump(clients, f, ensure_ascii=False, indent=2)

# ══════════════════════════════════════════════════════════════
#  用户数据库（账号管理）
# ══════════════════════════════════════════════════════════════
import hashlib
import secrets

ADMIN_PATH   = "/Admin123456"
ADMIN_USER   = "admin"
ADMIN_PASS   = "Bbin123456@"
USER_DB_PATH = f"{BASE_DIR}/users.db"

class UserDB:
    def __init__(self):
        self.lock = threading.Lock()
        self._init_db()
        threading.Thread(target=self._cleanup_loop, daemon=True).start()

    def _conn(self):
        c = sqlite3.connect(USER_DB_PATH, timeout=10)
        c.row_factory = sqlite3.Row
        return c

    def _init_db(self):
        with self._conn() as c:
            c.execute("""CREATE TABLE IF NOT EXISTS users (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                username    TEXT NOT NULL UNIQUE,
                password_hash TEXT NOT NULL,
                expires_at  TEXT,
                created_at  TEXT NOT NULL,
                remark      TEXT DEFAULT '',
                max_accounts INTEGER NOT NULL DEFAULT 5
            )""")
            # 兼容老表：自动加 max_accounts 列
            try:
                c.execute("ALTER TABLE users ADD COLUMN max_accounts INTEGER NOT NULL DEFAULT 5")
                print("[UserDB] users 表新增 max_accounts 列")
            except sqlite3.OperationalError:
                pass
            # 兼容老表：自动加 password_plain 列（管理端查询用，老用户为空待重置后填充）
            try:
                c.execute("ALTER TABLE users ADD COLUMN password_plain TEXT DEFAULT ''")
                print("[UserDB] users 表新增 password_plain 列")
            except sqlite3.OperationalError:
                pass
            c.execute("""CREATE TABLE IF NOT EXISTS user_sessions (
                token       TEXT PRIMARY KEY,
                username    TEXT NOT NULL,
                created_at  TEXT NOT NULL,
                expires_at  TEXT NOT NULL
            )""")
            c.execute("""CREATE TABLE IF NOT EXISTS user_sim_state (
                username    TEXT NOT NULL,
                key         TEXT NOT NULL,
                value       TEXT NOT NULL,
                updated_at  TEXT NOT NULL,
                PRIMARY KEY (username, key)
            )""")
            c.execute("""CREATE TABLE IF NOT EXISTS user_miss_state (
                username    TEXT NOT NULL,
                value       TEXT NOT NULL,
                updated_at  TEXT NOT NULL,
                PRIMARY KEY (username)
            )""")
            c.execute("""CREATE TABLE IF NOT EXISTS user_std_accounts (
                username    TEXT NOT NULL,
                uid         TEXT NOT NULL,
                tel         TEXT,
                token       TEXT,
                password    TEXT DEFAULT '',
                remark      TEXT DEFAULT '',
                updated_at  TEXT NOT NULL,
                PRIMARY KEY (username, uid)
            )""")
            # 兼容老表：自动加 password 列（石头岛版需要 password 存盘以便 token 失效自动续登）
            try:
                c.execute("ALTER TABLE user_std_accounts ADD COLUMN password TEXT DEFAULT ''")
                print("[UserDB] user_std_accounts 表新增 password 列")
            except sqlite3.OperationalError:
                pass
            # ═══ 支付系统 ═══
            # 支付配置：key-value 单行表（id=1 是单例）
            c.execute("""CREATE TABLE IF NOT EXISTS payment_config (
                id          INTEGER PRIMARY KEY,
                api_url     TEXT NOT NULL DEFAULT '',
                merchant_id TEXT NOT NULL DEFAULT '',
                merchant_key TEXT NOT NULL DEFAULT '',
                free_register_enabled INTEGER NOT NULL DEFAULT 1,
                free_register_days INTEGER NOT NULL DEFAULT 3,
                free_register_max_accounts INTEGER NOT NULL DEFAULT 2,
                plans       TEXT NOT NULL DEFAULT '',
                updated_at  TEXT NOT NULL DEFAULT ''
            )""")
            # 支付订单（含续费 / 加账号 / 注册 三种用途）
            c.execute("""CREATE TABLE IF NOT EXISTS payment_orders (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                out_trade_no TEXT NOT NULL UNIQUE,
                trade_no     TEXT DEFAULT '',
                username     TEXT NOT NULL,
                plan_type    TEXT NOT NULL,
                plan_key     TEXT NOT NULL,
                amount       TEXT NOT NULL,
                days         INTEGER NOT NULL DEFAULT 0,
                accounts     INTEGER NOT NULL DEFAULT 0,
                status       TEXT NOT NULL DEFAULT 'pending',
                pay_type     TEXT DEFAULT '',
                pay_url      TEXT DEFAULT '',
                register_password TEXT DEFAULT '',
                notify_payload TEXT DEFAULT '',
                created_at   TEXT NOT NULL,
                paid_at      TEXT DEFAULT '',
                refunded_at  TEXT DEFAULT ''
            )""")
            c.execute("CREATE INDEX IF NOT EXISTS idx_porders_user ON payment_orders(username, created_at DESC)")
            c.execute("CREATE INDEX IF NOT EXISTS idx_porders_status ON payment_orders(status, created_at DESC)")
            # 首次启动塞入默认配置（如果还没记录）
            row = c.execute("SELECT id FROM payment_config WHERE id=1").fetchone()
            if not row:
                default_plans = json.dumps({
                    "day":   {"label": "天卡",  "price": "5.00",   "days": 1,   "max_accounts": 2,  "enabled": True},
                    "week":  {"label": "周卡",  "price": "20.00",  "days": 7,   "max_accounts": 3,  "enabled": True},
                    "month": {"label": "月卡",  "price": "60.00",  "days": 30,  "max_accounts": 5,  "enabled": True},
                    "year":  {"label": "年卡",  "price": "500.00", "days": 365, "max_accounts": 10, "enabled": True},
                    "extra_account": {"label": "加 1 个平台账号", "price": "10.00", "accounts": 1, "enabled": True}
                }, ensure_ascii=False)
                c.execute("""INSERT INTO payment_config
                    (id, api_url, merchant_id, merchant_key, free_register_enabled,
                     free_register_days, free_register_max_accounts, plans, updated_at)
                    VALUES (1, 'https://eb9a928f.aodww.cn', '1168',
                            've3G3AfxJgmAIoyJRYEloyMgefZErVVG', 1, 3, 2, ?, ?)""",
                    (default_plans, now_cn().strftime("%Y-%m-%d %H:%M:%S")))
                print("[UserDB] payment_config 表初始化默认值")
            c.commit()

    @staticmethod
    def _hash(password):
        return hashlib.sha256(password.encode()).hexdigest()

    def create_user(self, username, password, expires_at=None, remark=''):
        try:
            with self.lock:
                with self._conn() as c:
                    c.execute("INSERT INTO users (username,password_hash,password_plain,expires_at,created_at,remark) VALUES (?,?,?,?,?,?)",
                        (username, self._hash(password), password, expires_at, now_cn().strftime("%Y-%m-%d %H:%M:%S"), remark))
                    c.commit()
            return True, "创建成功"
        except sqlite3.IntegrityError:
            return False, "用户名已存在"
        except Exception as e:
            return False, str(e)

    def delete_user(self, username):
        try:
            with self.lock:
                with self._conn() as c:
                    c.execute("DELETE FROM users WHERE username=?", (username,))
                    c.execute("DELETE FROM user_sessions WHERE username=?", (username,))
                    # 标记删除时间，7天后清理数据
                    c.execute("UPDATE users SET expires_at=? WHERE username=? OR 1=0",
                        ((now_cn() + timedelta(days=7)).strftime("%Y-%m-%d %H:%M:%S"), username))
                    # 直接删除用户数据（7天内保留sim/miss状态）
                    c.execute("DELETE FROM user_std_accounts WHERE username=?", (username,))
                    c.commit()
            return True, "删除成功"
        except Exception as e:
            return False, str(e)

    def update_user(self, username, password=None, expires_at=None, remark=None):
        try:
            with self.lock:
                with self._conn() as c:
                    if password:
                        c.execute("UPDATE users SET password_hash=?, password_plain=? WHERE username=?",
                                  (self._hash(password), password, username))
                    if expires_at is not None:
                        c.execute("UPDATE users SET expires_at=? WHERE username=?", (expires_at, username))
                    if remark is not None:
                        c.execute("UPDATE users SET remark=? WHERE username=?", (remark, username))
                    c.commit()
            return True, "更新成功"
        except Exception as e:
            return False, str(e)

    def get_user(self, username):
        with self._conn() as c:
            row = c.execute("SELECT * FROM users WHERE username=?", (username,)).fetchone()
        return dict(row) if row else None

    def list_users(self):
        with self._conn() as c:
            rows = c.execute("SELECT * FROM users ORDER BY created_at DESC").fetchall()
        return [dict(r) for r in rows]

    def verify_password(self, username, password):
        u = self.get_user(username)
        if not u:
            return False, "用户不存在"
        if u["password_hash"] != self._hash(password):
            return False, "密码错误"
        if u.get("expires_at"):
            try:
                exp = datetime.strptime(u["expires_at"], "%Y-%m-%d %H:%M:%S")
                if now_cn() > exp:
                    return False, "账号已到期"
            except:
                pass
        return True, "ok"

    def create_session(self, username):
        token = secrets.token_hex(32)
        expires = (now_cn() + timedelta(hours=24)).strftime("%Y-%m-%d %H:%M:%S")
        with self.lock:
            with self._conn() as c:
                c.execute("INSERT OR REPLACE INTO user_sessions (token,username,created_at,expires_at) VALUES (?,?,?,?)",
                    (token, username, now_cn().strftime("%Y-%m-%d %H:%M:%S"), expires))
                c.commit()
        return token

    def verify_session(self, token):
        if not token:
            return None
        with self._conn() as c:
            row = c.execute("SELECT * FROM user_sessions WHERE token=?", (token,)).fetchone()
        if not row:
            return None
        try:
            if now_cn() > datetime.strptime(row["expires_at"], "%Y-%m-%d %H:%M:%S"):
                return None
        except:
            return None
        u = self.get_user(row["username"])
        if not u:
            return None
        # 检查是否到期
        if u.get("expires_at"):
            try:
                if now_cn() > datetime.strptime(u["expires_at"], "%Y-%m-%d %H:%M:%S"):
                    return None
            except:
                pass
        return row["username"]

    def delete_session(self, token):
        with self.lock:
            with self._conn() as c:
                c.execute("DELETE FROM user_sessions WHERE token=?", (token,))
                c.commit()

    # ── sim/miss 状态存取 ──
    def save_sim_state(self, username, key, value_dict):
        try:
            with self.lock:
                with self._conn() as c:
                    c.execute("INSERT OR REPLACE INTO user_sim_state (username,key,value,updated_at) VALUES (?,?,?,?)",
                        (username, key, json.dumps(value_dict, ensure_ascii=False), now_cn().strftime("%Y-%m-%d %H:%M:%S")))
                    c.commit()
        except Exception as e:
            print(f"[UserDB.save_sim_state] {e}")

    def load_sim_state(self, username, key):
        try:
            with self._conn() as c:
                row = c.execute("SELECT value FROM user_sim_state WHERE username=? AND key=?", (username, key)).fetchone()
            return json.loads(row["value"]) if row else None
        except:
            return None

    def save_miss_state(self, username, value_dict):
        try:
            with self.lock:
                with self._conn() as c:
                    c.execute("INSERT OR REPLACE INTO user_miss_state (username,value,updated_at) VALUES (?,?,?)",
                        (username, json.dumps(value_dict, ensure_ascii=False), now_cn().strftime("%Y-%m-%d %H:%M:%S")))
                    c.commit()
        except Exception as e:
            print(f"[UserDB.save_miss_state] {e}")

    def load_miss_state(self, username):
        try:
            with self._conn() as c:
                row = c.execute("SELECT value FROM user_miss_state WHERE username=?", (username,)).fetchone()
            return json.loads(row["value"]) if row else None
        except:
            return None

    # ── 🪨 石头岛账号存取 ──
    def save_std_account(self, username, uid, tel, token, remark='', password=''):
        try:
            with self.lock:
                with self._conn() as c:
                    c.execute("INSERT OR REPLACE INTO user_std_accounts (username,uid,tel,token,password,remark,updated_at) VALUES (?,?,?,?,?,?,?)",
                        (username, uid, tel, token, password, remark, now_cn().strftime("%Y-%m-%d %H:%M:%S")))
                    c.commit()
        except Exception as e:
            print(f"[UserDB.save_std_account] {e}")

    def get_std_accounts(self, username):
        try:
            with self._conn() as c:
                rows = c.execute("SELECT * FROM user_std_accounts WHERE username=?", (username,)).fetchall()
            return [dict(r) for r in rows]
        except:
            return []

    def get_user_max_accounts(self, username):
        """🪨 拿该用户的账号上限。0 表示不限制。"""
        try:
            with self._conn() as c:
                row = c.execute("SELECT max_accounts FROM users WHERE username=?", (username,)).fetchone()
            return int(row["max_accounts"]) if row and row["max_accounts"] is not None else 5
        except Exception:
            return 5

    def set_user_max_accounts(self, username, max_accounts):
        try:
            with self.lock:
                with self._conn() as c:
                    c.execute("UPDATE users SET max_accounts=? WHERE username=?", (int(max_accounts), username))
                    c.commit()
            return True
        except Exception as e:
            print(f"[UserDB.set_max_accounts] {e}")
            return False

    def delete_std_account(self, username, uid):
        try:
            with self.lock:
                with self._conn() as c:
                    c.execute("DELETE FROM user_std_accounts WHERE username=? AND uid=?", (username, uid))
                    c.commit()
        except Exception as e:
            print(f"[UserDB.delete_std_account] {e}")

    def _cleanup_loop(self):
        while True:
            try:
                # 清理过期session
                with self.lock:
                    with self._conn() as c:
                        c.execute("DELETE FROM user_sessions WHERE expires_at < ?",
                            (now_cn().strftime("%Y-%m-%d %H:%M:%S"),))
                        c.commit()
            except:
                pass
            time.sleep(3600)

_user_db = UserDB()
admin_acc_mgr = AccountManager(ADMIN_ACCOUNTS_FILE)


# ══════════════════════════════════════════════════════════════
#  用户引擎管理（每个用户独立的SimEngine + MissEngine）
# ══════════════════════════════════════════════════════════════
class UserManager:
    def __init__(self):
        self._sims   = {}   # {username: SimEngine}
        self._miss   = {}   # {username: MissEngine}
        self._daweis = {}   # {username__dws{1-4}: DaweiEngine}
        self._plans  = {}   # {username: PlanEngine}
        self._accmgr = {}   # {username: AccountManager}
        self._lock   = threading.Lock()

    def _sim_save_file(self, username, slot=1):
        return f"{BASE_DIR}/user_sim_{username}_s{slot}.json"

    def _miss_save_file(self, username):
        return f"{BASE_DIR}/user_miss_{username}.json"

    def _dawei_save_file(self, username, slot=1):
        return f"{BASE_DIR}/user_dawei_{username}_s{slot}.json"

    def _plan_save_file(self, username):
        return f"{BASE_DIR}/user_plan_{username}.json"

    def _acc_save_file(self, username):
        return f"{BASE_DIR}/user_acc_{username}.json"

    def _make_sim_engine(self, username, slot):
        eng = SimEngine(
            save_file=self._sim_save_file(username, slot),
            engine_name=f"user_{username}_s{slot}",
            username=username,
        )
        saved = _user_db.load_sim_state(username, f"sim_s{slot}")
        if saved:
            try:
                eng.state_210 = saved.get("state_210", eng.state_210)
                eng.state_60  = saved.get("state_60",  eng.state_60)
            except:
                pass
        def make_db_saver(uname, slotnum, engine):
            orig_save = engine.save
            def new_save():
                orig_save()
                try:
                    _user_db.save_sim_state(uname, f"sim_s{slotnum}", {
                        "state_210": engine.state_210,
                        "state_60":  engine.state_60,
                    })
                except:
                    pass
            return new_save
        eng.save = make_db_saver(username, slot, eng)
        return eng

    def get_sim(self, username, slot=1) -> SimEngine:
        """slot 1~4 各自独立的 SimEngine，互不干扰"""
        slot = max(1, min(4, int(slot)))
        key = f"{username}__s{slot}"
        with self._lock:
            if key not in self._sims:
                self._sims[key] = self._make_sim_engine(username, slot)
            return self._sims[key]

    def get_miss(self, username) -> MissEngine:
        with self._lock:
            if username not in self._miss:
                eng = MissEngine(save_file=self._miss_save_file(username), username=username)
                saved = _user_db.load_miss_state(username)
                if saved:
                    try:
                        eng.state = saved
                    except:
                        pass
                def make_miss_saver(uname, engine):
                    orig_save = engine.save
                    def new_save():
                        orig_save()
                        try:
                            _user_db.save_miss_state(uname, engine.state)
                        except:
                            pass
                    return new_save
                eng.save = make_miss_saver(username, eng)
                self._miss[username] = eng
            return self._miss[username]

    def get_dawei(self, username, slot=1) -> "DaweiEngine":
        """slot 1~4 各自独立的 DaweiEngine"""
        slot = max(1, min(4, int(slot)))
        key = f"{username}__dws{slot}"
        with self._lock:
            if key not in self._daweis:
                self._daweis[key] = DaweiEngine(
                    save_file=self._dawei_save_file(username, slot),
                    engine_name=f"user_{username}_dw_s{slot}",
                    username=username,
                )
            return self._daweis[key]

    def get_plan(self, username) -> "PlanEngine":
        with self._lock:
            if username not in self._plans:
                self._plans[username] = PlanEngine(
                    save_file=self._plan_save_file(username),
                    username=username,
                )
            return self._plans[username]

    def get_acc(self, username) -> AccountManager:
        with self._lock:
            if username not in self._accmgr:
                acc = AccountManager(self._acc_save_file(username))
                # 从DB同步账号
                db_accs = _user_db.get_std_accounts(username)
                for a in db_accs:
                    if a.get("token"):
                        acc.accounts[a["uid"]] = {
                            "uid": a["uid"], "tel": a.get("tel",""),
                            "token": a["token"], "remark": a.get("remark","")
                        }
                self._accmgr[username] = acc
            return self._accmgr[username]

    def ensure_all_loaded(self):
        """遍历 DB 里所有用户，确保每个用户的 4 个 slot SimEngine 和 MissEngine 已加载到内存。
        ⭐ 防御性：避免"服务重启 / 用户未访问页面 → 引擎实例未懒加载 → broadcast_result 跳过 →
        停止前下的 pending 永远不结算"这个老 bug。
        get_sim/get_miss 对已加载的实例零成本（直接 dict 命中返回），新加载的会触发 load() 把磁盘 state 读进来。
        用户与用户之间严格隔离：每人独立 SimEngine 实例 + 独立 save_file，互不污染。"""
        try:
            all_users = _user_db.list_users() or []
        except Exception as e:
            print(f"[ensure_all_loaded] list_users err: {e}")
            return
        loaded = 0
        for u in all_users:
            uname = u.get("username") if isinstance(u, dict) else None
            if not uname:
                continue
            try:
                for slot in (1, 2, 3, 4):
                    self.get_sim(uname, slot)
                    self.get_dawei(uname, slot)
                self.get_miss(uname)
                self.get_plan(uname)
                loaded += 1
            except Exception as e:
                # 该用户加载失败（可能 state 文件损坏/账号都删了）→ 跳过不影响其他用户
                print(f"[ensure_all_loaded {uname}] {e}")
        print(f"[ensure_all_loaded] 已确保 {loaded} 个用户的引擎实例已加载")

    def disable_all_real_for_user(self, username, reason="账号已到期"):
        """静默关闭该用户所有真实参与开关（sim 4mode × 2style + miss 2style），防止账号过期还在烧钱下单。
        关闭时仅写日志，不通知用户。"""
        changed = []
        # SimEngine 4 slot × 4 mode × 2 style
        for slot in (1, 2, 3, 4):
            try:
                eng = self.get_sim(username, slot)
                with eng.lock:
                    for s in (eng.state_210, eng.state_60):
                        for mode in ("random", "map", "fix", "jump"):
                            key = f"real_enabled_{mode}"
                            if s.get(key):
                                s[key] = False
                                changed.append(f"slot{slot}/sim/{mode}")
                eng.save()
            except Exception as e:
                print(f"[disable_all_real {username} sim slot={slot}] {e}")
        # MissEngine
        try:
            meng = self.get_miss(username)
            with meng.lock:
                for key in ("real_enabled_210", "real_enabled_60"):
                    if meng.state.get(key):
                        meng.state[key] = False
                        changed.append(f"miss/{key}")
            meng.save()
        except Exception as e:
            print(f"[disable_all_real {username} miss] {e}")
        # DaweiEngine 4 slot × 2 style
        for slot in (1, 2, 3, 4):
            try:
                deng = self.get_dawei(username, slot)
                with deng.lock:
                    for s in (deng.state_210, deng.state_60):
                        if s.get("real_enabled"):
                            s["real_enabled"] = False
                            changed.append(f"slot{slot}/dawei")
                deng.save()
            except Exception as e:
                print(f"[disable_all_real {username} dawei slot={slot}] {e}")
        # PlanEngine
        try:
            peng = self.get_plan(username)
            with peng.lock:
                if peng.state.get("real_enabled"):
                    peng.state["real_enabled"] = False
                    changed.append("plan")
            peng.save()
        except Exception as e:
            print(f"[disable_all_real {username} plan] {e}")
        if changed:
            print(f"[auto-disable real] user={username} reason={reason} closed={changed}")
        return changed

    def broadcast_result(self, style, qishu, result_sum):
        """开奖结果广播给所有在线用户的引擎"""
        with self._lock:
            sims  = list(self._sims.items())
            misses = list(self._miss.items())
            daweis = list(self._daweis.items())
            plans  = list(self._plans.items())
        for uname, eng in sims:
            try:
                eng.process_result(style, qishu, result_sum)
                eng.settle_miss_bets(style, qishu, result_sum)
            except Exception as e:
                print(f"[UserMgr.broadcast] sim {uname}: {e}")
        for uname, eng in misses:
            try:
                eng.process_result(style, qishu, result_sum)
            except Exception as e:
                print(f"[UserMgr.broadcast] miss {uname}: {e}")
        for key, eng in daweis:
            try:
                eng.process_result(style, qishu, result_sum)
            except Exception as e:
                print(f"[UserMgr.broadcast] dawei {key}: {e}")
        # 计划跟投仅 210
        if int(style) == 210:
            for uname, eng in plans:
                try:
                    eng.process_result(qishu, result_sum)
                except Exception as e:
                    print(f"[UserMgr.broadcast] plan {uname}: {e}")

    def broadcast_place_bet(self, style, next_qishu):
        """新期号广播给所有在线用户的所有套引擎"""
        with self._lock:
            sims = list(self._sims.items())
        for key, eng in sims:
            try:
                eng.place_bet(style, next_qishu)
            except Exception as e:
                print(f"[UserMgr.broadcast_place_bet] {key}: {e}")

    def broadcast_miss_auto(self, style, history, next_qishu):
        """新期号广播：遍历所有用户的 miss 引擎，触发 auto_execute。
        ⭐ 完全独立：遗漏引擎自己下自己的单和走真单，不再注入到 sim 引擎。"""
        with self._lock:
            misses = list(self._miss.items())
        for uname, eng in misses:
            try:
                ok, results = eng.auto_execute(style, history, next_qishu, None)
                if results:
                    print(f"[broadcast_miss_auto] user={uname} style={style} qishu={next_qishu} 植入 {len(results)} 组")
            except Exception as e:
                print(f"[broadcast_miss_auto] user={uname}: {e}")

    def broadcast_dawei_auto(self, style, history, next_qishu):
        """新期号广播：遍历所有用户每个 slot 的 DaweiEngine 触发 auto_execute"""
        with self._lock:
            daweis = list(self._daweis.items())
        for key, eng in daweis:
            try:
                ok, results = eng.auto_execute(style, history, next_qishu)
                if results:
                    print(f"[broadcast_dawei_auto] {key} style={style} qishu={next_qishu}")
            except Exception as e:
                print(f"[broadcast_dawei_auto] {key}: {e}")

    def broadcast_plan_auto(self, next_qishu, history=None):
        """新期号广播（仅 210）：遍历所有用户的 PlanEngine 触发 auto_execute。
        history: 系统 210 开奖历史（最新在前），用于算冷号（新鲜对齐）。
        每个引擎内部有 wanjia28 缓存，8 次 HTTP 只在缓存过期时打一次。"""
        with self._lock:
            plans = list(self._plans.items())
        for uname, eng in plans:
            try:
                ok, res = eng.auto_execute(next_qishu, history)
                if res and not res.get("skipped"):
                    print(f"[broadcast_plan_auto] user={uname} qishu={next_qishu} {res.get('preds')}")
            except Exception as e:
                print(f"[broadcast_plan_auto] user={uname}: {e}")

    def remove_user(self, username):
        """用户删除时清理内存"""
        with self._lock:
            keys = [k for k in self._sims if k.startswith(f"{username}__s")]
            for k in keys:
                self._sims.pop(k, None)
            self._miss.pop(username, None)
            self._accmgr.pop(username, None)

_user_mgr = UserManager()


# ══════════════════════════════════════════════════════════════
#  新增HTML模板：客户端专用
# ══════════════════════════════════════════════════════════════

CLIENT_SIM_RANDOM_TAB_HTML = """
<div id="tab-sim-random" class="tab-content">
  <div class="std-main" style="max-width:1200px">
    <div style="display:flex;gap:0;border-radius:10px;overflow:hidden;border:1px solid var(--border);margin-bottom:12px">
      <button id="simr-slot-btn-1" onclick="simSwitchSlot(1,'random')" style="flex:1;padding:8px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 1</button>
      <button id="simr-slot-btn-2" onclick="simSwitchSlot(2,'random')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 2</button>
      <button id="simr-slot-btn-3" onclick="simSwitchSlot(3,'random')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 3</button>
      <button id="simr-slot-btn-4" onclick="simSwitchSlot(4,'random')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 4</button>
    </div>
    <div id="simr-slot-content"></div>
  </div>
</div>
"""

CLIENT_SIM_MAP_TAB_HTML = """
<div id="tab-sim-map" class="tab-content">
  <div class="std-main" style="max-width:1200px">
    <div style="display:flex;gap:0;border-radius:10px;overflow:hidden;border:1px solid var(--border);margin-bottom:12px">
      <button id="simm-slot-btn-1" onclick="simSwitchSlot(1,'map')" style="flex:1;padding:8px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 1</button>
      <button id="simm-slot-btn-2" onclick="simSwitchSlot(2,'map')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 2</button>
      <button id="simm-slot-btn-3" onclick="simSwitchSlot(3,'map')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 3</button>
      <button id="simm-slot-btn-4" onclick="simSwitchSlot(4,'map')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 4</button>
    </div>
    <div id="simm-slot-content"></div>
  </div>
</div>
"""

CLIENT_SIM_FIX_TAB_HTML = """
<div id="tab-sim-fix" class="tab-content">
  <div class="std-main" style="max-width:1200px">
    <div style="display:flex;gap:0;border-radius:10px;overflow:hidden;border:1px solid var(--border);margin-bottom:12px">
      <button id="simf-slot-btn-1" onclick="simSwitchSlot(1,'fix')" style="flex:1;padding:8px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 1</button>
      <button id="simf-slot-btn-2" onclick="simSwitchSlot(2,'fix')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 2</button>
      <button id="simf-slot-btn-3" onclick="simSwitchSlot(3,'fix')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 3</button>
      <button id="simf-slot-btn-4" onclick="simSwitchSlot(4,'fix')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 4</button>
    </div>
    <div id="simf-slot-content"></div>
  </div>
</div>
"""

CLIENT_SIM_JUMP_TAB_HTML = """
<div id="tab-sim-jump" class="tab-content">
  <div class="std-main" style="max-width:1200px">
    <div style="display:flex;gap:0;border-radius:10px;overflow:hidden;border:1px solid var(--border);margin-bottom:12px">
      <button id="simj-slot-btn-1" onclick="simSwitchSlot(1,'jump')" style="flex:1;padding:8px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 1</button>
      <button id="simj-slot-btn-2" onclick="simSwitchSlot(2,'jump')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 2</button>
      <button id="simj-slot-btn-3" onclick="simSwitchSlot(3,'jump')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 3</button>
      <button id="simj-slot-btn-4" onclick="simSwitchSlot(4,'jump')" style="flex:1;padding:8px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">套 4</button>
    </div>
    <div id="simj-slot-content"></div>
  </div>
</div>
"""

# ══════════════════════════════════════════════════════════════
#  🪨 平台参与记录 tab：查本地 DB real_orders 表（脚本下到石头岛的全部真实下单记录）
#  支持：游戏切换、账号筛选、日期日历、汇总盈亏；展示按账号分组的下单表格
# ══════════════════════════════════════════════════════════════
CLIENT_PLATFORM_TAB_HTML = """
<div id="tab-platform" class="tab-content">
  <div class="std-main" style="max-width:1500px">
    <div class="card" style="margin-bottom:12px">
      <div style="display:flex;flex-wrap:wrap;gap:12px;align-items:center">
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">游戏</label>
          <div style="display:inline-flex;gap:0;border-radius:8px;overflow:hidden;border:1px solid var(--border);vertical-align:middle">
            <button id="pf-game-210" onclick="platformSwitchGame(210)" style="padding:6px 16px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.82rem">🎮 欢乐210</button>
            <button id="pf-game-60" onclick="platformSwitchGame(60)" style="padding:6px 16px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.82rem">⚡ 比特60</button>
          </div>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">账号</label>
          <select id="pf-uid" onchange="platformLoad()" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:5px 8px;font-size:.82rem;min-width:160px">
            <option value="">全部账号</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">来源</label>
          <select id="pf-source" onchange="platformLoad()" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:5px 8px;font-size:.82rem;min-width:130px">
            <option value="">全部来源</option>
            <option value="normal">手动下单</option>
            <option value="sim_random">🎲 随机下</option>
            <option value="sim_map">🎯 开某投某</option>
            <option value="sim_fix">📌 固定</option>
            <option value="sim_jump">🔀 跳转</option>
            <option value="miss">🔍 遗漏检测</option>
            <option value="dawei">🎯 打尾</option>
            <option value="plan">📋 计划跟投</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">日期</label>
          <input id="pf-date" type="date" onchange="platformLoad()" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:5px 8px;font-size:.82rem">
        </div>
        <button class="btn btn-primary btn-sm" onclick="platformLoad()" style="padding:6px 18px">🔍 查询</button>
        <button class="btn btn-ghost btn-sm" onclick="platformReset()" style="padding:6px 14px">重置</button>
        <div style="margin-left:auto;display:flex;gap:14px;align-items:center;font-size:.85rem;flex-wrap:wrap">
          <span style="color:var(--muted)">共 <b id="pf-stat-count" style="color:var(--text)">0</b> 条</span>
          <span style="color:var(--muted)">中 <b id="pf-stat-won" style="color:var(--red)">0</b></span>
          <span style="color:var(--muted)">未中 <b id="pf-stat-lost" style="color:var(--green)">0</b></span>
          <span style="color:var(--muted)">待开奖 <b id="pf-stat-pending" style="color:#60a5fa">0</b></span>
          <span style="color:var(--muted)">投入 <b id="pf-stat-stake" style="color:var(--yellow)">0</b></span>
          <span style="color:var(--muted)">中奖 <b id="pf-stat-win" style="color:var(--green)">0</b></span>
          <span style="color:var(--muted)">盈亏 <b id="pf-stat-pnl" style="color:var(--yellow);font-size:1rem">0</b></span>
        </div>
      </div>
      <div style="font-size:.72rem;color:var(--muted);margin-top:8px;padding-top:8px;border-top:1px solid var(--border);line-height:1.5">
        ℹ️ 展示脚本下到石头岛平台的全部真实下单记录（含手动 / 模拟 / 遗漏所有来源）。脚本用户隔离：仅 <b id="pf-current-user" style="color:#93c5fd"></b> 自己的。
      </div>
    </div>
    <div id="pf-content">
      <div class="notif-empty">请选择筛选条件后点查询</div>
    </div>
  </div>
</div>
"""

CLIENT_ACCOUNTS_TAB_HTML = """
<div id="tab-accounts" class="tab-content">
  <div class="std-main">
    <div style="display:flex;gap:12px;align-items:flex-start;flex-wrap:wrap">
      <!-- 左：添加账号 + 账号概览 -->
      <div class="card" style="flex:1;min-width:280px;max-width:420px">
        <div class="card-title">🔐 添加账号</div>
        <div class="form-group"><label>手机号</label><input id="inp-tel" type="text" placeholder="13xxxxxxxxx"></div>
        <div class="form-group"><label>密码</label><input id="inp-pwd" type="password" placeholder="密码"></div>
        <!-- 🪨 石头岛需要验证码 -->
        <div class="form-group">
          <label>验证码</label>
          <div class="captcha-row">
            <input id="inp-captcha" type="text" placeholder="输入图片验证码" style="flex:1">
            <div class="captcha-frame" id="captcha-box"><span style="color:var(--muted);font-size:.75rem;padding:4px">点击加载</span></div>
            <button class="btn btn-ghost btn-sm" onclick="loadCaptcha()">刷新</button>
          </div>
        </div>
        <input type="hidden" id="inp-uniqid" value="">
        <button class="btn btn-primary" style="width:100%;margin-top:4px" onclick="doLogin()">✅ 登录账号</button>
        <div id="login-msg" style="margin-top:8px;font-size:.85rem;text-align:center;min-height:20px"></div>
        <div style="margin-top:12px;border-top:1px solid var(--border);padding-top:10px">
          <div style="font-size:.75rem;color:var(--muted);margin-bottom:6px">账号概览</div>
          <div id="acc-overview" style="max-height:300px;overflow-y:auto;display:flex;flex-direction:column;gap:4px">
            <div style="color:var(--muted);font-size:.78rem;text-align:center;padding:8px">暂无账号</div>
          </div>
        </div>
      </div>
      <!-- 右：石头岛账号详情 -->
      <div class="card" style="flex:2;min-width:380px">
        <div class="card-title">
          <span>🪨 石头岛账号</span>
          <button class="btn btn-ghost btn-sm" onclick="refreshAccounts()">🔄 刷新</button>
        </div>
        <div style="display:flex;gap:0;border-radius:8px;overflow:hidden;border:1px solid var(--border);margin-bottom:14px;width:fit-content">
          <button id="rec-btn-210" onclick="switchRecGame(210)" style="padding:7px 20px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.85rem">🎮 欢乐210</button>
          <button id="rec-btn-60" onclick="switchRecGame(60)" style="padding:7px 20px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">⚡ 比特60</button>
        </div>
        <div id="acc-grid" class="acc-grid"><div class="notif-empty">暂无账号</div></div>
      </div>
    </div>
  </div>
</div>
"""

# 管理端账号管理Tab
ADMIN_USERS_TAB_HTML = """
<div id="tab-users" class="tab-content active">
  <div class="std-main" style="max-width:1200px">
    <div class="card" style="margin-bottom:12px">
      <div class="card-title">
        <span>👥 客户账号管理</span>
        <button class="btn btn-primary btn-sm" onclick="showCreateUser()">➕ 新增账号</button>
      </div>
      <div id="users-list"><div class="notif-empty">加载中...</div></div>
    </div>
    <!-- 新增/编辑弹层 -->
    <div id="user-modal" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.75);z-index:999;align-items:center;justify-content:center">
      <div class="card" style="width:400px;max-width:95vw;padding:24px">
        <h3 id="modal-title" style="margin-bottom:16px;color:var(--accent)">新增账号</h3>
        <div class="form-group">
          <label>账号</label>
          <input id="modal-username" type="text" placeholder="登录账号">
        </div>
        <div class="form-group">
          <label>密码</label>
          <input id="modal-password" type="text" placeholder="留空则不修改">
        </div>
        <div class="form-group">
          <label>到期时间（留空=永不到期）</label>
          <input id="modal-expires" type="datetime-local">
        </div>
        <div class="form-group">
          <label>备注</label>
          <input id="modal-remark" type="text" placeholder="客户备注">
        </div>
        <div class="form-group">
          <label>🪨 可登录石头岛账号上限</label>
          <input id="modal-max" type="number" min="1" max="100" value="5" placeholder="默认 5">
        </div>
        <div style="display:flex;gap:8px;margin-top:16px">
          <button class="btn btn-primary" onclick="submitUserModal()" style="flex:1">保存</button>
          <button class="btn btn-ghost" onclick="closeUserModal()" style="flex:1">取消</button>
        </div>
        <div id="modal-msg" style="font-size:.82rem;margin-top:8px;text-align:center;min-height:18px"></div>
      </div>
    </div>
  </div>
</div>
"""

# 客户端专用JS（登录/退出/账号管理）
CLIENT_LOGIN_JS = """
async function doLogout(){
  await fetch('/api/logout',{method:'POST'});
  localStorage.removeItem('u_token');
  location.href='/';
}

// ── 💎 续费 modal ──
async function renewOpenModal(){
  var modal=document.getElementById('renew-modal');
  if(modal)modal.style.display='flex';
  await renewLoadPlans();
}
function renewCloseModal(){
  var m=document.getElementById('renew-modal');if(m)m.style.display='none';
  var msg=document.getElementById('renew-msg');if(msg)msg.textContent='';
}
async function renewLoadPlans(){
  var box=document.getElementById('renew-plans');
  if(!box)return;
  box.innerHTML='<div style="color:var(--muted);text-align:center;padding:20px">加载中...</div>';
  try{
    var d=await fetch('/api/payment/plans').then(function(r){return r.json();});
    if(!d.ok){box.innerHTML='<div style="color:var(--red);text-align:center;padding:20px">'+(d.msg||'加载失败')+'</div>';return;}
    var plans=d.plans||{};
    var ORDER=['day','week','month','year','extra_account'];
    var COLORS={day:'#60a5fa',week:'#a78bfa',month:'#fbbf24',year:'#22c55e',extra_account:'#ec4899'};
    var html='';
    ORDER.forEach(function(k){
      var p=plans[k];if(!p)return;
      var c=COLORS[k]||'#94a3b8';
      var isExtra=(k==='extra_account');
      var detail=isExtra?('+ '+(p.accounts||1)+' 个账号槽'):(p.days+' 天 · 上限 '+p.max_accounts+' 账号');
      html+='<div style="background:#0f1117;border:1px solid '+c+';border-radius:10px;padding:14px;cursor:pointer;transition:transform .15s;display:flex;flex-direction:column;align-items:center;text-align:center" onmouseover="this.style.transform=\\'translateY(-3px)\\'" onmouseout="this.style.transform=\\'translateY(0)\\'" onclick="renewBuy(\\''+k+'\\',this)">'
        +'<div style="font-size:.78rem;color:var(--muted)">'+detail+'</div>'
        +'<div style="font-size:1.1rem;color:'+c+';font-weight:800;margin:4px 0">'+p.label+'</div>'
        +'<div style="font-size:1.6rem;font-weight:900;color:#fbbf24">¥'+p.price+'</div>'
        +'<button class="btn btn-primary" style="margin-top:10px;padding:6px 16px;width:100%;background:'+c+';border:none">立即购买</button>'
        +'</div>';
    });
    box.innerHTML=html||'<div style="color:var(--muted);text-align:center;padding:20px">暂无可用套餐</div>';
  }catch(e){box.innerHTML='<div style="color:var(--red);text-align:center;padding:20px">'+e.message+'</div>';}
}
async function renewBuy(planKey, el){
  if(el){el.style.pointerEvents='none';el.style.opacity='.7';}
  var msg=document.getElementById('renew-msg');
  msg.style.color='var(--muted)';msg.textContent='⏳ 创建支付订单中...';
  try{
    var d=await fetch('/api/payment/create_order',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({plan_key:planKey})}).then(function(r){return r.json();});
    if(!d.ok){
      msg.style.color='var(--red)';msg.textContent='❌ '+(d.msg||'创建失败');
      if(el){el.style.pointerEvents='';el.style.opacity='';}return;
    }
    msg.style.color='var(--green)';msg.textContent='✅ 订单已创建 '+d.out_trade_no+' · 跳转支付...';
    if(d.payurl){setTimeout(function(){window.open(d.payurl,'_blank');},300);}
    else{msg.textContent='✅ 订单已创建，但未返回支付链接';}
  }catch(e){msg.style.color='var(--red)';msg.textContent='❌ '+e.message;}
}
"""

ADMIN_USER_DATA_TAB_HTML = """
<div id="tab-userdata" class="tab-content">
  <div class="std-main" style="max-width:1600px">
    <div class="card" style="margin-bottom:12px">
      <div style="display:flex;flex-wrap:wrap;gap:12px;align-items:center">
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">选择用户</label>
          <select id="ud-user" onchange="userDataLoad()" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:5px 8px;font-size:.82rem;min-width:200px">
            <option value="">— 请选择 —</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">游戏</label>
          <select id="ud-game" onchange="userDataLoad()" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:5px 8px;font-size:.82rem">
            <option value="all">全部</option>
            <option value="210">🎮 欢乐210</option>
            <option value="60">⚡ 比特60</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">来源</label>
          <select id="ud-source" onchange="userDataLoad()" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:5px 8px;font-size:.82rem;min-width:130px">
            <option value="">全部来源</option>
            <option value="normal">手动下单</option>
            <option value="sim_random">🎲 随机下</option>
            <option value="sim_map">🎯 开某投某</option>
            <option value="sim_fix">📌 固定</option>
            <option value="sim_jump">🔀 跳转</option>
            <option value="miss">🔍 遗漏检测</option>
            <option value="dawei">🎯 打尾</option>
            <option value="plan">📋 计划跟投</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">日期</label>
          <input id="ud-date" type="date" onchange="userDataLoad()" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:5px 8px;font-size:.82rem">
        </div>
        <button class="btn btn-primary btn-sm" onclick="userDataLoad()" style="padding:6px 18px">🔍 查询</button>
        <button class="btn btn-ghost btn-sm" onclick="userDataReset()" style="padding:6px 14px">重置</button>
      </div>
      <div style="font-size:.72rem;color:var(--muted);margin-top:8px;padding-top:8px;border-top:1px solid var(--border)">
        🔐 管理端专用：可查看客户的脚本登录密码、平台账号明文密码、所有真实下单记录。
      </div>
    </div>
    <div id="ud-content">
      <div class="notif-empty" style="padding:30px">请先在上方选择用户</div>
    </div>
  </div>
</div>
"""

ADMIN_PAYMENT_TAB_HTML = """
<div id="tab-payment" class="tab-content">
  <div class="std-main" style="max-width:1200px">
    <!-- 接口配置 -->
    <div class="card" style="margin-bottom:14px">
      <div class="card-title">⚙️ 支付接口配置</div>
      <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(280px,1fr));gap:12px">
        <div class="form-group"><label>API 地址</label><input id="pcfg-api" type="text" placeholder="https://example.com"></div>
        <div class="form-group"><label>商户 ID (pid)</label><input id="pcfg-pid" type="text"></div>
        <div class="form-group"><label>商户密钥 (KEY)</label><input id="pcfg-key" type="text"></div>
      </div>
      <div style="display:flex;gap:12px;flex-wrap:wrap;margin-top:6px">
        <label style="font-size:.85rem;color:var(--muted);user-select:none">
          <input id="pcfg-free-enable" type="checkbox" style="vertical-align:middle"> 开启免费注册
        </label>
        <div style="display:flex;align-items:center;gap:6px">
          <label style="font-size:.85rem;color:var(--muted)">免费天数</label>
          <input id="pcfg-free-days" type="number" min="1" max="30" style="width:80px">
        </div>
        <div style="display:flex;align-items:center;gap:6px">
          <label style="font-size:.85rem;color:var(--muted)">免费账号上限</label>
          <input id="pcfg-free-acc" type="number" min="1" max="20" style="width:80px">
        </div>
      </div>
      <div style="margin-top:14px;text-align:right">
        <button class="btn btn-primary" onclick="paymentSaveConfig()">💾 保存配置</button>
        <span id="pcfg-msg" style="margin-left:12px;font-size:.85rem"></span>
      </div>
    </div>

    <!-- 套餐编辑 -->
    <div class="card" style="margin-bottom:14px">
      <div class="card-title">📦 套餐价格 / 时长 / 账号数</div>
      <div id="pcfg-plans" style="display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:10px"></div>
      <div style="margin-top:14px;text-align:right">
        <button class="btn btn-primary" onclick="paymentSavePlans()">💾 保存套餐</button>
        <span id="pcfg-plans-msg" style="margin-left:12px;font-size:.85rem"></span>
      </div>
    </div>

    <!-- 订单列表 -->
    <div class="card">
      <div class="card-title">📋 支付订单（近 15 天）</div>
      <div style="display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin-bottom:10px">
        <select id="po-status" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px">
          <option value="">全部状态</option>
          <option value="pending">⏳ 待支付</option>
          <option value="paid">✅ 已支付</option>
          <option value="refunded">↩️ 已退款</option>
          <option value="failed">❌ 失败</option>
        </select>
        <select id="po-days" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px">
          <option value="3">3 天</option>
          <option value="7">7 天</option>
          <option value="15" selected>15 天</option>
          <option value="30">30 天</option>
        </select>
        <button class="btn btn-primary btn-sm" onclick="paymentLoadOrders()">🔍 查询</button>
        <span id="po-stats" style="margin-left:auto;font-size:.82rem;color:var(--muted)"></span>
      </div>
      <div id="po-list"><div class="notif-empty">点查询加载订单</div></div>
    </div>
  </div>
</div>
"""

ADMIN_PAYMENT_JS = """
var _paymentCfg = null;
async function paymentEnter(){
  await paymentLoadConfig();
  paymentLoadOrders();
}
async function paymentLoadConfig(){
  try{
    var d=await fetch('/api/admin/payment/config').then(function(r){return r.json();});
    if(!d.ok)return;
    _paymentCfg=d.data||{};
    $('pcfg-api').value=_paymentCfg.api_url||'';
    $('pcfg-pid').value=_paymentCfg.merchant_id||'';
    $('pcfg-key').value=_paymentCfg.merchant_key||'';
    $('pcfg-free-enable').checked=!!_paymentCfg.free_register_enabled;
    $('pcfg-free-days').value=_paymentCfg.free_register_days||3;
    $('pcfg-free-acc').value=_paymentCfg.free_register_max_accounts||2;
    paymentRenderPlans(_paymentCfg.plans||{});
  }catch(e){console.warn(e);}
}
function paymentRenderPlans(plans){
  var ORDER=['day','week','month','year','extra_account'];
  var box=$('pcfg-plans');var html='';
  ORDER.forEach(function(k){
    var p=plans[k]||{};
    var label=p.label||k;
    var price=p.price||'';
    var enabled=p.enabled!==false;
    var isExtra=(k==='extra_account');
    html+='<div style="background:#0f1117;border:1px solid var(--border);border-radius:8px;padding:10px">'
      +'<div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">'
        +'<input id="plan-'+k+'-label" type="text" value="'+_esc(label)+'" style="background:transparent;border:none;color:#fbbf24;font-weight:800;font-size:.95rem;width:60%">'
        +'<label style="font-size:.75rem;color:var(--muted);user-select:none">'
          +'<input id="plan-'+k+'-enabled" type="checkbox" '+(enabled?'checked':'')+' style="vertical-align:middle"> 启用'
        +'</label>'
      +'</div>'
      +'<div style="display:grid;grid-template-columns:1fr 1fr;gap:6px;font-size:.78rem">'
        +'<div><label style="color:var(--muted);font-size:.72rem">价格(元)</label><input id="plan-'+k+'-price" type="text" value="'+price+'" style="width:100%"></div>'
        +(isExtra
          ?'<div><label style="color:var(--muted);font-size:.72rem">加账号数</label><input id="plan-'+k+'-accounts" type="number" value="'+(p.accounts||1)+'" style="width:100%"></div>'
          :'<div><label style="color:var(--muted);font-size:.72rem">天数</label><input id="plan-'+k+'-days" type="number" value="'+(p.days||0)+'" style="width:100%"></div>'
        )
        +(isExtra?'':'<div style="grid-column:span 2"><label style="color:var(--muted);font-size:.72rem">默认平台账号上限</label><input id="plan-'+k+'-acc" type="number" value="'+(p.max_accounts||0)+'" style="width:100%"></div>')
      +'</div>'
      +'</div>';
  });
  box.innerHTML=html;
}
function _esc(s){return String(s||'').replace(/[<>"'&]/g,function(c){return '&#'+c.charCodeAt(0)+';';});}
async function paymentSaveConfig(){
  var msgEl=$('pcfg-msg');msgEl.textContent='保存中...';msgEl.style.color='var(--muted)';
  try{
    var d=await fetch('/api/admin/payment/config',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({
        api_url:$('pcfg-api').value.trim(),
        merchant_id:$('pcfg-pid').value.trim(),
        merchant_key:$('pcfg-key').value.trim(),
        free_register_enabled:$('pcfg-free-enable').checked?1:0,
        free_register_days:parseInt($('pcfg-free-days').value)||3,
        free_register_max_accounts:parseInt($('pcfg-free-acc').value)||2
      })}).then(function(r){return r.json();});
    msgEl.textContent=d.ok?'✅ '+d.msg:'❌ '+(d.msg||'失败');
    msgEl.style.color=d.ok?'var(--green)':'var(--red)';
  }catch(e){msgEl.textContent='❌ '+e.message;msgEl.style.color='var(--red)';}
}
async function paymentSavePlans(){
  var KEYS=['day','week','month','year','extra_account'];
  var plans={};
  KEYS.forEach(function(k){
    var p={
      label:$('plan-'+k+'-label').value.trim(),
      price:$('plan-'+k+'-price').value.trim(),
      enabled:$('plan-'+k+'-enabled').checked
    };
    if(k==='extra_account'){
      p.accounts=parseInt($('plan-'+k+'-accounts').value)||1;
    }else{
      p.days=parseInt($('plan-'+k+'-days').value)||0;
      p.max_accounts=parseInt($('plan-'+k+'-acc').value)||0;
    }
    plans[k]=p;
  });
  var msgEl=$('pcfg-plans-msg');msgEl.textContent='保存中...';msgEl.style.color='var(--muted)';
  try{
    var d=await fetch('/api/admin/payment/config',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({plans:plans})}).then(function(r){return r.json();});
    msgEl.textContent=d.ok?'✅ '+d.msg:'❌ '+(d.msg||'失败');
    msgEl.style.color=d.ok?'var(--green)':'var(--red)';
  }catch(e){msgEl.textContent='❌ '+e.message;msgEl.style.color='var(--red)';}
}
async function paymentLoadOrders(){
  var status=$('po-status').value;
  var days=$('po-days').value||15;
  var listEl=$('po-list');
  listEl.innerHTML='<div class="notif-empty">加载中...</div>';
  try{
    var u='/api/admin/payment/orders?days='+days;if(status)u+='&status='+status;
    var d=await fetch(u).then(function(r){return r.json();});
    if(!d.ok){listEl.innerHTML='<div class="notif-empty">❌ '+(d.msg||'加载失败')+'</div>';return;}
    var rows=d.data||[];
    var paid=rows.filter(function(r){return r.status==='paid';}).length;
    var totAmt=rows.filter(function(r){return r.status==='paid';})
                    .reduce(function(s,r){return s+parseFloat(r.amount||0);},0);
    $('po-stats').innerHTML='共 '+rows.length+' 单 · 已支付 <b style="color:var(--green)">'+paid+'</b> · 收入 ¥<b style="color:var(--yellow)">'+totAmt.toFixed(2)+'</b>';
    if(!rows.length){listEl.innerHTML='<div class="notif-empty">暂无订单</div>';return;}
    var html='<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:.78rem">'
      +'<thead><tr style="background:#0f1117">'
      +'<th style="padding:6px 8px;text-align:left;color:var(--muted)">订单号</th>'
      +'<th style="text-align:left;color:var(--muted)">用户</th>'
      +'<th style="text-align:left;color:var(--muted)">类型</th>'
      +'<th style="text-align:left;color:var(--muted)">套餐</th>'
      +'<th style="text-align:right;color:var(--muted)">金额</th>'
      +'<th style="text-align:center;color:var(--muted)">状态</th>'
      +'<th style="text-align:left;color:var(--muted)">下单时间</th>'
      +'<th style="text-align:left;color:var(--muted)">支付时间</th>'
      +'<th style="text-align:center;color:var(--muted)">操作</th>'
      +'</tr></thead><tbody>';
    rows.forEach(function(o){
      var statusBadge='⏳ 待支付';var sc='#94a3b8';
      if(o.status==='paid'){statusBadge='✅ 已支付';sc='#22c55e';}
      else if(o.status==='refunded'){statusBadge='↩️ 已退款';sc='#f59e0b';}
      else if(o.status==='failed'){statusBadge='❌ 失败';sc='#ef4444';}
      var typeText=({register:'🆕 注册',renew:'🔁 续费',extra_account:'➕ 加账号'})[o.plan_type]||o.plan_type;
      var refundBtn=(o.status==='paid')?'<button class="btn btn-ghost btn-sm" onclick="paymentRefund(\\''+o.out_trade_no+'\\')" style="font-size:.7rem;padding:2px 8px;color:var(--red)">↩️ 退款</button>':'';
      var payurlBtn=(o.status==='pending'&&o.pay_url)?'<a href="'+o.pay_url+'" target="_blank" class="btn btn-ghost btn-sm" style="font-size:.7rem;padding:2px 8px;color:var(--accent);text-decoration:none">🔗 付款</a>':'';
      html+='<tr style="border-top:1px solid var(--border)">'
        +'<td style="padding:5px 8px;font-family:monospace;color:#94a3b8">'+o.out_trade_no+'</td>'
        +'<td style="padding:5px 8px"><b>'+o.username+'</b></td>'
        +'<td style="padding:5px 8px">'+typeText+'</td>'
        +'<td style="padding:5px 8px">'+o.plan_key+'</td>'
        +'<td style="padding:5px 8px;text-align:right;color:var(--yellow);font-weight:700">¥'+o.amount+'</td>'
        +'<td style="padding:5px 8px;text-align:center;color:'+sc+';font-weight:700">'+statusBadge+'</td>'
        +'<td style="padding:5px 8px;font-size:.72rem;color:var(--muted)">'+(o.created_at||'').slice(5,16)+'</td>'
        +'<td style="padding:5px 8px;font-size:.72rem;color:var(--muted)">'+((o.paid_at||'').slice(5,16)||'--')+'</td>'
        +'<td style="padding:5px 8px;text-align:center">'+refundBtn+payurlBtn+'</td>'
      +'</tr>';
    });
    html+='</tbody></table></div>';
    listEl.innerHTML=html;
  }catch(e){listEl.innerHTML='<div class="notif-empty">❌ '+e.message+'</div>';}
}
async function paymentRefund(otn){
  if(!confirm('⚠️ 确定要退款订单 '+otn+' 吗？\\n退款会调用支付平台接口（不可撤销）'))return;
  try{
    var d=await fetch('/api/admin/payment/refund',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({out_trade_no:otn})}).then(function(r){return r.json();});
    alert(d.ok?('✅ '+d.msg):('❌ '+d.msg));
    if(d.ok)paymentLoadOrders();
  }catch(e){alert('❌ '+e.message);}
}
"""

ADMIN_USER_DATA_JS = """
async function userDataEnter(){
  // 进 tab 时填充用户下拉
  var sel=document.getElementById('ud-user');
  if(sel && sel.options.length<=1){
    try{
      var d=await fetch('/api/admin/users').then(function(r){return r.json();});
      if(d&&d.ok&&Array.isArray(d.data)){
        var html='<option value="">— 请选择 —</option>';
        d.data.forEach(function(u){
          var label=u.username+(u.remark?(' ('+u.remark+')'):'')+(u.expires_at?(' · 到期 '+u.expires_at.slice(0,10)):'');
          html+='<option value="'+u.username+'">'+label+'</option>';
        });
        sel.innerHTML=html;
      }
    }catch(e){console.warn('[userDataEnter]',e);}
  }
}
function userDataReset(){
  ['ud-game','ud-source','ud-date'].forEach(function(id){
    var el=document.getElementById(id);
    if(el)el.value=id==='ud-game'?'all':'';
  });
  userDataLoad();
}
function _udFmtSrc(src){
  if(!src||src==='normal'||src==='manual')return '<span style="color:#94a3b8;background:#1f2937;border:1px solid #4b5563;border-radius:4px;padding:1px 5px;font-size:.7rem">✋ 手动下单</span>';
  if(src==='miss'||src.indexOf('miss')===0)return '<span style="color:#fbbf24;background:#f5910022;border:1px solid #f59e00;border-radius:4px;padding:1px 5px;font-size:.7rem">🔍 遗漏</span>';
  if(src==='sim_random')return '<span style="color:#c084fc;background:#a855f722;border:1px solid #a855f7;border-radius:4px;padding:1px 5px;font-size:.7rem">🎲 随机下</span>';
  if(src==='sim_map')return '<span style="color:#67e8f9;background:#06b6d422;border:1px solid #06b6d4;border-radius:4px;padding:1px 5px;font-size:.7rem">🎯 开某投某</span>';
  if(src==='sim_fix')return '<span style="color:#86efac;background:#16a34a22;border:1px solid #16a34a;border-radius:4px;padding:1px 5px;font-size:.7rem">📌 固定</span>';
  if(src==='sim_jump')return '<span style="color:#f9a8d4;background:#ec489922;border:1px solid #ec4899;border-radius:4px;padding:1px 5px;font-size:.7rem">🔀 跳转</span>';
  if(src.indexOf('sim')===0)return '<span style="color:#c084fc;background:#a855f722;border:1px solid #a855f7;border-radius:4px;padding:1px 5px;font-size:.7rem">🎲 模拟</span>';
  return '<span style="color:var(--muted)">'+src+'</span>';
}
function _udMaskTel(tel){if(!tel||tel.length<7)return tel||'';return tel.slice(0,3)+'****'+tel.slice(7);}
// 28 球赔率表（跟服务端 ODDS 一致）
// ⭐ 赔率 = 官方 × 0.98（石头岛抽 2%）
var _UD_ODDS=[979.99,326.66,163.33,98.00,65.32,46.65,34.99,27.21,21.77,17.81,15.55,14.20,13.41,13.03,13.03,13.41,14.20,15.55,17.81,21.77,27.21,34.99,46.65,65.32,98.00,163.33,326.66,979.99];
// 解析 press_str 返回"位置(赔率)=金额"详情，并算出倍率估算（总投注/1000）
function _udFmtPress(o){
  if(!o.press_str)return {detail:'<span style="color:var(--muted)">--</span>', mul:'--', winAt:''};
  var parts=o.press_str.split(',');
  var detail=[];
  var winPos=parseInt(o.result,10);
  parts.forEach(function(v,i){
    var amt=parseInt(v,10)||0;
    if(amt<=0)return;
    var hit=(!o.pending && !isNaN(winPos) && i===winPos);
    var bg=hit?'background:#ec489922;border:1px solid #ec4899;border-radius:3px;padding:0 4px':'';
    detail.push('<span style="'+bg+'"><span style="color:#94a3b8">'+i+'</span><span style="color:#64748b;font-size:.65rem">('+_UD_ODDS[i]+'x)</span><span style="color:#fbbf24;font-weight:700">:'+amt.toLocaleString()+'</span></span>');
  });
  // 倍率估算 = 总投注 / 1000（base 默认 1000；自定义 base 时此估算偏差，仅供参考）
  var mul=o.betAmount>0?(o.betAmount/1000).toFixed(2)+'x':'--';
  return {detail: detail.length?detail.join(' · '):'<span style="color:var(--muted)">--</span>', mul:mul};
}
async function userDataLoad(){
  var contentEl=document.getElementById('ud-content');
  if(!contentEl)return;
  var uname=(document.getElementById('ud-user')||{}).value||'';
  if(!uname){contentEl.innerHTML='<div class="notif-empty" style="padding:30px">请先在上方选择用户</div>';return;}
  var game=(document.getElementById('ud-game')||{}).value||'all';
  var src=(document.getElementById('ud-source')||{}).value||'';
  var date=(document.getElementById('ud-date')||{}).value||'';
  contentEl.innerHTML='<div class="notif-empty" style="padding:30px">⏳ 查询中...</div>';
  try{
    var url='/api/admin/user_detail?username='+encodeURIComponent(uname)+'&game='+game+'&limit=2000';
    if(src)url+='&source='+encodeURIComponent(src);
    if(date)url+='&date='+encodeURIComponent(date);
    var d=await fetch(url).then(function(r){return r.json();});
    if(!d.ok){contentEl.innerHTML='<div class="notif-empty" style="padding:30px;color:var(--red)">❌ '+(d.msg||'查询失败')+'</div>';return;}
    var html='';
    // ── 用户基本信息卡 ──
    var u=d.user||{};
    var pwd=u.password_plain||'';
    var pwdDisplay=pwd?('<code style="background:#0c0e14;border:1px solid var(--border);border-radius:4px;padding:2px 8px;color:#fbbf24;font-size:.95rem">'+pwd+'</code>'):'<span style="color:var(--muted)">●●●●●●（老用户未存明文，可通过\"客户账号管理\"重置密码）</span>';
    html+='<div class="card" style="margin-bottom:12px">'
      +'<div style="display:flex;flex-wrap:wrap;gap:18px;align-items:center;font-size:.88rem">'
      +'<div>用户名：<b style="color:var(--text);font-size:1rem">'+u.username+'</b></div>'
      +'<div>登录密码：'+pwdDisplay+'</div>'
      +'<div style="color:var(--muted)">到期：<b style="color:var(--text)">'+(u.expires_at||'永不到期')+'</b></div>'
      +'<div style="color:var(--muted)">创建：'+(u.created_at||'').slice(0,16)+'</div>'
      +'<div style="color:var(--muted)">最大账号数：<b style="color:var(--text)">'+(u.max_accounts||5)+'</b></div>'
      +(u.remark?('<div style="color:var(--muted)">备注：<b style="color:var(--text)">'+u.remark+'</b></div>'):'')
      +'</div></div>';
    // ── 平台账号列表 ──
    var accs=d.accounts||[];
    if(accs.length){
      html+='<div class="card" style="margin-bottom:12px;padding:0;overflow:hidden">'
        +'<div style="padding:10px 14px;border-bottom:1px solid var(--border);background:#0f1117;font-size:.88rem;font-weight:800">🪨 平台账号 ('+accs.length+' 个)</div>'
        +'<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:.82rem">'
        +'<thead><tr style="background:#0a0c11;color:var(--muted)">'
        +'<th style="padding:6px 10px;text-align:left">手机号</th>'
        +'<th style="padding:6px 10px;text-align:left">UID</th>'
        +'<th style="padding:6px 10px;text-align:left">明文密码</th>'
        +'<th style="padding:6px 10px;text-align:left">备注</th>'
        +'<th style="padding:6px 10px;text-align:left">Token(脱敏)</th>'
        +'</tr></thead><tbody>';
      accs.forEach(function(a){
        var pwdCell=a.password
          ?'<code style="background:#0c0e14;border:1px solid var(--border);border-radius:4px;padding:1px 6px;color:#fbbf24">'+a.password+'</code>'
          :'<span style="color:var(--muted)">未保存</span>';
        html+='<tr style="border-top:1px solid #1e2235">'
          +'<td style="padding:5px 10px;font-family:monospace">'+(a.tel||'')+'</td>'
          +'<td style="padding:5px 10px;color:var(--muted);font-size:.72rem">'+(a.uid||'')+'</td>'
          +'<td style="padding:5px 10px">'+pwdCell+'</td>'
          +'<td style="padding:5px 10px;color:var(--muted)">'+(a.remark||'--')+'</td>'
          +'<td style="padding:5px 10px;color:var(--muted);font-size:.72rem;font-family:monospace">'+(a.token||'--')+'</td>'
          +'</tr>';
      });
      html+='</tbody></table></div></div>';
    }else{
      html+='<div class="card" style="margin-bottom:12px;color:var(--muted);font-size:.82rem;padding:10px 14px">该用户没有平台账号</div>';
    }
    // ── 下单记录（按账号分组）──
    var stat=d.stats||{count:0};
    var orders=d.orders||[];
    var pnlColor=stat.pnl>0?'var(--green)':(stat.pnl<0?'var(--red)':'var(--muted)');
    // 顶部全局汇总
    html+='<div class="card" style="margin-bottom:12px;padding:10px 14px;display:flex;flex-wrap:wrap;align-items:center;gap:14px;font-size:.85rem">'
      +'<div style="font-weight:800">📋 下单记录汇总</div>'
      +'<div style="color:var(--muted)">共 <b style="color:var(--text)">'+stat.count+'</b> 条</div>'
      +'<div style="color:var(--muted)">中 <b style="color:var(--red)">'+stat.won+'</b></div>'
      +'<div style="color:var(--muted)">未中 <b style="color:var(--green)">'+stat.lost+'</b></div>'
      +'<div style="color:var(--muted)">待开奖 <b style="color:#60a5fa">'+stat.pending+'</b></div>'
      +'<div style="color:var(--muted)">投入 <b style="color:var(--yellow)">'+(stat.stake||0).toLocaleString()+'</b></div>'
      +'<div style="color:var(--muted)">中奖 <b style="color:var(--green)">'+(stat.win||0).toLocaleString()+'</b></div>'
      +'<div style="margin-left:auto">总盈亏 <b style="color:'+pnlColor+';font-size:1.05rem">'+(stat.pnl>=0?'+':'')+(stat.pnl||0).toLocaleString()+'</b></div>'
      +'</div>';
    if(!orders.length){
      html+='<div class="card" style="padding:30px;text-align:center;color:var(--muted);font-size:.82rem">📭 该筛选条件下没有下单记录</div>';
    }else{
      // 按 uid 分组（多账号分卡片，方便阅读）
      var byUid={};
      orders.forEach(function(o){
        var k=o.uid||'unknown';
        if(!byUid[k])byUid[k]={uid:o.uid,tel:o.tel,orders:[]};
        byUid[k].orders.push(o);
      });
      Object.keys(byUid).forEach(function(k){
        var g=byUid[k];
        var gStake=0,gWin=0,gPnl=0,gWon=0,gLost=0,gPending=0;
        g.orders.forEach(function(o){
          if(!o.ok)return;
          gStake+=o.betAmount;
          if(o.pending){gPending++;return;}
          gWin+=o.winAmount; gPnl+=o.pnl;
          if(o.winAmount>0)gWon++; else gLost++;
        });
        var gPnlColor=gPnl>0?'var(--green)':(gPnl<0?'var(--red)':'var(--muted)');
        html+='<div class="card" style="margin-bottom:14px;padding:0;overflow:hidden">';
        // 账号头部
        html+='<div style="padding:10px 14px;border-bottom:1px solid var(--border);background:#0f1117;display:flex;flex-wrap:wrap;align-items:center;gap:14px;font-size:.85rem">'
          +'<div style="font-weight:800">👤 '+_udMaskTel(g.tel)+' <span style="font-size:.7rem;color:var(--muted);font-weight:400">UID '+(g.uid||'').slice(0,12)+'</span></div>'
          +'<div style="color:var(--muted)">共 <b style="color:var(--text)">'+g.orders.length+'</b> 条</div>'
          +'<div style="color:var(--muted)">中 <b style="color:var(--red)">'+gWon+'</b> · 未中 <b style="color:var(--green)">'+gLost+'</b> · 待 <b style="color:#60a5fa">'+gPending+'</b></div>'
          +'<div style="color:var(--muted)">投入 <b style="color:var(--yellow)">'+gStake.toLocaleString()+'</b> · 中奖 <b style="color:var(--green)">'+gWin.toLocaleString()+'</b></div>'
          +'<div style="margin-left:auto">盈亏 <b style="color:'+gPnlColor+';font-size:1rem">'+(gPnl>=0?'+':'')+gPnl.toLocaleString()+'</b></div>'
          +'</div>';
        // 该账号的表格
        html+='<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:.78rem">'
          +'<thead><tr style="background:#0a0c11;color:var(--muted)">'
          +'<th style="padding:6px 8px;text-align:left">时间</th>'
          +'<th style="padding:6px 8px;text-align:center">游戏</th>'
          +'<th style="padding:6px 8px;text-align:left">期号</th>'
          +'<th style="padding:6px 8px;text-align:left;min-width:280px">投注详情（位置/赔率/金额）</th>'
          +'<th style="padding:6px 8px;text-align:right">倍率≈</th>'
          +'<th style="padding:6px 8px;text-align:right">投入</th>'
          +'<th style="padding:6px 8px;text-align:center">开奖</th>'
          +'<th style="padding:6px 8px;text-align:right">中奖</th>'
          +'<th style="padding:6px 8px;text-align:right">盈亏</th>'
          +'<th style="padding:6px 8px;text-align:center">来源</th>'
          +'<th style="padding:6px 8px;text-align:center">状态</th>'
          +'</tr></thead><tbody>';
        g.orders.forEach(function(o){
          var tm=(o.createTime||'').slice(5,16);
          var gtag=o.style===210?'🎮 210':'⚡ 60';
          var press=_udFmtPress(o);
          var openCell,winCell,pnlCell,statusCell;
          if(!o.ok){
            openCell='<td style="padding:5px 8px;text-align:center;color:var(--red)">失败</td>';
            winCell='<td style="padding:5px 8px;text-align:right;color:var(--muted)">--</td>';
            pnlCell='<td style="padding:5px 8px;text-align:right;color:var(--muted)">--</td>';
            statusCell='<td style="padding:5px 8px;text-align:center;color:var(--red);font-size:.72rem">'+(o.msg||'下单失败')+'</td>';
          }else if(o.pending){
            openCell='<td style="padding:5px 8px;text-align:center;color:#60a5fa;font-weight:700">⏳待开奖</td>';
            winCell='<td style="padding:5px 8px;text-align:right;color:var(--muted)">--</td>';
            pnlCell='<td style="padding:5px 8px;text-align:right;color:var(--muted)">--</td>';
            statusCell='<td style="padding:5px 8px;text-align:center;color:#60a5fa;font-size:.72rem">待开奖</td>';
          }else{
            openCell='<td style="padding:5px 8px;text-align:center"><b style="color:var(--yellow);background:#0c0e14;border:1px solid var(--yellow);border-radius:5px;padding:1px 8px">'+o.result+'</b></td>';
            var c=o.winAmount>0?'var(--green)':'var(--muted)';
            winCell='<td style="padding:5px 8px;text-align:right;color:'+c+';font-weight:700">'+(o.winAmount?'+'+o.winAmount.toLocaleString():'0')+'</td>';
            var pc=o.pnl>0?'var(--green)':(o.pnl<0?'var(--red)':'var(--muted)');
            pnlCell='<td style="padding:5px 8px;text-align:right;color:'+pc+';font-weight:700">'+(o.pnl>=0?'+':'')+o.pnl.toLocaleString()+'</td>';
            statusCell=o.winAmount>0
              ?'<td style="padding:5px 8px;text-align:center"><span style="color:var(--red);background:#7f1d1d22;border:1px solid var(--red);border-radius:4px;padding:1px 6px;font-size:.7rem;font-weight:700">中</span></td>'
              :'<td style="padding:5px 8px;text-align:center"><span style="color:var(--green);background:#14532d22;border:1px solid var(--green);border-radius:4px;padding:1px 6px;font-size:.7rem;font-weight:700">未中</span></td>';
          }
          html+='<tr style="border-top:1px solid #1e2235;vertical-align:top">'
            +'<td style="padding:5px 8px;color:var(--muted);font-size:.72rem;white-space:nowrap">'+(tm||'--')+'</td>'
            +'<td style="padding:5px 8px;text-align:center;color:var(--muted);font-size:.72rem">'+gtag+'</td>'
            +'<td style="padding:5px 8px;font-family:monospace">'+o.qishu+'</td>'
            +'<td style="padding:5px 8px;font-size:.7rem;line-height:1.6;word-break:break-all">'+press.detail+'</td>'
            +'<td style="padding:5px 8px;text-align:right;color:var(--accent);font-weight:700">'+press.mul+'</td>'
            +'<td style="padding:5px 8px;text-align:right;color:var(--yellow);font-weight:700">'+o.betAmount.toLocaleString()+'</td>'
            +openCell+winCell+pnlCell
            +'<td style="padding:5px 8px;text-align:center">'+_udFmtSrc(o.source)+'</td>'
            +statusCell
            +'</tr>';
        });
        html+='</tbody></table></div></div>';
      });
    }
    contentEl.innerHTML=html;
  }catch(e){
    contentEl.innerHTML='<div class="notif-empty" style="padding:30px;color:var(--red)">❌ '+e+'</div>';
  }
}
"""

# 管理端额外JS
ADMIN_EXTRA_JS = """
async function adminLogout(){
  await fetch('/Admin123456/logout',{method:'POST'});
  location.href='/Admin123456/login';
}
// ⭐ 修管理端用户列表闪烁：增量更新 + 防抖 + 加 max_accounts 列
var _loadUsersInflight = false;
var _loadUsersLastSig = '';
async function loadUsers(){
  // 防抖：上一次请求还没回来就跳过
  if(_loadUsersInflight) return;
  _loadUsersInflight = true;
  var el=document.getElementById('users-list');
  // 仅当 list 为空（首次加载）时才显示"加载中"，避免每次刷新闪
  if(el && !el.querySelector('table') && _loadUsersLastSig === ''){
    el.innerHTML='<div class="notif-empty">加载中...</div>';
  }
  try{
    var d=await fetch('/api/admin/users').then(r=>r.json());
    if(!d.ok){
      if(el && _loadUsersLastSig === '') el.innerHTML='<div class="notif-empty">加载失败</div>';
      return;
    }
    var users=d.data||[];
    if(!users.length){
      if(el) el.innerHTML='<div class="notif-empty">暂无账号</div>';
      _loadUsersLastSig = 'empty';
      return;
    }
    // 计算签名：只在数据有变化时才重渲染（避免 5 秒内重复整表刷新）
    var sig = JSON.stringify(users.map(function(u){
      return [u.username, u.remark, u.expires_at, u.max_accounts, u.current_accounts,
              (u.std_accounts||[]).map(function(a){return [a.tel,a.online,a.balance];})];
    }));
    if(sig === _loadUsersLastSig) return;   // 数据没变 → 不重渲染
    _loadUsersLastSig = sig;

    var html='<table style="width:100%;border-collapse:collapse;font-size:.82rem">'
      +'<thead><tr style="background:#0f1117">'
      +'<th style="padding:8px;text-align:left">账号</th>'
      +'<th style="text-align:left">备注</th>'
      +'<th style="text-align:left">到期时间</th>'
      +'<th style="text-align:left">账号上限</th>'
      +'<th style="text-align:left">石头岛账号</th>'
      +'<th style="text-align:left">余额</th>'
      +'<th>操作</th></tr></thead><tbody>';
    users.forEach(function(u){
      var exp=u.expires_at?u.expires_at:'永不到期';
      var maxN = u.max_accounts || 5;
      var curN = u.current_accounts || (u.std_accounts ? u.std_accounts.length : 0);
      var maxColor = (curN >= maxN) ? 'var(--red)' : 'var(--muted)';
      var accInfo=u.std_accounts&&u.std_accounts.length?u.std_accounts.map(function(a){
        return a.online?'<span style="color:var(--green)">'+a.tel+'</span>':'<span style="color:var(--muted)">'+a.tel+'(离线)</span>';
      }).join('<br>'):'<span style="color:var(--muted)">未登录</span>';
      var bal=u.std_accounts&&u.std_accounts.length&&u.std_accounts[0].online?fmtNum(u.std_accounts[0].balance):'--';
      html+='<tr style="border-bottom:1px solid var(--border)">'
        +'<td style="padding:8px;font-weight:700">'+u.username+'</td>'
        +'<td style="padding:8px;color:var(--muted)">'+( u.remark||'--')+'</td>'
        +'<td style="padding:8px;color:var(--muted);font-size:.75rem">'+exp+'</td>'
        +'<td style="padding:8px;color:'+maxColor+';font-weight:700">'+curN+'/'+maxN+'</td>'
        +'<td style="padding:8px">'+accInfo+'</td>'
        +'<td style="padding:8px;color:var(--yellow)">'+bal+'</td>'
        +'<td style="padding:8px;text-align:center">'
        +'<button data-username="'+u.username+'" data-remark="'+(u.remark||'')+'" data-expires="'+(u.expires_at||'')+'" data-max="'+maxN+'" onclick="editUser(this)" class="btn btn-ghost btn-sm" style="margin-right:4px">编辑</button>'
        +'<button data-username="'+u.username+'" onclick="deleteUser(this)" class="btn btn-red btn-sm">删除</button>'
        +'</td></tr>';
    });
    html+='</tbody></table>';
    if(el)el.innerHTML=html;
  }catch(e){
    if(el && _loadUsersLastSig === '') el.innerHTML='<div class="notif-empty">加载失败</div>';
  }finally{
    _loadUsersInflight = false;
  }
}

var _editingUsername=null;
function showCreateUser(){
  _editingUsername=null;
  document.getElementById('modal-title').textContent='新增账号';
  document.getElementById('modal-username').value='';
  document.getElementById('modal-username').disabled=false;
  document.getElementById('modal-password').value='';
  document.getElementById('modal-expires').value='';
  document.getElementById('modal-remark').value='';
  document.getElementById('modal-max').value='5';
  document.getElementById('modal-msg').textContent='';
  document.getElementById('user-modal').style.display='flex';
}
function editUser(btn){
  _editingUsername=btn.dataset.username;
  document.getElementById('modal-title').textContent='编辑账号 · '+_editingUsername;
  document.getElementById('modal-username').value=_editingUsername;
  document.getElementById('modal-username').disabled=true;
  document.getElementById('modal-password').value='';
  var exp=btn.dataset.expires||'';
  document.getElementById('modal-expires').value=exp?exp.replace(' ','T').slice(0,16):'';
  document.getElementById('modal-remark').value=btn.dataset.remark||'';
  document.getElementById('modal-max').value=btn.dataset.max||'5';
  document.getElementById('modal-msg').textContent='';
  document.getElementById('user-modal').style.display='flex';
}
function closeUserModal(){document.getElementById('user-modal').style.display='none';}
async function submitUserModal(){
  var msg=document.getElementById('modal-msg');
  var username=document.getElementById('modal-username').value.trim();
  var password=document.getElementById('modal-password').value;
  var expires=document.getElementById('modal-expires').value;
  var remark=document.getElementById('modal-remark').value;
  var max_accounts=parseInt(document.getElementById('modal-max').value||'5');
  var expiresStr=expires?(expires.replace('T',' ')+':00'):'';
  msg.textContent='保存中...';msg.style.color='var(--muted)';
  try{
    var url=_editingUsername?'/api/admin/users/update':'/api/admin/users/create';
    var body={username:username,remark:remark,expires_at:expiresStr,max_accounts:max_accounts};
    if(password)body.password=password;
    var d=await fetch(url,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)}).then(r=>r.json());
    msg.textContent=d.ok?'✅ '+d.msg:'❌ '+d.msg;
    msg.style.color=d.ok?'var(--green)':'var(--red)';
    if(d.ok){setTimeout(function(){closeUserModal();_loadUsersLastSig='';loadUsers();},800);}
  }catch(e){msg.textContent='❌ 网络错误';msg.style.color='var(--red)';}
}
async function deleteUser(btn){
  var username=btn.dataset.username;
  if(!confirm('确认删除账号 '+username+' ？数据保留7天后清理。'))return;
  var d=await fetch('/api/admin/users/delete',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:username})}).then(r=>r.json());
  if(d.ok)loadUsers();
  else alert('删除失败：'+d.msg);
}
setInterval(loadUsers,30000);
"""

# 管理端 LOGIN_JS（用/api/admin前缀）
# admin CSS extra
admin_css_extra = """
.acc-grid{display:flex;flex-wrap:wrap;gap:12px}
.acc-card{background:#12151e;border:1px solid var(--border);border-radius:10px;padding:14px;min-width:240px;flex:1}
"""






COMMON_CSS = """
:root{--bg:#0f1117;--card:#1a1d27;--border:#2a2d3a;--accent:#4f8ef7;--green:#22c55e;--red:#ef4444;--yellow:#f59e0b;--text:#e2e8f0;--muted:#64748b}
*{box-sizing:border-box;margin:0;padding:0}
body{background:var(--bg);color:var(--text);font-family:'Segoe UI',sans-serif;min-height:100vh}
.header{background:var(--card);border-bottom:1px solid var(--border);padding:14px 24px;display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:10px}
.header h1{font-size:1.2rem;color:var(--accent);font-weight:700}
.status-bar{display:flex;align-items:center;gap:16px;font-size:.85rem;color:var(--muted)}
.dot{width:8px;height:8px;border-radius:50%;background:var(--green);animation:pulse 1.5s infinite}
.dot.fast{background:var(--red);animation:pulse .3s infinite}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.3}}
.countdown-box{text-align:center;padding:10px 20px;background:linear-gradient(135deg,#1e2235,#252840);border:1px solid var(--border);border-radius:12px}
.countdown-box .label{font-size:.75rem;color:var(--muted);margin-bottom:2px}
.countdown-box .num{font-size:1.6rem;font-weight:800;color:var(--yellow);font-variant-numeric:tabular-nums}
.countdown-box.urgent .num{color:var(--red)}
/* ── 顶部滚动提示条（免责声明） ── */
.header-marquee{flex:1;min-width:0;overflow:hidden;margin:0 16px;white-space:nowrap;position:relative;
  -webkit-mask-image:linear-gradient(90deg,transparent 0,#000 5%,#000 95%,transparent 100%);
  mask-image:linear-gradient(90deg,transparent 0,#000 5%,#000 95%,transparent 100%)}
.header-marquee-track{display:inline-block;padding-left:100%;animation:hdr-marquee 38s linear infinite;
  font-size:.85rem;color:#fbbf24;font-weight:600;letter-spacing:.5px}
.header-marquee-track:hover{animation-play-state:paused}
.header-marquee-track .sep{display:inline-block;width:60px;text-align:center;color:#f87171;font-weight:900}
@keyframes hdr-marquee{0%{transform:translate3d(0,0,0)}100%{transform:translate3d(-100%,0,0)}}
@media(max-width:899px){.header-marquee{display:none}} /* 手机端隐藏，太挤 */
/* ── 手机适配 ── */
.tabs{display:none}
.tab-select-wrap{padding:0 12px 0;border-bottom:1px solid var(--border);background:var(--card)}
.tab-select{width:100%;background:transparent;border:none;color:var(--text);font-size:.9rem;padding:12px 0;outline:none;cursor:pointer;font-weight:600}
@media(min-width:600px){
  .tabs{display:flex}
  .tab-select-wrap{display:none}
}
@media(max-width:599px){
  .header{padding:10px 14px;gap:6px}
  .header h1{font-size:1rem}
  .countdown-box{padding:6px 12px}
  .countdown-box .num{font-size:1.2rem}
  .std-main{padding:8px}
  .card{padding:10px}
  .form-group{margin-bottom:10px}
  table{font-size:.72rem}
}
.tabs{display:flex;border-bottom:1px solid var(--border);padding:0 24px;background:var(--card)}
.tab{padding:12px 20px;cursor:pointer;font-size:.9rem;font-weight:600;color:var(--muted);border-bottom:2px solid transparent;transition:.2s}
.tab.active{color:var(--accent);border-bottom-color:var(--accent)}
.tab-content{display:none}.tab-content.active{display:block}
.main{display:grid;grid-template-columns:1fr 320px;gap:16px;padding:16px 24px;max-width:1400px;margin:0 auto}
@media(max-width:900px){.main{grid-template-columns:1fr}}
.card{background:var(--card);border:1px solid var(--border);border-radius:12px;padding:16px}
.card-title{font-size:.85rem;font-weight:600;color:var(--muted);text-transform:uppercase;letter-spacing:.05em;margin-bottom:12px;display:flex;align-items:center;justify-content:space-between}
.info-row{display:flex;align-items:center;justify-content:space-between;padding:8px 0;border-bottom:1px solid var(--border);font-size:.85rem}
.info-row:last-child{border-bottom:none}
.info-val{color:var(--accent);font-weight:600}
.btn{display:inline-flex;align-items:center;gap:6px;padding:8px 16px;border-radius:8px;border:none;cursor:pointer;font-size:.85rem;font-weight:600;transition:.2s}
.btn-primary{background:var(--accent);color:#fff}.btn-primary:hover{opacity:.85}
.btn-green{background:var(--green);color:#fff}.btn-green:hover{opacity:.85}
.btn-red{background:var(--red);color:#fff}.btn-red:hover{opacity:.85}
.btn-ghost{background:transparent;border:1px solid var(--border);color:var(--muted)}
.btn-ghost:hover{border-color:var(--accent);color:var(--accent)}
.btn-sm{padding:4px 10px;font-size:.78rem}
.notif-list{display:flex;flex-direction:column;gap:8px;max-height:400px;overflow-y:auto}
.notif-item{background:#12151e;border-left:3px solid var(--yellow);border-radius:6px;padding:10px 12px}
.notif-item .nt{font-size:.78rem;color:var(--muted)}
.notif-item .nb{font-size:.92rem;font-weight:700;color:var(--yellow);margin:3px 0}
.notif-item .nr{font-size:.8rem;color:#94a3b8}
.notif-empty{color:var(--muted);font-size:.85rem;text-align:center;padding:20px 0}
.table-wrap{overflow-x:auto;max-height:75vh;overflow-y:auto}
table{width:100%;border-collapse:collapse;font-size:.83rem}
th{background:#12151e;color:var(--muted);font-weight:600;padding:7px 10px;text-align:center;position:sticky;top:0;z-index:1}
td{padding:6px 10px;text-align:center;border-bottom:1px solid #1e2235}
tr:hover td{background:#1e2235}
tr.hit td{background:#1c1a10}
.sum-badge{display:inline-flex;align-items:center;justify-content:center;width:34px;height:34px;border-radius:50%;font-weight:800;font-size:.92rem}
.sum-big{background:#7f1d1d;color:#fca5a5}
.sum-small{background:#1e3a5f;color:#93c5fd}
.sum-hit{background:#78350f;color:#fde68a;box-shadow:0 0 8px #f59e0b88}
.tag{display:inline-block;padding:2px 7px;border-radius:12px;font-size:.72rem;font-weight:600;margin:1px}
.tag-shunzi{background:#14532d;color:#86efac}
.tag-fixed{background:#7c2d12;color:#fdba74}
.dx-da{color:#f87171;font-weight:600}
.dx-xiao{color:#60a5fa;font-weight:600}
.ds-dan{color:#fb923c;font-weight:600}
.ds-shuang{color:#a78bfa;font-weight:600}
.std-main{padding:16px 24px;max-width:900px;margin:0 auto;display:flex;flex-direction:column;gap:16px}
input{background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);padding:8px 12px;font-size:.9rem;width:100%;outline:none;transition:.2s}
input:focus{border-color:var(--accent)}
label{font-size:.8rem;color:var(--muted);margin-bottom:4px;display:block}
.form-group{margin-bottom:12px}
.captcha-row{display:flex;gap:8px;align-items:center}
.captcha-frame{border:1px solid var(--border);border-radius:8px;overflow:hidden;background:#fff;width:120px;height:40px;flex-shrink:0;display:flex;align-items:center;justify-content:center}
.captcha-frame img{max-width:100%;max-height:100%;object-fit:contain;cursor:pointer;display:block}
.captcha-frame iframe{width:230px;height:80px;border:none;transform:scale(0.7);transform-origin:top left;pointer-events:none}
.multi-btns{display:flex;flex-wrap:wrap;gap:6px;margin-bottom:10px}
.multi-btn{padding:5px 12px;border-radius:8px;border:1px solid var(--border);cursor:pointer;font-size:.8rem;font-weight:700;color:var(--muted);background:transparent;transition:.2s}
.multi-btn:hover{border-color:var(--yellow);color:var(--yellow)}
.multi-btn.active{background:var(--yellow);border-color:var(--yellow);color:#000}
.sel-accounts{display:flex;flex-wrap:wrap;gap:6px;margin-bottom:10px;min-height:28px}
.sel-btn{padding:4px 12px;border-radius:20px;border:1px solid var(--border);cursor:pointer;font-size:.8rem;color:var(--muted);background:transparent;transition:.2s}
.sel-btn.selected{background:var(--accent);border-color:var(--accent);color:#fff}
.order-result{margin-top:10px;padding:10px;background:#12151e;border-radius:8px;font-size:.85rem;max-height:200px;overflow-y:auto}
.res-ok{color:var(--green)}
.res-fail{color:var(--red)}
.acc-grid{display:flex;flex-direction:column;gap:12px}
.acc-card{background:#12151e;border:1px solid var(--border);border-radius:10px;padding:14px}
.acc-header{display:flex;align-items:flex-start;justify-content:space-between;margin-bottom:10px}
.acc-name{font-weight:700;font-size:.95rem}
.acc-meta{display:flex;align-items:center;gap:5px;font-size:.78rem;margin-top:3px}
.dot-sm{width:6px;height:6px;border-radius:50%;display:inline-block}
.dot-online{background:var(--green)}
.dot-offline{background:var(--red)}
.acc-stats{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin:8px 0}
.stat-box{background:var(--card);border-radius:8px;padding:8px;text-align:center}
.stat-label{font-size:.7rem;color:var(--muted)}
.stat-val{font-size:1rem;font-weight:700;margin-top:2px}
.pnl-pos{color:var(--green)}
.pnl-neg{color:var(--red)}
.rec-wrap{max-height:180px;overflow-y:auto;margin-top:8px}
/* 密码锁 */
.lock-overlay{position:fixed;inset:0;background:rgba(0,0,0,.85);z-index:2000;display:flex;align-items:center;justify-content:center}
.lock-box{background:var(--card);border:1px solid var(--border);border-radius:16px;padding:32px;width:320px;text-align:center}
.lock-box h2{font-size:1.1rem;margin-bottom:20px;color:var(--accent)}
.lock-box input{margin-bottom:12px;text-align:center;letter-spacing:2px}
.lock-box .err{color:var(--red);font-size:.82rem;margin-top:8px;min-height:18px}
"""

COMMON_JS = """
const $ = id => document.getElementById(id);
// 全局fetch拦截，自动带认证token
(function(){var _f=window.fetch;window.fetch=function(url,opts){opts=opts||{};if(typeof url==='string'&&(url.startsWith('/api/')||url.startsWith('/Admin123456/'))){var hdrs={};var utok=localStorage.getItem('u_token');var atok=localStorage.getItem('a_token');if(utok)hdrs['X-User-Token']=utok;if(atok)hdrs['X-Admin-Token']=atok;opts.headers=Object.assign(hdrs,opts.headers||{});}return _f.call(this,url,opts);};})();
const SHUNZI_GROUPS=["123","321","234","432","345","543","456","654","567","765","678","876","789","987","358","853","147","471","741","369","963","579","975","479","974","468","864"];
const SHUNZI_PAIRS=new Set();
SHUNZI_GROUPS.forEach(g=>{const d=g.split('').map(Number);for(let i=0;i<d.length;i++)for(let j=0;j<d.length;j++)if(i!==j)SHUNZI_PAIRS.add(d[i]+','+d[j]);});
const FIXED_SUMS=new Set([1,2,3,4,5,6,7,8,9,16,17,18,19,20,21,22,23,24,25,26]);
function classifyRow(item,prev){
  const hits=[];const v=parseInt(item.sum);const t=v%10;
  if(FIXED_SUMS.has(v))hits.push({type:'fixed',label:'固定'});
  if(prev){const pt=parseInt(prev.sum)%10;if(SHUNZI_PAIRS.has(pt+','+t))hits.push({type:'shunzi',label:'顺子'});}
  return hits;
}
let localCD=0,localCD60=0;
setInterval(()=>{
  if(localCD>0)localCD--;
  if(localCD60>0)localCD60--;
  const m=Math.floor(localCD/60),s=localCD%60;
  const el=$('countdown');if(el)el.textContent=String(m).padStart(2,'0')+':'+String(s).padStart(2,'0');
  const m6=Math.floor(localCD60/60),s6=localCD60%60;
  const el6=$('countdown60');if(el6)el6.textContent=String(m6).padStart(2,'0')+':'+String(s6).padStart(2,'0');
  $('cd-box')&&(localCD<=5?$('cd-box').classList.add('urgent'):$('cd-box').classList.remove('urgent'));
  $('cd-box60')&&(localCD60<=5?$('cd-box60').classList.add('urgent'):$('cd-box60').classList.remove('urgent'));
},1000);
let prevQishu=null;
async function poll(){
  try{
    const [sr,hr,hr60]=await Promise.all([
      fetch('/api/status').then(r=>r.json()),
      fetch('/api/history').then(r=>r.json()),
      fetch('/api/history60').then(r=>r.json()),
    ]);
    const {countdown,countdown_60,last_qishu,fetch_time,fast_mode,notifications}=sr;
    const history=hr.data||[];
    const history60=hr60.data||[];
    // ⭐ 修复跳 0 bug：服务端瞬间给 0 时本地不归零，让本地秒表继续倒数
    if(countdown && countdown>0) localCD = countdown;
    if(countdown_60 && countdown_60>0) localCD60 = countdown_60;
    $('fetch-time').textContent='更新: '+(fetch_time||'--');
    $('last-qishu').textContent=last_qishu||'--';
    $('mode-text').textContent=fast_mode?'⚡ 加速抢号中':'正常轮询';
    $('mode-text').style.color=fast_mode?'var(--red)':'var(--green)';
    fast_mode?$('dot').classList.add('fast'):$('dot').classList.remove('fast');
    renderTable(history);renderNotifs(notifications);
    renderTable60(history60);
    // 新期号出来时自动刷新石头岛期号
    if(last_qishu && last_qishu!==prevQishu){
      getExpect210();getExpect60();
    }
    prevQishu=last_qishu;
  }catch(e){console.error(e);}
}
poll();setInterval(poll,3000);

var _lastTbody60Sig = '';
function renderTable60(history){
  var tbody=document.getElementById('tbody-60');
  if(!tbody)return;
  // ⭐ bug 1：history 暂时为空时不要清表，保留上次数据（避免欢乐210/比特60 偶发空数据时整片消失）
  if(!history || !history.length) return;
  // 签名：仅当数据变化时才重渲染（避免每3秒整个表清空+拼接造成闪烁）
  var sig = history.map(function(x){return x.qishu+':'+x.sum;}).join('|');
  if(sig === _lastTbody60Sig) return;
  _lastTbody60Sig = sig;
  var html='';
  history.forEach(function(item){
    var v=parseInt(item.sum);
    var dx=v>=14?'大':'小';var ds=v%2===0?'双':'单';
    var sc=v>=14?'sum-big':'sum-small';
    html+='<tr>'
      +'<td>'+item.qishu+'</td>'
      +'<td><span class="sum-badge '+sc+'">'+String(v).padStart(2,'0')+'</span></td>'
      +'<td class="'+(dx==='大'?'dx-da':'dx-xiao')+'">'+dx+'</td>'
      +'<td class="'+(ds==='单'?'ds-dan':'ds-shuang')+'">'+ds+'</td>'
      +'</tr>';
  });
  tbody.innerHTML = html;
}

var _lastTbodySig = '';
function renderTable(history){
  const tbody=$('tbody');if(!tbody)return;
  // ⭐ bug 1：history 暂时为空时不要清表
  if(!history || !history.length) return;
  // 签名：仅当数据变化时才重渲染（避免欢乐210闪退/闪烁）
  var sig = history.map(function(x){return x.qishu+':'+x.sum;}).join('|');
  if(sig === _lastTbodySig) return;
  _lastTbodySig = sig;
  var html='';
  history.forEach((item,idx)=>{
    const prev=history[idx+1]||null;const hits=classifyRow(item,prev);
    const v=parseInt(item.sum);const tail=v%10;
    let sc=hits.length?'sum-hit':(v>=14?'sum-big':'sum-small');
    const tags=hits.map(h=>`<span class="tag tag-${h.type}">${h.label}</span>`).join('');
    html+=`<tr class="${hits.length?'hit':''}">
      <td>${item.qishu}</td>
      <td><span class="sum-badge ${sc}">${String(v).padStart(2,'0')}</span></td>
      <td style="font-weight:700;color:var(--yellow)">${tail}</td>
      <td class="${item.dx==='大'?'dx-da':'dx-xiao'}">${item.dx}</td>
      <td class="${item.ds==='单'?'ds-dan':'ds-shuang'}">${item.ds}</td>
      <td>${tags||'<span style="color:#4b5563">-</span>'}</td></tr>`;
  });
  tbody.innerHTML = html;
}
function renderNotifs(notifications){
  const el=$('notif-list');
  if(!el)return;   // ⭐ bug 11 后 notif-list 隐藏，admin 页也可能无此元素
  if(!notifications||!notifications.length){el.innerHTML='<div class="notif-empty">暂无命中记录</div>';return;}
  el.innerHTML=notifications.map(n=>`
    <div class="notif-item">
      <div class="nt">${n.ts} · 第${n.qishu}期</div>
      <div class="nb">本期合计 ${n.sum}（尾${parseInt(n.sum)%10}） · 上期合计 ${n.prev_sum}</div>
      <div class="nr">${n.reason}</div>
    </div>`).join('');
}

// 石头岛
// ⭐ 赔率 = 官方 × 0.98（石头岛抽 2%）
const ODDS={0:979.99,1:326.66,2:163.33,3:98.00,4:65.32,5:46.65,6:34.99,7:27.21,8:21.77,9:17.81,10:15.55,11:14.20,12:13.41,13:13.03,14:13.03,15:13.41,16:14.20,17:15.55,18:17.81,19:21.77,20:27.21,21:34.99,22:46.65,23:65.32,24:98.00,25:163.33,26:326.66,27:979.99};
function calcPress(tailsStr,total){
  const tails=[...new Set(tailsStr.split('').filter(c=>/\d/.test(c)).map(Number))];
  if(!tails.length)return null;
  const positions=[];
  for(let p=0;p<28;p++)if(tails.includes(p%10))positions.push(p);
  const invSum=positions.reduce((s,p)=>s+1/ODDS[p],0);
  const alloc={};
  positions.forEach(p=>{alloc[p]=Math.round(total/ODDS[p]/invSum);});
  return alloc;
}

// ── 号码按钮 ──
var selectedNums210=new Set();
var selectedNums60=new Set();
function initNumBtns(){
  ['210','60'].forEach(function(g){
    var el=document.getElementById('num-btns-'+g);
    if(!el)return;
    var html='';
    for(var i=0;i<28;i++){
      html+='<button id="nbtn-'+g+'-'+i+'" onclick="toggleNum(this.dataset.g,'+i+',this)" data-g="'+g+'" '
        +'style="width:36px;height:30px;border-radius:6px;border:1px solid var(--border);background:#12151e;color:var(--muted);font-size:.78rem;font-weight:700;cursor:pointer">'+i+'</button>';
    }
    el.innerHTML=html;
  });
}
function toggleNum(g,n,btn){
  var set=g==='210'?selectedNums210:selectedNums60;
  if(set.has(n)){set.delete(n);btn.style.background='#12151e';btn.style.color='var(--muted)';btn.style.borderColor='var(--border)';}
  else{set.add(n);btn.style.background='var(--accent)';btn.style.color='#fff';btn.style.borderColor='var(--accent)';}
  if(g==='210')updateOddsPreview(); else update60Preview();
}
function clearNumBtns210(){
  selectedNums210.clear();
  for(var i=0;i<28;i++){var b=document.getElementById('nbtn-210-'+i);if(b){b.style.background='#12151e';b.style.color='var(--muted)';b.style.borderColor='var(--border)';}}
  updateOddsPreview();
}
function clearNumBtns60(){
  selectedNums60.clear();
  for(var i=0;i<28;i++){var b=document.getElementById('nbtn-60-'+i);if(b){b.style.background='#12151e';b.style.color='var(--muted)';b.style.borderColor='var(--border)';}}
  update60Preview();
}

// ── 欢乐210 单双大小中边（多选：Set 存所有选中的类型字符串） ──
var selectedBetType210=new Set();
// 求当前所有选中类型的位置并集（去重 + 排序）
function _unionBetTypes210(){
  var u=new Set();
  selectedBetType210.forEach(function(t){
    (BET_TYPE_MAP_210[t]||[]).forEach(function(p){u.add(p);});
  });
  return Array.from(u).sort(function(a,b){return a-b;});
}
var BET_TYPE_MAP_210={
  '单':  [1,3,5,7,9,11,13,15,17,19,21,23,25,27],
  '双':  [0,2,4,6,8,10,12,14,16,18,20,22,24,26],
  '大':  [14,15,16,17,18,19,20,21,22,23,24,25,26,27],
  '小':  [0,1,2,3,4,5,6,7,8,9,10,11,12,13],
  '小单':[1,3,5,7,9,11,13],
  '大单':[15,17,19,21,23,25,27],
  '小双':[0,2,4,6,8,10,12],
  '大双':[14,16,18,20,22,24,26],
  '中':  [10,11,12,13,14,15,16,17],
  '边':  [0,1,2,3,4,5,6,7,8,9,18,19,20,21,22,23,24,25,26,27],
  '小边':[0,1,2,3,4,5,6,7,8,9],
  '大边':[18,19,20,21,22,23,24,25,26,27],
  // ── 3 余 N 组（自定义号码集）──
  '3余0':[7,8,10,11,13,14,16,17,19,20],
  '3余1':[6,8,9,11,12,14,15,17,18,20,21],
  '3余2':[6,7,9,10,12,13,15,16,18,19,21],
  // ── 4 余 N 组（按 4 取模分组）──
  '4余0':[0,4,8,12,16,20,24],
  '4余1':[1,5,9,13,17,21,25],
  '4余2':[2,6,10,14,18,22,26],
  '4余3':[3,7,11,15,19,23,27],
  // ── 5 余 N 组（按 5 取模分组）──
  '5余0':[0,5,10,15,20,25],
  '5余1':[1,6,11,16,21,26],
  '5余2':[2,7,12,17,22,27],
  '5余3':[3,8,13,18,23],
  '5余4':[4,9,14,19,24]
};
// 把对应 mode 的号码按钮高亮蓝色；不属于该组合的恢复（按号码自身选中态）
function _highlightBetTypePositions(g, positions){
  var selSet = (g==='210')?selectedNums210:selectedNums60;
  var posSet = {};
  if(positions&&positions.length)positions.forEach(function(p){posSet[p]=1;});
  for(var i=0;i<28;i++){
    var b=document.getElementById('nbtn-'+g+'-'+i);
    if(!b)continue;
    if(posSet[i]){
      // 组合命中位置 → 蓝色高亮
      b.style.background='#1e40af';
      b.style.color='#fff';
      b.style.borderColor='#3b82f6';
    }else if(selSet.has(i)){
      // 号码按钮自己选中 → accent 色
      b.style.background='var(--accent)';
      b.style.color='#fff';
      b.style.borderColor='var(--accent)';
    }else{
      // 默认态
      b.style.background='#12151e';
      b.style.color='var(--muted)';
      b.style.borderColor='var(--border)';
    }
  }
}
function selectBetType210(t,btn){
  // 多选：每个按钮独立 toggle，重复点取消
  if(selectedBetType210.has(t)){
    selectedBetType210.delete(t);
    btn.classList.remove('active');
  }else{
    selectedBetType210.add(t);
    btn.classList.add('active');
  }
  var lbl=document.getElementById('bet-type-selected-210');
  if(selectedBetType210.size===0){
    lbl.textContent='未选择';
  }else{
    lbl.textContent='已选：'+Array.from(selectedBetType210).join(' + ');
  }
  _highlightBetTypePositions('210', _unionBetTypes210());
  updateOddsPreview();
}
function clearBetType210(){
  selectedBetType210.clear();
  document.querySelectorAll('#bet-type-btns-210 .multi-btn').forEach(function(b){b.classList.remove('active');});
  document.getElementById('bet-type-selected-210').textContent='未选择';
  _highlightBetTypePositions('210', []);
  updateOddsPreview();
}
// 反选：把"号码按钮 ∪ 组合类型并集"取反 → 结果赋给号码按钮，清空组合类型
function invertSelection210(){
  var current=new Set(selectedNums210);
  _unionBetTypes210().forEach(function(p){current.add(p);});
  selectedNums210.clear();
  for(var i=0;i<28;i++){
    if(!current.has(i))selectedNums210.add(i);
  }
  // 清空组合类型
  selectedBetType210.clear();
  document.querySelectorAll('#bet-type-btns-210 .multi-btn').forEach(function(b){b.classList.remove('active');});
  document.getElementById('bet-type-selected-210').textContent='未选择';
  _highlightBetTypePositions('210', []);  // 内部会按 selectedNums210 重画号码按钮
  updateOddsPreview();
}

// ── 欢乐210 预览 ──
// 命中预计盈利（净）：等额回报算法下，命中任一位置赢回 ≈ stake[p] * ODDS[p]（不含本金算入）。
// 净盈利 = stake[p] * ODDS[p] - 实际总投入。所有 p 理论相同，所以预览只显示一个数。
function _calcProfit(arr, positions){
  if(!positions||!positions.length)return 0;
  var totalStake=positions.reduce(function(s,p){return s+(arr[p]||0);},0);
  if(!totalStake)return 0;
  // 取任意一个命中位置的赢回值（毛收益，含本金）
  var p0=positions[0];
  var gross=Math.round((arr[p0]||0)*ODDS[p0]);
  return gross - totalStake;
}
function _setProfitDisplay(elId, profit){
  var el=document.getElementById(elId);
  if(!el)return;
  if(!profit&&profit!==0){el.textContent='--';return;}
  var sign=profit>=0?'+':'';
  el.textContent=sign+profit.toLocaleString()+' 刀币';
  el.style.color=profit>=0?'var(--yellow)':'#f87171';
}
function updateOddsPreview(){
  var amount=parseInt(document.getElementById('inp-amount').value)||1000;
  var preview=document.getElementById('odds-preview');
  var content=document.getElementById('odds-preview-content');
  var positions=[];
  var arr=new Array(28).fill(0);
  if(selectedNums210.size>0){
    // 号码按钮优先
    positions=[...selectedNums210].sort(function(a,b){return a-b;});
    var invSum=positions.reduce(function(s,p){return s+1/ODDS[p];},0);
    positions.forEach(function(p){arr[p]=Math.round(amount/ODDS[p]/invSum);});
    document.getElementById('odds-total').textContent=positions.reduce(function(s,p){return s+arr[p];},0).toLocaleString()+' 刀币';
    _setProfitDisplay('odds-profit', _calcProfit(arr, positions));
    content.innerHTML=positions.map(function(p){return '<span style="color:var(--text)">位置'+p+'('+ODDS[p]+'x)=<b style="color:var(--yellow)">'+arr[p]+'</b></span>';}).join(' · ');
    preview.style.display='block';
  } else if(selectedBetType210.size>0){
    // 多选组合类型并集
    positions=_unionBetTypes210();
    var invSum2=positions.reduce(function(s,p){return s+1/ODDS[p];},0);
    positions.forEach(function(p){arr[p]=Math.round(amount/ODDS[p]/invSum2);});
    document.getElementById('odds-total').textContent=positions.reduce(function(s,p){return s+arr[p];},0).toLocaleString()+' 刀币';
    _setProfitDisplay('odds-profit', _calcProfit(arr, positions));
    content.innerHTML=positions.map(function(p){return '<span style="color:var(--text)">位置'+p+'('+ODDS[p]+'x)=<b style="color:var(--yellow)">'+arr[p]+'</b></span>';}).join(' · ');
    preview.style.display='block';
  } else {
    // 尾数
    var tails=document.getElementById('inp-tails').value.trim();
    if(!tails){preview.style.display='none';return;}
    var alloc=calcPress(tails,amount);
    if(!alloc){preview.style.display='none';return;}
    preview.style.display='block';
    var total=Object.values(alloc).reduce(function(s,v){return s+v;},0);
    document.getElementById('odds-total').textContent=total.toLocaleString()+' 刀币';
    var tailPositions=Object.keys(alloc).map(Number);
    var allocArr=new Array(28).fill(0);
    tailPositions.forEach(function(p){allocArr[p]=alloc[p]||0;});
    _setProfitDisplay('odds-profit', _calcProfit(allocArr, tailPositions));
    var tailDigits=[...new Set(tails.split('').filter(function(c){return /\d/.test(c);}).map(Number))];
    content.innerHTML=tailDigits.map(function(tail){
      var poses=[...Array(28).keys()].filter(function(p){return p%10===tail;});
      var row=poses.map(function(p){return '<span style="color:var(--text)">位置'+p+'('+ODDS[p]+'x)=<b style="color:var(--yellow)">'+(alloc[p]||0)+'</b></span>';}).join(' · ');
      return '<div style="margin-bottom:4px;color:var(--accent)">尾'+tail+'：'+row+'</div>';
    }).join('');
  }
}

// ── 欢乐210 倍数 ──
var currentMulti210=1;
function applyMulti210(x,btn){
  var base=parseInt(document.getElementById('inp-amount').value)||1000;
  document.getElementById('inp-amount').value=Math.max(1000,Math.round(base*x/1000)*1000);
  document.querySelectorAll('#multi-btns-210 .multi-btn').forEach(function(b){b.classList.remove('active');});
  btn.classList.add('active');
  currentMulti210=x;
  updateOddsPreview();
}
function applyCustomMulti210(){
  var x=parseFloat(document.getElementById('custom-multi-210').value);
  if(!x||x<1){alert('请输入有效倍数');return;}
  var base=parseInt(document.getElementById('inp-amount').value)||1000;
  document.getElementById('inp-amount').value=Math.max(1000,Math.round(base*x/1000)*1000);
  document.querySelectorAll('#multi-btns-210 .multi-btn').forEach(function(b){b.classList.remove('active');});
  updateOddsPreview();
}
function clearMulti210(){
  document.querySelectorAll('#multi-btns-210 .multi-btn').forEach(function(b){b.classList.remove('active');});
  document.getElementById('custom-multi-210').value='';
}
function clearMultiActive(){document.querySelectorAll('#multi-btns-210 .multi-btn').forEach(function(b){b.classList.remove('active');});}

// ── 欢乐210 金额 ──
function clearAmount210(){document.getElementById('inp-amount').value='';document.getElementById('avg-hint-210').textContent='';updateOddsPreview();}
function avgAmount210(){
  var total=parseInt(document.getElementById('inp-amount').value)||0;
  var online=accountsData.filter(function(a){return a.online;}).length;
  if(!online){document.getElementById('avg-hint-210').textContent='无在线账号';return;}
  var per=Math.round(total/online);
  document.getElementById('avg-hint-210').textContent=total.toLocaleString()+' ÷ '+online+' 个账号 = 每账号 '+per.toLocaleString()+' 刀币';
}

// ── 比特60 单双大小中边 ──
function clearBetType60(){
  selectedBetType.clear();
  document.querySelectorAll('#bet-type-btns .multi-btn').forEach(function(b){b.classList.remove('active');});
  var lbl=document.getElementById('bet-type-selected');
  if(lbl){lbl.textContent='未选择';lbl.style.color='var(--muted)';}
  _highlightBetTypePositions('60', []);
  update60Preview();
}

// ── 比特60 倍数 ──
function applyMulti60(x,btn){
  var cur=parseInt(document.getElementById('inp-amount-60').value)||1000;
  document.getElementById('inp-amount-60').value=Math.max(1000,Math.round(cur*x/1000)*1000);
  document.querySelectorAll('#multi-btns-60 .multi-btn').forEach(function(b){b.classList.remove('active');});
  btn.classList.add('active');
  update60Preview();
}
function applyCustomMulti60(){
  var x=parseFloat(document.getElementById('custom-multi-60').value);
  if(!x||x<1){alert('请输入有效倍数');return;}
  var base=parseInt(document.getElementById('inp-amount-60').value)||1000;
  document.getElementById('inp-amount-60').value=Math.max(1000,Math.round(base*x/1000)*1000);
  document.querySelectorAll('#multi-btns-60 .multi-btn').forEach(function(b){b.classList.remove('active');});
  update60Preview();
}
function clearMulti60(){
  document.querySelectorAll('#multi-btns-60 .multi-btn').forEach(function(b){b.classList.remove('active');});
  document.getElementById('custom-multi-60').value='';
}

// ── 比特60 金额 ──
function clearAmount60(){document.getElementById('inp-amount-60').value='';document.getElementById('avg-hint-60').textContent='';update60Preview();}
function avgAmount60(){
  var total=parseInt(document.getElementById('inp-amount-60').value)||0;
  var online=accountsData.filter(function(a){return a.online;}).length;
  if(!online){document.getElementById('avg-hint-60').textContent='无在线账号';return;}
  var per=Math.round(total/online);
  document.getElementById('avg-hint-60').textContent=total.toLocaleString()+' ÷ '+online+' 个账号 = 每账号 '+per.toLocaleString()+' 刀币';
}

let selectedUids=new Set();
function renderSelAccounts(accounts){
  const el=$('sel-accounts');
  if(!accounts.length){el.innerHTML='<span style="color:var(--muted);font-size:.8rem">暂无账号</span>';return;}
  el.innerHTML=accounts.map(a=>`
    <button class="sel-btn ${selectedUids.has(a.uid)?'selected':''}"
      onclick="toggleSel('${a.uid}',this)">${a.tel}</button>`).join('');
}
function toggleSel(uid,btn){
  if(selectedUids.has(uid)){selectedUids.delete(uid);btn.classList.remove('selected');}
  else{selectedUids.add(uid);btn.classList.add('selected');}
}
// getExpect210 and getExpect60 defined below
// doOrder210 and doOrder60 defined below
let accountsData=[];
async function refreshAccounts(){
  try{
    // 服务器中转：服务器能正常访问石头岛，由它查 getUserInfo 返回余额/在线状态
    const d=await fetch('/api/std/accounts').then(r=>r.json());
    if(d&&d.ok){
      accountsData=d.data||[];
      renderAccGrid(accountsData);
      renderSelAccounts(accountsData);
      renderAccOverview(accountsData);
      if(accountsData.length){
        var allRecs210=[],allRecs60=[];
        accountsData.forEach(function(a){
          allRecs210=allRecs210.concat(a.records||[]);
          allRecs60=allRecs60.concat(a.records60||[]);
        });
        try{checkPendingResults(allRecs210,allRecs60);}catch(e){}
      }
    }
  }catch(e){}
}
async function refreshAllAccounts(){
  for(const a of accountsData){
    await fetch('/api/std/refresh',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({uid:a.uid})});
  }
  setTimeout(refreshAccounts,2000);
}
async function removeAccount(uid){
  if(!confirm('确认删除该账号？'))return;
  await fetch('/api/std/remove',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({uid})});
  selectedUids.delete(uid);refreshAccounts();
}
function doRefreshOne(btn){refreshOne(btn.getAttribute('data-uid'));}
async function saveRemark(uid,remark){
  await fetch('/api/std/remark',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({uid:uid,remark:remark})});
  setTimeout(refreshAccounts,300);
}
function doRemoveAccount(btn){removeAccount(btn.getAttribute('data-uid'));}
async function refreshOne(uid){
  await fetch('/api/std/refresh',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({uid})});
  setTimeout(refreshAccounts,1500);
}
function renderAccOverview(accounts){
  var el=document.getElementById('acc-overview');
  if(!el)return;
  if(!accounts.length){el.innerHTML='<div style="color:var(--muted);font-size:.78rem;text-align:center;padding:8px">暂无账号</div>';return;}
  el.innerHTML=accounts.map(function(a){
    var pnl=a.total_today||0;
    var pnlColor=pnl>=0?'var(--green)':'var(--red)';
    var pnlStr=(pnl>=0?'+':'')+pnl.toLocaleString();
    var name=a.remark||(a.nickname||a.tel);
    return '<div style="display:flex;align-items:center;justify-content:space-between;padding:5px 8px;background:#12151e;border-radius:6px;font-size:.78rem">'
      +'<span style="color:var(--text);font-weight:600">'+name+'</span>'
      +'<span style="color:var(--accent);margin:0 8px">'+(a.silver||0).toLocaleString()+'</span>'
      +'<span style="color:'+pnlColor+';font-weight:700">'+pnlStr+'</span>'
      +'</div>';
  }).join('');
}

function renderAccGrid(accounts){
  var el=document.getElementById('acc-grid');
  if(!accounts.length){el.innerHTML='<div class="notif-empty">暂无账号，请先登录</div>';return;}
  el.innerHTML=accounts.map(function(a){
    var useRecords=currentRecGame===60?(a.records60||[]):(a.records||[]);
    var useStats=currentRecGame===60?(a.stats60||{}):(a.stats||{});
    var pnl=useStats.today||0;
    var pnlClass=pnl>=0?'pnl-pos':'pnl-neg';
    var pnlStr=(pnl>=0?'+':'')+pnl.toLocaleString();
    var gameName=currentRecGame===60?'比特60 ':'欢乐210 ';
    var recRows=useRecords.slice(0,10).map(function(r){
      var win=r.WinAmount||0;var cost=r.CountBA||0;var rp=win-cost;
      return '<tr><td>'+r.Periods+'</td><td>'+(r.OpenTime||'').slice(5,16)+'</td>'
        +'<td style="font-weight:700">'+(r.SumNum!=null?r.SumNum:'-')+'</td>'
        +'<td>'+cost.toLocaleString()+'</td><td>'+win.toLocaleString()+'</td>'
        +'<td class="'+(rp>=0?'pnl-pos':'pnl-neg')+'">'+(rp>=0?'+':'')+rp.toLocaleString()+'</td></tr>';
    }).join('');
    return '<div class="acc-card" id="acc-card-'+a.uid+'">'
      +'<div class="acc-header"><div>'
      +'<div class="acc-name">'+(a.remark||(a.nickname||a.tel))+'</div>'
      +'<div style="display:flex;align-items:center;gap:6px;margin-top:4px">'
      +'<input type="text" placeholder="设置备注" value="'+(a.remark||'')+'" maxlength="20" data-uid="'+a.uid+'" '
      +'style="background:#1e2235;border:1px solid var(--border);border-radius:4px;color:var(--text);padding:2px 6px;font-size:.72rem;width:100px" '
      +'onchange="saveRemark(this.dataset.uid,this.value)">'
      +'</div>'
      +'<div class="acc-meta">'
      +'<span class="dot-sm '+(a.online?'dot-online':'dot-offline')+'"></span>'
      +'<span style="color:'+(a.online?'var(--green)':'var(--red)')+'"> '+(a.online?'在线':'离线')+'</span>'
      +'<span style="color:var(--muted);margin-left:6px">刷新于 '+a.last_check+'</span>'
      +'</div></div>'
      +'<div style="display:flex;gap:6px;flex-shrink:0">'
      +'<button class="btn btn-ghost btn-sm" onclick="doRefreshOne(this)" data-uid="'+a.uid+'">刷新</button>'
      +'<button class="btn btn-red btn-sm" onclick="doRemoveAccount(this)" data-uid="'+a.uid+'">删除</button>'
      +'</div></div>'
      +'<div class="acc-stats">'
      +'<div class="stat-box"><div class="stat-label">余额</div><div class="stat-val" style="color:var(--accent)">'+(a.silver||0).toLocaleString()+'</div></div>'
      +'<div class="stat-box"><div class="stat-label">今日总盈亏</div><div class="stat-val '+pnlClass+'">'+pnlStr+'</div></div>'
      +'<div class="stat-box"><div class="stat-label">'+gameName+'胜率</div><div class="stat-val">'+(useStats.win_rate||0)+'%</div></div>'
      +'</div>'
      +(useRecords.length
        ?'<div class="rec-wrap"><table><thead><tr><th>期号</th><th>时间</th><th>结果</th><th>投入</th><th>获得</th><th>盈亏</th></tr></thead><tbody>'+recRows+'</tbody></table></div>'
        :'<div style="color:var(--muted);font-size:.8rem;text-align:center;padding:8px">暂无记录</div>')
      +'<div id="real-orders-'+a.uid+'" style="margin-top:8px"></div>'
      +'</div>';
  }).join('');
  fetch('/api/std/recent_orders').then(function(r){return r.json();}).then(function(res){
    if(!res||!res.ok)return;
    accounts.forEach(function(a){
      var el2=document.getElementById('real-orders-'+a.uid);
      if(!el2)return;
      var d=res.data[a.uid];
      if(!d){el2.innerHTML='';return;}
      var game=currentRecGame===60?'60':'210';
      var recs=d[game]||[];
      if(!recs.length){el2.innerHTML='<div style="font-size:.72rem;color:var(--muted);padding:4px 0">暂无真实参与记录</div>';return;}
      var rows=recs.map(function(r){
        var ok=r.ok;
        var srcTag='';
        if((r.source && (r.source==='miss' || r.source.indexOf('miss')===0)))srcTag=' <span style="background:#f5910022;color:#fbbf24;border:1px solid #f59e00;border-radius:3px;padding:0 4px;font-size:.62rem">🔍遗漏</span>';
        else if((r.source && (r.source==='sim' || r.source.indexOf('sim')===0)))srcTag=' <span style="background:#a855f722;color:#c084fc;border:1px solid #a855f7;border-radius:3px;padding:0 4px;font-size:.62rem">🎲模拟</span>';
        return '<div style="display:flex;justify-content:space-between;align-items:center;padding:4px 0;border-top:1px solid var(--border);font-size:.75rem">'
          +'<span style="color:var(--muted)">期号 '+r.qishu+srcTag+'</span>'
          +'<span style="color:var(--muted)">'+r.created_at.slice(5,16)+'</span>'
          +'<span style="font-weight:700;color:'+(ok?'var(--green)':'var(--red)')+'"">'
          +(ok?'✅ 成功 '+parseInt(r.bet_amount).toLocaleString()+'刀':'❌ '+(r.msg||'失败'))+'</span>'
          +'</div>';
      }).join('');
      el2.innerHTML='<div style="background:#0c0e14;border:1px solid var(--border);border-radius:6px;padding:6px 10px">'
        +'<div style="font-size:.72rem;color:var(--muted);margin-bottom:4px;font-weight:700">📋 最近真实参与</div>'
        +rows+'</div>';
    });
  }).catch(function(){});
}


let audioCtx=null;
function getAudioCtx(){
  if(!audioCtx)audioCtx=new(window.AudioContext||window.webkitAudioContext)();
  if(audioCtx.state==='suspended')audioCtx.resume();
  return audioCtx;
}
document.addEventListener('click',()=>getAudioCtx(),{once:false});
function playSound(type){
  try{
    const ctx=getAudioCtx();const t=ctx.currentTime;
    if(type==='order'){
      const osc=ctx.createOscillator(),g=ctx.createGain();
      osc.connect(g);g.connect(ctx.destination);
      osc.type='sine';osc.frequency.setValueAtTime(600,t);osc.frequency.linearRampToValueAtTime(900,t+0.1);
      g.gain.setValueAtTime(0.5,t);g.gain.exponentialRampToValueAtTime(0.001,t+0.8);
      osc.start(t);osc.stop(t+0.8);
    }else if(type==='win'){
      // 🎉 中奖：明亮上升琶音（7 个上升音 + 三角波，高音清脆）
      [[523,0],[659,0.12],[784,0.24],[1047,0.36],[1319,0.48],[1568,0.6],[2093,0.72]].forEach(function(pair){
        const f=pair[0], s=pair[1];
        const osc=ctx.createOscillator(),g=ctx.createGain();
        osc.connect(g);g.connect(ctx.destination);
        osc.type='triangle';osc.frequency.setValueAtTime(f,t+s);
        g.gain.setValueAtTime(0.45,t+s);
        g.gain.exponentialRampToValueAtTime(0.001,t+s+0.5);
        osc.start(t+s);osc.stop(t+s+0.5);
      });
      // 收尾的高音长拖音
      const oscEnd=ctx.createOscillator(),gEnd=ctx.createGain();
      oscEnd.connect(gEnd);gEnd.connect(ctx.destination);
      oscEnd.type='sine';oscEnd.frequency.setValueAtTime(2093,t+0.9);
      gEnd.gain.setValueAtTime(0.4,t+0.9);
      gEnd.gain.exponentialRampToValueAtTime(0.001,t+1.6);
      oscEnd.start(t+0.9);oscEnd.stop(t+1.6);
    }else if(type==='lose'){
      // 😞 输：低沉嗡嗡号角，从 220Hz 拉到 55Hz，sawtooth 粗糙音色 + 颤音
      const osc=ctx.createOscillator(),g=ctx.createGain();
      osc.connect(g);g.connect(ctx.destination);
      osc.type='sawtooth';
      osc.frequency.setValueAtTime(220,t);
      osc.frequency.exponentialRampToValueAtTime(55,t+1.8);
      g.gain.setValueAtTime(0.4,t);
      g.gain.exponentialRampToValueAtTime(0.001,t+1.8);
      osc.start(t);osc.stop(t+1.8);
      // 颤音：LFO 调制频率，让声音抖动
      const lfo=ctx.createOscillator(),lfoGain=ctx.createGain();
      lfo.frequency.setValueAtTime(7,t);
      lfoGain.gain.setValueAtTime(12,t);
      lfo.connect(lfoGain);lfoGain.connect(osc.frequency);
      lfo.start(t);lfo.stop(t+1.8);
    }
  }catch(e){}
}
// ── 游戏切换 ──
var currentGame=210;
function switchGame(g){
  currentGame=g;
  document.getElementById('order-210').style.display=g===210?'block':'none';
  document.getElementById('order-60').style.display=g===60?'block':'none';
  document.getElementById('game-btn-210').style.background=g===210?'var(--accent)':'transparent';
  document.getElementById('game-btn-210').style.color=g===210?'#fff':'var(--muted)';
  document.getElementById('game-btn-60').style.background=g===60?'var(--accent)':'transparent';
  document.getElementById('game-btn-60').style.color=g===60?'#fff':'var(--muted)';
  if(g===210)getExpect210();
  if(g===60)getExpect60();
}

// ── 🪨 石头岛前端常量（石头岛版默认走服务端，前端常量保留兼容）──
const STD_API_BASE = 'https://api.shitoudao.com';

async function stdFetchTokens(){
  try{
    var d=await fetch('/api/std/tokens').then(r=>r.json());
    if(d&&d.ok&&Array.isArray(d.accounts))return d.accounts;
  }catch(e){}
  return [];
}

async function stdGetExpectFE(style){
  // 🪨 石头岛版：走服务端取期号
  try{
    var r=await fetch('/api/std/expect?style='+style);
    var d=await r.json();
    if(d && d.ok && d.expect) return String(d.expect);
  }catch(e){console.warn('[stdGetExpectFE]',e);}
  return '';
}

async function stdLogOrderFE(uid, tel, style, expect, pressStr, ok, msg, source){
  // 下单完成后回传服务器（石头岛版下单本身走服务端，此函数仅供旧逻辑兼容调用）
  try{
    var betAmount=0;
    try{
      betAmount=pressStr.split(',').reduce(function(s,x){
        var n=parseInt(x,10);return s+(isNaN(n)?0:n);
      },0);
    }catch(e){}
    await fetch('/api/std/log_order',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({uid:uid,tel:tel||'',style:String(style),
        expect:String(expect||''),press_str:pressStr,
        bet_amount:betAmount,ok:!!ok,msg:msg||'',
        source:source||'normal'})
    });
  }catch(e){console.warn('[stdLogOrderFE]',e);}
}

async function stdSingleOrder(token, style, expect, pressStr){
  // 🪨 石头岛版：走服务端下单
  try{
    var r=await fetch('/api/std/order',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({style:parseInt(style),press_str:pressStr})
    });
    var d=await r.json();
    if(d.ok){
      var any=(d.data||[]).some(function(x){return x.ok;});
      return {ok:any, msg:''};
    }
    return {ok:false, msg:d.msg||'下单失败'};
  }catch(e){
    return {ok:false,msg:'网络错误: '+(e&&e.message||e)};
  }
}

async function stdDirectOrder(style, pressStr, resEl){
  // 🪨 石头岛版：走服务端下单
  resEl.innerHTML='<div style="padding:14px;text-align:center;color:var(--muted);background:#0c0e14;border:1px solid var(--border);border-radius:8px"><span style="font-size:.92rem">⏳ 下单中...</span></div>';
  var t0=Date.now();
  try{
    var d=await fetch('/api/std/order',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({style:parseInt(style), press_str:pressStr})
    }).then(r=>r.json());
    var elapsed=Date.now()-t0;
    if(!d.ok){
      resEl.innerHTML=_renderOrderResultCard('error',{msg:d.msg||'下单失败', elapsed:elapsed});
      return;
    }
    var results=d.results||d.data||[];   // backend 返 results 字段（旧字段 data 兜底）
    var expect=d.expect||(results[0]||{}).expect||'';
    var okCount=results.filter(function(r){return r.ok;}).length;
    var total=results.length;
    var failed=results.filter(function(r){return !r.ok;});
    var status='success';
    if(total===0){
      status='no-account';
    }else if(okCount===0){
      status='all-fail';
    }else if(okCount<total){
      status='partial';
    }
    resEl.innerHTML=_renderOrderResultCard(status,{
      expect:expect, ok:okCount, total:total, elapsed:elapsed, failed:failed, results:results
    });
    if(expect)watchExpect(expect,String(style));
    setTimeout(refreshAccounts,2000);
    if(typeof refreshRealPendingPanel==='function')setTimeout(refreshRealPendingPanel,800);
  }catch(e){
    resEl.innerHTML=_renderOrderResultCard('error',{msg:'网络错误: '+e.message});
  }
}

// 下单结果卡片：success / partial / all-fail / no-account / error
function _renderOrderResultCard(status, info){
  info=info||{};
  var expect=info.expect||'';
  var ok=info.ok||0, total=info.total||0;
  var elapsed=info.elapsed||0;
  var failed=info.failed||[];
  // 头部卡片样式
  var headBg, headBorder, headIcon, headTitle, headSub, accentColor;
  if(status==='success'){
    headBg='linear-gradient(135deg,#16a34a22,#10b98122)';
    headBorder='#22c55e'; accentColor='#22c55e';
    headIcon='✅'; headTitle='下单成功';
    headSub='全部 '+total+' 个账号已下单 · 期号 '+expect;
  }else if(status==='partial'){
    headBg='linear-gradient(135deg,#f59e0b22,#fbbf2422)';
    headBorder='#fbbf24'; accentColor='#fbbf24';
    headIcon='⚠️'; headTitle='部分成功';
    headSub=ok+' / '+total+' 个账号已下单 · 期号 '+expect;
  }else if(status==='all-fail'){
    headBg='linear-gradient(135deg,#ef444422,#dc262622)';
    headBorder='#ef4444'; accentColor='#ef4444';
    headIcon='❌'; headTitle='全部失败';
    headSub='0 / '+total+' 个账号成功 · 期号 '+(expect||'未取到');
  }else if(status==='no-account'){
    headBg='linear-gradient(135deg,#64748b22,#94a3b822)';
    headBorder='#64748b'; accentColor='#94a3b8';
    headIcon='👤'; headTitle='暂无可用账号';
    headSub='请到「👤 我的账号」tab 添加石头岛账号后再下单';
  }else{ // error
    headBg='linear-gradient(135deg,#ef444422,#dc262622)';
    headBorder='#ef4444'; accentColor='#ef4444';
    headIcon='❌'; headTitle='下单失败';
    headSub=info.msg||'未知错误';
  }
  var html=''+
    '<div style="background:'+headBg+';border:1px solid '+headBorder+';border-radius:10px;padding:14px 16px;margin-bottom:8px">'+
      '<div style="display:flex;align-items:center;gap:12px">'+
        '<div style="font-size:2.4rem;line-height:1">'+headIcon+'</div>'+
        '<div style="flex:1">'+
          '<div style="font-size:1.05rem;font-weight:800;color:'+accentColor+';letter-spacing:.5px">'+headTitle+'</div>'+
          '<div style="font-size:.82rem;color:var(--text);margin-top:3px;opacity:.9">'+headSub+'</div>'+
        '</div>'+
        (elapsed?'<div style="font-size:.72rem;color:var(--muted);text-align:right">耗时<br><b style="color:var(--text);font-size:.85rem">'+elapsed+'ms</b></div>':'')+
      '</div>'+
    '</div>';
  // 仅在 partial / all-fail 时展示错误明细
  if(failed.length>0){
    var failLines=failed.map(function(r){
      var t=r.tel?(r.tel.slice(0,3)+'****'+r.tel.slice(7)):(r.uid||'--');
      return '<div style="background:#0c0e14;border-left:3px solid #ef4444;border-radius:4px;padding:6px 10px;margin-bottom:4px;font-size:.78rem">'+
        '<span style="color:#fca5a5;font-weight:700">'+t+'</span>'+
        '<span style="color:var(--muted);margin-left:8px">'+(r.msg||'失败')+'</span>'+
        '</div>';
    }).join('');
    html+='<div style="margin-top:8px"><div style="font-size:.72rem;color:var(--muted);margin-bottom:4px">⚠️ 错误明细：</div>'+failLines+'</div>';
  }
  return html;
}

// ══════════════════════════════════════════════════════════════
//  ⭐ 真实下单待开奖大卡片（红框区，跨账号汇总，醒目显示）
// ══════════════════════════════════════════════════════════════
var _realPendingGame=210;
var _realPendingCache=null;        // 上次拉到的 recent_orders 原始数据
var _realPendingTimer=null;
var _realPendingHistory210=[];     // 用于检测开奖结果的最近期号缓存
var _realPendingHistory60=[];

function setRealPendingGame(g){
  _realPendingGame=g;
  var t210=document.getElementById('rp-tab-210');
  var t60=document.getElementById('rp-tab-60');
  if(t210){
    t210.style.background=(g===210)?'var(--accent)':'';
    t210.style.color=(g===210)?'#fff':'';
  }
  if(t60){
    t60.style.background=(g===60)?'var(--accent)':'';
    t60.style.color=(g===60)?'#fff':'';
  }
  renderRealPendingPanel();
}

// ⭐ 待开奖卡片只展示"石头岛游戏参与"手动下单的（source=normal）
// 模拟/遗漏触发的真单去 "🪨 平台参与记录" tab 看
function _rpIsManualSource(src){
  return !src || src==='normal' || src==='manual';
}
async function refreshRealPendingPanel(){
  // 拉最近2期下单 + 最近开奖历史
  try{
    // ⭐ 拉每账号 limit=15 条，前端按"石头岛游戏参与"过滤+期号去重后取最近 5 期展示
    var d=await fetch('/api/std/recent_orders?limit=15').then(function(r){return r.json();});
    if(d&&d.ok)_realPendingCache=d.data||{};
  }catch(e){}
  // 本地服务器 28xiaomi 监控历史（最近 ~50 期），用于近期记录的快速匹配
  try{
    var h210=await fetch('/api/history').then(function(r){return r.json();});
    if(h210&&Array.isArray(h210.data))_realPendingHistory210=h210.data;
  }catch(e){}
  try{
    var h60=await fetch('/api/history60').then(function(r){return r.json();});
    if(h60&&Array.isArray(h60.data))_realPendingHistory60=h60.data;
  }catch(e){}
  // ⭐ 前端兜底：触发石头岛开奖历史拉取（最近 ~200 期），跟参与记录 tab 共享缓存
  if(typeof _refreshShitoudOpenMap==='function'){
    try{await _refreshShitoudOpenMap(_realPendingGame);}catch(e){}
  }
  renderRealPendingPanel();
}

function _rpFindOpenSum(qishu, game){
  // 在本地 + 石头岛兜底两个来源里找该期开奖号码
  // 1) 先查本地 28xiaomi 监控的 state.history
  var list=(game===60)?_realPendingHistory60:_realPendingHistory210;
  if(list){
    for(var i=0;i<list.length;i++){
      var r=list[i];
      var q=String(r.Periods||r.qishu||r.qihao||'');
      if(q===String(qishu)){
        var s=r.SumNum;
        if(s===null||s===undefined)s=r.sum;
        if(s===null||s===undefined)s=r.jieguo;
        if(s!==null&&s!==undefined)return parseInt(s);
        break;
      }
    }
  }
  // 2) 兜底查石头岛 openMap 缓存
  try{
    if(typeof _stdOpenMap!=='undefined'&&_stdOpenMap[game]){
      var v=_stdOpenMap[game][String(qishu)];
      if(v!==undefined&&v!==null)return parseInt(v);
    }
  }catch(e){}
  return null;
}

function _rpFormatPress(pressStr){
  // 只显示下注不为0的数字：14:150  15:146 ...
  if(!pressStr)return '';
  var parts=pressStr.split(',');
  var nonzero=[];
  for(var i=0;i<parts.length;i++){
    var v=parseInt(parts[i],10);
    if(!isNaN(v)&&v>0)nonzero.push({pos:i,amt:v});
  }
  if(!nonzero.length)return '';
  // 数字 + 金额，紧凑展示
  return nonzero.map(function(x){
    return '<span style="color:var(--muted)">'+x.pos+':</span><b style="color:var(--text)">'+x.amt.toLocaleString()+'</b>';
  }).join(' · ');
}

function renderRealPendingPanel(){
  var panel=document.getElementById('real-pending-panel');
  if(!panel)return;
  if(!_realPendingCache){
    panel.innerHTML='<div style="color:var(--muted);font-size:.78rem;text-align:center;padding:14px">加载中...</div>';
    return;
  }
  // 合并所有账号的指定游戏数据，仅保留"石头岛游戏参与"手动下单的（source=normal）
  var game=String(_realPendingGame);
  var rows=[];
  Object.keys(_realPendingCache).forEach(function(uid){
    var byGame=_realPendingCache[uid];
    if(!byGame||!byGame[game])return;
    byGame[game].forEach(function(r){
      if(!_rpIsManualSource(r.source))return;   // ⭐ 只展示石头岛游戏参与下的真单
      rows.push(Object.assign({uid:uid}, r));
    });
  });
  if(!rows.length){
    panel.innerHTML='<div style="color:var(--muted);font-size:.78rem;text-align:center;padding:14px">暂无石头岛游戏参与下单记录<br/><span style="font-size:.7rem">(模拟/遗漏触发的下单请到 🪨 平台参与记录 查看)</span></div>';
    return;
  }
  // ⭐ 只保留最近 5 个唯一期号的下单
  var qishuSet={}, qishuList=[];
  rows.forEach(function(r){
    var q=String(r.qishu||'');
    if(!qishuSet[q]){qishuSet[q]=1;qishuList.push(q);}
  });
  qishuList.sort(function(a,b){return b.localeCompare(a);});
  var keep={};
  qishuList.slice(0,5).forEach(function(q){keep[q]=1;});
  rows=rows.filter(function(r){return keep[String(r.qishu||'')];});
  // 用账号 tel 映射（从 accountsData 全局拿）
  var telMap={};
  try{
    if(typeof accountsData!=='undefined'&&Array.isArray(accountsData)){
      accountsData.forEach(function(a){telMap[a.uid]={tel:a.tel||'',remark:a.remark||''};});
    }
  }catch(e){}
  // 按时间倒序
  rows.sort(function(a,b){return (b.created_at||'').localeCompare(a.created_at||'');});
  // 渲染卡片
  var html=rows.map(function(r){
    // ⭐ bug 2：优先用 DB 持久化的开奖号（解决历史期号卡待开奖）
    var openSum=null;
    var expired=false;
    if(r.settled_at && r.result!==null && r.result!==undefined){
      if(parseInt(r.result)===-1){
        expired=true;  // 超1小时未结算，已标记数据缺失
      }else{
        openSum=parseInt(r.result);
      }
    }else{
      var fromMem=_rpFindOpenSum(r.qishu, _realPendingGame);
      if(fromMem!==null && fromMem!==undefined)openSum=parseInt(fromMem);
    }
    var pending=(!expired && (openSum===null||openSum===undefined||isNaN(openSum)));
    var won=false, winAmt=0;
    if(!pending && !expired){
      // 中奖金额：DB 已算过的优先用；否则前端按 press_str 现算
      if(r.win_amount!==null && r.win_amount!==undefined && r.win_amount>0){
        won=true;
        winAmt=parseInt(r.win_amount);
      }else{
        var parts=(r.press_str||'').split(',');
        var stake=parseInt(parts[openSum]||'0',10)||0;
        var oddsArr=[979.99,326.66,163.33,98.00,65.32,46.65,34.99,27.21,21.77,17.81,15.55,14.20,13.41,13.03,13.03,13.41,14.20,15.55,17.81,21.77,27.21,34.99,46.65,65.32,98.00,163.33,326.66,979.99];
        if(stake>0){won=true;winAmt=Math.round(stake*oddsArr[openSum]);}
      }
    }
    // 账号信息
    var ai=telMap[r.uid]||{};
    var telDisplay=ai.tel?(ai.tel.slice(0,3)+'****'+ai.tel.slice(7)):('UID '+(r.uid||'').slice(0,6));
    if(ai.remark)telDisplay=ai.remark+' · '+telDisplay;
    // 状态颜色和样式
    var statusColor, statusText, borderColor, bg;
    if(expired){
      // ⭐ bug 2：超 1 小时仍未结算 → 数据缺失
      statusColor='#9ca3af';
      statusText='⚠️ 数据缺失';
      borderColor='#4b5563';
      bg='#1f2937';
    }else if(pending){
      statusColor='#60a5fa';
      statusText='⏳ 待开奖';
      borderColor='#3b82f6';
      bg='linear-gradient(135deg,#1e3a8a22,#1e40af11)';
    }else if(won){
      statusColor='#4ade80';
      statusText='✅ 中奖 +'+winAmt.toLocaleString();
      borderColor='#22c55e';
      bg='linear-gradient(135deg,#14532d33,#15803d11)';
    }else{
      statusColor='#f87171';
      statusText='❌ 未中';
      borderColor='#ef4444';
      bg='linear-gradient(135deg,#7f1d1d22,#991b1b11)';
    }
    // 下单失败的特殊样式
    if(!r.ok){
      statusColor='#9ca3af';
      statusText='⚠️ 下单失败';
      borderColor='#6b7280';
      bg='#1f2937';
    }
    var pressDisplay=_rpFormatPress(r.press_str);
    var pressHtml=pressDisplay
      ?'<div style="margin-top:6px;font-size:.7rem;line-height:1.6;background:#0c0e14;padding:5px 8px;border-radius:5px;word-break:break-all">'+pressDisplay+'</div>'
      :'';
    var openHtml=(!pending&&!isNaN(openSum))
      ?'<div style="margin-top:5px;font-size:.72rem;color:var(--muted)">开奖号码：<b style="color:var(--yellow);font-size:.9rem">'+openSum+'</b></div>'
      :'';
    var srcTag='';
    if((r.source && (r.source==='miss' || r.source.indexOf('miss')===0)))srcTag=' <span style="background:#f5910022;color:#fbbf24;border:1px solid #f59e00;border-radius:3px;padding:0 4px;font-size:.62rem;font-weight:700">🔍遗漏</span>';
    else if((r.source && (r.source==='sim' || r.source.indexOf('sim')===0)))srcTag=' <span style="background:#a855f722;color:#c084fc;border:1px solid #a855f7;border-radius:3px;padding:0 4px;font-size:.62rem;font-weight:700">🎲模拟</span>';
    return '<div style="border:1.5px solid '+borderColor+';border-radius:8px;padding:10px 12px;background:'+bg+';'+
      (pending?'animation:pulse 2s infinite;':'')+'">'+
      '<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:4px">'+
        '<div style="font-size:.9rem;font-weight:800;color:var(--text)">期号 '+r.qishu+srcTag+'</div>'+
        '<div style="font-size:.8rem;font-weight:800;color:'+statusColor+'">'+statusText+'</div>'+
      '</div>'+
      '<div style="display:flex;justify-content:space-between;align-items:center;font-size:.72rem;color:var(--muted)">'+
        '<span>'+telDisplay+'</span>'+
        '<span>投入 <b style="color:var(--text)">'+(parseInt(r.bet_amount)||0).toLocaleString()+'</b></span>'+
      '</div>'+
      openHtml+
      pressHtml+
    '</div>';
  }).join('');
  panel.innerHTML=html;
}

// 启动自动刷新（5秒一次，足够追踪开奖）
function startRealPendingAutoRefresh(){
  if(_realPendingTimer)clearInterval(_realPendingTimer);
  refreshRealPendingPanel();
  _realPendingTimer=setInterval(refreshRealPendingPanel,5000);
}
// 页面就绪后启动
if(document.readyState==='loading'){
  document.addEventListener('DOMContentLoaded',function(){setTimeout(startRealPendingAutoRefresh,1500);});
}else{
  setTimeout(startRealPendingAutoRefresh,1500);
}

// ══════════════════════════════════════════════════════════════
//  🎯 真实下单 tab（独立页，30 条卡片，左右并排）
// ══════════════════════════════════════════════════════════════
var _roTimer=null;
var _roEntered=false;

function roEnter(){
  // 切到 tab 时调用：写死每秒自动刷新，无人工开关
  _roEntered=true;
  roRefreshNow();
  if(!_roTimer){
    _roTimer=setInterval(roRefreshNow, 1000);
  }
}

async function roClearAll(btn){
  var style=parseInt(btn.dataset.style);
  var gameLabel=style===210?'欢乐210':'比特60';
  if(!confirm('⚠️ 删除记录将无法恢复\\n本系统所有该数据全部删除\\n是否确认删除「'+gameLabel+'」全部参与记录？'))return;
  btn.disabled=true;btn.textContent='删除中...';
  try{
    var d=await fetch('/api/real_orders/clear',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({style:style})}).then(r=>r.json());
    if(d.ok){
      btn.textContent='✅ '+d.msg;
      setTimeout(function(){btn.textContent='🗑 删除全部';btn.disabled=false;},2000);
      roRefreshNow();
    }else{
      btn.textContent='❌ '+(d.msg||'失败');btn.disabled=false;
      setTimeout(function(){btn.textContent='🗑 删除全部';},3000);
    }
  }catch(e){
    btn.textContent='❌ 网络错误';btn.disabled=false;
    setTimeout(function(){btn.textContent='🗑 删除全部';},3000);
  }
}

async function roRefreshNow(){
  // ⭐ 主数据源：本地 real_orders 表（/api/real_orders）
  // 只显示本网站触发的下单（手动/遗漏/模拟），不再显示历史杂单
  // 字段已齐：{qishu, uid, tel, betAmount, winAmount, result, createTime, ok, pending, press_str, source, msg}
  // 开奖号码兜底：浏览器调石头岛接口 getHisList 给 pending 的记录补开奖号
  try{
    var both=await Promise.all([
      fetch('/api/real_orders?game=210&limit=200').then(function(r){return r.json();}),
      fetch('/api/real_orders?game=60&limit=200').then(function(r){return r.json();})
    ]);
    var d210=(both[0]&&both[0].ok)?(both[0].data||[]):[];
    var d60 =(both[1]&&both[1].ok)?(both[1].data||[]):[];
    // 浏览器调石头岛接口兜底：服务端 state.history 只有 ~50/200 期，pending 的老期号需要前端补
    try{
      if(typeof _roApplyOpenMapFallback==='function'){
        await Promise.all([
          _roApplyOpenMapFallback(d210,210),
          _roApplyOpenMapFallback(d60,60)
        ]);
      }
    }catch(e){console.warn('[roRefreshNow] openmap fallback',e);}
    roRenderList(210,d210);
    roRenderList(60,d60);
    roUpdateSummary(210,d210);
    roUpdateSummary(60,d60);
    var tEl=document.getElementById('ro-update-time');
    if(tEl){
      var now=new Date();
      tEl.textContent=String(now.getHours()).padStart(2,'0')+':'+
        String(now.getMinutes()).padStart(2,'0')+':'+
        String(now.getSeconds()).padStart(2,'0');
    }
  }catch(e){console.warn('[roRefreshNow]',e);}
}

// 🪨 石头岛版：参与记录走服务端 /api/real_orders（只显示本系统下的单，不查石头岛平台历史）
async function fetchShitoudOrders(style, perAccountLimit){
  perAccountLimit=perAccountLimit||100;
  // ⭐ bug 8：优先调石头岛接口直接拉真实下单+开奖；拿不到再降级本地DB
  // 加 15s 超时兜底，防止石头岛接口卡死导致前端永远"加载中"
  try{
    var ctrl=null;var timer=null;
    try{ctrl=new AbortController();timer=setTimeout(function(){ctrl.abort();},15000);}catch(e){}
    var r1=await fetch('/api/std/jingyu_orders?game='+style, ctrl?{signal:ctrl.signal}:undefined);
    if(timer)clearTimeout(timer);
    var d1=await r1.json();
    if(d1&&d1.ok&&Array.isArray(d1.data)&&d1.data.length){
      return d1.data;
    }
    console.log('[fetchShitoudOrders] 石头岛接口返回空，降级本地 DB');
  }catch(e){console.warn('[fetchShitoudOrders jingyu]',e);}
  // 降级：本地 DB
  try{
    var r=await fetch('/api/real_orders?game='+style+'&limit='+perAccountLimit);
    var d=await r.json();
    if(!d||!d.ok||!Array.isArray(d.data))return [];
    return d.data.map(function(o){
      return {
        qishu:String(o.qishu||''),
        uid:o.uid||'',
        tel:o.tel||'',
        remark:'',
        betAmount:parseInt(o.betAmount||o.bet_amount)||0,
        winAmount:parseInt(o.winAmount||o.win_amount||0)||0,
        lossAmount:0,
        result:(o.result===undefined||o.result===null||o.result==='--')?'--':o.result,
        createTime:o.createTime||o.created_at||'',
        openTime:o.settled_at||'',
        ok:!!o.ok,
        pending:!!o.pending,
        press_str:o.press_str||'',
        source:o.source||'normal'
      };
    });
  }catch(e){console.warn('[fetchShitoudOrders local]',e);return [];}
}

// ── 🪨 石头岛版：服务端能直连 api.shitoudao.com，开奖历史走服务端 /api/history ──
var _stdOpenMap={60:{},210:{}};      // 期号 -> 开奖号 缓存
var _stdOpenMapTs={60:0,210:0};      // 缓存时间戳
var _stdOpenMapInflight={60:null,210:null};  // 正在进行的请求 Promise

// 固定赔率表（前端独立一份，用于兜底后算 winAmount）
var _RO_ODDS=[979.99,326.66,163.33,98.00,65.32,46.65,34.99,27.21,21.77,17.81,15.55,14.20,13.41,13.03,13.03,13.41,14.20,15.55,17.81,21.77,27.21,34.99,46.65,65.32,98.00,163.33,326.66,979.99];

async function _refreshShitoudOpenMap(style){
  // 🪨 石头岛版：服务端能直连石头岛，拉 history 即可（不再做浏览器直连）
  var now=Date.now();
  if(now-_stdOpenMapTs[style]<30000&&Object.keys(_stdOpenMap[style]).length){
    return _stdOpenMap[style];
  }
  if(_stdOpenMapInflight[style]){
    return _stdOpenMapInflight[style];
  }
  var p=(async function(){
    try{
      var url = (style==60 || style=='60') ? '/api/history60' : '/api/history';
      var r=await fetch(url);
      if(!r.ok)return _stdOpenMap[style];
      var d=await r.json();
      if(!d||!d.ok||!Array.isArray(d.data))return _stdOpenMap[style];
      var newMap={};
      d.data.forEach(function(rec){
        if(!rec)return;
        var qs=rec.qishu, sn=rec.sum;
        if(qs===null||qs===undefined||sn===null||sn===undefined)return;
        newMap[String(qs)]=parseInt(sn);
      });
      _stdOpenMap[style]=newMap;
      _stdOpenMapTs[style]=now;
      return newMap;
    }catch(e){console.warn('[_refreshShitoudOpenMap]',style,e);return _stdOpenMap[style];}
    finally{_stdOpenMapInflight[style]=null;}
  })();
  _stdOpenMapInflight[style]=p;
  return p;
}

async function _roApplyOpenMapFallback(orders, style){
  // 把 orders 里 pending 的记录，用浏览器拉到的开奖号补上
  if(!orders||!orders.length)return;
  var hasPending=orders.some(function(o){return o.ok&&o.pending;});
  if(!hasPending)return;
  var openMap=await _refreshShitoudOpenMap(style);
  if(!openMap||!Object.keys(openMap).length)return;
  orders.forEach(function(o){
    if(!o.ok||!o.pending)return;
    var openNum=openMap[String(o.qishu)];
    if(openNum===undefined||openNum===null)return;
    o.pending=false;
    o.result=openNum;
    // 重算 winAmount
    try{
      var parts=(o.press_str||'').split(',');
      var stake=parseInt(parts[openNum]||'0',10)||0;
      var win=(stake>0)?Math.round(stake*_RO_ODDS[openNum]):0;
      o.winAmount=win;
    }catch(e){o.winAmount=o.winAmount||0;}
  });
}

function _roTelDisplay(rec){
  var t=rec.tel||'';
  return t?(t.slice(0,3)+'****'+t.slice(7)):'UID:'+(rec.uid||'').slice(0,6);
}

function _roFmtPress(pressStr){
  if(!pressStr)return '';
  var parts=pressStr.split(',');
  var nonzero=[];
  for(var i=0;i<parts.length;i++){
    var v=parseInt(parts[i],10);
    if(!isNaN(v)&&v>0)nonzero.push({pos:i,amt:v});
  }
  if(!nonzero.length)return '';
  return nonzero.map(function(x){
    return '<span style="color:#94a3b8">'+x.pos+'</span>:<b style="color:#e2e8f0">'+x.amt.toLocaleString()+'</b>';
  }).join(' · ');
}

function roRenderList(game,orders){
  var listEl=document.getElementById('ro-list-'+game);
  var cntEl=document.getElementById('ro-'+game+'-count');
  if(!listEl)return;
  if(cntEl)cntEl.textContent=orders.length;
  if(!orders.length){
    listEl.innerHTML='<div style="color:var(--muted);font-size:.82rem;text-align:center;padding:30px">暂无下单记录</div>';
    return;
  }
  var primary=(game===210)?'#3b82f6':'#f59e0b';
  var html=orders.map(function(o){
    var pending=!!o.pending;
    var won=!pending&&(parseInt(o.winAmount)||0)>0;
    var failed=!o.ok;
    var bet=parseInt(o.betAmount)||0;
    var win=parseInt(o.winAmount)||0;
    var pnl=win-bet;
    var statusColor,statusText,borderColor,bg,extraClass='';
    if(failed){
      statusColor='#9ca3af';statusText='⚠️ 下单失败';borderColor='#6b7280';bg='#1f2937';
    }else if(pending){
      statusColor='#60a5fa';statusText='⏳ 待开奖';borderColor='#3b82f6';
      bg='linear-gradient(135deg,#1e3a8a33,#1e40af11)';
      extraClass='ro-card-pending';
    }else if(won){
      statusColor='#4ade80';statusText='✅ 中奖 +'+win.toLocaleString();
      borderColor='#22c55e';bg='linear-gradient(135deg,#14532d44,#15803d22)';
    }else{
      statusColor='#f87171';statusText='❌ 未中';borderColor='#ef4444';
      bg='linear-gradient(135deg,#7f1d1d33,#991b1b11)';
    }
    var pnlColor=pnl>0?'#4ade80':(pnl<0?'#f87171':'#9ca3af');
    var pnlSign=pnl>0?'+':(pnl<0?'':'');
    var openHtml=(!pending&&!failed&&o.result!=='--')
      ?'<div style="display:inline-block;background:#0c0e14;border:1.5px solid '+primary+';color:'+primary+';border-radius:6px;padding:2px 10px;font-size:.95rem;font-weight:900;letter-spacing:1px">'+o.result+'</div>'
      :'<span style="color:var(--muted);font-size:.78rem">未开奖</span>';
    var pressDisplay=_roFmtPress(o.press_str);
    var pressHtml=pressDisplay
      ?'<div style="margin-top:8px;font-size:.7rem;line-height:1.6;background:#0a0c11;padding:6px 9px;border-radius:5px;word-break:break-all;color:#cbd5e1">'+pressDisplay+'</div>'
      :'';
    var pnlBlock=failed?'':
      ('<div style="font-size:.72rem;color:var(--muted);margin-top:2px">盈亏：<b style="color:'+pnlColor+';font-size:.85rem">'+pnlSign+pnl.toLocaleString()+'</b></div>');
    var msgBlock=(failed&&o.msg)
      ?'<div style="margin-top:6px;font-size:.7rem;color:#f87171;background:#7f1d1d22;padding:4px 8px;border-radius:5px">'+o.msg+'</div>'
      :'';
    // ⭐ 来源标签（遗漏植入显示橙色小标签；模拟参与按 random/map/fix/jump 拆分）
    var srcTag='';
    if((o.source && (o.source==='miss' || o.source.indexOf('miss')===0))){
      srcTag='<span style="display:inline-block;background:#f5910022;color:#fbbf24;border:1px solid #f59e00;border-radius:4px;padding:1px 6px;font-size:.65rem;font-weight:700;margin-left:6px;vertical-align:middle">🔍 遗漏植入</span>';
    }else if(o.source==='sim_random'){
      srcTag='<span style="display:inline-block;background:#a855f722;color:#c084fc;border:1px solid #a855f7;border-radius:4px;padding:1px 6px;font-size:.65rem;font-weight:700;margin-left:6px;vertical-align:middle">🎲 随机下植入</span>';
    }else if(o.source==='sim_map'){
      srcTag='<span style="display:inline-block;background:#06b6d422;color:#67e8f9;border:1px solid #06b6d4;border-radius:4px;padding:1px 6px;font-size:.65rem;font-weight:700;margin-left:6px;vertical-align:middle">🎯 开某投某植入</span>';
    }else if(o.source==='sim_fix'){
      srcTag='<span style="display:inline-block;background:#16a34a22;color:#86efac;border:1px solid #16a34a;border-radius:4px;padding:1px 6px;font-size:.65rem;font-weight:700;margin-left:6px;vertical-align:middle">📌 固定植入</span>';
    }else if(o.source==='sim_jump'){
      srcTag='<span style="display:inline-block;background:#ec489922;color:#f9a8d4;border:1px solid #ec4899;border-radius:4px;padding:1px 6px;font-size:.65rem;font-weight:700;margin-left:6px;vertical-align:middle">🔀 跳转植入</span>';
    }else if(o.source && (o.source==='dawei' || o.source.indexOf('dawei')===0)){
      srcTag='<span style="display:inline-block;background:#22d3ee22;color:#67e8f9;border:1px solid #22d3ee;border-radius:4px;padding:1px 6px;font-size:.65rem;font-weight:700;margin-left:6px;vertical-align:middle">🎯 打尾植入</span>';
    }else if(o.source && (o.source==='plan' || o.source.indexOf('plan')===0)){
      srcTag='<span style="display:inline-block;background:#84cc1622;color:#bef264;border:1px solid #84cc16;border-radius:4px;padding:1px 6px;font-size:.65rem;font-weight:700;margin-left:6px;vertical-align:middle">📋 计划跟投</span>';
    }else if((o.source && (o.source==='sim' || o.source.indexOf('sim')===0))){
      srcTag='<span style="display:inline-block;background:#a855f722;color:#c084fc;border:1px solid #a855f7;border-radius:4px;padding:1px 6px;font-size:.65rem;font-weight:700;margin-left:6px;vertical-align:middle">🎲 模拟触发</span>';
    }
    return '<div class="'+extraClass+'" style="border:1.5px solid '+borderColor+';border-radius:9px;padding:10px 12px;background:'+bg+'">'+
      '<div style="display:flex;justify-content:space-between;align-items:flex-start;margin-bottom:6px;gap:8px">'+
        '<div>'+
          '<div style="font-size:.92rem;font-weight:800;color:#e2e8f0">期号 '+o.qishu+srcTag+'</div>'+
          '<div style="font-size:.7rem;color:var(--muted);margin-top:2px">'+_roTelDisplay(o)+' · '+(o.createTime||'').slice(5,16)+'</div>'+
        '</div>'+
        '<div style="text-align:right">'+
          '<div style="font-size:.82rem;font-weight:800;color:'+statusColor+'">'+statusText+'</div>'+
          pnlBlock+
        '</div>'+
      '</div>'+
      '<div style="display:flex;justify-content:space-between;align-items:center;gap:8px">'+
        '<div style="font-size:.74rem;color:var(--muted)">投入 <b style="color:#e2e8f0;font-size:.88rem">'+bet.toLocaleString()+'</b></div>'+
        '<div>开奖：'+openHtml+'</div>'+
      '</div>'+
      pressHtml+
      msgBlock+
    '</div>';
  }).join('');
  listEl.innerHTML=html;
}

function roUpdateSummary(game,orders){
  // 排除下单失败的，只统计成功的
  var stake=0,winSum=0;
  orders.forEach(function(o){
    if(!o.ok)return;
    stake+=parseInt(o.betAmount)||0;
    winSum+=parseInt(o.winAmount)||0;
  });
  var pnl=winSum-stake;
  var pnlColor=pnl>0?'#4ade80':(pnl<0?'#f87171':'#9ca3af');
  var sEl=document.getElementById('ro-'+game+'-stake');
  var wEl=document.getElementById('ro-'+game+'-win');
  var pEl=document.getElementById('ro-'+game+'-pnl');
  if(sEl)sEl.textContent=stake.toLocaleString();
  if(wEl)wEl.textContent=winSum.toLocaleString();
  if(pEl){pEl.textContent=(pnl>=0?'+':'')+pnl.toLocaleString();pEl.style.color=pnlColor;}
}

// ── 功能3：开奖号码实时显示 ──
// 后端 /api/xiaomi_proxy 已统一走 fetch_28vp（石头岛优先，28vp 兜底）
// 字段：{qishu, sum, nums:[n1,n2,n3], time} + 顶层 next_ts（下期开奖 Unix 秒）
var _lotteryCache={210:null,60:null};
var _lotteryNextTs={210:0,60:0};
var _lotteryCD={210:null,60:null};

async function lotteryFetch(style){
  try{
    var d=await fetch('/api/xiaomi_proxy?game='+(style===210?5:67)+'&n=2').then(function(r){return r.json();});
    var list=d&&d.ok&&d.data;
    if(!list||!list.length)return;
    _lotteryCache[style]=list[0];
    // 只信后端 next_ts（Unix 秒，已处理时区）；没有则不更新倒计时
    if(d.next_ts){
      _lotteryNextTs[style]=parseFloat(d.next_ts);
    }
    lotteryRender(style);
  }catch(e){}
}

function lotteryRender(style){
  var latest=_lotteryCache[style];
  if(!latest)return;
  var qishuEl=document.getElementById('lottery-qishu-'+style);
  var numsEl=document.getElementById('lottery-nums-'+style);
  if(qishuEl)qishuEl.textContent='#'+(latest.qishu||'--');
  if(numsEl){
    var sumVal=(latest.sum!==null&&latest.sum!==undefined)?latest.sum:'?';
    var nums=Array.isArray(latest.nums)?latest.nums:[];
    if(nums.length>=3){
      numsEl.innerHTML='<span style="color:#93c5fd">'+nums[0]+'</span>'
        +'<span style="color:var(--muted);padding:0 3px">+</span>'
        +'<span style="color:#93c5fd">'+nums[1]+'</span>'
        +'<span style="color:var(--muted);padding:0 3px">+</span>'
        +'<span style="color:#93c5fd">'+nums[2]+'</span>'
        +'<span style="color:var(--muted);padding:0 4px">=</span>'
        +'<span style="color:#fbbf24;font-size:1.1rem">'+sumVal+'</span>';
    }else{
      // 石头岛 index 接口不带分量，只显示合计
      numsEl.innerHTML='<span style="color:#fbbf24;font-size:1.1rem;font-weight:900">'+sumVal+'</span>';
    }
  }
}

function lotteryTick(){
  [210,60].forEach(function(style){
    var nextTs=_lotteryNextTs[style];
    var cdEl=document.getElementById('lottery-cd-'+style);
    if(!cdEl)return;
    if(!nextTs){cdEl.textContent='--';return;}
    var now=Date.now()/1000;
    var remain=Math.round(nextTs-now);
    var period=style===210?210:60;
    // 滚动补期（开奖后接口未更新时不卡0）
    while(remain<-5&&period>0)remain+=period;
    if(remain<=0){
      cdEl.textContent='⏳ 开奖中';
      cdEl.style.color='#f87171';
    }else if(remain<=10){
      cdEl.textContent='⚡ '+remain+'秒';
      cdEl.style.color='#f87171';
    }else{
      var m=Math.floor(remain/60),s=remain%60;
      cdEl.textContent=(m>0?m+'分':'')+s+'秒';
      cdEl.style.color='var(--yellow)';
    }
  });
}

// 5秒拉一次开奖数据，1秒更新倒计时
setInterval(function(){lotteryFetch(210);lotteryFetch(60);},5000);
setInterval(lotteryTick,1000);
// 页面加载立即拉一次
setTimeout(function(){lotteryFetch(210);lotteryFetch(60);},500);

async function getExpect210(){
  try{var e=await stdGetExpectFE('210');
    if(e)document.getElementById('cur-expect-210').textContent=e;}catch(e){}
}
async function doOrder210(){
  var amount=parseInt(document.getElementById('inp-amount').value)||0;
  var res=document.getElementById('order-result-210');
  if(amount<1000){alert('最低下单金额1000');return;}
  // 取消优先级：把号码 / 组合 / 尾数所有非空输入都合并成 positions 集合（并集）
  var posSet=new Set();
  if(selectedNums210.size>0){
    selectedNums210.forEach(function(p){posSet.add(p);});
  }
  if(selectedBetType210.size>0){
    _unionBetTypes210().forEach(function(p){posSet.add(p);});
  }
  var tails=document.getElementById('inp-tails').value.trim();
  if(tails){
    var tailDigits=[...new Set(tails.split('').filter(function(c){return /\d/.test(c);}).map(Number))];
    for(var p=0;p<28;p++){
      if(tailDigits.indexOf(p%10)>=0)posSet.add(p);
    }
  }
  if(posSet.size===0){alert('请选择号码、组合类型或输入尾数');return;}
  var positions=Array.from(posSet).sort(function(a,b){return a-b;});
  var invSum=positions.reduce(function(s,p){return s+1/ODDS[p];},0);
  var arr=new Array(28).fill(0);
  positions.forEach(function(p){arr[p]=Math.round(amount/ODDS[p]/invSum);});
  var pressStr=arr.join(',');
  res.style.display='block';res.innerHTML='<span style="color:var(--muted)">检查期号...</span>';
  playSound('order');
  await stdDirectOrder('210', pressStr, res);
}

// ── 比特60 下单 ──
// 多选 Set：存所有选中的类型字符串
var selectedBetType=new Set();
function _unionBetTypes60(){
  var u=new Set();
  selectedBetType.forEach(function(t){
    (BET_TYPE_MAP[t]||[]).forEach(function(p){u.add(p);});
  });
  return Array.from(u).sort(function(a,b){return a-b;});
}
var BET_TYPE_MAP={
  '单':  [1,3,5,7,9,11,13,15,17,19,21,23,25,27],
  '双':  [0,2,4,6,8,10,12,14,16,18,20,22,24,26],
  '大':  [14,15,16,17,18,19,20,21,22,23,24,25,26,27],
  '小':  [0,1,2,3,4,5,6,7,8,9,10,11,12,13],
  '小单':[1,3,5,7,9,11,13],
  '大单':[15,17,19,21,23,25,27],
  '小双':[0,2,4,6,8,10,12],
  '大双':[14,16,18,20,22,24,26],
  '中':  [10,11,12,13,14,15,16,17],
  '边':  [0,1,2,3,4,5,6,7,8,9,18,19,20,21,22,23,24,25,26,27],
  '小边':[0,1,2,3,4,5,6,7,8,9],
  '大边':[18,19,20,21,22,23,24,25,26,27],
  // ── 3 余 N 组（自定义号码集）──
  '3余0':[7,8,10,11,13,14,16,17,19,20],
  '3余1':[6,8,9,11,12,14,15,17,18,20,21],
  '3余2':[6,7,9,10,12,13,15,16,18,19,21],
  // ── 4 余 N 组 ──
  '4余0':[0,4,8,12,16,20,24],
  '4余1':[1,5,9,13,17,21,25],
  '4余2':[2,6,10,14,18,22,26],
  '4余3':[3,7,11,15,19,23,27],
  // ── 5 余 N 组 ──
  '5余0':[0,5,10,15,20,25],
  '5余1':[1,6,11,16,21,26],
  '5余2':[2,7,12,17,22,27],
  '5余3':[3,8,13,18,23],
  '5余4':[4,9,14,19,24]
};
function selectBetType(type,btn){
  // 多选 toggle
  if(selectedBetType.has(type)){
    selectedBetType.delete(type);
    btn.classList.remove('active');
  }else{
    selectedBetType.add(type);
    btn.classList.add('active');
  }
  var lbl=document.getElementById('bet-type-selected');
  if(selectedBetType.size===0){
    lbl.textContent='未选择';lbl.style.color='var(--muted)';
  }else{
    lbl.textContent='已选：'+Array.from(selectedBetType).join(' + ');
    lbl.style.color='var(--yellow)';
  }
  _highlightBetTypePositions('60', _unionBetTypes60());
  update60Preview();
}
function invertSelection60(){
  var current=new Set(selectedNums60);
  _unionBetTypes60().forEach(function(p){current.add(p);});
  selectedNums60.clear();
  for(var i=0;i<28;i++){
    if(!current.has(i))selectedNums60.add(i);
  }
  selectedBetType.clear();
  document.querySelectorAll('#bet-type-btns .multi-btn').forEach(function(b){b.classList.remove('active');});
  var lbl=document.getElementById('bet-type-selected');
  if(lbl){lbl.textContent='未选择';lbl.style.color='var(--muted)';}
  _highlightBetTypePositions('60', []);
  update60Preview();
}
function calcPress60(type,total){
  var positions=BET_TYPE_MAP[type];
  if(!positions||!positions.length)return null;
  var invSum=positions.reduce(function(s,p){return s+1/ODDS[p];},0);
  var arr=new Array(28).fill(0);
  positions.forEach(function(p){arr[p]=Math.round(total/ODDS[p]/invSum);});
  return arr;
}
function update60Preview(){
  var amount=parseInt(document.getElementById('inp-amount-60').value)||1000;
  var preview=document.getElementById('bet60-preview');
  var ct=document.getElementById('bet60-preview-content');
  var arr=null;var positions=[];
  if(selectedNums60.size>0){
    // 号码按钮优先
    positions=[...selectedNums60].sort(function(a,b){return a-b;});
    var invSum=positions.reduce(function(s,p){return s+1/ODDS[p];},0);
    arr=new Array(28).fill(0);
    positions.forEach(function(p){arr[p]=Math.round(amount/ODDS[p]/invSum);});
  } else {
    var tails=(document.getElementById('inp-tails-60')||{}).value||'';
    if(tails.trim()){
      var tailDigits=[...new Set(tails.trim().split('').filter(function(c){return /\d/.test(c);}).map(Number))];
      if(tailDigits.length){
        positions=[...Array(28).keys()].filter(function(p){return tailDigits.includes(p%10);});
        var invSum2=positions.reduce(function(s,p){return s+1/ODDS[p];},0);
        arr=new Array(28).fill(0);
        positions.forEach(function(p){arr[p]=Math.round(amount/ODDS[p]/invSum2);});
      }
    } else if(selectedBetType.size>0){
      // 多选组合类型并集
      positions=_unionBetTypes60();
      var invSumX=positions.reduce(function(s,p){return s+1/ODDS[p];},0);
      arr=new Array(28).fill(0);
      positions.forEach(function(p){arr[p]=Math.round(amount/ODDS[p]/invSumX);});
    }
  }
  if(!arr){preview.style.display='none';return;}
  preview.style.display='block';
  var total=arr.reduce(function(s,v){return s+v;},0);
  document.getElementById('bet60-total').textContent=total.toLocaleString()+' 刀币';
  _setProfitDisplay('bet60-profit', _calcProfit(arr, positions));
  ct.innerHTML=positions.map(function(p){
    return '<span style="color:var(--text)">位置'+p+'('+ODDS[p]+'x)=<b style="color:var(--yellow)">'+arr[p]+'</b></span>';
  }).join(' · ');
}
async function getExpect60(){
  try{var e=await stdGetExpectFE('60');
    if(e)document.getElementById('cur-expect-60').textContent=e;}catch(e){}
}
async function doOrder60(){
  var amount=parseInt(document.getElementById('inp-amount-60').value)||0;
  var res=document.getElementById('order-result-60');
  if(amount<1000){alert('最低下单金额1000');return;}
  // 取消优先级：号码 / 组合 / 尾数所有非空输入合并成 positions 并集
  var posSet=new Set();
  if(selectedNums60.size>0){
    selectedNums60.forEach(function(p){posSet.add(p);});
  }
  if(selectedBetType.size>0){
    _unionBetTypes60().forEach(function(p){posSet.add(p);});
  }
  var tails=((document.getElementById('inp-tails-60')||{}).value||'').trim();
  if(tails){
    var tailDigits=[...new Set(tails.split('').filter(function(c){return /\d/.test(c);}).map(Number))];
    for(var p=0;p<28;p++){
      if(tailDigits.indexOf(p%10)>=0)posSet.add(p);
    }
  }
  if(posSet.size===0){alert('请选择号码、组合类型或输入尾数');return;}
  var positions=Array.from(posSet).sort(function(a,b){return a-b;});
  var invSum=positions.reduce(function(s,p){return s+1/ODDS[p];},0);
  var arr=new Array(28).fill(0);
  positions.forEach(function(p){arr[p]=Math.round(amount/ODDS[p]/invSum);});
  var pressStr=arr.join(',');
  res.style.display='block';res.innerHTML='<span style="color:var(--muted)">检查期号...</span>';
  playSound('order');
  await stdDirectOrder('60', pressStr, res);
}

// ── 开发者记录切换 ──
var currentRecGame=210;
function switchRecGame(g){
  currentRecGame=g;
  document.getElementById('rec-btn-210').style.background=g===210?'var(--accent)':'transparent';
  document.getElementById('rec-btn-210').style.color=g===210?'#fff':'var(--muted)';
  document.getElementById('rec-btn-60').style.background=g===60?'var(--accent)':'transparent';
  document.getElementById('rec-btn-60').style.color=g===60?'#fff':'var(--muted)';
  renderAccGrid(accountsData);
}

// ── 输赢结果 ──
var pendingExpects={};
var lastShownPeriod210=null;
var lastShownPeriod60=null;
var resultLocked=false; // 开奖后锁定，不再自动覆盖

// 智能轮询：倒计时<=8秒时2秒拉一次，否则8秒拉一次
var smartPollTimer=null;
function startSmartPoll(){
  if(smartPollTimer)clearInterval(smartPollTimer);
  smartPollTimer=setInterval(function(){
    refreshAccounts();
  },2000);
}
function stopFastPoll(){
  if(smartPollTimer){clearInterval(smartPollTimer);smartPollTimer=null;}
}

// 监听倒计时决定轮询频率
var normalPollTimer=setInterval(function(){
  refreshAccounts();
},8000);
// 用 localCD（倒计时变量）控制快速轮询
var lastFastMode=false;
setInterval(function(){
  var fast=localCD<=8;
  if(fast&&!lastFastMode){startSmartPoll();}
  if(!fast&&lastFastMode){stopFastPoll();}
  lastFastMode=fast;
},1000);

function watchExpect(expect,game){
  pendingExpects[String(expect)]=game||'210';
  resultLocked=false;
  // 下单后立即高频拉取
  startSmartPoll();
}

function showBetResult(rec,game,playAudio){
  var panel=document.getElementById('bet-result-panel');
  var gameEl=document.getElementById('bet-result-game');
  var word=document.getElementById('bet-result-word');
  var period=document.getElementById('bet-result-period');
  var numEl=document.getElementById('bet-result-num');
  if(!panel)return;
  var won=(rec.WinAmount||0)>0;
  panel.style.display='block';
  panel.style.border='1px solid '+(won?'var(--green)':'var(--red)');
  gameEl.textContent=game==='60'?'⚡ 比特60':'🎮 欢乐210';
  // ⭐ bug 10：won=true 显示「中」红色；won=false 显示「失败」绿色（用户要求颠倒）
  word.textContent=won?'中':'失败';
  word.style.color=won?'var(--red)':'var(--green)';
  word.style.textShadow=won?'0 0 40px #ef4444aa':'0 0 40px #22c55eaa';
  period.textContent='第 '+rec.Periods+' 期';
  numEl.textContent='开奖号码：'+(rec.SumNum!==null&&rec.SumNum!==undefined?rec.SumNum:'--');
  numEl.style.color=won?'var(--green)':'var(--red)';
  if(playAudio){if(won)playSound('win');else playSound('lose');}
}

function checkPendingResults(records210,records60){
  // 检查主动下单追踪
  var resolved=false;
  Object.keys(pendingExpects).forEach(function(expect){
    var game=pendingExpects[expect];
    var recs=game==='60'?records60:records210;
    var rec=recs&&recs.find(function(r){return String(r.Periods)===String(expect)&&r.SumNum!==null&&r.SumNum!==undefined;});
    if(rec){
      delete pendingExpects[expect];
      resultLocked=true;
      resolved=true;
      showBetResult(rec,game,true);
      stopFastPoll(); // 开奖后停止快速轮询
    }
  });
  if(resolved)return;
  // 页面加载/刷新时自动显示最新已开奖记录（未锁定时）
  if(!resultLocked){
    if(records210&&records210.length){
      var l=records210.find(function(r){return r.CountBA>0&&r.SumNum!==null&&r.SumNum!==undefined;});
      if(l&&String(l.Periods)!==lastShownPeriod210){
        lastShownPeriod210=String(l.Periods);
        showBetResult(l,'210',false);
      }
    }
    if(records60&&records60.length){
      var l2=records60.find(function(r){return r.CountBA>0&&r.SumNum!==null&&r.SumNum!==undefined;});
      if(l2&&String(l2.Periods)!==lastShownPeriod60){
        lastShownPeriod60=String(l2.Periods);
        showBetResult(l2,'60',false);
      }
    }
  }
}
setInterval(function(){getExpect210();getExpect60();},15000);

// 一次性把旧的 localStorage 真实参与开关迁移到服务端（迁移完清掉本地）
async function migrateRealSwitchesOnce(){
  if(localStorage.getItem('_real_switches_migrated')==='1')return;
  var simList=[];var missList=[];
  for(var i=0;i<localStorage.length;i++){
    var k=localStorage.key(i);if(!k)continue;
    // sim_real_{px}_{slot}_{style}_{mode}  px=sim|sim2
    var m=k.match(/^sim_real_(sim2?)_(\\d+)_(\\d+)_(random|map)$/);
    if(m){
      var on=localStorage.getItem(k)==='1';
      // 只迁普通客户端的 sim（px='sim'）；sim2 是 admin 第二套，普通用户不该有
      if(m[1]==='sim'){
        simList.push({slot:parseInt(m[2]),style:parseInt(m[3]),mode:m[4],on:on});
      }
      continue;
    }
    var mm=k.match(/^miss_real_(\\d+)$/);
    if(mm){
      missList.push({style:parseInt(mm[1]),on:localStorage.getItem(k)==='1'});
    }
  }
  if(simList.length||missList.length){
    try{
      var d=await fetch('/api/sim/real/migrate',{
        method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify({sim:simList,miss:missList})
      }).then(r=>r.json());
      console.log('[migrate]', d);
    }catch(e){console.warn('[migrate]',e);return;}
  }
  // 不论有没有数据都标记完成，清理 localStorage 残留
  var keysToRemove=[];
  for(var j=0;j<localStorage.length;j++){
    var kk=localStorage.key(j);if(!kk)continue;
    if(/^sim_real(State)?_/.test(kk)||/^miss_real_/.test(kk)){
      keysToRemove.push(kk);
    }
  }
  keysToRemove.forEach(function(k){localStorage.removeItem(k);});
  localStorage.setItem('_real_switches_migrated','1');
}

document.addEventListener('DOMContentLoaded',function(){
  // ⭐ 这些函数只在用户端定义；admin 页加载 COMMON_JS 但不加载 SIM_JS，需 guard
  if(typeof initNumBtns==='function')initNumBtns();
  if(typeof refreshAccounts==='function')refreshAccounts();
  if(typeof simRenderSlot==='function'){simRenderSlot(1,'random');simRenderSlot(1,'map');simRenderSlot(1,'fix');simRenderSlot(1,'jump');}
  if(typeof migrateRealSwitchesOnce==='function')migrateRealSwitchesOnce();
  if(typeof startBannedPolling==='function')startBannedPolling();
});

// 爆仓 banner 轮询：每 3 秒查一次
async function startBannedPolling(){
  async function tick(){
    try{
      var d=await fetch('/api/sim/banned_accounts').then(r=>r.json());
      var bar=document.getElementById('banned-banner');
      var txt=document.getElementById('banned-banner-text');
      if(!bar||!txt)return;
      if(d.ok&&d.data&&d.data.length){
        var msgs=d.data.map(function(b){
          return '账号 '+(b.tel||b.uid)+' 已爆仓（'+(b.reason||'余额不足')+'）';
        });
        txt.textContent=msgs.join(' · ')+' · 所有下单任务已暂停。重启任意模拟参与后恢复。';
        bar.style.display='block';
      }
    }catch(e){}
  }
  tick();
  setInterval(tick, 3000);
}
"""

ORDER_TAB_HTML = """
<!-- 石头岛 Tab -->
<div id="tab-order" class="tab-content">
  <div class="std-main">
    <div style="display:flex;gap:12px;align-items:flex-start;flex-wrap:wrap">
      <!-- ⭐ 真实下单待开奖大卡片（添加账号已搬到「我的账号」tab） -->
      <div class="card" style="flex:1;min-width:280px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">
          <div style="font-size:.9rem;font-weight:800;color:var(--text)">
            🎯 真实参与 · 待开奖
          </div>
          <div style="display:flex;gap:4px;align-items:center">
            <button id="rp-tab-210" class="btn btn-ghost btn-sm" style="font-size:.7rem;padding:3px 8px;background:var(--accent);color:#fff" onclick="setRealPendingGame(210)">欢乐210</button>
            <button id="rp-tab-60" class="btn btn-ghost btn-sm" style="font-size:.7rem;padding:3px 8px" onclick="setRealPendingGame(60)">比特60</button>
          </div>
        </div>
        <div id="real-pending-panel" style="display:flex;flex-direction:column;gap:8px;min-height:90px">
          <div style="color:var(--muted);font-size:.78rem;text-align:center;padding:14px">暂无下单记录</div>
        </div>
        <div style="margin-top:12px;padding-top:10px;border-top:1px dashed var(--border);font-size:.72rem;color:var(--muted);text-align:center">
          💡 账号管理 / 添加账号请到「👤 我的账号」tab
        </div>
      </div>
      <div style="flex:1;min-width:280px;display:flex;flex-direction:column;gap:12px">
        <!-- 游戏切换 -->
        <div style="display:flex;gap:0;border-radius:10px;overflow:hidden;border:1px solid var(--border)">
          <button id="game-btn-210" onclick="switchGame(210)" style="flex:1;padding:10px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.9rem">🎮 欢乐210（3分钟）</button>
          <button id="game-btn-60" onclick="switchGame(60)" style="flex:1;padding:10px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.9rem">⚡ 比特60（1分钟）</button>
        </div>

        <!-- 欢乐210 下单区 -->
        <div id="order-210" class="card">
          <!-- 开奖号码显示（功能3）-->
          <div id="lottery-bar-210" style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px;padding:8px 12px;background:#0c0e14;border:1px solid var(--border);border-radius:8px;min-height:36px">
            <div>
              <span style="font-size:.72rem;color:var(--muted)">最新开奖</span>
              <span id="lottery-qishu-210" style="font-size:.72rem;color:var(--muted);margin-left:4px"></span>
            </div>
            <div id="lottery-nums-210" style="font-size:1rem;font-weight:900;color:var(--text);letter-spacing:2px">--</div>
            <div id="lottery-cd-210" style="font-size:.82rem;font-weight:700;color:var(--yellow);min-width:70px;text-align:right">--</div>
          </div>
          <div class="card-title">🎯 欢乐210 · 快速下单</div>
          <div id="sel-accounts" style="display:none"></div>

          <!-- 号码按钮 0~27 -->
          <div class="form-group">
            <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:6px">
              <label style="margin:0">号码选择</label>
              <button class="btn btn-ghost btn-sm" onclick="clearNumBtns210()" style="font-size:.72rem;padding:2px 8px">清除选中</button>
            </div>
            <div id="num-btns-210" style="display:flex;flex-wrap:wrap;gap:5px;margin-bottom:6px">
            </div>
          </div>

          <!-- 单双大小中边 -->
          <div class="form-group">
            <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:6px">
              <label style="margin:0">组合类型（可多选）</label>
              <div style="display:flex;gap:6px">
                <button class="btn btn-ghost btn-sm" onclick="invertSelection210()" style="font-size:.72rem;padding:2px 8px;color:#fbbf24">🔄 反选</button>
                <button class="btn btn-ghost btn-sm" onclick="clearBetType210()" style="font-size:.72rem;padding:2px 8px">清除选中</button>
              </div>
            </div>
            <div class="multi-btns" id="bet-type-btns-210" style="flex-wrap:wrap;gap:4px">
              <button class="multi-btn" onclick="selectBetType210('大',this)">大</button>
              <button class="multi-btn" onclick="selectBetType210('小',this)">小</button>
              <button class="multi-btn" onclick="selectBetType210('单',this)">单</button>
              <button class="multi-btn" onclick="selectBetType210('双',this)">双</button>
              <button class="multi-btn" onclick="selectBetType210('中',this)">中</button>
              <button class="multi-btn" onclick="selectBetType210('边',this)">边</button>
              <button class="multi-btn" onclick="selectBetType210('小单',this)">小单</button>
              <button class="multi-btn" onclick="selectBetType210('大单',this)">大单</button>
              <button class="multi-btn" onclick="selectBetType210('小双',this)">小双</button>
              <button class="multi-btn" onclick="selectBetType210('大双',this)">大双</button>
              <button class="multi-btn" onclick="selectBetType210('小边',this)">小边</button>
              <button class="multi-btn" onclick="selectBetType210('大边',this)">大边</button>
              <button class="multi-btn" onclick="selectBetType210('3余0',this)">3余0</button>
              <button class="multi-btn" onclick="selectBetType210('3余1',this)">3余1</button>
              <button class="multi-btn" onclick="selectBetType210('3余2',this)">3余2</button>
              <button class="multi-btn" onclick="selectBetType210('4余0',this)">4余0</button>
              <button class="multi-btn" onclick="selectBetType210('4余1',this)">4余1</button>
              <button class="multi-btn" onclick="selectBetType210('4余2',this)">4余2</button>
              <button class="multi-btn" onclick="selectBetType210('4余3',this)">4余3</button>
              <button class="multi-btn" onclick="selectBetType210('5余0',this)">5余0</button>
              <button class="multi-btn" onclick="selectBetType210('5余1',this)">5余1</button>
              <button class="multi-btn" onclick="selectBetType210('5余2',this)">5余2</button>
              <button class="multi-btn" onclick="selectBetType210('5余3',this)">5余3</button>
              <button class="multi-btn" onclick="selectBetType210('5余4',this)">5余4</button>
            </div>
            <div id="bet-type-selected-210" style="font-size:.82rem;color:var(--muted);margin-top:6px">未选择</div>
          </div>

          <!-- 尾数输入框 -->
          <div class="form-group">
            <label>下注尾数（如 <b style="color:var(--yellow)">345</b>）</label>
            <input id="inp-tails" type="text" placeholder="例如：345 或 67890" maxlength="10" style="letter-spacing:4px;font-size:1.1rem;font-weight:700" oninput="updateOddsPreview()">
          </div>
          <div id="odds-preview" style="display:none;background:#12151e;border-radius:8px;padding:10px;margin-bottom:12px;font-size:.8rem">
            <div style="color:var(--muted);margin-bottom:6px">📊 赔率分配预览</div>
            <div id="odds-preview-content"></div>
            <div style="margin-top:10px;padding:8px 10px;background:#0c0e14;border-radius:6px;border:1px solid #f59e0033;display:flex;align-items:center;justify-content:space-between">
              <span style="color:var(--muted);font-size:.85rem">💰 命中预计盈利</span>
              <span id="odds-profit" style="color:var(--yellow);font-weight:900;font-size:1.15rem">--</span>
            </div>
            <div style="margin-top:6px;color:var(--muted)">预计总花费：<span id="odds-total" style="color:var(--yellow);font-weight:700">--</span></div>
          </div>

          <!-- 总金额 -->
          <div class="form-group">
            <label>总金额（最低 1000）</label>
            <div style="display:flex;gap:6px;align-items:center">
              <input id="inp-amount" type="number" placeholder="1000" value="1000" min="1000" step="1000" style="flex:1" oninput="clearMultiActive();updateOddsPreview()">
              <button class="btn btn-ghost btn-sm" onclick="clearAmount210()" style="white-space:nowrap">清零</button>
              <button class="btn btn-ghost btn-sm" onclick="avgAmount210()" style="white-space:nowrap">平均</button>
            </div>
            <div id="avg-hint-210" style="font-size:.78rem;color:var(--accent);margin-top:4px;min-height:16px"></div>
          </div>

          <!-- 倍数 -->
          <div class="form-group">
            <label>金币倍数</label>
            <div class="multi-btns" id="multi-btns-210" style="flex-wrap:wrap;gap:5px">
              <button class="multi-btn" onclick="applyMulti210(1.6,this)">1.6x</button>
              <button class="multi-btn" onclick="applyMulti210(1.8,this)">1.8x</button>
              <button class="multi-btn" onclick="applyMulti210(1.9,this)">1.9x</button>
              <button class="multi-btn" onclick="applyMulti210(2.0,this)">2.0x</button>
              <button class="multi-btn" onclick="applyMulti210(2.1,this)">2.1x</button>
              <button class="multi-btn" onclick="applyMulti210(2.2,this)">2.2x</button>
              <button class="multi-btn" onclick="applyMulti210(2.3,this)">2.3x</button>
              <button class="multi-btn" onclick="applyMulti210(2.4,this)">2.4x</button>
              <button class="multi-btn" onclick="applyMulti210(2.5,this)">2.5x</button>
              <button class="multi-btn" onclick="applyMulti210(2.6,this)">2.6x</button>
              <button class="multi-btn" onclick="applyMulti210(2.7,this)">2.7x</button>
              <button class="multi-btn" onclick="applyMulti210(3.0,this)">3.0x</button>
              <button class="multi-btn" onclick="applyMulti210(3.5,this)">3.5x</button>
              <button class="multi-btn" onclick="applyMulti210(4.0,this)">4.0x</button>
            </div>
            <div style="display:flex;align-items:center;gap:6px;margin-top:6px">
              <input id="custom-multi-210" type="number" placeholder="自定义倍数" step="0.1" min="1" style="width:120px;font-size:.85rem">
              <button class="btn btn-ghost btn-sm" onclick="applyCustomMulti210()">应用</button>
              <button class="btn btn-ghost btn-sm" onclick="clearMulti210()">清除</button>
            </div>
          </div>

          <div style="display:flex;gap:8px;margin-bottom:8px">
            <button class="btn" style="flex:1;background:#38bdf8;color:#fff" onclick="doOrder210()">🚀 立即参与</button>
            <button class="btn btn-ghost btn-sm" onclick="getExpect210()" style="white-space:nowrap">🔄 期数刷新</button>
          </div>
          <div style="font-size:.82rem;color:var(--muted)">当前期号：<span id="cur-expect-210" style="color:var(--yellow);font-weight:700;font-size:.95rem">--</span></div>
          <div class="order-result" id="order-result-210" style="display:none"></div>
        </div>

        <!-- 比特60 下单区 -->
        <div id="order-60" class="card" style="display:none">
          <div class="card-title">⚡ 比特60 · 快速下单</div>
          <!-- 开奖号码显示（功能3）-->
          <div id="lottery-bar-60" style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px;padding:8px 12px;background:#0c0e14;border:1px solid var(--border);border-radius:8px;min-height:36px">
            <div>
              <span style="font-size:.72rem;color:var(--muted)">最新开奖</span>
              <span id="lottery-qishu-60" style="font-size:.72rem;color:var(--muted);margin-left:4px"></span>
            </div>
            <div id="lottery-nums-60" style="font-size:1rem;font-weight:900;color:var(--text);letter-spacing:2px">--</div>
            <div id="lottery-cd-60" style="font-size:.82rem;font-weight:700;color:var(--yellow);min-width:70px;text-align:right">--</div>
          </div>

          <!-- 号码按钮 0~27 -->
          <div class="form-group">
            <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:6px">
              <label style="margin:0">号码选择</label>
              <button class="btn btn-ghost btn-sm" onclick="clearNumBtns60()" style="font-size:.72rem;padding:2px 8px">清除选中</button>
            </div>
            <div id="num-btns-60" style="display:flex;flex-wrap:wrap;gap:5px;margin-bottom:6px">
            </div>
          </div>

          <!-- 单双大小中边 -->
          <div class="form-group">
            <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:6px">
              <label style="margin:0">组合类型（可多选）</label>
              <div style="display:flex;gap:6px">
                <button class="btn btn-ghost btn-sm" onclick="invertSelection60()" style="font-size:.72rem;padding:2px 8px;color:#fbbf24">🔄 反选</button>
                <button class="btn btn-ghost btn-sm" onclick="clearBetType60()" style="font-size:.72rem;padding:2px 8px">清除选中</button>
              </div>
            </div>
            <div class="multi-btns" id="bet-type-btns" style="flex-wrap:wrap;gap:4px">
              <button class="multi-btn" onclick="selectBetType('大',this)">大</button>
              <button class="multi-btn" onclick="selectBetType('小',this)">小</button>
              <button class="multi-btn" onclick="selectBetType('单',this)">单</button>
              <button class="multi-btn" onclick="selectBetType('双',this)">双</button>
              <button class="multi-btn" onclick="selectBetType('中',this)">中</button>
              <button class="multi-btn" onclick="selectBetType('边',this)">边</button>
              <button class="multi-btn" onclick="selectBetType('小单',this)">小单</button>
              <button class="multi-btn" onclick="selectBetType('大单',this)">大单</button>
              <button class="multi-btn" onclick="selectBetType('小双',this)">小双</button>
              <button class="multi-btn" onclick="selectBetType('大双',this)">大双</button>
              <button class="multi-btn" onclick="selectBetType('小边',this)">小边</button>
              <button class="multi-btn" onclick="selectBetType('大边',this)">大边</button>
              <button class="multi-btn" onclick="selectBetType('3余0',this)">3余0</button>
              <button class="multi-btn" onclick="selectBetType('3余1',this)">3余1</button>
              <button class="multi-btn" onclick="selectBetType('3余2',this)">3余2</button>
              <button class="multi-btn" onclick="selectBetType('4余0',this)">4余0</button>
              <button class="multi-btn" onclick="selectBetType('4余1',this)">4余1</button>
              <button class="multi-btn" onclick="selectBetType('4余2',this)">4余2</button>
              <button class="multi-btn" onclick="selectBetType('4余3',this)">4余3</button>
              <button class="multi-btn" onclick="selectBetType('5余0',this)">5余0</button>
              <button class="multi-btn" onclick="selectBetType('5余1',this)">5余1</button>
              <button class="multi-btn" onclick="selectBetType('5余2',this)">5余2</button>
              <button class="multi-btn" onclick="selectBetType('5余3',this)">5余3</button>
              <button class="multi-btn" onclick="selectBetType('5余4',this)">5余4</button>
            </div>
            <div id="bet-type-selected" style="font-size:.82rem;color:var(--muted);margin-top:6px">未选择</div>
          </div>

          <!-- 尾数输入 -->
          <div class="form-group">
            <label>下注尾数（如 <b style="color:var(--yellow)">345</b>）</label>
            <input id="inp-tails-60" type="text" placeholder="例如：345 或 67890" maxlength="10" style="letter-spacing:4px;font-size:1.1rem;font-weight:700;margin-bottom:10px" oninput="update60Preview()">
          </div>
          <div id="bet60-preview" style="display:none;background:#12151e;border-radius:8px;padding:10px;margin-bottom:12px;font-size:.8rem">
            <div style="color:var(--muted);margin-bottom:4px">📊 下注位置预览</div>
            <div id="bet60-preview-content"></div>
            <div style="margin-top:10px;padding:8px 10px;background:#0c0e14;border-radius:6px;border:1px solid #f59e0033;display:flex;align-items:center;justify-content:space-between">
              <span style="color:var(--muted);font-size:.85rem">💰 命中预计盈利</span>
              <span id="bet60-profit" style="color:var(--yellow);font-weight:900;font-size:1.15rem">--</span>
            </div>
            <div style="margin-top:6px;color:var(--muted)">预计总花费：<span id="bet60-total" style="color:var(--yellow);font-weight:700">--</span></div>
          </div>

          <!-- 总金额 -->
          <div class="form-group">
            <label>总金额（最低 1000）</label>
            <div style="display:flex;gap:6px;align-items:center">
              <input id="inp-amount-60" type="number" placeholder="1000" value="1000" min="1000" step="1000" style="flex:1" oninput="update60Preview()">
              <button class="btn btn-ghost btn-sm" onclick="clearAmount60()" style="white-space:nowrap">清零</button>
              <button class="btn btn-ghost btn-sm" onclick="avgAmount60()" style="white-space:nowrap">平均</button>
            </div>
            <div id="avg-hint-60" style="font-size:.78rem;color:var(--accent);margin-top:4px;min-height:16px"></div>
          </div>

          <!-- 倍数 -->
          <div class="form-group">
            <label>金币倍数</label>
            <div class="multi-btns" id="multi-btns-60" style="flex-wrap:wrap;gap:5px">
              <button class="multi-btn" onclick="applyMulti60(1.6,this)">1.6x</button>
              <button class="multi-btn" onclick="applyMulti60(1.8,this)">1.8x</button>
              <button class="multi-btn" onclick="applyMulti60(1.9,this)">1.9x</button>
              <button class="multi-btn" onclick="applyMulti60(2.0,this)">2.0x</button>
              <button class="multi-btn" onclick="applyMulti60(2.1,this)">2.1x</button>
              <button class="multi-btn" onclick="applyMulti60(2.2,this)">2.2x</button>
              <button class="multi-btn" onclick="applyMulti60(2.3,this)">2.3x</button>
              <button class="multi-btn" onclick="applyMulti60(2.4,this)">2.4x</button>
              <button class="multi-btn" onclick="applyMulti60(2.5,this)">2.5x</button>
              <button class="multi-btn" onclick="applyMulti60(2.6,this)">2.6x</button>
              <button class="multi-btn" onclick="applyMulti60(2.7,this)">2.7x</button>
              <button class="multi-btn" onclick="applyMulti60(3.0,this)">3.0x</button>
              <button class="multi-btn" onclick="applyMulti60(3.5,this)">3.5x</button>
              <button class="multi-btn" onclick="applyMulti60(4.0,this)">4.0x</button>
            </div>
            <div style="display:flex;align-items:center;gap:6px;margin-top:6px">
              <input id="custom-multi-60" type="number" placeholder="自定义倍数" step="0.1" min="1" style="width:120px;font-size:.85rem">
              <button class="btn btn-ghost btn-sm" onclick="applyCustomMulti60()">应用</button>
              <button class="btn btn-ghost btn-sm" onclick="clearMulti60()">清除</button>
            </div>
          </div>

          <div style="display:flex;gap:8px;margin-bottom:8px">
            <button class="btn" style="flex:1;background:#f59e0b;color:#000" onclick="doOrder60()">🚀 立即参与</button>
            <button class="btn btn-ghost btn-sm" onclick="getExpect60()" style="white-space:nowrap">🔄 期数刷新</button>
          </div>
          <div style="font-size:.82rem;color:var(--muted)">当前期号：<span id="cur-expect-60" style="color:var(--yellow);font-weight:700;font-size:.95rem">--</span></div>
          <div class="order-result" id="order-result-60" style="display:none"></div>
        </div>

        <!-- 输赢结果 -->
        <div id="bet-result-panel" style="display:none;text-align:center;padding:24px 10px;background:#12151e;border-radius:12px;border:1px solid var(--border);position:relative">
          <div id="bet-result-game" style="font-size:.8rem;color:var(--muted);margin-bottom:6px"></div>
          <div id="bet-result-word" style="font-size:5.5rem;font-weight:900;letter-spacing:6px;line-height:1"></div>
          <div id="bet-result-period" style="font-size:.88rem;margin-top:14px;color:var(--muted)"></div>
          <div id="bet-result-num" style="font-size:1.9rem;font-weight:800;margin-top:6px"></div>
        </div>
      </div>
    </div>
  </div>
</div>
"""

DEV_TAB_HTML = """
<!-- 开发者 Tab -->
<div id="tab-accounts" class="tab-content">
  <div class="std-main">
    <div class="card">
      <div class="card-title">
        <span>👥 开发者 · 账号管理</span>
        <button class="btn btn-ghost btn-sm" onclick="refreshAllAccounts()">🔄 全部刷新</button>
      </div>
      <!-- 记录游戏切换 -->
      <div style="display:flex;gap:0;border-radius:8px;overflow:hidden;border:1px solid var(--border);margin-bottom:14px;width:fit-content">
        <button id="rec-btn-210" onclick="switchRecGame(210)" style="padding:7px 20px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.85rem">🎮 欢乐210</button>
        <button id="rec-btn-60" onclick="switchRecGame(60)" style="padding:7px 20px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">⚡ 比特60</button>
      </div>
      <div id="acc-grid" class="acc-grid"><div class="notif-empty">暂无账号</div></div>
    </div>
  </div>
</div>
"""

LOGIN_JS = """
async function loadCaptcha(){
  // 🪨 石头岛验证码：拉一次 /api/std/captcha 拿 src + uniqid
  var box=$('captcha-box');
  if(box) box.innerHTML='<span style="color:var(--muted);font-size:.75rem;padding:4px">加载中...</span>';
  try{
    const d=await fetch('/api/std/captcha').then(r=>r.json());
    if(d.ok && d.src){
      if(box) box.innerHTML='<img src="'+d.src+'" alt="验证码" onclick="loadCaptcha()" title="点击刷新">';
      var u=$('inp-uniqid'); if(u) u.value=d.uniqid||'';
      var cap=$('inp-captcha'); if(cap){ cap.value=''; cap.style.display=''; }
    }else{
      if(box) box.innerHTML='<span style="color:var(--red);font-size:.7rem;padding:4px">❌ 加载失败</span>';
    }
  }catch(e){
    if(box) box.innerHTML='<span style="color:var(--red);font-size:.7rem;padding:4px">❌ '+e.message+'</span>';
  }
}
async function doLogin(){
  const tel=$('inp-tel').value.trim();
  const pwd=$('inp-pwd').value.trim();
  const captcha=($('inp-captcha').value||'').trim();
  const uniqid=($('inp-uniqid').value||'').trim();
  const msg=$('login-msg');
  if(!tel||!pwd){msg.textContent='请填写手机号和密码';msg.style.color='var(--red)';return;}
  if(!captcha||!uniqid){msg.textContent='请先加载并输入验证码';msg.style.color='var(--red)';return;}
  msg.textContent='登录中...';msg.style.color='var(--muted)';
  try{
    const d=await fetch('/api/std/login',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({tel:tel, password:pwd, captcha:captcha, uniqid:uniqid})}).then(r=>r.json());
    if(d.ok){
      msg.textContent='✅ 登录成功！余额 '+(d.balance||0).toLocaleString();
      msg.style.color='var(--green)';
      $('inp-pwd').value=''; $('inp-captcha').value=''; $('inp-uniqid').value='';
      setTimeout(()=>{msg.textContent='';},3000);
      refreshAccounts();
    }else{
      msg.textContent='❌ '+(d.msg||'登录失败');msg.style.color='var(--red)';
      loadCaptcha();  // 登录失败重新拉验证码
    }
  }catch(e){msg.textContent='❌ 网络错误:'+e.message;msg.style.color='var(--red)';}
}
"""

ADMIN_LOGIN_JS = """
""" + LOGIN_JS.replace("/api/sim/", "/api/admin/sim/").replace("/api/miss/", "/api/admin/miss/").replace("/api/status", "/api/admin/status").replace("/api/history", "/api/admin/history")

# 客户端额外JS：退出、账号管理
CLIENT_EXTRA_JS = """
"""

# ══════════════════════════════════════════════════════════════
#  🎯 真实下单 tab（独立页，左欢乐210 / 右比特60，每边 30 条）
# ══════════════════════════════════════════════════════════════
REALORDER_TAB_HTML = """
<div id="tab-realorder" class="tab-content">
  <div class="std-main" style="max-width:1600px">
    <!-- 顶部工具栏 -->
    <div class="card" style="margin-bottom:12px">
      <div style="display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap">
        <div style="display:flex;align-items:center;gap:14px">
          <div style="font-size:1.05rem;font-weight:800;color:var(--text)">📋 参与记录 · 实时跟踪</div>
          <div style="font-size:.78rem;color:var(--muted)">每秒自动刷新</div>
        </div>
      </div>
      <div id="ro-meta" style="margin-top:8px;display:flex;gap:14px;flex-wrap:wrap;font-size:.78rem;color:var(--muted)">
        <span>最后更新：<b id="ro-update-time" style="color:var(--text)">--</b></span>
        <span>欢乐210 总投入：<b id="ro-210-stake" style="color:var(--text)">--</b> · 总返奖：<b id="ro-210-win" style="color:var(--green)">--</b> · 盈亏：<b id="ro-210-pnl" style="color:var(--text)">--</b></span>
        <span>比特60 总投入：<b id="ro-60-stake" style="color:var(--text)">--</b> · 总返奖：<b id="ro-60-win" style="color:var(--green)">--</b> · 盈亏：<b id="ro-60-pnl" style="color:var(--text)">--</b></span>
      </div>
    </div>

    <!-- 左右并排（模式 A）-->
    <div id="ro-grid" style="display:grid;grid-template-columns:1fr 1fr;gap:14px">
      <!-- 欢乐210 -->
      <div class="card" style="padding:14px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px;border-bottom:2px solid #3b82f6;padding-bottom:8px">
          <div style="font-size:1rem;font-weight:800;color:#60a5fa">🎮 欢乐210（3分30秒）</div>
          <div style="display:flex;align-items:center;gap:8px">
            <div style="font-size:.78rem;color:var(--muted)">最近 <b id="ro-210-count" style="color:var(--text)">0</b> 条</div>
            <button class="btn btn-red btn-sm" data-style="210" onclick="roClearAll(this)" style="padding:3px 10px;font-size:.72rem">🗑 删除全部</button>
          </div>
        </div>
        <div id="ro-list-210" style="display:flex;flex-direction:column;gap:8px;max-height:78vh;overflow-y:auto;padding-right:4px">
          <div style="color:var(--muted);font-size:.82rem;text-align:center;padding:30px">暂无下单记录</div>
        </div>
      </div>
      <!-- 比特60 -->
      <div class="card" style="padding:14px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:10px;border-bottom:2px solid #f59e0b;padding-bottom:8px">
          <div style="font-size:1rem;font-weight:800;color:#fbbf24">⚡ 比特60（1分钟）</div>
          <div style="display:flex;align-items:center;gap:8px">
            <div style="font-size:.78rem;color:var(--muted)">最近 <b id="ro-60-count" style="color:var(--text)">0</b> 条</div>
            <button class="btn btn-red btn-sm" data-style="60" onclick="roClearAll(this)" style="padding:3px 10px;font-size:.72rem">🗑 删除全部</button>
          </div>
        </div>
        <div id="ro-list-60" style="display:flex;flex-direction:column;gap:8px;max-height:78vh;overflow-y:auto;padding-right:4px">
          <div style="color:var(--muted);font-size:.82rem;text-align:center;padding:30px">暂无下单记录</div>
        </div>
      </div>
    </div>
  </div>

  <style>
  /* 手机端：上下排（不让两个游戏挤在一起）*/
  @media(max-width:900px){
    #ro-grid{grid-template-columns:1fr !important}
    #ro-list-210,#ro-list-60{max-height:60vh !important}
  }
  /* 卡片脉冲（待开奖状态）*/
  @keyframes ropulse{0%{box-shadow:0 0 0 0 rgba(59,130,246,.5)}70%{box-shadow:0 0 0 8px rgba(59,130,246,0)}100%{box-shadow:0 0 0 0 rgba(59,130,246,0)}}
  .ro-card-pending{animation:ropulse 2s infinite}
  /* 自定义滚动条 */
  #ro-list-210::-webkit-scrollbar,#ro-list-60::-webkit-scrollbar{width:6px}
  #ro-list-210::-webkit-scrollbar-thumb,#ro-list-60::-webkit-scrollbar-thumb{background:#374151;border-radius:3px}
  </style>
</div>
"""

# SIM_TAB_HTML / SIM2_TAB_HTML 已删除（管理端已只剩客户账号管理，不再需要模拟参与 tab）

MISS_TAB_HTML = """
<div id="tab-miss" class="tab-content">
  <div class="std-main" style="max-width:1400px">
    <div style="display:flex;gap:12px;flex-wrap:wrap;margin-bottom:12px">
      <div class="card" style="flex:1;min-width:160px;text-align:center">
        <div style="font-size:.75rem;color:var(--muted);margin-bottom:2px">🎮 欢乐210 · 遗漏盈亏</div>
        <div id="miss-pnl-210" style="font-size:2rem;font-weight:900;color:var(--yellow)">--</div>
        <div id="miss-pnl-date" style="font-size:.72rem;color:var(--muted);margin-top:2px">-- · 每天24点清空</div>
      </div>
      <div class="card" style="flex:1;min-width:160px;text-align:center">
        <div style="font-size:.75rem;color:var(--muted);margin-bottom:2px">⚡ 比特60 · 遗漏盈亏</div>
        <div id="miss-pnl-60" style="font-size:2rem;font-weight:900;color:var(--yellow)">--</div>
      </div>
    </div>
    <div style="display:flex;gap:12px;flex-wrap:wrap;align-items:flex-start">
      <div class="card" style="flex:1;min-width:280px">
        <div class="card-title">🎮 欢乐210 遗漏配置</div>
        <div class="form-group">
          <label>遗漏数字组（每行一组，0~27用-分隔）</label>
          <textarea id="miss-groups-210" rows="6" style="width:100%;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);padding:8px;font-size:.78rem;font-family:monospace;resize:vertical" placeholder="0-1-2-3-4-10-11-12-13-14&#10;..."></textarea>
        </div>
        <div class="form-group" style="display:flex;gap:8px">
          <div style="flex:1"><label>查前N期</label><input id="miss-n-210" type="number" value="5" min="1" max="50" style="width:100%"></div>
          <div style="flex:2"><label>基础金额</label><input id="miss-base-210" type="number" value="10000" min="100" step="100" style="width:100%"></div>
        </div>
        <div class="form-group">
          <label>倍数序列（首次遗漏固定1倍）</label>
          <input id="miss-muls-210" type="text" value="1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625">
        </div>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          <button class="btn btn-primary" data-style="210" onclick="missConfigure(this)" style="flex:1">💾 保存</button>
          <button class="btn btn-green" data-style="210" onclick="missExecute(this)" style="flex:1">⚡ 执行检测</button>
          <button class="btn btn-red" data-style="210" onclick="missReset(this)" style="flex:1">🗑 删除记录</button>
        </div>
        <div id="miss-msg-210" style="font-size:.82rem;margin-top:8px;min-height:18px;text-align:center"></div>
        <!-- ⭐ 真实参与开关（遗漏检测命中时直接下单）-->
        <div id="miss-real-wrap-210" style="display:flex;align-items:center;justify-content:space-between;margin-top:10px;padding:8px 10px;background:#12151e;border:1.5px solid #374151;border-radius:8px;transition:all .3s">
          <span id="miss-real-lbl-210" style="font-size:.82rem;font-weight:900;color:var(--muted)">⚫ 真实参与 已关闭</span>
          <div onclick="missToggleReal(210)" id="miss-real-btn-210" style="position:relative;width:48px;height:26px;background:#374151;border-radius:13px;cursor:pointer;transition:background .25s">
            <div id="miss-real-knob-210" style="position:absolute;top:3px;left:3px;width:20px;height:20px;background:#fff;border-radius:50%;transition:left .25s"></div>
          </div>
        </div>
        <div style="margin-top:10px;border-top:1px solid var(--border);padding-top:8px;font-size:.78rem;color:var(--muted)">
          自动检测：<button id="miss-auto-btn-210" data-style="210" data-on="0" onclick="missToggleAuto(this)" style="background:#1e2235;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:2px 10px;cursor:pointer;font-size:.75rem">关</button>
        </div>
      </div>
      <div class="card" style="flex:1;min-width:280px">
        <div class="card-title">⚡ 比特60 遗漏配置</div>
        <div class="form-group">
          <label>遗漏数字组（每行一组，0~27用-分隔）</label>
          <textarea id="miss-groups-60" rows="6" style="width:100%;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);padding:8px;font-size:.78rem;font-family:monospace;resize:vertical" placeholder="0-1-2-3-4-10-11-12-13-14&#10;..."></textarea>
        </div>
        <div class="form-group" style="display:flex;gap:8px">
          <div style="flex:1"><label>查前N期</label><input id="miss-n-60" type="number" value="5" min="1" max="50" style="width:100%"></div>
          <div style="flex:2"><label>基础金额</label><input id="miss-base-60" type="number" value="10000" min="100" step="100" style="width:100%"></div>
        </div>
        <div class="form-group">
          <label>倍数序列（首次遗漏固定1倍）</label>
          <input id="miss-muls-60" type="text" value="1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625">
        </div>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          <button class="btn btn-primary" data-style="60" onclick="missConfigure(this)" style="flex:1">💾 保存</button>
          <button class="btn btn-green" data-style="60" onclick="missExecute(this)" style="flex:1">⚡ 执行检测</button>
          <button class="btn btn-red" data-style="60" onclick="missReset(this)" style="flex:1">🗑 删除记录</button>
        </div>
        <div id="miss-msg-60" style="font-size:.82rem;margin-top:8px;min-height:18px;text-align:center"></div>
        <!-- ⭐ 真实参与开关（遗漏检测命中时直接下单）-->
        <div id="miss-real-wrap-60" style="display:flex;align-items:center;justify-content:space-between;margin-top:10px;padding:8px 10px;background:#12151e;border:1.5px solid #374151;border-radius:8px;transition:all .3s">
          <span id="miss-real-lbl-60" style="font-size:.82rem;font-weight:900;color:var(--muted)">⚫ 真实参与 已关闭</span>
          <div onclick="missToggleReal(60)" id="miss-real-btn-60" style="position:relative;width:48px;height:26px;background:#374151;border-radius:13px;cursor:pointer;transition:background .25s">
            <div id="miss-real-knob-60" style="position:absolute;top:3px;left:3px;width:20px;height:20px;background:#fff;border-radius:50%;transition:left .25s"></div>
          </div>
        </div>
        <div style="margin-top:10px;border-top:1px solid var(--border);padding-top:8px;font-size:.78rem;color:var(--muted)">
          自动检测：<button id="miss-auto-btn-60" data-style="60" data-on="0" onclick="missToggleAuto(this)" style="background:#1e2235;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:2px 10px;cursor:pointer;font-size:.75rem">关</button>
        </div>
      </div>
      <div style="flex:2;min-width:300px;display:flex;flex-direction:column;gap:12px">
        <div class="card">
          <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">
            <span style="font-weight:700;color:var(--muted)">🎮 欢乐210 · 遗漏记录</span>
            <div style="display:flex;gap:6px;align-items:center">
              <span id="miss-log-pnl-210" style="font-size:.85rem;font-weight:800;color:var(--yellow)">--</span>
              <button onclick="missPage(210,-1)" style="background:transparent;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:2px 8px;cursor:pointer;font-size:.78rem">◀</button>
              <span id="miss-page-label-210" style="font-size:.78rem;color:var(--muted)">第1页</span>
              <button onclick="missPage(210,1)" style="background:transparent;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:2px 8px;cursor:pointer;font-size:.78rem">▶</button>
            </div>
          </div>
          <div id="miss-log-210"><div class="notif-empty">暂无记录</div></div>
        </div>
        <div class="card">
          <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">
            <span style="font-weight:700;color:var(--muted)">⚡ 比特60 · 遗漏记录</span>
            <div style="display:flex;gap:6px;align-items:center">
              <span id="miss-log-pnl-60" style="font-size:.85rem;font-weight:800;color:var(--yellow)">--</span>
              <button onclick="missPage(60,-1)" style="background:transparent;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:2px 8px;cursor:pointer;font-size:.78rem">◀</button>
              <span id="miss-page-label-60" style="font-size:.78rem;color:var(--muted)">第1页</span>
              <button onclick="missPage(60,1)" style="background:transparent;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:2px 8px;cursor:pointer;font-size:.78rem">▶</button>
            </div>
          </div>
          <div id="miss-log-60"><div class="notif-empty">暂无记录</div></div>
        </div>
      </div>
    </div>
  </div>
</div>
"""

DAWEI_TAB_HTML = """
<div id="tab-dawei" class="tab-content">
  <div class="std-main" style="max-width:1400px">
    <!-- 顶部：盈亏 + slot 切换 -->
    <div style="display:flex;gap:12px;flex-wrap:wrap;margin-bottom:12px">
      <div class="card" style="flex:1;min-width:160px;text-align:center">
        <div style="font-size:.75rem;color:var(--muted);margin-bottom:2px">🎮 欢乐210 · 打尾盈亏</div>
        <div id="dawei-pnl-210" style="font-size:2rem;font-weight:900;color:var(--yellow)">--</div>
        <div id="dawei-pnl-date" style="font-size:.72rem;color:var(--muted);margin-top:2px">-- · 近3天滚动</div>
      </div>
      <div class="card" style="flex:1;min-width:160px;text-align:center">
        <div style="font-size:.75rem;color:var(--muted);margin-bottom:2px">⚡ 比特60 · 打尾盈亏</div>
        <div id="dawei-pnl-60" style="font-size:2rem;font-weight:900;color:var(--yellow)">--</div>
      </div>
    </div>
    <!-- slot 切换 -->
    <div style="display:flex;gap:6px;margin-bottom:12px;align-items:center;flex-wrap:wrap">
      <span style="font-size:.78rem;color:var(--muted);margin-right:6px">实例：</span>
      <button id="dawei-slot-btn-1" onclick="daweiSelectSlot(1)" class="slot-btn">1</button>
      <button id="dawei-slot-btn-2" onclick="daweiSelectSlot(2)" class="slot-btn">2</button>
      <button id="dawei-slot-btn-3" onclick="daweiSelectSlot(3)" class="slot-btn">3</button>
      <button id="dawei-slot-btn-4" onclick="daweiSelectSlot(4)" class="slot-btn">4</button>
      <span style="font-size:.72rem;color:var(--muted);margin-left:auto">💡 每期重算尾数；<b>每次不中倍率即 ++</b>（爆档归零，中了归零）；累计连续 K 次不中（K=不中暂停期数）触发<b>暂停 K 期</b>，暂停只冷却节奏，不再额外倍投</span>
    </div>
    <style>
      .slot-btn{background:#1e2235;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:4px 14px;cursor:pointer;font-weight:800;font-size:.85rem;transition:all .2s}
      .slot-btn.active{background:var(--accent);color:#fff;border-color:var(--accent)}
    </style>
    <!-- 配置 + 记录 -->
    <div style="display:flex;gap:12px;flex-wrap:wrap;align-items:flex-start">
      <!-- 210 配置 -->
      <div class="card" style="flex:1;min-width:300px">
        <div class="card-title">🎮 欢乐210 打尾配置</div>
        <div class="form-group" style="display:flex;gap:8px">
          <div style="flex:1"><label>取尾数个数</label><input id="dawei-tail-210" type="number" value="5" min="1" max="10" style="width:100%"></div>
          <div style="flex:1"><label>检测前 N 期</label><input id="dawei-detn-210" type="number" value="30" min="1" max="200" style="width:100%"></div>
        </div>
        <div class="form-group" style="display:flex;gap:8px">
          <div style="flex:2"><label>基础金额</label><input id="dawei-base-210" type="number" value="1000" min="100" step="100" style="width:100%"></div>
          <div style="flex:1"><label>连K不中暂停K期</label><input id="dawei-pause-210" type="number" value="0" min="0" max="50" style="width:100%"></div>
        </div>
        <div class="form-group">
          <label>倍率序列（不中走下个；中了归零；- 分隔）</label>
          <input id="dawei-muls-210" type="text" value="1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625">
        </div>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          <button class="btn btn-primary" data-style="210" onclick="daweiConfigure(this)" style="flex:1">💾 保存</button>
          <button class="btn btn-green" data-style="210" data-on="0" onclick="daweiStart(this)" style="flex:1">▶ 启动</button>
          <button class="btn btn-red" data-style="210" onclick="daweiReset(this)" style="flex:1">🗑 删除记录</button>
        </div>
        <div id="dawei-msg-210" style="font-size:.82rem;margin-top:8px;min-height:18px;text-align:center"></div>
        <div id="dawei-status-210" style="font-size:.78rem;color:var(--muted);margin-top:6px;min-height:18px;text-align:center"></div>
        <!-- 真实参与开关 -->
        <div id="dawei-real-wrap-210" style="display:flex;align-items:center;justify-content:space-between;margin-top:10px;padding:8px 10px;background:#12151e;border:1.5px solid #374151;border-radius:8px;transition:all .3s">
          <span id="dawei-real-lbl-210" style="font-size:.82rem;font-weight:900;color:var(--muted)">⚫ 真实参与 已关闭</span>
          <div onclick="daweiToggleReal(210)" id="dawei-real-btn-210" style="position:relative;width:48px;height:26px;background:#374151;border-radius:13px;cursor:pointer;transition:background .25s">
            <div id="dawei-real-knob-210" style="position:absolute;top:3px;left:3px;width:20px;height:20px;background:#fff;border-radius:50%;transition:left .25s"></div>
          </div>
        </div>
      </div>
      <!-- 60 配置 -->
      <div class="card" style="flex:1;min-width:300px">
        <div class="card-title">⚡ 比特60 打尾配置</div>
        <div class="form-group" style="display:flex;gap:8px">
          <div style="flex:1"><label>取尾数个数</label><input id="dawei-tail-60" type="number" value="5" min="1" max="10" style="width:100%"></div>
          <div style="flex:1"><label>检测前 N 期</label><input id="dawei-detn-60" type="number" value="30" min="1" max="200" style="width:100%"></div>
        </div>
        <div class="form-group" style="display:flex;gap:8px">
          <div style="flex:2"><label>基础金额</label><input id="dawei-base-60" type="number" value="1000" min="100" step="100" style="width:100%"></div>
          <div style="flex:1"><label>不中暂停期数</label><input id="dawei-pause-60" type="number" value="0" min="0" max="50" style="width:100%"></div>
        </div>
        <div class="form-group">
          <label>倍率序列（- 分隔）</label>
          <input id="dawei-muls-60" type="text" value="1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625">
        </div>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          <button class="btn btn-primary" data-style="60" onclick="daweiConfigure(this)" style="flex:1">💾 保存</button>
          <button class="btn btn-green" data-style="60" data-on="0" onclick="daweiStart(this)" style="flex:1">▶ 启动</button>
          <button class="btn btn-red" data-style="60" onclick="daweiReset(this)" style="flex:1">🗑 删除记录</button>
        </div>
        <div id="dawei-msg-60" style="font-size:.82rem;margin-top:8px;min-height:18px;text-align:center"></div>
        <div id="dawei-status-60" style="font-size:.78rem;color:var(--muted);margin-top:6px;min-height:18px;text-align:center"></div>
        <div id="dawei-real-wrap-60" style="display:flex;align-items:center;justify-content:space-between;margin-top:10px;padding:8px 10px;background:#12151e;border:1.5px solid #374151;border-radius:8px;transition:all .3s">
          <span id="dawei-real-lbl-60" style="font-size:.82rem;font-weight:900;color:var(--muted)">⚫ 真实参与 已关闭</span>
          <div onclick="daweiToggleReal(60)" id="dawei-real-btn-60" style="position:relative;width:48px;height:26px;background:#374151;border-radius:13px;cursor:pointer;transition:background .25s">
            <div id="dawei-real-knob-60" style="position:absolute;top:3px;left:3px;width:20px;height:20px;background:#fff;border-radius:50%;transition:left .25s"></div>
          </div>
        </div>
      </div>
      <!-- 记录 -->
      <div style="flex:2;min-width:300px;display:flex;flex-direction:column;gap:12px">
        <div class="card">
          <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">
            <span style="font-weight:700;color:var(--muted)">🎮 欢乐210 · 打尾记录</span>
            <span id="dawei-log-pnl-210" style="font-size:.85rem;font-weight:800;color:var(--yellow)">--</span>
          </div>
          <div id="dawei-log-210"><div class="notif-empty">暂无记录</div></div>
        </div>
        <div class="card">
          <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">
            <span style="font-weight:700;color:var(--muted)">⚡ 比特60 · 打尾记录</span>
            <span id="dawei-log-pnl-60" style="font-size:.85rem;font-weight:800;color:var(--yellow)">--</span>
          </div>
          <div id="dawei-log-60"><div class="notif-empty">暂无记录</div></div>
        </div>
      </div>
    </div>
  </div>
</div>
"""

DAWEI_JS = """
// ══ 🎯 打尾玩法（4 slot × 2 style 独立）══
var daweiCurrentSlot = 1;
var _daweiTimer = null;

function daweiSelectSlot(n){
  daweiCurrentSlot = Math.max(1, Math.min(4, parseInt(n)||1));
  for(var i=1;i<=4;i++){
    var b=document.getElementById('dawei-slot-btn-'+i);
    if(b)b.classList.toggle('active', i===daweiCurrentSlot);
  }
  daweiRefresh();
}

async function daweiConfigure(btn){
  var style = parseInt(btn.dataset.style);
  var tail  = parseInt(document.getElementById('dawei-tail-'+style).value)||5;
  var detn  = parseInt(document.getElementById('dawei-detn-'+style).value)||30;
  var base  = parseInt(document.getElementById('dawei-base-'+style).value)||1000;
  var pause = parseInt(document.getElementById('dawei-pause-'+style).value)||0;
  var muls  = (document.getElementById('dawei-muls-'+style).value||'1').trim();
  var msg   = document.getElementById('dawei-msg-'+style);
  try{
    var d = await fetch('/api/dawei/configure',{
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({
        slot: daweiCurrentSlot, style: style,
        tail_count: tail, detect_n: detn,
        base_amount: base, muls_text: muls, pause_periods: pause
      })
    }).then(r=>r.json());
    msg.textContent = d.msg||(d.ok?'已保存':'保存失败');
    msg.style.color = d.ok ? 'var(--accent)' : 'var(--red)';
  }catch(e){ msg.textContent='网络错误'; msg.style.color='var(--red)'; }
}

async function daweiStart(btn){
  var style = parseInt(btn.dataset.style);
  var on = (btn.dataset.on||'0') !== '1';
  var msg = document.getElementById('dawei-msg-'+style);
  try{
    var d = await fetch('/api/dawei/start',{
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({slot: daweiCurrentSlot, style: style, on: on})
    }).then(r=>r.json());
    if(d.ok){
      btn.dataset.on = on ? '1' : '0';
      btn.textContent = on ? '⏸ 停止' : '▶ 启动';
      btn.className = on ? 'btn btn-red' : 'btn btn-green';
      msg.textContent = on ? '已启动，等下一期开奖自动下尾数' : '已停止';
      msg.style.color = on ? 'var(--accent)' : 'var(--muted)';
      daweiRefresh();
    } else {
      msg.textContent = d.msg || '操作失败';
      msg.style.color = 'var(--red)';
    }
  }catch(e){ msg.textContent='网络错误'; msg.style.color='var(--red)'; }
}

async function daweiReset(btn){
  var style = parseInt(btn.dataset.style);
  if(!confirm('确认清空 slot'+daweiCurrentSlot+' / '+style+' 的打尾记录？')) return;
  try{
    var d = await fetch('/api/dawei/reset',{
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({slot: daweiCurrentSlot, style: style})
    }).then(r=>r.json());
    var msg = document.getElementById('dawei-msg-'+style);
    msg.textContent = d.msg||(d.ok?'已重置':'失败');
    msg.style.color = d.ok ? 'var(--accent)' : 'var(--red)';
    daweiRefresh();
  }catch(e){}
}

async function daweiToggleReal(style){
  var lbl = document.getElementById('dawei-real-lbl-'+style);
  var btn = document.getElementById('dawei-real-btn-'+style);
  var on  = !btn.dataset.on || btn.dataset.on !== '1';
  try{
    var d = await fetch('/api/dawei/real/toggle',{
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({slot: daweiCurrentSlot, style: style, on: on})
    }).then(r=>r.json());
    if(d.ok){
      _daweiPaintReal(style, on);
    }
  }catch(e){}
}

function _daweiPaintReal(style, on){
  var lbl  = document.getElementById('dawei-real-lbl-'+style);
  var wrap = document.getElementById('dawei-real-wrap-'+style);
  var btn  = document.getElementById('dawei-real-btn-'+style);
  var knob = document.getElementById('dawei-real-knob-'+style);
  if(!lbl||!btn) return;
  btn.dataset.on = on ? '1' : '0';
  if(on){
    lbl.innerHTML  = '🔴 真实参与 <b style="color:#22c55e">已开启</b>';
    lbl.style.color= 'var(--text)';
    wrap.style.borderColor = '#22c55e';
    wrap.style.background  = '#0f1f12';
    btn.style.background   = '#22c55e';
    knob.style.left='25px';
  } else {
    lbl.textContent = '⚫ 真实参与 已关闭';
    lbl.style.color = 'var(--muted)';
    wrap.style.borderColor = '#374151';
    wrap.style.background  = '#12151e';
    btn.style.background   = '#374151';
    knob.style.left = '3px';
  }
}

function _daweiRenderRecords(style, recs){
  var box = document.getElementById('dawei-log-'+style);
  if(!box) return;
  if(!recs || !recs.length){ box.innerHTML='<div class="notif-empty">暂无记录</div>'; return; }
  var html = '';
  recs.forEach(function(r){
    var when = (r.created_at||'').slice(11,19);
    var tailTxt = (r.tails && r.tails.length) ? r.tails.join(',') : '--';
    var posCount = (r.positions || []).length;
    var status, color;
    if(r.skipped){
      status = r.label || '⏸ 暂停';
      color = '#94a3b8';
    } else if(r.pending){
      status = '⏳ 待开奖';
      color = '#fbbf24';
    } else if(r.won){
      status = '✅ 中 +'+r.net_pnl;
      color = '#22c55e';
    } else {
      status = '❌ 不中 '+r.net_pnl;
      color = '#ef4444';
    }
    html += '<div style="display:flex;justify-content:space-between;align-items:center;'
         + 'padding:6px 8px;background:#12151e;border-radius:6px;margin-bottom:4px;font-size:.78rem">'
         + '<div><span style="color:var(--muted)">'+when+'</span> · '
         + '<b>'+(r.qishu||'--')+'</b> · '+(r.label||'打尾')+'</div>'
         + '<div style="font-size:.72rem;color:var(--muted)">尾['+tailTxt+']·'+posCount+'位 x'+(r.multiplier||0)
         + ' ¥'+(r.bet_amount||0)+'</div>'
         + '<div style="color:'+color+';font-weight:800">'+status+'</div>'
         + '</div>';
  });
  box.innerHTML = html;
}

function _daweiRenderStyleStatus(style, snap){
  var st = document.getElementById('dawei-status-'+style);
  if(!st) return;
  var muls = snap.multipliers || [1];
  var midx = snap.mul_idx || 0;
  var pr   = snap.pause_remaining || 0;
  var cl   = snap.consecutive_losses || 0;
  var runTxt = snap.running ? '<b style="color:#22c55e">▶ 运行中</b>' : '<span style="color:var(--muted)">⏹ 已停止</span>';
  var pauseTxt = (pr>0) ? ' · <b style="color:#fbbf24">⏸ 暂停剩 '+pr+' 期</b>' : '';
  var pp = snap.pause_periods || 0;
  var clTxt = '';
  if(cl>0 && pp>0){
    clTxt = ' · <span style="color:#f87171">连不中 '+cl+'/'+pp+'</span>';
  } else if(cl>0){
    clTxt = ' · <span style="color:#f87171">连不中 '+cl+'</span>';
  }
  st.innerHTML = runTxt + ' · 倍率第 '+(midx+1)+'/'+muls.length+' 位 ('+muls[Math.min(midx,muls.length-1)]+'x)' + clTxt + pauseTxt;
}

function _daweiFillForm(style, snap){
  var setIf = function(id, val){
    var el = document.getElementById(id);
    if(el && document.activeElement !== el) el.value = val;
  };
  setIf('dawei-tail-'+style, snap.tail_count);
  setIf('dawei-detn-'+style, snap.detect_n);
  setIf('dawei-base-'+style, snap.base_amount);
  setIf('dawei-pause-'+style, snap.pause_periods);
  var muls = (snap.multipliers || [1]).join('-');
  setIf('dawei-muls-'+style, muls);
}

async function daweiRefresh(){
  try{
    var d = await fetch('/api/dawei/status?slot='+daweiCurrentSlot).then(r=>r.json());
    if(!d.ok) return;
    var data = d.data || {};
    for(var i=1;i<=4;i++){
      var b=document.getElementById('dawei-slot-btn-'+i);
      if(b)b.classList.toggle('active', i===daweiCurrentSlot);
    }
    [210, 60].forEach(function(style){
      var snap = data[String(style)] || {};
      _daweiFillForm(style, snap);
      _daweiRenderStyleStatus(style, snap);
      _daweiRenderRecords(style, snap.records || []);
      _daweiPaintReal(style, !!snap.real_enabled);
      var pnlEl = document.getElementById('dawei-pnl-'+style);
      if(pnlEl){
        var v = snap.total_pnl || 0;
        pnlEl.textContent = v;
        pnlEl.style.color = v>=0 ? 'var(--yellow)' : '#ef4444';
      }
      var lpnl = document.getElementById('dawei-log-pnl-'+style);
      if(lpnl){
        var v = snap.total_pnl || 0;
        lpnl.textContent = (v>=0?'+':'')+v;
        lpnl.style.color = v>=0 ? '#22c55e' : '#ef4444';
      }
      // start 按钮态
      var startBtn = document.querySelector('#tab-dawei button[data-style="'+style+'"][onclick="daweiStart(this)"]');
      if(startBtn){
        startBtn.dataset.on = snap.running ? '1' : '0';
        startBtn.textContent = snap.running ? '⏸ 停止' : '▶ 启动';
        startBtn.className = snap.running ? 'btn btn-red' : 'btn btn-green';
      }
    });
    var pdate = document.getElementById('dawei-pnl-date');
    if(pdate){
      var dt = data['210'] && data['210'].pnl_date || '';
      pdate.textContent = (dt||'--')+' · 近3天滚动';
    }
  }catch(e){ console.warn('[dawei refresh]', e); }
}

function daweiStartAutoRefresh(){
  if(_daweiTimer) clearInterval(_daweiTimer);
  _daweiTimer = setInterval(function(){
    var tab = document.getElementById('tab-dawei');
    if(tab && tab.classList.contains('active')) daweiRefresh();
  }, 3000);
}
// 进入 tab 时由 switchTab 调 daweiRefresh + 启动定时
"""

PLAN_TAB_HTML = """
<div id="tab-plan" class="tab-content">
  <div class="std-main" style="max-width:1400px">
    <div style="display:flex;gap:12px;flex-wrap:wrap;margin-bottom:12px">
      <div class="card" style="flex:1;min-width:180px;text-align:center">
        <div style="font-size:.75rem;color:var(--muted);margin-bottom:2px">🎮 欢乐210 · 计划跟投盈亏</div>
        <div id="plan-pnl" style="font-size:2rem;font-weight:900;color:var(--yellow)">--</div>
        <div id="plan-pnl-date" style="font-size:.72rem;color:var(--muted);margin-top:2px">-- · 每天24点清空</div>
      </div>
    </div>
    <div style="font-size:.72rem;color:var(--muted);margin-bottom:10px">
      💡 读 wanjia28 的 8 个「杀5余」预测专家，取连对≥阈值里连对最高的，<b>必须凑到两个不一样的预测</b>才下（都一样则空仓）。杀5余N=杀尾 N 和 N+5；两个不同计划<b>合并杀尾</b>（如 5余1+5余2 → 杀尾 1/6/2/7）下剩余号；再<b>剔除冷号</b>（8-19 遗漏≥20，来自 28vp）。仅欢乐210。
    </div>
    <div style="display:flex;gap:12px;flex-wrap:wrap;align-items:flex-start">
      <!-- 配置 -->
      <div class="card" style="flex:1;min-width:280px">
        <div class="card-title">📋 计划跟投配置</div>
        <div class="form-group" style="display:flex;gap:8px">
          <div style="flex:2"><label>基础金额</label><input id="plan-base" type="number" value="1000" min="100" step="100" style="width:100%"></div>
          <div style="flex:1"><label>连对阈值</label><input id="plan-minlz" type="number" value="4" min="1" max="20" style="width:100%"></div>
        </div>
        <div class="form-group">
          <label>止盈金额（0=不止盈）</label>
          <input id="plan-stop" type="number" value="0" min="0" step="1000" style="width:100%">
        </div>
        <div class="form-group">
          <label>倍率序列（不中→下个倍率，爆档归零；中了归零；- 分隔）</label>
          <input id="plan-muls" type="text" value="1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625">
        </div>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          <button class="btn btn-primary" onclick="planConfigure()" style="flex:1">💾 保存</button>
          <button class="btn btn-green" id="plan-start-btn" data-on="0" onclick="planStart()" style="flex:1">▶ 启动</button>
          <button class="btn btn-red" onclick="planReset()" style="flex:1">🗑 删除记录</button>
        </div>
        <div id="plan-msg" style="font-size:.82rem;margin-top:8px;min-height:18px;text-align:center"></div>
        <div id="plan-status" style="font-size:.78rem;color:var(--muted);margin-top:6px;min-height:18px;text-align:center"></div>
        <!-- 真实参与开关 -->
        <div id="plan-real-wrap" style="display:flex;align-items:center;justify-content:space-between;margin-top:10px;padding:8px 10px;background:#12151e;border:1.5px solid #374151;border-radius:8px;transition:all .3s">
          <span id="plan-real-lbl" style="font-size:.82rem;font-weight:900;color:var(--muted)">⚫ 真实参与 已关闭</span>
          <div onclick="planToggleReal()" id="plan-real-btn" style="position:relative;width:48px;height:26px;background:#374151;border-radius:13px;cursor:pointer;transition:background .25s">
            <div id="plan-real-knob" style="position:absolute;top:3px;left:3px;width:20px;height:20px;background:#fff;border-radius:50%;transition:left .25s"></div>
          </div>
        </div>
      </div>
      <!-- 实时预览：8 专家 -->
      <div class="card" style="flex:1;min-width:280px">
        <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">
          <span style="font-weight:700;color:var(--muted)">🔮 8 专家实时预览</span>
          <span id="plan-preview-qishu" style="font-size:.75rem;color:var(--yellow)"></span>
        </div>
        <div id="plan-experts"><div class="notif-empty">加载中...</div></div>
        <div id="plan-selected" style="margin-top:10px;padding:8px 10px;background:#0c0e14;border-radius:6px;border:1px solid #f59e0033;font-size:.82rem;text-align:center;color:var(--muted)">--</div>
      </div>
      <!-- 记录 -->
      <div style="flex:2;min-width:300px">
        <div class="card">
          <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">
            <span style="font-weight:700;color:var(--muted)">🎮 欢乐210 · 计划跟投记录</span>
            <span id="plan-log-pnl" style="font-size:.85rem;font-weight:800;color:var(--yellow)">--</span>
          </div>
          <div id="plan-log"><div class="notif-empty">暂无记录</div></div>
        </div>
      </div>
    </div>
  </div>
</div>
"""

PLAN_JS = """
// ══ 📋 计划跟投（杀5余，仅欢乐210）══
var _planTimer = null;

async function planConfigure(){
  var base = parseInt(document.getElementById('plan-base').value)||1000;
  var stop = parseInt(document.getElementById('plan-stop').value)||0;
  var minlz = parseInt(document.getElementById('plan-minlz').value)||4;
  var muls = (document.getElementById('plan-muls').value||'1').trim();
  var msg = document.getElementById('plan-msg');
  try{
    var d = await fetch('/api/plan/configure',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({base_amount:base, stop_profit:stop, min_lianzhong:minlz, muls_text:muls})}).then(r=>r.json());
    msg.textContent = d.msg||(d.ok?'已保存':'失败');
    msg.style.color = d.ok?'var(--accent)':'var(--red)';
  }catch(e){ msg.textContent='网络错误'; msg.style.color='var(--red)'; }
}

async function planStart(){
  var btn = document.getElementById('plan-start-btn');
  var on = (btn.dataset.on||'0') !== '1';
  var msg = document.getElementById('plan-msg');
  try{
    var d = await fetch('/api/plan/start',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({on:on})}).then(r=>r.json());
    if(d.ok){
      btn.dataset.on = on?'1':'0';
      btn.textContent = on?'⏸ 停止':'▶ 启动';
      btn.className = on?'btn btn-red':'btn btn-green';
      msg.textContent = on?'已启动，下一期欢乐210开奖后自动评估跟投':'已停止';
      msg.style.color = on?'var(--accent)':'var(--muted)';
      planRefresh();
    } else { msg.textContent=d.msg||'失败'; msg.style.color='var(--red)'; }
  }catch(e){ msg.textContent='网络错误'; msg.style.color='var(--red)'; }
}

async function planReset(){
  if(!confirm('确认清空计划跟投记录？')) return;
  try{
    var d = await fetch('/api/plan/reset',{method:'POST',headers:{'Content-Type':'application/json'},body:'{}'}).then(r=>r.json());
    var msg = document.getElementById('plan-msg');
    msg.textContent = d.msg||'已重置'; msg.style.color='var(--accent)';
    planRefresh();
  }catch(e){}
}

async function planToggleReal(){
  var btn = document.getElementById('plan-real-btn');
  var on = !btn.dataset.on || btn.dataset.on!=='1';
  try{
    var d = await fetch('/api/plan/real/toggle',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({on:on})}).then(r=>r.json());
    if(d.ok) _planPaintReal(on);
  }catch(e){}
}

function _planPaintReal(on){
  var lbl=document.getElementById('plan-real-lbl'), wrap=document.getElementById('plan-real-wrap');
  var btn=document.getElementById('plan-real-btn'), knob=document.getElementById('plan-real-knob');
  if(!lbl||!btn) return;
  btn.dataset.on = on?'1':'0';
  if(on){
    lbl.innerHTML='🔴 真实参与 <b style="color:#22c55e">已开启</b>'; lbl.style.color='var(--text)';
    wrap.style.borderColor='#22c55e'; wrap.style.background='#0f1f12';
    btn.style.background='#22c55e'; knob.style.left='25px';
  }else{
    lbl.textContent='⚫ 真实参与 已关闭'; lbl.style.color='var(--muted)';
    wrap.style.borderColor='#374151'; wrap.style.background='#12151e';
    btn.style.background='#374151'; knob.style.left='3px';
  }
}

function _planRenderRecords(recs){
  var box=document.getElementById('plan-log');
  if(!box) return;
  if(!recs||!recs.length){ box.innerHTML='<div class="notif-empty">暂无记录</div>'; return; }
  var html='';
  recs.forEach(function(r){
    var when=(r.created_at||'').slice(11,19);
    var status,color;
    if(r.skipped){ status=r.label||'空仓'; color='#94a3b8'; }
    else if(r.pending){ status='⏳ 待开奖'; color='#fbbf24'; }
    else if(r.won){ status='✅ 中 +'+r.net_pnl; color='#22c55e'; }
    else { status='❌ 不中 '+r.net_pnl; color='#ef4444'; }
    var mulTag = (r.multiplier && r.multiplier!=1) ? (r.multiplier+'x ') : '';
    var predTxt = r.pred ? (r.pred+'·'+((r.positions||[]).length)+'号') : '空仓';
    var coldTxt = (r.removed_cold && r.removed_cold.length) ? ('<span style="color:#60a5fa">剔冷'+r.removed_cold.join(',')+'</span> ') : '';
    html += '<div style="display:flex;justify-content:space-between;align-items:center;padding:6px 8px;background:#12151e;border-radius:6px;margin-bottom:4px;font-size:.78rem">'
      + '<div><span style="color:var(--muted)">'+when+'</span> · <b>'+(r.qishu||'--')+'</b> · '+(r.label||'跟投')+'</div>'
      + '<div style="font-size:.72rem;color:var(--muted)">'+coldTxt+predTxt+' '+mulTag+'¥'+(r.bet_amount||0)+'</div>'
      + '<div style="color:'+color+';font-weight:800">'+status+'</div></div>';
  });
  box.innerHTML=html;
}

function _planRenderExperts(experts, selected, cold, minlz){
  var box=document.getElementById('plan-experts');
  if(!box) return;
  if(!experts||!experts.length){ box.innerHTML='<div class="notif-empty">无数据</div>'; return; }
  var selIds = (selected && selected.expert_ids) || [];
  var thr = minlz||4;
  var html='<div style="display:grid;grid-template-columns:repeat(2,1fr);gap:4px">';
  experts.forEach(function(e){
    var hot = e.lianzhong>=thr;
    var picked = selIds.indexOf(e.id)>=0;
    var bg = picked?'#1e40af':(hot?'#14331e':'#12151e');
    var bc = picked?'#3b82f6':(hot?'#22c55e55':'var(--border)');
    html += '<div style="padding:5px 8px;background:'+bg+';border:1px solid '+bc+';border-radius:5px;font-size:.72rem;display:flex;justify-content:space-between">'
      + '<span>专家'+e.id+'</span>'
      + '<span style="color:'+(hot?'#22c55e':'var(--muted)')+';font-weight:700">连'+e.lianzhong+'</span>'
      + '<span style="color:#cbd5e1">'+(e.pred||'-')+'</span></div>';
  });
  html += '</div>';
  // 冷号提示
  if(cold && cold.length){
    html += '<div style="margin-top:6px;font-size:.7rem;color:#60a5fa">❄️ 冷号(8-19 遗漏≥20)：'+cold.join(', ')+' → 剔除不下</div>';
  }
  box.innerHTML=html;
  var sd=document.getElementById('plan-selected');
  if(sd){
    if(selected){
      var predsTxt = (selected.preds||[]).join(' + ');
      var killTxt = (selected.killed_tails && selected.killed_tails.length) ? ('，杀尾 '+selected.killed_tails.join(',')) : '';
      var coldTxt = (selected.removed_cold && selected.removed_cold.length) ? ('，剔冷号 '+selected.removed_cold.join(',')) : '';
      sd.innerHTML='🎯 本期选中：<b style="color:#3b82f6">'+predsTxt+'</b>（连对 '+selected.lianzhong+'，专家 '+(selected.expert_ids||[]).join('/')+killTxt+coldTxt+'）→ 下 <b>'+(selected.positions||[]).length+'</b> 个号';
      sd.style.color='var(--text)';
    }else{
      sd.innerHTML='💤 本期空仓（无专家连对达标）'; sd.style.color='var(--muted)';
    }
  }
}

async function planRefresh(){
  try{
    var d = await fetch('/api/plan/status').then(r=>r.json());
    if(!d.ok) return;
    var s=d.data||{};
    var setIf=function(id,v){var el=document.getElementById(id); if(el&&document.activeElement!==el)el.value=v;};
    setIf('plan-base', s.base_amount);
    setIf('plan-stop', s.stop_profit);
    setIf('plan-minlz', s.min_lianzhong);
    setIf('plan-muls', s.muls_text);
    var pnlEl=document.getElementById('plan-pnl');
    if(pnlEl){ var v=s.total_pnl||0; pnlEl.textContent=v; pnlEl.style.color=v>=0?'var(--yellow)':'#ef4444'; }
    var lp=document.getElementById('plan-log-pnl');
    if(lp){ var v=s.total_pnl||0; lp.textContent=(v>=0?'+':'')+v; lp.style.color=v>=0?'#22c55e':'#ef4444'; }
    var pd=document.getElementById('plan-pnl-date');
    if(pd) pd.textContent=(s.pnl_date||'--')+' · 每天24点清空';
    _planRenderRecords(s.records||[]);
    _planPaintReal(!!s.real_enabled);
    var btn=document.getElementById('plan-start-btn');
    if(btn){ btn.dataset.on=s.running?'1':'0'; btn.textContent=s.running?'⏸ 停止':'▶ 启动'; btn.className=s.running?'btn btn-red':'btn btn-green'; }
    var st=document.getElementById('plan-status');
    if(st){
      var runTxt=s.running?'<b style="color:#22c55e">▶ 运行中</b>':'<span style="color:var(--muted)">⏹ 已停止</span>';
      var sp=s.stop_profit>0?(' · 止盈 '+s.stop_profit):'';
      var muls=s.multipliers||[1];
      var midx=s.mul_idx||0;
      var mulTxt=muls.length>1?(' · 倍率第 '+(midx+1)+'/'+muls.length+' 位('+muls[Math.min(midx,muls.length-1)]+'x)'):'';
      var curTxt = (s.cur_preds&&s.cur_preds.length)?s.cur_preds.join('+'):(s.cur_pred||'');
      var cur=curTxt?(' · 当前 '+curTxt+'(连'+s.cur_lianzhong+')'):'';
      var coldc=(s.cur_removed_cold&&s.cur_removed_cold.length)?(' · 剔冷'+s.cur_removed_cold.join(',')):'';
      st.innerHTML=runTxt+' · 连对阈值 '+s.min_lianzhong+mulTxt+sp+cur+coldc;
    }
  }catch(e){ console.warn('[plan refresh]',e); }
}

async function planPreview(){
  try{
    var d = await fetch('/api/plan/preview').then(r=>r.json());
    if(!d.ok) return;
    var q=document.getElementById('plan-preview-qishu');
    if(q) q.textContent = d.pending_qishu?('待开 '+d.pending_qishu):'';
    var minlz = parseInt((document.getElementById('plan-minlz')||{}).value)||4;
    _planRenderExperts(d.experts||[], d.selected, d.cold, minlz);
  }catch(e){ console.warn('[plan preview]',e); }
}

function planEnter(){
  planRefresh();
  planPreview();
  if(_planTimer) clearInterval(_planTimer);
  _planTimer=setInterval(function(){
    var tab=document.getElementById('tab-plan');
    if(tab&&tab.classList.contains('active')){ planRefresh(); planPreview(); }
  }, 5000);
}
"""

HISTORY_TAB_HTML = """
<div id="tab-history" class="tab-content">
  <div class="std-main" style="max-width:1200px">
    <!-- 类型切换 -->
    <div style="display:flex;gap:0;border-radius:8px;overflow:hidden;border:1px solid var(--border);margin-bottom:12px;width:fit-content">
      <button id="hist-type-sim" onclick="histSwitchType('sim')" style="padding:8px 20px;background:var(--accent);color:#fff;border:none;cursor:pointer;font-weight:700;font-size:.85rem">🎲 模拟记录</button>
      <button id="hist-type-real" onclick="histSwitchType('real')" style="padding:8px 20px;background:transparent;color:var(--muted);border:none;cursor:pointer;font-weight:700;font-size:.85rem">🪨 参与记录</button>
    </div>
    <!-- 模拟筛选条件 -->
    <div id="hist-sim-filters" class="card" style="margin-bottom:12px">
      <div style="display:flex;gap:12px;flex-wrap:wrap;align-items:center">
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">游戏</label>
          <select id="hist-style" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px;font-size:.82rem">
            <option value="210">🎮 欢乐210</option>
            <option value="60">⚡ 比特60</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">模式</label>
          <select id="hist-mode" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px;font-size:.82rem">
            <option value="random">🎲 随机</option>
            <option value="map">🎯 开某投某</option>
            <option value="fix">📌 固定</option>
            <option value="jump">🔀 跳转</option>
            <option value="miss">🔍 遗漏</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">日期</label>
          <select id="hist-date" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px;font-size:.82rem">
            <option value="">今天</option>
          </select>
        </div>
        <button class="btn btn-primary" onclick="historyTabLoad()" style="padding:6px 16px">🔍 查询</button>
        <span id="hist-pnl" style="font-size:1rem;font-weight:800;color:var(--yellow);margin-left:auto"></span>
      </div>
    </div>
    <!-- 真实下单筛选 -->
    <div id="hist-real-filters" class="card" style="margin-bottom:12px;display:none">
      <div style="display:flex;gap:12px;flex-wrap:wrap;align-items:center">
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">游戏</label>
          <select id="hist-real-game" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px;font-size:.82rem">
            <option value="210">🎮 欢乐210</option>
            <option value="60">⚡ 比特60</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">日期</label>
          <input id="hist-real-date" type="date" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px;font-size:.82rem">
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">来源</label>
          <select id="hist-real-source" onchange="historyRealLoad()" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px;font-size:.82rem">
            <option value="">全部来源</option>
            <option value="normal">手动下单</option>
            <option value="sim_random">🎲 随机下</option>
            <option value="sim_map">🎯 开某投某</option>
            <option value="sim_fix">📌 固定</option>
            <option value="sim_jump">🔀 跳转</option>
            <option value="miss">🔍 遗漏检测</option>
            <option value="dawei">🎯 打尾</option>
            <option value="plan">📋 计划跟投</option>
          </select>
        </div>
        <div>
          <label style="font-size:.78rem;color:var(--muted);margin-right:6px">数量</label>
          <select id="hist-real-limit" style="background:#12151e;border:1px solid var(--border);color:var(--text);border-radius:6px;padding:4px 8px;font-size:.82rem">
            <option value="30">30 条</option>
            <option value="50" selected>50 条</option>
            <option value="100">100 条</option>
          </select>
        </div>
        <button class="btn btn-primary" onclick="historyRealLoad()" style="padding:6px 16px">🔍 查询</button>
        <label style="font-size:.78rem;color:var(--muted);user-select:none;cursor:pointer">
          <input id="hist-real-groupby" type="checkbox" onchange="historyRealLoad()" style="vertical-align:middle"> 按账号分组
        </label>
        <label style="font-size:.78rem;color:var(--muted);margin-left:auto;user-select:none;cursor:pointer">
          <input id="hist-real-autoref" type="checkbox" onchange="historyRealToggleAuto()" style="vertical-align:middle"> 自动刷新（5秒）
        </label>
      </div>
      <div style="margin-top:6px;font-size:.7rem;color:var(--muted)">💡 数据直接来自石头岛账号下单记录，每个账号拉一次</div>
    </div>
    <div id="hist-content" style="display:flex;flex-direction:column;gap:8px">
      <div class="notif-empty">请选择条件后点查询</div>
    </div>
  </div>
</div>
"""

SIM_JS = """
// ══ 模拟下单（random/map 各 4 套，两个 mode 完全独立 slot）══
var simCurrentSlotRandom=1;
var simCurrentSlotMap=1;
var simCurrentSlotFix=1;
var simCurrentSlotJump=1;
// 兼容旧引用（已不再使用，仅防止脚本里残留访问报错）
var simCurrentSlot=1;
var simSlotData={};
var simSlotPage={};
var SIM_PAGE_SIZE=3;

function _initSlotPage(store,slot){
  if(!store[slot])store[slot]={};
  ['random','map','fix','jump'].forEach(function(m){
    if(!store[slot][m])store[slot][m]={210:0,60:0};
  });
}

function simSwitchSlot(slot,mode){
  mode=mode||'random';
  if(mode==='random')simCurrentSlotRandom=slot;
  else if(mode==='map')simCurrentSlotMap=slot;
  else if(mode==='fix')simCurrentSlotFix=slot;
  else if(mode==='jump')simCurrentSlotJump=slot;
  var prefix=mode==='random'?'simr':(mode==='map'?'simm':(mode==='fix'?'simf':(mode==='jump'?'simj':'simr')));
  for(var i=1;i<=4;i++){
    var b=document.getElementById(prefix+'-slot-btn-'+i);
    if(b){b.style.background=i===slot?'var(--accent)':'transparent';b.style.color=i===slot?'#fff':'var(--muted)';}
  }
  simRenderSlot(slot,mode);
}

function simSlotHTML(slot,mode){
  mode=mode||'random';
  var px='sim';
  // 兼容旧调用：第2参数若是数字（grp），按 random 渲染
  if(typeof mode==='number')mode='random';
  var modeLabel=(mode==='random')?'随机下':(mode==='map')?'开某投某':(mode==='fix')?'固定':(mode==='jump')?'跳转':mode;
  return '<div style="display:flex;gap:12px;flex-wrap:wrap">'
    +'<div class="card" style="flex:1;min-width:160px;text-align:center;position:relative">'
      +'<button class="btn btn-red btn-sm" data-px="'+px+'" data-slot="'+slot+'" data-mode="'+mode+'" data-style="210" onclick="simClearAll(this)" style="position:absolute;top:6px;right:6px;padding:2px 8px;font-size:.68rem">🗑 清空</button>'
      +'<div style="font-size:.75rem;color:var(--muted);margin-bottom:2px">🎮 欢乐210 · '+modeLabel+' · 套'+slot+' 今日盈亏</div>'
      +'<div id="sim-'+mode+'-pnl-'+slot+'-210" style="font-size:1.8rem;font-weight:900;color:var(--yellow)">--</div>'
      +'<div id="sim-'+mode+'-pnl-date-'+slot+'" style="font-size:.72rem;color:var(--muted);margin-top:2px">-- · 每天24点清空</div>'
    +'</div>'
    +'<div class="card" style="flex:1;min-width:160px;text-align:center;position:relative">'
      +'<button class="btn btn-red btn-sm" data-px="'+px+'" data-slot="'+slot+'" data-mode="'+mode+'" data-style="60" onclick="simClearAll(this)" style="position:absolute;top:6px;right:6px;padding:2px 8px;font-size:.68rem">🗑 清空</button>'
      +'<div style="font-size:.75rem;color:var(--muted);margin-bottom:2px">⚡ 比特60 · '+modeLabel+' · 套'+slot+' 今日盈亏</div>'
      +'<div id="sim-'+mode+'-pnl-'+slot+'-60" style="font-size:1.8rem;font-weight:900;color:var(--yellow)">--</div>'
    +'</div>'
    +'</div>'
    +'<div style="display:flex;gap:12px;flex-wrap:wrap;align-items:flex-start">'
    +'<div style="flex:1;min-width:280px;display:flex;flex-direction:column;gap:10px">'+simGameCardHTML(slot,1,210,mode)+'</div>'
    +'<div style="flex:1;min-width:280px;display:flex;flex-direction:column;gap:10px">'+simGameCardHTML(slot,1,60,mode)+'</div>'
    +'</div>'
    +'<div style="display:flex;gap:10px;flex-wrap:wrap;align-items:flex-start">'
    +simLogCardHTML(slot,1,mode,210)+simLogCardHTML(slot,1,mode,60)
    +'</div>';
}

async function simClearAll(btn){
  var px=btn.dataset.px;
  var slot=parseInt(btn.dataset.slot);
  var style=parseInt(btn.dataset.style);
  var gameLabel=style===210?'欢乐210':'比特60';
  if(!confirm('⚠️ 删除记录将无法恢复\\n本系统所有该数据全部删除\\n是否确认清空「套'+slot+' · '+gameLabel+'」的所有模拟数据？\\n（配置保留）'))return;
  btn.disabled=true;btn.textContent='清空中...';
  try{
    var d=await fetch('/api/sim/clear',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({slot:slot,style:style})}).then(r=>r.json());
    if(d.ok){
      btn.textContent='✅ 已清空';
      setTimeout(function(){btn.textContent='🗑 清空';btn.disabled=false;},2000);
      if(typeof simRefresh==='function')simRefresh();
    }else{
      btn.textContent='❌ '+(d.msg||'失败');btn.disabled=false;
      setTimeout(function(){btn.textContent='🗑 清空';},3000);
    }
  }catch(e){
    btn.textContent='❌ 网络错误';btn.disabled=false;
    setTimeout(function(){btn.textContent='🗑 清空';},3000);
  }
}

function simGameCardHTML(slot,grp,style,mode){
  var px=grp===1?'sim':'sim2';
  var icon=style===210?'🎮':'⚡';
  var label=style===210?'欢乐210':'比特60';
  var modeLabel=(mode==='random')?'随机下注':(mode==='map')?'开某投某':(mode==='fix')?'固定':(mode==='jump')?'跳转':mode;
  var id=px+'-'+slot+'-'+style+'-'+mode;
  // 文本框
  var textarea;
  if(mode==='random'){
    textarea='<textarea id="'+id+'-ta" rows="5" style="width:100%;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);padding:8px;font-size:.78rem;font-family:monospace;resize:vertical" placeholder="每行一组，数字用-分隔，0~27"></textarea>';
  }else if(mode==='map'){
    textarea='<textarea id="'+id+'-ta" rows="7" style="width:100%;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);padding:8px;font-size:.75rem;font-family:monospace;resize:vertical" placeholder="28行，第1行=开0，...，第28行=开27"></textarea><div id="'+id+'-lc" style="font-size:.7rem;color:var(--muted);margin-top:2px">已输入0行/需28行</div>';
  }else if(mode==='fix'){
    textarea='<textarea id="'+id+'-ta" rows="6" style="width:100%;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);padding:8px;font-size:.78rem;font-family:monospace;resize:vertical" placeholder="每行一组，启动后每期同时下所有行；不限行数"></textarea><div id="'+id+'-lc" style="font-size:.7rem;color:var(--muted);margin-top:2px">已输入0行</div>';
  }else if(mode==='jump'){
    textarea='<textarea id="'+id+'-ta" rows="6" style="width:100%;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);padding:8px;font-size:.78rem;font-family:monospace;resize:vertical" placeholder="每行一组，行数必须 = 倍率个数；按序推进，中→回首组"></textarea><div id="'+id+'-lc" style="font-size:.7rem;color:var(--muted);margin-top:2px">已输入0行</div>';
  }else{
    textarea='<textarea id="'+id+'-ta" rows="5" style="width:100%;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);padding:8px;font-size:.78rem;font-family:monospace;resize:vertical"></textarea>';
  }
  var mutsInput='<div class="form-group" style="margin-bottom:6px"><label style="font-size:.72rem">倍数序列</label><input id="'+id+'-muls" type="text" value="1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625" style="font-size:.75rem"></div><div class="form-group" style="margin-bottom:6px"><label style="font-size:.72rem">基础金额</label><input id="'+id+'-base" type="number" value="10000" min="100" style="font-size:.75rem"></div>';
  // 固定模式专属两个开关
  var fixOptionsHtml='';
  if(mode==='fix'){
    fixOptionsHtml=''
      +'<div style="display:flex;gap:6px;margin-bottom:6px">'
      +'<button id="'+id+'-sow" class="btn btn-ghost btn-sm" onclick="simToggleFixOption(this)" data-px="'+px+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-opt="stop_on_win" style="flex:1;font-size:.72rem">🎯 中了就停：关</button>'
      +'<button id="'+id+'-soe" class="btn btn-ghost btn-sm" onclick="simToggleFixOption(this)" data-px="'+px+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-opt="stop_on_exhaust" style="flex:1;font-size:.72rem">📛 倍率打完就停：关</button>'
      +'</div>';
  }
  var stopProfitInput='<div class="form-group" style="margin-bottom:8px;display:flex;align-items:center;gap:6px"><label style="font-size:.72rem;white-space:nowrap">止盈金额（0=不止盈）</label><input id="'+id+'-sp" type="number" value="0" min="0" step="1000" style="font-size:.75rem;flex:1"><button class="btn btn-ghost btn-sm" onclick="simSetSP(this)" data-px="'+px+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-mode="'+mode+'" style="white-space:nowrap;padding:4px 8px">设置</button></div>';
  var saveHandler=(mode==='random')?'simConfigure':(mode==='map')?'simConfigureMap':(mode==='fix')?'simConfigureFix':(mode==='jump')?'simConfigureJump':'simConfigure';
  var saveBtn='<button class="btn btn-primary btn-sm" onclick="'+saveHandler+'(this)" data-px="'+px+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" style="flex:1">💾 保存</button>';
  // 真实参与开关：初始按"关"渲染；simApplySlotData 会根据 data.real_enabled_* 自动更新外观
  var realToggle='<div style="display:flex;align-items:center;justify-content:space-between;margin:8px 0 4px;padding:8px 10px;background:#12151e;border:1.5px solid #374151;border-radius:8px;transition:all .3s" id="'+id+'-real-wrap">'
    +'<span style="font-size:.82rem;font-weight:900;color:var(--muted)" id="'+id+'-real-lbl">⚫ 真实参与 已关闭</span>'
    +'<div onclick="simToggleReal(this)" data-id="'+id+'" data-slot="'+slot+'" data-style="'+style+'" data-mode="'+mode+'" style="position:relative;width:48px;height:26px;background:#374151;border-radius:13px;cursor:pointer;transition:background .25s" id="'+id+'-real-btn">'
    +'<div style="position:absolute;top:3px;left:3px;width:20px;height:20px;background:#fff;border-radius:50%;transition:left .25s" id="'+id+'-real-knob"></div>'
    +'</div></div>';
  return '<div class="card" style="padding:10px">'
    +'<div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:8px">'
    +'<span style="font-size:.82rem;font-weight:700">'+icon+' '+label+' · '+modeLabel+'</span>'
    +'<span id="'+id+'-status" style="font-size:.72rem;padding:2px 7px;border-radius:8px;background:#1e2235;color:var(--muted)">未启动</span>'
    +'</div>'
    +realToggle
    +'<div class="form-group" style="margin-bottom:6px">'+textarea+'</div>'
    +mutsInput+fixOptionsHtml+stopProfitInput
    +'<div style="display:flex;gap:4px;flex-wrap:wrap">'+saveBtn
    +'<button class="btn btn-green btn-sm" onclick="simStart(this)" data-px="'+px+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-mode="'+mode+'" style="flex:1">启动</button>'
    +'<button class="btn btn-red btn-sm" onclick="simStop(this)" data-px="'+px+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-mode="'+mode+'" style="flex:1">停止</button>'
    +'<button class="btn btn-ghost btn-sm" onclick="simReset(this)" data-px="'+px+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-mode="'+mode+'" style="flex:1">重置</button>'
    +'</div>'
    +'<div id="'+id+'-msg" style="font-size:.78rem;margin-top:6px;min-height:16px;text-align:center"></div>'
    +'</div>';
}

function simLogCardHTML(slot,grp,mode,style){
  var px=grp===1?'sim':'sim2';
  var icon=style===210?'🎮':'⚡';
  var label=style===210?'欢乐210':'比特60';
  var modeLabel=(mode==='random')?'随机':(mode==='map')?'开某投某':(mode==='fix')?'固定':(mode==='jump')?'跳转':mode;
  var id=px+'-'+slot+'-'+mode+'-'+style;
  return '<div class="card" style="flex:1;min-width:220px;padding:10px">'
    +'<div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:6px">'
    +'<span style="font-size:.78rem;font-weight:700;color:var(--muted)">'+icon+' '+label+' · '+modeLabel+'</span>'
    +'<div style="display:flex;align-items:center;gap:4px">'
    +'<span id="'+id+'-pnl" style="font-size:.8rem;font-weight:800;color:var(--yellow)">--</span>'
    +'<button data-px="'+px+'" data-mode="'+mode+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-dir="-1" onclick="simPageBtn(this)" style="background:transparent;border:1px solid var(--border);color:var(--muted);border-radius:4px;padding:1px 6px;cursor:pointer;font-size:.72rem">◀</button>'
    +'<span id="'+id+'-pg" style="font-size:.72rem;color:var(--muted)">1/1</span>'
    +'<button data-px="'+px+'" data-mode="'+mode+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-dir="1" onclick="simPageBtn(this)" style="background:transparent;border:1px solid var(--border);color:var(--muted);border-radius:4px;padding:1px 6px;cursor:pointer;font-size:.72rem">▶</button>'
    +'<button data-px="'+px+'" data-slot="'+slot+'" data-grp="'+grp+'" data-style="'+style+'" data-mode="'+mode+'" onclick="simOpenDBHistory(this)" style="background:#1e2235;border:1px solid var(--border);color:#93c5fd;border-radius:4px;padding:1px 6px;cursor:pointer;font-size:.68rem">📅 历史</button>'
    +'</div></div>'
    +'<div id="'+id+'-log" style="display:flex;flex-direction:column;gap:4px"><div class="notif-empty">暂无记录</div></div>'
    +'</div>';
}

// ── 真实参与开关 ──
// 真实参与开关：调后端 API（服务端持久化，跨设备）
async function simToggleReal(el){
  var id=el.dataset.id;
  var slot=parseInt(el.dataset.slot);
  var style=parseInt(el.dataset.style);
  var mode=el.dataset.mode;
  // 当前 UI 状态从 wrap 边框色判断；绝对状态由服务端给出
  var wrap=document.getElementById(id+'-real-wrap');
  var currOn=wrap&&wrap.style.borderColor==='rgb(220, 38, 38)';
  if(!currOn){
    var ok=confirm('打开此开关会真实跟单（独立倍率序列，从最低倍率开始），默认下单你已登录的所有平台账号。即使关闭浏览器，服务端依然会按模拟引擎下单。确认开启？');
    if(!ok)return;
  }
  var newOn=!currOn;
  try{
    var d=await fetch('/api/sim/real/toggle',{
      method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({slot:slot,style:style,mode:mode,on:newOn})
    }).then(r=>r.json());
    if(!d.ok){alert('切换失败: '+(d.msg||'未知'));return;}
    simApplyRealUIState(id, newOn);
  }catch(e){alert('网络错误: '+e);}
}

function simApplyRealUIState(id, on){
  var wrap=document.getElementById(id+'-real-wrap');
  var lbl=document.getElementById(id+'-real-lbl');
  var btn=document.getElementById(id+'-real-btn');
  var knob=document.getElementById(id+'-real-knob');
  if(on){
    if(wrap){wrap.style.background='linear-gradient(90deg,#7c3aed33,#dc262633)';wrap.style.borderColor='rgb(220, 38, 38)';}
    if(lbl){lbl.textContent='🔴 真实参与 已开启（服务端跟单）';lbl.style.color='#f87171';}
    if(btn)btn.style.background='#dc2626';
    if(knob)knob.style.left='23px';
  }else{
    if(wrap){wrap.style.background='#12151e';wrap.style.borderColor='#374151';}
    if(lbl){lbl.textContent='⚫ 真实参与 已关闭';lbl.style.color='var(--muted)';}
    if(btn)btn.style.background='#374151';
    if(knob)knob.style.left='3px';
  }
}


function simPageBtn(btn){
  var px=btn.dataset.px;var mode=btn.dataset.mode;
  var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);
  var style=parseInt(btn.dataset.style);var dir=parseInt(btn.dataset.dir);
  _initSlotPage(simSlotPage,slot);
  var logs=((simSlotData[slot]||{})[style]||{})[('groups_log_'+mode)]||[];
  var maxPage=Math.max(0,Math.ceil(logs.length/SIM_PAGE_SIZE)-1);
  simSlotPage[slot][mode][style]=Math.max(0,Math.min(maxPage,simSlotPage[slot][mode][style]+dir));
  renderSimLogPage2(px,mode,slot,grp,style,logs);
}

function simMsg2(id,txt,color){
  var el=document.getElementById(id+'-msg');
  if(el){el.textContent=txt;el.style.color=color||'var(--muted)';}
}

function fmtNum(n){return n>=0?('+'+n.toLocaleString()):n.toLocaleString();}
function fmtColor(n){return n>=0?'var(--green)':'var(--red)';}

function simRenderSlot(slot,mode){
  // 兼容旧调用：simRenderSlot(slot,1) → mode='random'
  if(mode===1||mode===2||mode==null)mode='random';
  var px='sim';
  var containerId;
  if(mode==='random')containerId='simr-slot-content';
  else if(mode==='map')containerId='simm-slot-content';
  else if(mode==='fix')containerId='simf-slot-content';
  else if(mode==='jump')containerId='simj-slot-content';
  else containerId='simr-slot-content';
  var el=document.getElementById(containerId);
  if(!el)return;
  el.innerHTML=simSlotHTML(slot,mode);
  // 文本框行数实时统计（map/fix/jump 都需要）
  if(mode==='map'||mode==='fix'||mode==='jump'){
    [210,60].forEach(function(style){
      var id=px+'-'+slot+'-'+style+'-'+mode;
      var ta=document.getElementById(id+'-ta');
      if(ta)ta.addEventListener('input',function(){
        var lc=ta.value.split(String.fromCharCode(10)).filter(function(l){return l.trim();}).length;
        var el2=document.getElementById(id+'-lc');
        if(!el2)return;
        if(mode==='map'){
          el2.textContent='已输入'+lc+'行/需28行';
          el2.style.color=lc===28?'var(--green)':'var(--muted)';
        }else if(mode==='jump'){
          // jump 要求行数=倍率个数；从同卡的 muls 输入框算
          var muls=(document.getElementById(id+'-muls')||{}).value||'';
          var mn=muls.split('-').filter(function(x){return x.trim()&&!isNaN(parseFloat(x));}).length;
          el2.textContent='已输入'+lc+'行 / 倍率'+mn+'个'+(lc===mn&&lc>0?'（匹配 ✓）':'（必须相等）');
          el2.style.color=(lc===mn&&lc>0)?'var(--green)':'var(--red)';
        }else{
          el2.textContent='已输入'+lc+'行';
          el2.style.color=lc>0?'var(--green)':'var(--muted)';
        }
      });
    });
  }
  if(simSlotData[slot]){
    if(simSlotData[slot][210])simApplySlotData(px,slot,1,210,simSlotData[slot][210]);
    if(simSlotData[slot][60])simApplySlotData(px,slot,1,60,simSlotData[slot][60]);
  }
}

async function simConfigure(btn){var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);
  var id=px+'-'+slot+'-'+style+'-random';
  var gt=(document.getElementById(id+'-ta')||{}).value||'';
  var mt=(document.getElementById(id+'-muls')||{}).value||'1';
  var ba=parseInt((document.getElementById(id+'-base')||{}).value)||10000;
  if(!gt.trim()){simMsg2(id,'❌ 请填写数字组','var(--red)');return;}
  simMsg2(id,'保存中...','var(--muted)');
  try{
    var d=await fetch('/api/sim/configure',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({slot:slot,group:grp,style:style,groups_text:gt,multipliers_text:mt,base_amount:ba})}).then(r=>r.json());
    simMsg2(id,d.ok?'✅ '+d.msg:'❌ '+d.msg,d.ok?'var(--green)':'var(--red)');
  }catch(e){simMsg2(id,'❌ 网络错误','var(--red)');}
}
async function simConfigureMap(btn){var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);
  var id=px+'-'+slot+'-'+style+'-map';
  var mv=(document.getElementById(id+'-ta')||{}).value||'';
  var mt=(document.getElementById(id+'-muls')||{}).value||'1';
  var ba=parseInt((document.getElementById(id+'-base')||{}).value)||10000;
  var lc=mv.split(String.fromCharCode(10)).filter(function(l){return l.trim();}).length;
  if(lc!==28){simMsg2(id,'❌ 需要28行，当前'+lc+'行','var(--red)');return;}
  simMsg2(id,'保存中...','var(--muted)');
  try{
    var d=await fetch('/api/sim/configure_map',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({slot:slot,group:grp,style:style,map_text:mv,multipliers_text:mt,base_amount:ba})}).then(r=>r.json());
    simMsg2(id,d.ok?'✅ '+d.msg:'❌ '+d.msg,d.ok?'var(--green)':'var(--red)');
  }catch(e){simMsg2(id,'❌ 网络错误','var(--red)');}
}
// ══════════════════════════════════════════════════════════════
// 🪨 平台参与记录 tab JS
// ══════════════════════════════════════════════════════════════
var _pfGame=210;
function platformSwitchGame(game){
  _pfGame=game;
  var b210=document.getElementById('pf-game-210');
  var b60=document.getElementById('pf-game-60');
  if(b210){b210.style.background=game===210?'var(--accent)':'transparent';b210.style.color=game===210?'#fff':'var(--muted)';}
  if(b60){b60.style.background=game===60?'var(--accent)':'transparent';b60.style.color=game===60?'#fff':'var(--muted)';}
  platformLoad();
}
function _platformToday(){
  var d=new Date();
  var y=d.getFullYear();
  var m=String(d.getMonth()+1).padStart(2,'0');
  var dd=String(d.getDate()).padStart(2,'0');
  return y+'-'+m+'-'+dd;
}
function platformReset(){
  var uid=document.getElementById('pf-uid');if(uid)uid.value='';
  var src=document.getElementById('pf-source');if(src)src.value='';
  var dt=document.getElementById('pf-date');if(dt)dt.value='';
  platformLoad();
}
function _platformFmtSrc(src){
  if(!src||src==='normal'||src==='manual')return '<span style="color:#94a3b8;background:#1f2937;border:1px solid #4b5563;border-radius:4px;padding:1px 5px;font-size:.7rem">✋ 手动下单</span>';
  if(src==='miss'||src.indexOf('miss')===0)return '<span style="color:#fbbf24;background:#f5910022;border:1px solid #f59e00;border-radius:4px;padding:1px 5px;font-size:.7rem">🔍 遗漏</span>';
  if(src==='sim_random')return '<span style="color:#c084fc;background:#a855f722;border:1px solid #a855f7;border-radius:4px;padding:1px 5px;font-size:.7rem">🎲 随机下</span>';
  if(src==='sim_map')return '<span style="color:#67e8f9;background:#06b6d422;border:1px solid #06b6d4;border-radius:4px;padding:1px 5px;font-size:.7rem">🎯 开某投某</span>';
  if(src==='sim_fix')return '<span style="color:#86efac;background:#16a34a22;border:1px solid #16a34a;border-radius:4px;padding:1px 5px;font-size:.7rem">📌 固定</span>';
  if(src==='sim_jump')return '<span style="color:#f9a8d4;background:#ec489922;border:1px solid #ec4899;border-radius:4px;padding:1px 5px;font-size:.7rem">🔀 跳转</span>';
  if(src.indexOf('sim')===0)return '<span style="color:#c084fc;background:#a855f722;border:1px solid #a855f7;border-radius:4px;padding:1px 5px;font-size:.7rem">🎲 模拟</span>';
  return '<span style="color:var(--muted)">'+src+'</span>';
}
function _platformMaskTel(tel){
  if(!tel||tel.length<7)return tel||'';
  return tel.slice(0,3)+'****'+tel.slice(7);
}
async function platformLoad(){
  var contentEl=document.getElementById('pf-content');
  if(!contentEl)return;
  var uid=(document.getElementById('pf-uid')||{}).value||'';
  var srcFilter=(document.getElementById('pf-source')||{}).value||'';
  var date=(document.getElementById('pf-date')||{}).value||'';
  contentEl.innerHTML='<div class="notif-empty" style="padding:30px">⏳ 查询中...</div>';
  try{
    var url='/api/std/platform_orders?game='+_pfGame+'&limit=2000';
    if(uid)url+='&uid='+encodeURIComponent(uid);
    if(srcFilter)url+='&source='+encodeURIComponent(srcFilter);
    if(date)url+='&date='+encodeURIComponent(date);
    var d=await fetch(url).then(function(r){return r.json();});
    if(!d.ok){
      contentEl.innerHTML='<div class="notif-empty" style="padding:30px;color:var(--red)">❌ '+(d.msg||'查询失败')+'</div>';
      return;
    }
    // 填账号下拉（如果还没填过）
    var sel=document.getElementById('pf-uid');
    if(sel&&sel.options.length<=1&&Array.isArray(d.accounts)){
      var cur=sel.value;
      var html='<option value="">全部账号</option>';
      d.accounts.forEach(function(a){
        var label=a.remark?(a.remark+' · '+_platformMaskTel(a.tel)):_platformMaskTel(a.tel);
        html+='<option value="'+a.uid+'">'+label+'</option>';
      });
      sel.innerHTML=html;
      if(cur)sel.value=cur;
    }
    // 汇总
    var stat=d.stats||{count:0,stake:0,win:0,pnl:0,won:0,lost:0,pending:0};
    function _setStat(id,val){var el=document.getElementById(id);if(el)el.textContent=(val||0).toLocaleString();}
    _setStat('pf-stat-count',stat.count);
    _setStat('pf-stat-won',stat.won);
    _setStat('pf-stat-lost',stat.lost);
    _setStat('pf-stat-pending',stat.pending);
    _setStat('pf-stat-stake',stat.stake);
    _setStat('pf-stat-win',stat.win);
    var pEl=document.getElementById('pf-stat-pnl');
    if(pEl){
      pEl.textContent=(stat.pnl>=0?'+':'')+(stat.pnl||0).toLocaleString();
      pEl.style.color=stat.pnl>0?'var(--green)':(stat.pnl<0?'var(--red)':'var(--yellow)');
    }
    var rows=d.data||[];
    if(!rows.length){
      contentEl.innerHTML='<div class="notif-empty" style="padding:30px">📭 该筛选条件下没有下单记录</div>';
      return;
    }
    // 按 uid 分组
    var byUid={};
    rows.forEach(function(o){
      var k=o.uid||'unknown';
      if(!byUid[k])byUid[k]={uid:o.uid,tel:o.tel,orders:[]};
      byUid[k].orders.push(o);
    });
    var html='';
    Object.keys(byUid).forEach(function(k){
      var g=byUid[k];
      var stake=0,win=0,pnl=0,won=0,lost=0,pending=0;
      g.orders.forEach(function(o){
        if(!o.ok)return;
        stake+=o.betAmount;
        if(o.pending){pending++;return;}
        win+=o.winAmount;
        pnl+=o.pnl;
        if(o.winAmount>0)won++;else lost++;
      });
      var pnlColor=pnl>0?'var(--green)':(pnl<0?'var(--red)':'var(--muted)');
      html+='<div class="card" style="margin-bottom:14px;padding:0;overflow:hidden">';
      // 账号头
      html+='<div style="padding:10px 14px;border-bottom:1px solid var(--border);background:#0f1117;display:flex;flex-wrap:wrap;align-items:center;gap:14px">';
      html+='<div style="font-size:.95rem;font-weight:800">👤 '+_platformMaskTel(g.tel)+' <span style="font-size:.72rem;color:var(--muted);font-weight:400">UID '+(g.uid||'').slice(0,8)+'</span></div>';
      html+='<div style="font-size:.78rem;color:var(--muted)">共 <b style="color:var(--text)">'+g.orders.length+'</b> 条</div>';
      html+='<div style="font-size:.78rem;color:var(--muted)">投入 <b style="color:var(--yellow)">'+stake.toLocaleString()+'</b></div>';
      html+='<div style="font-size:.78rem;color:var(--muted)">中奖 <b style="color:var(--green)">'+win.toLocaleString()+'</b></div>';
      html+='<div style="font-size:.85rem;color:var(--muted);margin-left:auto">盈亏 <b style="color:'+pnlColor+';font-size:1rem">'+(pnl>=0?'+':'')+pnl.toLocaleString()+'</b></div>';
      html+='</div>';
      // 表格
      html+='<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:.8rem">';
      html+='<thead><tr style="background:#0a0c11;color:var(--muted)">'
        +'<th style="padding:6px 8px;text-align:left;white-space:nowrap">时间</th>'
        +'<th style="padding:6px 8px;text-align:left">期号</th>'
        +'<th style="padding:6px 8px;text-align:right">投注</th>'
        +'<th style="padding:6px 8px;text-align:center">开奖号</th>'
        +'<th style="padding:6px 8px;text-align:right">中奖</th>'
        +'<th style="padding:6px 8px;text-align:right">盈亏</th>'
        +'<th style="padding:6px 8px;text-align:center">来源</th>'
        +'<th style="padding:6px 8px;text-align:center">状态</th>'
        +'</tr></thead><tbody>';
      g.orders.forEach(function(o){
        var tm=(o.createTime||'').slice(5,19);
        var openCell,winCell,pnlCell,statusCell;
        if(!o.ok){
          openCell='<td style="padding:5px 8px;text-align:center;color:var(--red)">失败</td>';
          winCell='<td style="padding:5px 8px;text-align:right;color:var(--muted)">--</td>';
          pnlCell='<td style="padding:5px 8px;text-align:right;color:var(--muted)">--</td>';
          statusCell='<td style="padding:5px 8px;text-align:center;color:var(--red);font-size:.72rem">'+(o.msg||'下单失败')+'</td>';
        }else if(o.pending){
          openCell='<td style="padding:5px 8px;text-align:center;color:#60a5fa;font-weight:700">⏳待开奖</td>';
          winCell='<td style="padding:5px 8px;text-align:right;color:var(--muted)">--</td>';
          pnlCell='<td style="padding:5px 8px;text-align:right;color:var(--muted)">--</td>';
          statusCell='<td style="padding:5px 8px;text-align:center;color:#60a5fa;font-size:.72rem">待开奖</td>';
        }else{
          openCell='<td style="padding:5px 8px;text-align:center"><b style="color:var(--yellow);background:#0c0e14;border:1px solid var(--yellow);border-radius:5px;padding:1px 8px">'+o.result+'</b></td>';
          var c=o.winAmount>0?'var(--green)':'var(--muted)';
          winCell='<td style="padding:5px 8px;text-align:right;color:'+c+';font-weight:700">'+(o.winAmount?'+'+o.winAmount.toLocaleString():'0')+'</td>';
          var pc=o.pnl>0?'var(--green)':(o.pnl<0?'var(--red)':'var(--muted)');
          pnlCell='<td style="padding:5px 8px;text-align:right;color:'+pc+';font-weight:700">'+(o.pnl>=0?'+':'')+o.pnl.toLocaleString()+'</td>';
          statusCell=o.winAmount>0
            ?'<td style="padding:5px 8px;text-align:center"><span style="color:var(--red);background:#7f1d1d22;border:1px solid var(--red);border-radius:4px;padding:1px 6px;font-size:.7rem;font-weight:700">中</span></td>'
            :'<td style="padding:5px 8px;text-align:center"><span style="color:var(--green);background:#14532d22;border:1px solid var(--green);border-radius:4px;padding:1px 6px;font-size:.7rem;font-weight:700">未中</span></td>';
        }
        html+='<tr style="border-top:1px solid #1e2235">'
          +'<td style="padding:5px 8px;color:var(--muted);font-size:.72rem;white-space:nowrap">'+(tm||'--')+'</td>'
          +'<td style="padding:5px 8px;font-family:monospace">'+o.qishu+'</td>'
          +'<td style="padding:5px 8px;text-align:right;color:var(--yellow);font-weight:700">'+o.betAmount.toLocaleString()+'</td>'
          +openCell+winCell+pnlCell
          +'<td style="padding:5px 8px;text-align:center">'+_platformFmtSrc(o.source)+'</td>'
          +statusCell
          +'</tr>';
      });
      html+='</tbody></table></div></div>';
    });
    contentEl.innerHTML=html;
  }catch(e){
    contentEl.innerHTML='<div class="notif-empty" style="padding:30px;color:var(--red)">❌ 网络错误: '+e+'</div>';
  }
}
function platformEnter(){
  // 进入 tab 默认日期=今天
  var dt=document.getElementById('pf-date');
  if(dt&&!dt.value)dt.value=_platformToday();
  var u=document.getElementById('pf-current-user');
  if(u&&!u.textContent){
    try{
      var name=localStorage.getItem('client_username')||sessionStorage.getItem('client_username')||'';
      u.textContent=name||'(本账号)';
    }catch(e){u.textContent='(本账号)';}
  }
  platformLoad();
}

async function simConfigureFix(btn){var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);
  var id=px+'-'+slot+'-'+style+'-fix';
  var mv=(document.getElementById(id+'-ta')||{}).value||'';
  var mt=(document.getElementById(id+'-muls')||{}).value||'1';
  var ba=parseInt((document.getElementById(id+'-base')||{}).value)||10000;
  var lc=mv.split(String.fromCharCode(10)).filter(function(l){return l.trim();}).length;
  if(lc<1){simMsg2(id,'❌ 至少需要 1 行数字组','var(--red)');return;}
  simMsg2(id,'保存中...','var(--muted)');
  try{
    var d=await fetch('/api/sim/configure_fix',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({slot:slot,group:grp,style:style,fix_text:mv,multipliers_text:mt,base_amount:ba})}).then(r=>r.json());
    simMsg2(id,d.ok?'✅ '+d.msg:'❌ '+d.msg,d.ok?'var(--green)':'var(--red)');
  }catch(e){simMsg2(id,'❌ 网络错误','var(--red)');}
}
async function simConfigureJump(btn){var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);
  var id=px+'-'+slot+'-'+style+'-jump';
  var mv=(document.getElementById(id+'-ta')||{}).value||'';
  var mt=(document.getElementById(id+'-muls')||{}).value||'1';
  var ba=parseInt((document.getElementById(id+'-base')||{}).value)||10000;
  var lc=mv.split(String.fromCharCode(10)).filter(function(l){return l.trim();}).length;
  var mn=mt.split('-').filter(function(x){return x.trim()&&!isNaN(parseFloat(x));}).length;
  if(lc<1){simMsg2(id,'❌ 至少需要 1 行数字组','var(--red)');return;}
  if(lc!==mn){simMsg2(id,'❌ 数字组数（'+lc+'）必须等于倍率个数（'+mn+'）','var(--red)');return;}
  simMsg2(id,'保存中...','var(--muted)');
  try{
    var d=await fetch('/api/sim/configure_jump',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({slot:slot,group:grp,style:style,jump_text:mv,multipliers_text:mt,base_amount:ba})}).then(r=>r.json());
    simMsg2(id,d.ok?'✅ '+d.msg:'❌ '+d.msg,d.ok?'var(--green)':'var(--red)');
  }catch(e){simMsg2(id,'❌ 网络错误','var(--red)');}
}
async function simToggleFixOption(btn){
  var slot=parseInt(btn.dataset.slot);var style=parseInt(btn.dataset.style);var opt=btn.dataset.opt;
  var id='sim-'+slot+'-'+style+'-fix';
  // 当前 UI 状态从按钮文字"开/关"判断（":开"/":关"）
  var curOn=btn.textContent.indexOf('：开')>=0;
  var newVal=!curOn;
  var body={slot:slot,style:style};
  body[opt]=newVal;
  try{
    var d=await fetch('/api/sim/fix_options',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify(body)}).then(r=>r.json());
    if(d.ok){
      simRefresh();
    }else{simMsg2(id,'❌ '+(d.msg||'失败'),'var(--red)');}
  }catch(e){simMsg2(id,'❌ 网络错误','var(--red)');}
}
async function simSetSP(btn){var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);var mode=btn.dataset.mode;
  var id=px+'-'+slot+'-'+style+'-'+mode;
  var sp=parseInt((document.getElementById(id+'-sp')||{}).value)||0;
  try{
    var d=await fetch('/api/sim/stop_profit',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({slot:slot,group:grp,style:style,mode:mode,amount:sp})}).then(r=>r.json());
    simMsg2(id,d.ok?'✅ '+d.msg:'❌ '+d.msg,d.ok?'var(--green)':'var(--red)');
  }catch(e){simMsg2(id,'❌ 网络错误','var(--red)');}
}
async function simStart(btn){var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);var mode=btn.dataset.mode;
  var id=px+'-'+slot+'-'+style+'-'+mode;
  try{
    var d=await fetch('/api/sim/start',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({slot:slot,group:grp,style:style,mode:mode})}).then(r=>r.json());
    simMsg2(id,d.ok?'✅ '+d.msg:'❌ '+d.msg,d.ok?'var(--green)':'var(--red)');
    simRefresh();
  }catch(e){simMsg2(id,'❌ 网络错误','var(--red)');}
}
async function simStop(btn){var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);var mode=btn.dataset.mode;
  var id=px+'-'+slot+'-'+style+'-'+mode;
  try{
    await fetch('/api/sim/stop',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({slot:slot,group:grp,style:style,mode:mode})});
    simMsg2(id,'⏹ 已停止','var(--muted)');simRefresh();
  }catch(e){}
}
async function simReset(btn){var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);var mode=btn.dataset.mode;
  var id=px+'-'+slot+'-'+style+'-'+mode;
  if(!confirm('确认重置？'))return;
  try{
    await fetch('/api/sim/reset',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({slot:slot,group:grp,style:style,mode:mode})});
    simMsg2(id,'🗑 已重置','var(--muted)');simRefresh();
  }catch(e){}
}

function renderSimLogPage2(px,mode,slot,grp,style,logs){
  _initSlotPage(simSlotPage,slot);
  var page=simSlotPage[slot][mode][style];
  var id=px+'-'+slot+'-'+mode+'-'+style;
  var maxPage=Math.max(0,Math.ceil(logs.length/SIM_PAGE_SIZE)-1);
  var lbl=document.getElementById(id+'-pg');
  if(lbl)lbl.textContent=(page+1)+'/'+(maxPage+1);
  var el=document.getElementById(id+'-log');
  if(!el)return;
  var pageLogs=logs.slice(page*SIM_PAGE_SIZE,(page+1)*SIM_PAGE_SIZE);
  if(!pageLogs.length){el.innerHTML='<div class="notif-empty">暂无记录</div>';return;}
  el.innerHTML=pageLogs.map(function(grpLog){
    var rounds=grpLog.rounds||[];
    var gPnl=grpLog.group_pnl||0;
    var lossCount=rounds.filter(function(r){return !r.won && !r.pending;}).length;
    var ended=grpLog.ended;var exhausted=grpLog.exhausted;
    var statusTag=!ended?'<span style="background:#1e3a5f;color:#93c5fd;padding:1px 5px;border-radius:6px;font-size:.68rem">进行中</span>':
      exhausted?'<span style="background:#7c2d12;color:#fdba74;padding:1px 5px;border-radius:6px;font-size:.68rem">爆档</span>':
      '<span style="background:#14532d;color:#86efac;padding:1px 5px;border-radius:6px;font-size:.68rem">中奖</span>';
    var rows=rounds.map(function(r){
      var posList=(r.positions||[]).slice(0,6).join(',')+(r.positions&&r.positions.length>6?'...':'');
      if(r.pending){
        return '<tr style="background:#0f1a2e"><td style="color:var(--muted);font-size:.68rem">'+r.qishu+'</td>'
          +'<td style="color:#475569;font-weight:700">?</td>'
          +'<td style="font-size:.68rem;color:#94a3b8">['+posList+']</td>'
          +'<td style="color:var(--accent)">'+r.multiplier+'x</td>'
          +'<td colspan="2" style="color:#3b82f6;font-size:.68rem;animation:pulse 1s infinite">⏳ 待开奖</td></tr>';
      }
      return '<tr><td style="color:var(--muted);font-size:.68rem">'+r.qishu+'</td>'
        +'<td style="color:var(--yellow);font-weight:700">'+r.result+'</td>'
        +'<td style="font-size:.68rem;color:#94a3b8">['+posList+']</td>'
        +'<td style="color:var(--accent)">'+r.multiplier+'x</td>'
        +'<td>'+(r.won?'<span style="color:var(--green)">中</span>':'<span style="color:var(--red)">不中</span>')+'</td>'
        +'<td style="color:'+fmtColor(r.net_pnl)+';font-weight:700">'+fmtNum(r.net_pnl)+'</td></tr>';
    }).join('');
    var summaryRow='<tr style="background:#1a1d27"><td colspan="3" style="color:var(--muted);font-size:.72rem">共'+rounds.length+'期·不中'+lossCount+'次</td><td colspan="3" style="color:'+fmtColor(gPnl)+';font-weight:700">'+fmtNum(gPnl)+'</td></tr>';
    return '<div style="background:#12151e;border-radius:6px;border:1px solid var(--border);overflow:hidden;margin-bottom:4px">'
      +'<div style="display:flex;align-items:center;justify-content:space-between;padding:5px 8px;border-bottom:1px solid var(--border)">'
      +statusTag+'<span style="font-size:.72rem;color:var(--muted)">不中'+lossCount+'次</span>'
      +'<span style="font-size:.8rem;color:'+fmtColor(gPnl)+';font-weight:800">'+fmtNum(gPnl)+'</span></div>'
      +'<div style="overflow:auto;max-height:'+(28*3+24)+'px"><table style="width:100%;font-size:.72rem;border-collapse:collapse">'
      +'<thead><tr style="background:#0f1117;position:sticky;top:0"><th style="padding:3px 5px">期号</th><th>结果</th><th>数字</th><th>倍</th><th>结果</th><th>盈亏</th></tr></thead>'
      +'<tbody>'+rows+summaryRow+'</tbody></table></div></div>';
  }).join('');
}

// ⭐ 安全填充 input/textarea 的工具：用户改过的值不会被自动刷新覆盖
//   - 当前正在聚焦 → 不动
//   - 当前值跟上次服务端值不一样（说明用户改过） → 不动
//   - 否则同步服务端最新值
function _safeSetVal(el, serverVal){
  if(!el) return;
  var sv = (serverVal === null || serverVal === undefined) ? '' : String(serverVal);
  if(document.activeElement === el) { el.dataset.lastserver = sv; return; }
  var lastSeen = el.dataset.lastserver;
  // 首次填值（lastSeen 未设置）→ 直接覆盖
  if(lastSeen === undefined || lastSeen === null) { el.value = sv; el.dataset.lastserver = sv; return; }
  // 用户改过（当前值 !== 上次服务端值）→ 不动
  if(String(el.value) !== lastSeen) { el.dataset.lastserver = sv; return; }
  el.value = sv;
  el.dataset.lastserver = sv;
}

function simApplySlotData(px,slot,grp,style,data){
  if(!data)return;
  _initSlotPage(simSlotPage,slot);
  (function(){
    ['random','map','fix','jump'].forEach(function(mode){
      // 顶部今日盈亏（按 mode 独立显示，4 套各自一份）
      var pnlValTop = data['total_pnl_'+mode]||0;
      var pnlElTop = document.getElementById('sim-'+mode+'-pnl-'+slot+'-'+style);
      if(pnlElTop){pnlElTop.textContent=fmtNum(pnlValTop);pnlElTop.style.color=fmtColor(pnlValTop);}
      var dateElTop = document.getElementById('sim-'+mode+'-pnl-date-'+slot);
      if(dateElTop)dateElTop.textContent=(data.pnl_date||'')+'  · 每天24点清空';
      var id=px+'-'+slot+'-'+style+'-'+mode;
      var stEl=document.getElementById(id+'-status');
      var runKey=mode+'_running';
      if(stEl){
        if(data[runKey]){stEl.textContent='运行中';stEl.style.background='#14532d';stEl.style.color='#86efac';}
        else{stEl.textContent='已停止';stEl.style.background='#1e2235';stEl.style.color='var(--muted)';}
      }
      var pnlLogEl=document.getElementById(px+'-'+slot+'-'+mode+'-'+style+'-pnl');
      var pnlVal=data['total_pnl_'+mode];
      if(pnlLogEl){pnlLogEl.textContent=fmtNum(pnlVal||0);pnlLogEl.style.color=fmtColor(pnlVal||0);}
      // 止盈回显（_safeSetVal 防止用户改过后被覆盖）
      var spEl=document.getElementById(id+'-sp');
      if(spEl&&data['stop_profit_'+mode]!==undefined) _safeSetVal(spEl, data['stop_profit_'+mode]);
      // 记录
      var logKey='groups_log_'+mode;
      renderSimLogPage2(px,mode,slot,grp,style,data[logKey]||[]);
      // 回显数字组配置（同样脏数据保护）
      var ta=document.getElementById(id+'-ta');
      var mt=document.getElementById(id+'-muls');
      var ba=document.getElementById(id+'-base');
      var textKey=mode==='random'?'groups_text':(mode==='map'?'map_text':(mode==='fix'?'fix_text':'jump_text'));
      if(ta&&data[textKey]!==undefined) _safeSetVal(ta, data[textKey]);
      // 按 mode 回显各自独立的倍率序列+基础金额
      var mulsForMode = data['muls_text_'+mode] || data.muls_text;
      var baseForMode = data['base_amount_'+mode] || data.base_amount;
      if(mt&&mulsForMode!==undefined) _safeSetVal(mt, mulsForMode);
      if(ba&&baseForMode!==undefined) _safeSetVal(ba, baseForMode);
      // 行数标签实时刷新（map/fix/jump）
      if(ta&&(mode==='map'||mode==='fix'||mode==='jump')){
        var lcEl=document.getElementById(id+'-lc');
        if(lcEl){
          var lc=(ta.value||'').split(String.fromCharCode(10)).filter(function(l){return l.trim();}).length;
          if(mode==='map'){
            lcEl.textContent='已输入'+lc+'行/需28行';
            lcEl.style.color=lc===28?'var(--green)':'var(--muted)';
          }else if(mode==='jump'){
            var muls=(mt&&mt.value)||'';
            var mn=muls.split('-').filter(function(x){return x.trim()&&!isNaN(parseFloat(x));}).length;
            lcEl.textContent='已输入'+lc+'行 / 倍率'+mn+'个'+(lc===mn&&lc>0?'（匹配 ✓）':'（必须相等）');
            lcEl.style.color=(lc===mn&&lc>0)?'var(--green)':'var(--red)';
          }else{
            lcEl.textContent='已输入'+lc+'行';
            lcEl.style.color=lc>0?'var(--green)':'var(--muted)';
          }
        }
      }
      // 固定模式：两个开关按钮文字回显
      if(mode==='fix'){
        var sowBtn=document.getElementById(id+'-sow');
        var soeBtn=document.getElementById(id+'-soe');
        if(sowBtn){
          var on1=!!data.fix_stop_on_win;
          sowBtn.textContent='🎯 中了就停：'+(on1?'开':'关');
          sowBtn.style.background=on1?'var(--accent)':'';
          sowBtn.style.color=on1?'#fff':'';
        }
        if(soeBtn){
          var on2=!!data.fix_stop_on_exhaust;
          soeBtn.textContent='📛 倍率打完就停：'+(on2?'开':'关');
          soeBtn.style.background=on2?'var(--accent)':'';
          soeBtn.style.color=on2?'#fff':'';
        }
      }
      // 真实参与 UI 同步
      var realOnFromServer = !!data['real_enabled_'+mode];
      simApplyRealUIState(px+'-'+slot+'-'+style+'-'+mode, realOnFromServer);
    });
  })();
}

var _simFetching=false;
async function simRefresh(){
  if(_simFetching)return;_simFetching=true;
  try{
    // 4 个 tab 各自当前 slot 拉数据；去重避免重复拉
    var slotR=simCurrentSlotRandom||1;
    var slotM=simCurrentSlotMap||1;
    var slotF=simCurrentSlotFix||1;
    var slotJ=simCurrentSlotJump||1;
    var seen={};
    var slots=[];
    [slotR,slotM,slotF,slotJ].forEach(function(s){
      if(!seen[s]){seen[s]=1;slots.push(s);}
    });
    var reqs=[];
    slots.forEach(function(s){
      reqs.push(fetch('/api/sim/status?style=210&slot='+s+'&group=1').then(r=>r.json()));
      reqs.push(fetch('/api/sim/status?style=60&slot='+s+'&group=1').then(r=>r.json()));
    });
    var results=await Promise.all(reqs);
    slots.forEach(function(s,i){
      var d210=results[i*2], d60=results[i*2+1];
      if(d210&&d210.ok){simSlotData[s]=simSlotData[s]||{};simSlotData[s][210]=d210.data;simApplySlotData('sim',s,1,210,d210.data);}
      if(d60&&d60.ok){simSlotData[s]=simSlotData[s]||{};simSlotData[s][60]=d60.data;simApplySlotData('sim',s,1,60,d60.data);}
    });
  }catch(e){}finally{_simFetching=false;}
}
setInterval(simRefresh,2000);
setInterval(function(){if(typeof localCD!=='undefined'&&localCD<=10)simRefresh();},1500);

// ══ 历史DB查询 ══
function simOpenDBHistory(btn){
  var px=btn.dataset.px;var slot=parseInt(btn.dataset.slot);
  var grp=parseInt(btn.dataset.grp);var style=parseInt(btn.dataset.style);
  var mode=btn.dataset.mode;
  var today=new Date().toISOString().slice(0,10);
  simQueryDB(px,slot,grp,style,mode,today);
}
function simDBDateBtn(btn){
  simQueryDB(btn.dataset.px,parseInt(btn.dataset.slot),parseInt(btn.dataset.grp),
    parseInt(btn.dataset.style),btn.dataset.mode,btn.dataset.date);
}


var missAllRecs={210:[],60:[]};
var missPage2={210:0,60:0};
var MISS_PAGE=10;

async function missConfigure(btn){
  var style=btn.dataset.style;
  var gt=document.getElementById('miss-groups-'+style).value.trim();
  var mt=document.getElementById('miss-muls-'+style).value.trim();
  var ba=parseInt(document.getElementById('miss-base-'+style).value)||10000;
  var mn=parseInt(document.getElementById('miss-n-'+style).value)||5;
  var msg=document.getElementById('miss-msg-'+style);
  if(!gt){msg.textContent='❌ 请填写遗漏数字组';msg.style.color='var(--red)';return;}
  msg.textContent='保存中...';msg.style.color='var(--muted)';
  try{
    var d=await fetch('/api/miss/configure',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({style:parseInt(style),groups_text:gt,muls_text:mt,base_amount:ba,miss_n:mn})}).then(r=>r.json());
    msg.textContent=d.ok?'✅ '+d.msg:'❌ '+d.msg;msg.style.color=d.ok?'var(--green)':'var(--red)';
  }catch(e){msg.textContent='❌ 网络错误';msg.style.color='var(--red)';}
}
async function missExecute(btn){
  if(btn.disabled)return;
  var style=btn.dataset.style;
  var msg=document.getElementById('miss-msg-'+style);
  btn.disabled=true;
  var origText=btn.textContent;
  btn.textContent='检测中...';
  msg.textContent='检测中...';msg.style.color='var(--muted)';
  try{
    var d=await fetch('/api/miss/execute',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({style:parseInt(style)})}).then(r=>r.json());
    msg.textContent=d.ok?'✅ '+d.msg:'❌ '+d.msg;msg.style.color=d.ok?'var(--green)':'var(--red)';
    missRefresh();
    // 真实参与已搬到服务端：MissEngine.execute 收到 real_enabled 开关后自动触发下单
  }catch(e){msg.textContent='❌ 网络错误';msg.style.color='var(--red)';}
  finally{
    // 3秒后允许再次点击
    setTimeout(function(){btn.disabled=false;btn.textContent=origText;},3000);
  }
}

// ══════════════════════════════════════════════════════════════
//  🔍 遗漏检测 - 真实参与开关（服务端持久化）
// ══════════════════════════════════════════════════════════════

async function missToggleReal(style){
  // UI 当前状态从边框色判断（绝对状态由服务端 status 给出）
  var wrap=document.getElementById('miss-real-wrap-'+style);
  var currOn=wrap&&wrap.style.borderColor==='rgb(220, 38, 38)';
  if(!currOn){
    var ok=confirm('打开后，遗漏检测命中时会真实参与下注，下单已登录的所有平台账号。即使关闭浏览器也照常下。确认开启？');
    if(!ok)return;
  }
  var newOn=!currOn;
  try{
    var d=await fetch('/api/miss/real/toggle',{
      method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({style:parseInt(style),on:newOn})
    }).then(r=>r.json());
    if(!d.ok){alert('切换失败: '+(d.msg||'未知'));return;}
    missApplyRealUI(style, newOn);
  }catch(e){alert('网络错误: '+e);}
}

function missApplyRealUI(style, on){
  var wrap=document.getElementById('miss-real-wrap-'+style);
  var lbl=document.getElementById('miss-real-lbl-'+style);
  var btn=document.getElementById('miss-real-btn-'+style);
  var knob=document.getElementById('miss-real-knob-'+style);
  if(on){
    if(wrap){wrap.style.background='linear-gradient(90deg,#7c3aed33,#dc262633)';wrap.style.borderColor='rgb(220, 38, 38)';}
    if(lbl){lbl.textContent='🔴 真实参与 已开启（服务端跟单）';lbl.style.color='#f87171';}
    if(btn)btn.style.background='#dc2626';
    if(knob)knob.style.left='23px';
  }else{
    if(wrap){wrap.style.background='#12151e';wrap.style.borderColor='#374151';}
    if(lbl){lbl.textContent='⚫ 真实参与 已关闭';lbl.style.color='var(--muted)';}
    if(btn)btn.style.background='#374151';
    if(knob)knob.style.left='3px';
  }
}

// 兼容旧调用名
function missRenderRealUI(style){
  // 不再从 localStorage 读取；如有需要刷一次 status 让 missApplyRealUI 同步
  if(typeof missRefresh==='function')missRefresh();
}


async function missReset(btn){
  var style=btn.dataset.style;
  var gameLabel=style==='210'?'欢乐210':'比特60';
  if(!confirm('⚠️ 删除记录将无法恢复\\n本系统所有该数据全部删除\\n是否确认删除「'+gameLabel+'」全部遗漏检测历史记录？\\n（配置保留）'))return;
  await fetch('/api/miss/reset',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({style:parseInt(style)})});
  missRefresh();
}
async function missToggleAuto(btn){
  var style=btn.dataset.style;
  var on=btn.dataset.on!=='1';
  try{
    await fetch('/api/miss/auto',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({style:parseInt(style),enabled:on})});
    missRefresh();
  }catch(e){
    var msg=document.getElementById('miss-msg-'+style);
    if(msg){msg.textContent='❌ 设置失败';msg.style.color='var(--red)';}
  }
}
function missPage(style,dir){
  var total=missAllRecs[style].length;
  var maxPage=Math.max(0,Math.ceil(total/MISS_PAGE)-1);
  missPage2[style]=Math.max(0,Math.min(maxPage,missPage2[style]+dir));
  renderMissLog(style);
}
function renderMissLog(style){
  var recs=missAllRecs[style];var page=missPage2[style];
  var maxPage=Math.max(0,Math.ceil(recs.length/MISS_PAGE)-1);
  var lbl=document.getElementById('miss-page-label-'+style);
  if(lbl)lbl.textContent='第'+(page+1)+'页/共'+(maxPage+1)+'页';
  var el=document.getElementById('miss-log-'+style);
  if(!el)return;
  var pageRecs=recs.slice(page*MISS_PAGE,(page+1)*MISS_PAGE);
  if(!pageRecs.length){el.innerHTML='<div class="notif-empty">暂无记录</div>';return;}
  el.innerHTML='<table style="width:100%;font-size:.78rem;border-collapse:collapse">'
    +'<thead><tr style="background:#0f1117"><th style="padding:3px 6px">期号</th><th>结果</th><th>标签</th><th>下注数字</th><th>倍数</th><th>结果</th><th>盈亏</th></tr></thead>'
    +'<tbody>'+pageRecs.map(function(r){
      var posList=(r.positions||[]).slice(0,6).join(',')+(r.positions&&r.positions.length>6?'...':'');
      var labelTag='<span style="color:#f59e0b">'+(r.label||r.type||'遗漏')+'</span>';
      if(r.pending)return '<tr><td style="color:var(--muted);font-size:.7rem">'+(r.qishu||'--')+'</td>'
        +'<td style="color:#475569;font-weight:700">?</td><td>'+labelTag+'</td>'
        +'<td style="font-size:.7rem;color:#94a3b8">['+posList+']</td>'
        +'<td style="color:var(--accent)">'+r.multiplier+'x</td>'
        +'<td colspan="2" style="color:#93c5fd;text-align:center">⏳ 待开奖</td></tr>';
      var wonStr=r.won?'<span style="color:var(--green)">中</span>':'<span style="color:var(--red)">不中</span>';
      var pnlStr='<span style="color:'+fmtColor(r.net_pnl)+';font-weight:700">'+fmtNum(r.net_pnl)+'</span>';
      return '<tr><td style="color:var(--muted);font-size:.7rem">'+r.qishu+'</td>'
        +'<td style="color:var(--yellow);font-weight:700">'+r.result+'</td>'
        +'<td>'+labelTag+'</td><td style="font-size:.7rem;color:#94a3b8">['+posList+']</td>'
        +'<td style="color:var(--accent)">'+r.multiplier+'x</td>'
        +'<td>'+wonStr+'</td><td>'+pnlStr+'</td></tr>';
    }).join('')+'</tbody></table>';
}
// ⭐ bug 6：给遗漏检测输入框加 userTouched 标记，用户改过就不让 missRefresh 覆盖
(function bindMissInputTouch(){
  function bind(){
    ['miss-groups-210','miss-groups-60','miss-muls-210','miss-muls-60',
     'miss-base-210','miss-base-60','miss-n-210','miss-n-60'].forEach(function(id){
      var el=document.getElementById(id);
      if(el && !el._touchBound){
        el._touchBound = true;
        el.addEventListener('input',function(){el.dataset.userTouched='1';});
        el.addEventListener('focus',function(){el.dataset.userTouched='1';});
      }
    });
  }
  if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',bind);
  else bind();
  // 标签切换后元素可能重渲染，再绑一次
  setInterval(bind, 5000);
})();

async function missRefresh(){
  try{
    var d=await fetch('/api/miss/status').then(r=>r.json());
    if(!d.ok)return;
    var s=d.data;
    ['210','60'].forEach(function(style){
      var pnlVal=style==='210'?s.total_pnl_210:s.total_pnl_60;
      var pnlEl=document.getElementById('miss-pnl-'+style);
      if(pnlEl){pnlEl.textContent=fmtNum(pnlVal);pnlEl.style.color=fmtColor(pnlVal);}
      var logPnlEl=document.getElementById('miss-log-pnl-'+style);
      if(logPnlEl){logPnlEl.textContent=fmtNum(pnlVal);logPnlEl.style.color=fmtColor(pnlVal);}
      var ab=document.getElementById('miss-auto-btn-'+style);
      if(ab){
        var on=!!(style==='210'?s.auto_enabled_210:s.auto_enabled_60);
        ab.dataset.on=on?'1':'0';
        ab.textContent=on?'开':'关';
        ab.style.background=on?'#166534':'#1e2235';
        ab.style.color=on?'#dcfce7':'var(--muted)';
      }
      var gtKey=style==='210'?'groups_text':'groups_text';
      var gt=document.getElementById('miss-groups-'+style);
      var mt=document.getElementById('miss-muls-'+style);
      var ba=document.getElementById('miss-base-'+style);
      var mn=document.getElementById('miss-n-'+style);
      // ⭐ bug 6 修复：输入框只在首次（空值）时从服务端填充；
      //   一旦用户输过任何值（哪怕保存前焦点已移开），就不再自动覆盖，
      //   避免每3秒轮询把用户正在编辑的内容刷回去。
      if(gt && !gt.dataset.userTouched && !gt.value.trim() && s.groups_text){
        gt.value=s.groups_text;
      }
      if(mt && !mt.dataset.userTouched && !mt.value.trim() && s.muls_text){
        mt.value=s.muls_text;
      }
      if(ba && !ba.dataset.userTouched && (!ba.value || ba.value==='10000') && s.base_amount){
        ba.value=s.base_amount;
      }
      if(mn && !mn.dataset.userTouched && (!mn.value || mn.value==='5') && s.miss_n){
        mn.value=s.miss_n;
      }
      // 真实参与开关 UI 同步（服务端持久化）
      var realOn=!!(style==='210'?s.real_enabled_210:s.real_enabled_60);
      if(typeof missApplyRealUI==='function')missApplyRealUI(style, realOn);
    });
    var dateEl=document.getElementById('miss-pnl-date');
    if(dateEl)dateEl.textContent=(s.pnl_date||'')+'  · 每天24点清空';
    missAllRecs[210]=s.records_210||[];
    missAllRecs[60]=s.records_60||[];
    renderMissLog(210);renderMissLog(60);
  }catch(e){}
}
setInterval(missRefresh,3000);

// ══ 历史记录Tab ══
function simOpenDBHistory(btn){
  // 跳转到历史Tab并预填条件
  var grp=parseInt(btn.dataset.grp);
  var slot=parseInt(btn.dataset.slot);
  var style=btn.dataset.style;
  var mode=btn.dataset.mode;
  var gsel=document.getElementById('hist-group');
  var ssel=document.getElementById('hist-style');
  var msel=document.getElementById('hist-mode');
  if(gsel)gsel.value=grp+'-'+slot;
  if(ssel)ssel.value=style;
  if(msel)msel.value=mode;
  switchTab('history');
}
function simDBDateBtn(btn){
  var dsel=document.getElementById('hist-date');
  if(dsel)dsel.value=btn.dataset.date;
  historyTabLoad();
}
async function historyTabLoad(){
  if(typeof _histType!=='undefined'&&_histType==='real'){historyRealLoad();return;}
  var style=parseInt((document.getElementById('hist-style')||{}).value||'210');
  var grp=1;var slot=1;
  var mode=(document.getElementById('hist-mode')||{}).value||'random';
  var dateVal=(document.getElementById('hist-date')||{}).value||'';
  var today=new Date().toISOString().slice(0,10);
  var date=dateVal||today;
  var container=document.getElementById('hist-content');
  if(container)container.innerHTML='<div class="notif-empty">加载中...</div>';
  try{
    var url='/api/sim/history_db?slot='+slot+'&group='+grp+'&style='+style+'&mode='+mode+'&date='+date;
    var data=await fetch(url).then(function(r){return r.json();});
    if(!data.ok){if(container)container.innerHTML='<div class="notif-empty">加载失败</div>';return;}
    // 更新日期选项
    var dsel=document.getElementById('hist-date');
    if(dsel){
      var cur=dsel.value||today;
      dsel.innerHTML=(data.dates||[]).map(function(d){
        return '<option value="'+d+'"'+(d===cur?' selected':'')+'>'+d+'</option>';
      }).join('')||'<option value="'+today+'">'+today+'</option>';
    }
    // 显示盈亏
    var pnlEl=document.getElementById('hist-pnl');
    if(pnlEl){pnlEl.textContent=date+' 总盈亏: '+fmtNum(data.daily_pnl||0);pnlEl.style.color=fmtColor(data.daily_pnl||0);}
    var groups=data.groups||[];
    if(!groups.length){if(container)container.innerHTML='<div class="notif-empty">该日期暂无记录</div>';return;}
    var html=groups.map(function(g){
      var rounds=g.rounds||[];
      var gPnl=g.group_pnl||0;
      var lossCount=rounds.filter(function(r){return !r.won&&!r.pending;}).length;
      var statusTag=g.exhausted
        ?'<span style="background:#7c2d12;color:#fdba74;padding:2px 8px;border-radius:6px;font-size:.75rem">爆档</span>'
        :'<span style="background:#14532d;color:#86efac;padding:2px 8px;border-radius:6px;font-size:.75rem">中奖</span>';
      var roundRows=rounds.map(function(r){
        // ⭐ bug 9：完整显示所有数字 + 加下单时间
        var posList=(r.positions||[]).join(',');
        var timeStr=r.created_at?(r.created_at.length>=19?r.created_at.slice(11,19):r.created_at):'--';
        var resCell=r.pending
          ?'<td colspan="3" style="color:#93c5fd;text-align:center;padding:4px">⏳ 待开奖</td>'
          :'<td style="color:#fbbf24;font-weight:700;padding:4px">'+r.result+'</td>'
           +'<td>'+(r.won?'<span style="color:#4ade80">中</span>':'<span style="color:#f87171">不中</span>')+'</td>'
           +'<td style="color:'+fmtColor(r.net_pnl)+';font-weight:700">'+fmtNum(r.net_pnl)+'</td>';
        return '<tr style="border-bottom:1px solid #1e293b">'
          +'<td style="color:#64748b;font-size:.7rem;padding:4px 6px">'+r.qishu+'</td>'
          +'<td style="color:#64748b;font-size:.68rem;padding:4px;white-space:nowrap">'+timeStr+'</td>'
          +'<td style="font-size:.7rem;color:#94a3b8;padding:4px;word-break:break-all">['+posList+']</td>'
          +'<td style="color:#60a5fa;padding:4px">'+r.multiplier+'x</td>'
          +resCell+'</tr>';
      }).join('');
      var sumRow='<tr style="background:#0a0d14"><td colspan="4" style="color:#64748b;font-size:.72rem;padding:4px 6px">共'+rounds.length+'期·不中'+lossCount+'次</td>'
        +'<td colspan="3" style="color:'+fmtColor(gPnl)+';font-weight:700;padding:4px">'+fmtNum(gPnl)+'</td></tr>';
      return '<div class="card" style="padding:0;overflow:hidden">'
        +'<div style="display:flex;align-items:center;justify-content:space-between;padding:8px 12px;border-bottom:1px solid var(--border)">'
        +statusTag+'<span style="font-size:.78rem;color:var(--muted)">不中'+lossCount+'次</span>'
        +'<span style="font-size:.9rem;color:'+fmtColor(gPnl)+';font-weight:800">'+fmtNum(gPnl)+'</span></div>'
        +'<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:.78rem">'
        +'<thead><tr style="background:#0f1117"><th style="padding:4px 6px;color:#64748b;text-align:left">期号</th>'
        +'<th style="color:#64748b;text-align:left">时间</th>'
        +'<th style="color:#64748b;text-align:left">数字</th><th style="color:#64748b">倍数</th>'
        +'<th style="color:#64748b">结果</th><th style="color:#64748b">中奖</th><th style="color:#64748b">盈亏</th></tr></thead>'
        +'<tbody>'+roundRows+sumRow+'</tbody></table></div></div>';
    }).join('');
    if(container)container.innerHTML=html;
  }catch(e){if(container)container.innerHTML='<div class="notif-empty">加载失败: '+e.message+'</div>';}
}
var _histType='sim';
function histSwitchType(type){
  _histType=type;
  document.getElementById('hist-type-sim').style.background=type==='sim'?'var(--accent)':'transparent';
  document.getElementById('hist-type-sim').style.color=type==='sim'?'#fff':'var(--muted)';
  document.getElementById('hist-type-real').style.background=type==='real'?'var(--accent)':'transparent';
  document.getElementById('hist-type-real').style.color=type==='real'?'#fff':'var(--muted)';
  document.getElementById('hist-sim-filters').style.display=type==='sim'?'':'none';
  document.getElementById('hist-real-filters').style.display=type==='real'?'':'none';
  document.getElementById('hist-content').innerHTML='<div class="notif-empty">请选择条件后点查询</div>';
}
var _histRealTimer=null;
function historyRealToggleAuto(){
  var cb=document.getElementById('hist-real-autoref');
  if(cb&&cb.checked){
    if(_histRealTimer)clearInterval(_histRealTimer);
    _histRealTimer=setInterval(historyRealLoad,5000);
  }else{
    if(_histRealTimer){clearInterval(_histRealTimer);_histRealTimer=null;}
  }
}
async function historyRealLoad(){
  var game=(document.getElementById('hist-real-game')||{}).value||'210';
  var dateEl=document.getElementById('hist-real-date');
  var dateStr=dateEl&&dateEl.value?dateEl.value:'';
  if(!dateStr){
    var today=new Date();
    dateStr=today.getFullYear()+'-'+String(today.getMonth()+1).padStart(2,'0')+'-'+String(today.getDate()).padStart(2,'0');
    if(dateEl)dateEl.value=dateStr;
  }
  var limitEl=document.getElementById('hist-real-limit');
  var limit=limitEl?(parseInt(limitEl.value)||50):50;
  var groupBy=document.getElementById('hist-real-groupby');
  var groupByAcc=!!(groupBy&&groupBy.checked);
  var container=document.getElementById('hist-content');
  if(container&&!container.querySelector('table'))container.innerHTML='<div class="notif-empty">加载中（调石头岛接口拉记录中）...</div>';
  try{
    // ⭐ 使用公共函数拉数据
    var allRecords=await fetchShitoudOrders(parseInt(game), limit);
    // ⭐ bug 8：石头岛接口不返回 createTime，按日期过滤会把所有记录干掉，所以不再过滤
    // 日期选项保留只为兼容旧本地 DB 数据；当数据没时间字段时全部展示
    if(dateStr){
      var filtered=allRecords.filter(function(o){
        var t=o.createTime||o.openTime||'';
        // 没时间字段的石头岛直拉数据：默认显示（视为当前日期）
        if(!t)return true;
        return t.length>=10 && t.slice(0,10)===dateStr;
      });
      allRecords=filtered;
    }
    // 补充 source（从本地 recent_orders）
    try{
      var local=await fetch('/api/std/recent_orders?limit=500').then(function(r){return r.json();});
      if(local&&local.ok&&local.data){
        var sourceMap={};
        Object.keys(local.data).forEach(function(uid){
          ['60','210'].forEach(function(g){
            (local.data[uid][g]||[]).forEach(function(r){
              if(r.source)sourceMap[uid+':'+r.qishu]=r.source;
            });
          });
        });
        allRecords.forEach(function(o){var k=o.uid+':'+o.qishu;if(sourceMap[k])o.source=sourceMap[k];});
      }
    }catch(e){console.warn('[historyRealLoad] source',e);}
    // 按来源筛选（前端）
    var srcSel=(document.getElementById('hist-real-source')||{}).value||'';
    if(srcSel){
      allRecords=allRecords.filter(function(o){
        var s=o.source||'';
        if(srcSel==='normal')return !s||s==='normal'||s==='manual';
        if(srcSel==='miss')return s.indexOf('miss')===0;
        return s===srcSel;
      });
    }
    if(!allRecords.length){
      if(container)container.innerHTML='<div class="notif-empty">'+dateStr+' 暂无下单记录</div>';
      return;
    }
    // 汇总
    var gameLabel=game==='60'?'⚡ 比特60':'🎮 欢乐210';
    var totBet=0,totWin=0,winCnt=0,pendCnt=0;
    allRecords.forEach(function(o){
      totBet+=o.betAmount;
      totWin+=o.winAmount;
      if(o.pending)pendCnt++;
      else if(o.winAmount>0)winCnt++;
    });
    var totPnl=totWin-totBet;
    var accCount={};
    allRecords.forEach(function(o){accCount[o.uid]=1;});
    var summary='<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;flex-wrap:wrap;gap:8px">'
      +'<div style="font-weight:700;color:var(--text);font-size:.88rem">'+gameLabel+' · '+dateStr+' · 共 '+allRecords.length+' 单 · 跨 '+Object.keys(accCount).length+' 个账号</div>'
      +'<div style="font-size:.78rem;color:var(--muted)">'
      +'已开奖 '+(allRecords.length-pendCnt)+' · 中 '+winCnt+' · 待开奖 <b style="color:#60a5fa">'+pendCnt+'</b>'
      +' · 投入 <b style="color:var(--text)">'+totBet.toLocaleString()+'</b>'
      +' · 返奖 <b style="color:var(--green)">'+totWin.toLocaleString()+'</b>'
      +' · 盈亏 <b style="color:'+fmtColor(totPnl)+'">'+fmtNum(totPnl)+'</b>'
      +'</div></div>';
    var html=summary;
    if(groupByAcc){
      // B1：按账号分组
      var byAcc={};
      allRecords.forEach(function(o){
        if(!byAcc[o.uid])byAcc[o.uid]={tel:o.tel,remark:o.remark,records:[]};
        byAcc[o.uid].records.push(o);
      });
      html+=Object.keys(byAcc).map(function(uid){
        var grp=byAcc[uid];
        var telDisplay=grp.tel?(grp.tel.slice(0,3)+'****'+grp.tel.slice(7)):uid.slice(0,8);
        if(grp.remark)telDisplay=grp.remark+' · '+telDisplay;
        var gBet=0,gWin=0;
        grp.records.forEach(function(o){gBet+=o.betAmount;gWin+=o.winAmount;});
        var gPnl=gWin-gBet;
        return '<div class="card" style="padding:10px;margin-bottom:12px">'
          +'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;border-bottom:1px solid var(--border);padding-bottom:6px">'
            +'<div style="font-size:.88rem;font-weight:800;color:var(--text)">👤 '+telDisplay+' · '+grp.records.length+' 单</div>'
            +'<div style="font-size:.78rem;color:var(--muted)">投入 '+gBet.toLocaleString()+' · 返奖 <b style="color:var(--green)">'+gWin.toLocaleString()+'</b> · 盈亏 <b style="color:'+fmtColor(gPnl)+'">'+fmtNum(gPnl)+'</b></div>'
          +'</div>'
          +_histRenderTable(grp.records,false)
        +'</div>';
      }).join('');
    }else{
      html+=_histRenderTable(allRecords,true);
    }
    if(container)container.innerHTML=html;
  }catch(e){
    if(container)container.innerHTML='<div class="notif-empty">加载失败: '+(e&&e.message||e)+'</div>';
  }
}

// 渲染历史记录表格（共享，分组/不分组都用它）
// records 字段：{qishu, uid, tel, betAmount, winAmount, result, createTime, pending, press_str, source}
function _histRenderTable(records, showAccCol){
  var html='<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:.78rem">'
    +'<thead><tr style="background:#0f1117">'
    +'<th style="padding:6px 8px;text-align:left;color:var(--muted)">期号</th>'
    +(showAccCol?'<th style="text-align:left;color:var(--muted)">账号</th>':'')
    +'<th style="text-align:left;color:var(--muted)">时间</th>'
    +'<th style="text-align:left;color:var(--muted)">来源</th>'
    +'<th style="text-align:right;color:var(--muted)">开奖</th>'
    +'<th style="text-align:left;color:var(--muted)">投注详情</th>'
    +'<th style="text-align:right;color:var(--muted)">投入</th>'
    +'<th style="text-align:right;color:var(--muted)">获得</th>'
    +'<th style="text-align:right;color:var(--muted)">盈亏</th>'
    +'</tr></thead><tbody>';
  records.forEach(function(o){
    var bet=parseInt(o.betAmount)||0;
    var win=parseInt(o.winAmount)||0;
    var pnl=win-bet;
    var pending=!!o.pending;
    var t=(o.createTime||'').slice(5,16);
    var tel=o.tel?(o.tel.slice(0,3)+'****'+o.tel.slice(7)):(o.uid||'').slice(0,6);
    // 投注详情：只显示非0
    var pressDisplay='';
    try{
      var parts=(o.press_str||'').split(',');
      var nz=[];
      for(var i=0;i<parts.length;i++){
        var v=parseInt(parts[i],10);
        if(!isNaN(v)&&v>0)nz.push('<span style="color:#94a3b8">'+i+'</span>:<b style="color:#e2e8f0">'+v.toLocaleString()+'</b>');
      }
      pressDisplay=nz.length?nz.join(' · '):'--';
    }catch(e){pressDisplay='--';}
    // 来源（模拟参与按 random/map/fix/jump 拆分）
    var srcCell;
    if((o.source && (o.source==='miss' || o.source.indexOf('miss')===0))){
      srcCell='<td style="padding:6px 4px"><span style="color:#fbbf24;font-size:.7rem;background:#f5910022;border:1px solid #f59e00;border-radius:4px;padding:1px 5px;white-space:nowrap">🔍 遗漏植入</span></td>';
    }else if(o.source==='sim_random'){
      srcCell='<td style="padding:6px 4px"><span style="color:#c084fc;font-size:.7rem;background:#a855f722;border:1px solid #a855f7;border-radius:4px;padding:1px 5px;white-space:nowrap">🎲 随机下植入</span></td>';
    }else if(o.source==='sim_map'){
      srcCell='<td style="padding:6px 4px"><span style="color:#67e8f9;font-size:.7rem;background:#06b6d422;border:1px solid #06b6d4;border-radius:4px;padding:1px 5px;white-space:nowrap">🎯 开某投某植入</span></td>';
    }else if(o.source==='sim_fix'){
      srcCell='<td style="padding:6px 4px"><span style="color:#86efac;font-size:.7rem;background:#16a34a22;border:1px solid #16a34a;border-radius:4px;padding:1px 5px;white-space:nowrap">📌 固定植入</span></td>';
    }else if(o.source==='sim_jump'){
      srcCell='<td style="padding:6px 4px"><span style="color:#f9a8d4;font-size:.7rem;background:#ec489922;border:1px solid #ec4899;border-radius:4px;padding:1px 5px;white-space:nowrap">🔀 跳转植入</span></td>';
    }else if(o.source && (o.source==='dawei' || o.source.indexOf('dawei')===0)){
      srcCell='<td style="padding:6px 4px"><span style="color:#67e8f9;font-size:.7rem;background:#22d3ee22;border:1px solid #22d3ee;border-radius:4px;padding:1px 5px;white-space:nowrap">🎯 打尾植入</span></td>';
    }else if(o.source && (o.source==='plan' || o.source.indexOf('plan')===0)){
      srcCell='<td style="padding:6px 4px"><span style="color:#bef264;font-size:.7rem;background:#84cc1622;border:1px solid #84cc16;border-radius:4px;padding:1px 5px;white-space:nowrap">📋 计划跟投</span></td>';
    }else if((o.source && (o.source==='sim' || o.source.indexOf('sim')===0))){
      srcCell='<td style="padding:6px 4px"><span style="color:#c084fc;font-size:.7rem;background:#a855f722;border:1px solid #a855f7;border-radius:4px;padding:1px 5px;white-space:nowrap">🎲 模拟</span></td>';
    }else{
      srcCell='<td style="padding:6px 4px;color:var(--muted);font-size:.7rem">手动</td>';
    }
    var rowBg='',openCell,winCell,pnlCell;
    if(pending){
      rowBg='background:#1e3a8a22;';
      openCell='<td style="padding:6px 4px;text-align:right;color:#60a5fa;font-weight:700">⏳待开奖</td>';
      winCell='<td style="padding:6px 4px;text-align:right;color:var(--muted)">--</td>';
      pnlCell='<td style="padding:6px 4px;text-align:right;color:var(--muted)">--</td>';
    }else{
      openCell='<td style="padding:6px 4px;text-align:right"><b style="color:var(--yellow);font-size:.95rem;background:#0c0e14;border:1px solid var(--yellow);border-radius:5px;padding:1px 8px">'+o.result+'</b></td>';
      winCell='<td style="padding:6px 4px;text-align:right;color:'+(win>0?'var(--green)':'var(--muted)')+'">'+fmtNum(win)+'</td>';
      pnlCell='<td style="padding:6px 4px;text-align:right;color:'+fmtColor(pnl)+';font-weight:700">'+fmtNum(pnl)+'</td>';
    }
    html+='<tr style="border-bottom:1px solid var(--border);'+rowBg+'">'
      +'<td style="padding:6px 8px;color:var(--muted);font-size:.7rem">'+o.qishu+'</td>'
      +(showAccCol?'<td style="padding:6px 4px;color:var(--muted);font-size:.7rem">'+tel+'</td>':'')
      +'<td style="padding:6px 4px;color:var(--muted);font-size:.7rem;white-space:nowrap">'+t+'</td>'
      +srcCell
      +openCell
      +'<td style="padding:6px 4px;font-size:.7rem;max-width:280px;word-break:break-all">'+pressDisplay+'</td>'
      +'<td style="padding:6px 4px;text-align:right">'+fmtNum(bet)+'</td>'
      +winCell+pnlCell
      +'</tr>';
  });
  html+='</tbody></table></div>';
  return html;
}

"""





MONITOR_HTML = """
<div id="tab-monitor" class="tab-content active">
  <div style="display:flex;gap:12px;flex-wrap:wrap;align-items:flex-start">
    <div class="card" style="flex:1;min-width:340px">
      <div class="card-title">🎮 欢乐210 · 最新 50 期开奖结果</div>
      <div class="table-wrap">
        <table>
          <thead><tr><th>期号</th><th>合计</th><th>尾数</th><th>大小</th><th>单双</th><th>命中</th></tr></thead>
          <tbody id="tbody"></tbody>
        </table>
      </div>
    </div>
    <div class="card" style="flex:1;min-width:300px">
      <div class="card-title">⚡ 比特60 · 最新开奖结果</div>
      <div class="table-wrap">
        <table>
          <thead><tr><th>期号</th><th>合计</th><th>大小</th><th>单双</th></tr></thead>
          <tbody id="tbody-60"></tbody>
        </table>
      </div>
    </div>
  </div>
  <span id="mode-text" style="display:none"></span>
  <span id="last-qishu" style="display:none"></span>
  <div id="notif-list" style="display:none"></div>
</div>
"""

def _platform_rewrite(html):
    """🔀 把 HTML/JS 里 hardcode 的'石头岛/🪨'按当前 PLATFORM 替换。
    石头岛部署：不动；鲸鱼部署：石头岛→鲸鱼、🪨→🐋。"""
    if IS_SHITOUD or not html:
        return html
    return html.replace("石头岛", "鲸鱼").replace("🪨", "🐋")

def build_client_html(username, user_info):
    expires = user_info.get("expires_at","") if user_info else ""
    switch_tab_js = (
        'function switchTab(name){'
        'var tabs=["monitor","accounts","order","realorder","sim-random","sim-map","sim-fix","sim-jump","miss","dawei","plan","platform","history"];'
        'document.querySelectorAll(".tab").forEach(function(el,i){el.classList.toggle("active",tabs[i]===name);});'
        'document.querySelectorAll(".tab-content").forEach(function(el){el.classList.remove("active");});'
        'document.getElementById("tab-"+name).classList.add("active");'
        'var sel=document.querySelector(".tab-select");if(sel)sel.value=name;'
        'if(name==="accounts"){refreshAccounts();var u=document.getElementById("inp-uniqid");if(!u||!u.value)loadCaptcha();}'
        'if(name==="order"){getExpect210();getExpect60();}'
        'if(name==="realorder"){if(typeof roEnter==="function")roEnter();}'
        'if(name==="sim-random"){simRenderSlot(simCurrentSlotRandom||1,"random");simRefresh();}'
        'if(name==="sim-map"){simRenderSlot(simCurrentSlotMap||1,"map");simRefresh();}'
        'if(name==="sim-fix"){simRenderSlot(simCurrentSlotFix||1,"fix");simRefresh();}'
        'if(name==="sim-jump"){simRenderSlot(simCurrentSlotJump||1,"jump");simRefresh();}'
        'if(name==="miss"){missRefresh();}'
        'if(name==="dawei"){daweiSelectSlot(daweiCurrentSlot||1);daweiStartAutoRefresh();}'
        'if(name==="plan"){if(typeof planEnter==="function")planEnter();}'
        'if(name==="platform"){if(typeof platformEnter==="function")platformEnter();}'
        'if(name==="history"){historyTabLoad();}'
        '}'
    )
    if expires:
        try:
            from datetime import datetime as _dt
            exp_dt = _dt.strptime(expires[:19], "%Y-%m-%d %H:%M:%S")
            days_left = (exp_dt - _dt.now()).days
            exp_color = 'var(--red)' if days_left <= 3 else 'var(--muted)'
            exp_text = f'{expires[:10]}（剩{days_left}天）' if days_left >= 0 else f'{expires[:10]}（已到期）'
            expires_tip = f'<span style="font-size:.72rem;color:{exp_color}">到期：{exp_text}</span>'
        except:
            expires_tip = f'<span style="font-size:.72rem;color:var(--muted)">到期：{expires[:10]}</span>'
    else:
        expires_tip = '<span style="font-size:.72rem;color:#22c55e">永久有效</span>'
    return (
        '<!DOCTYPE html><html lang="zh-CN"><head>'
        '<meta charset="UTF-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        f'<title>娱乐打金系统 · {username}</title>'
        '<style>' + COMMON_CSS + '</style></head><body>'
        # 爆仓警告 banner（默认隐藏，由 banned_accounts 轮询填充）
        '<div id="banned-banner" style="display:none;position:sticky;top:0;z-index:9999;'
        'background:linear-gradient(90deg,#dc2626,#991b1b);color:#fff;padding:14px 20px;'
        'font-size:1.05rem;font-weight:800;text-align:center;box-shadow:0 4px 12px rgba(220,38,38,.5);'
        'border-bottom:3px solid #fbbf24;">'
        '<span style="font-size:1.4rem;margin-right:8px">🚨</span>'
        '<span id="banned-banner-text"></span>'
        '<button onclick="document.getElementById(\'banned-banner\').style.display=\'none\'" '
        'style="margin-left:16px;background:rgba(0,0,0,.3);color:#fff;border:1px solid rgba(255,255,255,.4);'
        'border-radius:4px;padding:3px 10px;cursor:pointer;font-size:.85rem">关闭</button>'
        '</div>'
        '<div class="header">'
        f'<h1>⚡ 雷霆群控打金助手 · <span style="color:var(--yellow)">{username}</span></h1>'
        '<div class="header-marquee">'
        '<div class="header-marquee-track">'
        '⚠️ 雷霆群控提醒您：本脚本只要你不停止就会一直下单（切后台或关闭浏览器也会继续）'
        '<span class="sep">·</span>'
        '请务必确认操作，雷霆群控不承担任何下单风险'
        '<span class="sep">·</span>'
        '切勿用于赌博，不得传播非法用途，否则后果自负！'
        '<span class="sep">·</span>'
        '本软件仅供编程技术交流参考，不提供任何平台支持，任何疑问请联系相关网站在线客服'
        '<span class="sep">·</span>'
        '⚠️ 雷霆群控提醒您：本脚本只要你不停止就会一直下单（切后台或关闭浏览器也会继续）'
        '<span class="sep">·</span>'
        '请务必确认操作，雷霆群控不承担任何下单风险'
        '</div>'
        '</div>'
        '<div class="status-bar">'
        '<span class="dot" id="dot"></span>'
        '<span id="fetch-time">--</span>'
        '<div class="countdown-box" id="cd-box">'
        '<div class="label">🎮 欢乐210</div>'
        '<div class="num" id="countdown">--:--</div>'
        '</div>'
        '<div class="countdown-box" id="cd-box60" style="margin-left:8px">'
        '<div class="label">⚡ 比特60</div>'
        '<div class="num" id="countdown60">--:--</div>'
        f'</div>{expires_tip}'
        '<button onclick="renewOpenModal()" style="background:linear-gradient(135deg,#f59e0b,#ef4444);border:none;color:#fff;border-radius:6px;padding:6px 14px;cursor:pointer;font-size:.8rem;font-weight:800;margin-left:10px;box-shadow:0 0 12px #f59e0b66">💎 续费</button>'
        '<button onclick="doLogout()" style="background:transparent;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:4px 10px;cursor:pointer;font-size:.75rem;margin-left:8px">退出</button>'
        '</div></div>'
        # ── 💎 续费弹层（modal）──
        '<div id="renew-modal" style="display:none;position:fixed;inset:0;background:rgba(0,0,0,.78);z-index:9999;align-items:center;justify-content:center;padding:20px">'
          '<div class="card" style="width:680px;max-width:95vw;max-height:92vh;overflow-y:auto;padding:24px">'
            '<div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:14px">'
              f'<h3 style="margin:0;color:var(--accent);font-size:1.2rem">💎 续费 / 升级</h3>'
              '<button onclick="renewCloseModal()" style="background:transparent;border:none;color:var(--muted);font-size:1.4rem;cursor:pointer">✕</button>'
            '</div>'
            '<div id="renew-userinfo" style="background:#0f1117;border:1px solid var(--border);border-radius:8px;padding:12px 16px;margin-bottom:16px">'
              '<div style="font-size:.78rem;color:var(--muted);margin-bottom:4px">当前账号</div>'
              f'<div style="font-size:1.05rem;font-weight:800;color:var(--text)">{username}</div>'
              f'<div style="margin-top:6px;font-size:.78rem">{expires_tip}</div>'
            '</div>'
            '<div style="font-size:.78rem;color:var(--muted);margin-bottom:8px">📦 选择套餐</div>'
            '<div id="renew-plans" style="display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:10px;margin-bottom:14px">'
              '<div style="color:var(--muted);font-size:.85rem;padding:20px;text-align:center">加载中...</div>'
            '</div>'
            '<div id="renew-msg" style="margin-top:10px;font-size:.85rem;text-align:center;min-height:20px"></div>'
          '</div>'
        '</div>'
        '<div class="tabs">'
        '<div class="tab active" onclick="switchTab(\'monitor\')">📊 号码监控</div>'
        '<div class="tab" onclick="switchTab(\'accounts\')">👤 我的账号</div>'
        '<div class="tab" onclick="switchTab(\'order\')">🪨 石头岛游戏参与</div>'
        '<div class="tab" onclick="switchTab(\'realorder\')">📋 参与记录</div>'
        '<div class="tab" onclick="switchTab(\'sim-random\')">🎲 随机下</div>'
        '<div class="tab" onclick="switchTab(\'sim-map\')">🎯 开某投某</div>'
        '<div class="tab" onclick="switchTab(\'sim-fix\')">📌 固定</div>'
        '<div class="tab" onclick="switchTab(\'sim-jump\')">🔀 跳转</div>'
        '<div class="tab" onclick="switchTab(\'miss\')">🔍 遗漏检测</div>'
        '<div class="tab" onclick="switchTab(\'dawei\')">🎯 打尾</div>'
        '<div class="tab" onclick="switchTab(\'plan\')">📋 计划跟投</div>'
        '<div class="tab" onclick="switchTab(\'platform\')">🪨 平台参与记录</div>'
        '<div class="tab" onclick="switchTab(\'history\')">📅 历史记录</div>'
        '</div>'
        '<div class="tab-select-wrap">'
        '<select class="tab-select" onchange="switchTab(this.value);this.blur()">'
        '<option value="monitor">📊 号码监控</option>'
        '<option value="accounts">👤 我的账号</option>'
        '<option value="order">🪨 石头岛游戏参与</option>'
        '<option value="realorder">📋 参与记录</option>'
        '<option value="sim-random">🎲 随机下</option>'
        '<option value="sim-map">🎯 开某投某</option>'
        '<option value="sim-fix">📌 固定</option>'
        '<option value="sim-jump">🔀 跳转</option>'
        '<option value="miss">🔍 遗漏检测</option>'
        '<option value="dawei">🎯 打尾</option>'
        '<option value="plan">📋 计划跟投</option>'
        '<option value="platform">🪨 平台参与记录</option>'
        '<option value="history">📅 历史记录</option>'
        '</select>'
        '</div>'
        + MONITOR_HTML + CLIENT_ACCOUNTS_TAB_HTML + ORDER_TAB_HTML + REALORDER_TAB_HTML + CLIENT_SIM_RANDOM_TAB_HTML + CLIENT_SIM_MAP_TAB_HTML + CLIENT_SIM_FIX_TAB_HTML + CLIENT_SIM_JUMP_TAB_HTML + MISS_TAB_HTML + DAWEI_TAB_HTML + PLAN_TAB_HTML + CLIENT_PLATFORM_TAB_HTML + HISTORY_TAB_HTML
        + '<script>' + switch_tab_js + COMMON_JS + LOGIN_JS + CLIENT_LOGIN_JS + SIM_JS + DAWEI_JS + PLAN_JS + '</script>'
        '</body></html>'
    )


def build_admin_html():
    admin_switch_tab = (
        'function switchTab(name){'
        'var tabs=["users","userdata","payment"];'
        'document.querySelectorAll(".tab").forEach(function(el,i){el.classList.toggle("active",tabs[i]===name);});'
        'document.querySelectorAll(".tab-content").forEach(function(el){el.classList.remove("active");});'
        'var t=document.getElementById("tab-"+name);if(t)t.classList.add("active");'
        'if(name==="users"){loadUsers();}'
        'if(name==="userdata"){if(typeof userDataEnter==="function")userDataEnter();}'
        'if(name==="payment"){if(typeof paymentEnter==="function")paymentEnter();}'
        '}'
    )
    # ⭐ 管理端独立的最小 JS：只含工具函数 + admin 自身 token 注入；
    # 不引入 COMMON_JS（避免触发 setInterval(poll/simRefresh/missRefresh) 等用户端轮询，
    # 那些会调用 /api/std/accounts / /api/sim/banned_accounts 返回 401）
    ADMIN_MIN_JS = """
const $=id=>document.getElementById(id);
// 全局 fetch 拦截：仅注入 admin token（不带 user token）
(function(){var _f=window.fetch;window.fetch=function(url,opts){opts=opts||{};if(typeof url==='string'&&(url.startsWith('/api/')||url.startsWith('/Admin123456/'))){var hdrs={};var atok=localStorage.getItem('a_token');if(atok)hdrs['X-Admin-Token']=atok;opts.headers=Object.assign(hdrs,opts.headers||{});}return _f.call(this,url,opts);};})();
function fmtNum(n){if(n===null||n===undefined||isNaN(n))return '--';return n>=0?('+'+n.toLocaleString()):n.toLocaleString();}
function fmtColor(n){if(n===null||n===undefined||isNaN(n))return 'var(--muted)';return n>=0?'var(--green)':'var(--red)';}
"""
    return (
        '<!DOCTYPE html><html lang="zh-CN"><head>'
        '<meta charset="UTF-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        '<title>🪨 石头岛平台管理端</title>'
        '<style>' + COMMON_CSS + admin_css_extra + '</style></head><body>'
        '<div class="header">'
        '<h1>⚙️ 🪨 石头岛平台管理端</h1>'
        '<div class="status-bar">'
        f'<button onclick="adminLogout()" style="background:transparent;border:1px solid var(--border);color:var(--muted);border-radius:6px;padding:4px 10px;cursor:pointer;font-size:.75rem;margin-left:8px">退出</button>'
        '</div></div>'
        '<div class="tabs">'
        '<div class="tab active" onclick="switchTab(\'users\')">👥 客户账号管理</div>'
        '<div class="tab" onclick="switchTab(\'userdata\')">🔐 客户数据查询</div>'
        '<div class="tab" onclick="switchTab(\'payment\')">💳 支付管理</div>'
        '</div>'
        + ADMIN_USERS_TAB_HTML + ADMIN_USER_DATA_TAB_HTML + ADMIN_PAYMENT_TAB_HTML
        + '<script>'
        + ADMIN_MIN_JS + admin_switch_tab + ADMIN_EXTRA_JS + ADMIN_USER_DATA_JS + ADMIN_PAYMENT_JS + ADMIN_LOGIN_JS
        + 'document.addEventListener("DOMContentLoaded",function(){loadUsers();setInterval(loadUsers,15000);});'
        + '</script></body></html>'
    )


# ══════════════════════════════════════════════════════════════
#  HTML 页面构建
# ══════════════════════════════════════════════════════════════

def build_login_html():
    return """<!DOCTYPE html>
<html lang="zh-CN"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>娱乐打金系统 · 登录</title>
<style>
""" + COMMON_CSS + """
.login-wrap{min-height:100vh;display:flex;align-items:center;justify-content:center;background:var(--bg);padding:20px 0}
.login-box{background:var(--card);border:1px solid var(--border);border-radius:16px;padding:30px 30px 24px;width:400px;max-width:95vw}
.login-box h2{text-align:center;color:var(--accent);margin-bottom:16px;font-size:1.3rem}
.login-box input{width:100%;padding:11px 14px;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);font-size:.95rem;margin-bottom:12px;outline:none;box-sizing:border-box}
.login-box input:focus{border-color:var(--accent)}
.login-box button{width:100%;padding:12px;border:none;border-radius:8px;background:var(--accent);color:#fff;font-size:1rem;font-weight:700;cursor:pointer;margin-top:4px}
.login-err{color:var(--red);font-size:.85rem;text-align:center;min-height:20px;margin-top:8px}
.tab-switcher{display:flex;background:#0f1117;border:1px solid var(--border);border-radius:8px;padding:3px;margin-bottom:18px;gap:3px}
.tab-switcher button{flex:1;padding:8px;background:transparent;border:none;color:var(--muted);font-size:.85rem;font-weight:700;border-radius:6px;cursor:pointer;margin:0}
.tab-switcher button.active{background:var(--accent);color:#fff}
.plan-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:8px;margin-bottom:12px}
.plan-tile{background:#0f1117;border:1.5px solid var(--border);border-radius:8px;padding:10px;text-align:center;cursor:pointer;transition:all .15s}
.plan-tile:hover{transform:translateY(-2px)}
.plan-tile.selected{border-color:var(--accent);background:#1e293b}
.plan-tile .name{font-size:.8rem;color:var(--text);font-weight:700;margin-bottom:3px}
.plan-tile .price{font-size:1.1rem;color:#fbbf24;font-weight:900}
.plan-tile .info{font-size:.7rem;color:var(--muted);margin-top:2px}
.free-btn{background:linear-gradient(135deg,#22c55e,#16a34a)!important;margin-top:8px!important}
</style></head><body>
<div class="login-wrap">
  <div class="login-box">
    <!-- 登录 / 注册 切换 -->
    <div class="tab-switcher">
      <button id="tab-btn-login"  class="active" onclick="switchAuthTab('login')">🔓 登录</button>
      <button id="tab-btn-reg"               onclick="switchAuthTab('reg')">📝 注册</button>
    </div>

    <!-- 登录区 -->
    <div id="auth-login">
      <h2 style="margin-top:0">🎮 娱乐打金系统</h2>
      <input id="inp-user" type="text" placeholder="账号" autocomplete="username">
      <input id="inp-pass" type="password" placeholder="密码" autocomplete="current-password">
      <div style="display:flex;align-items:center;gap:6px;margin-bottom:6px">
        <input type="checkbox" id="remember-me" style="width:auto;margin:0">
        <label for="remember-me" style="font-size:.82rem;color:var(--muted);cursor:pointer">记住密码</label>
      </div>
      <button onclick="doLogin()">登 录</button>
      <div class="login-err" id="login-err"></div>
    </div>

    <!-- 注册区 -->
    <div id="auth-reg" style="display:none">
      <h2 style="margin-top:0">📝 注册新账号</h2>
      <input id="reg-user" type="text" placeholder="设置账号（3-30 位）" autocomplete="username">
      <input id="reg-pass" type="password" placeholder="设置密码（至少 4 位）" autocomplete="new-password">
      <div style="font-size:.75rem;color:var(--muted);margin-bottom:6px">选择套餐</div>
      <div class="plan-grid" id="reg-plans">
        <div style="grid-column:span 2;text-align:center;color:var(--muted);padding:10px;font-size:.85rem">加载中...</div>
      </div>
      <button id="reg-paid-btn" onclick="doRegPaid()">💳 付费注册</button>
      <button id="reg-free-btn" class="free-btn" style="display:none" onclick="doRegFree()">🎁 免费注册</button>
      <div class="login-err" id="reg-err"></div>
    </div>

    <div style="margin-top:16px;padding-top:12px;border-top:1px solid var(--border);font-size:.74rem;color:#64748b;line-height:1.6;text-align:center">
      ⚠️ 免责声明：编译本软件仅供编程技术交流，切勿用于赌博。
    </div>
  </div>
</div>
<script>
(function(){var su=localStorage.getItem('saved_u'),sp=localStorage.getItem('saved_p');if(su){document.getElementById('inp-user').value=su;document.getElementById('remember-me').checked=true;}if(sp&&su){document.getElementById('inp-pass').value=sp;}})();

var _regSelectedPlan = null;
var _regFreeEnabled = false;
var _regPlans = {};

function switchAuthTab(tab){
  var isLogin = (tab === 'login');
  document.getElementById('tab-btn-login').classList.toggle('active', isLogin);
  document.getElementById('tab-btn-reg').classList.toggle('active', !isLogin);
  document.getElementById('auth-login').style.display = isLogin ? 'block' : 'none';
  document.getElementById('auth-reg').style.display = isLogin ? 'none' : 'block';
  if(!isLogin) regLoadPlans();
}

async function regLoadPlans(){
  if(Object.keys(_regPlans).length>0) return;
  try{
    var d=await fetch('/api/payment/plans').then(function(r){return r.json();});
    if(!d.ok) return;
    _regPlans = d.plans || {};
    _regFreeEnabled = !!d.free_enabled;
    var freeDays = d.free_days || 3;
    var freeAcc = d.free_max_accounts || 2;
    if(_regFreeEnabled){
      var fb = document.getElementById('reg-free-btn');
      fb.style.display = 'block';
      fb.textContent = '🎁 免费注册（'+freeDays+'天 · '+freeAcc+'账号）';
    }
    var ORDER = ['day','week','month','year'];
    var grid = document.getElementById('reg-plans');
    var html = '';
    ORDER.forEach(function(k){
      var p = _regPlans[k];
      if(!p) return;
      html += '<div class="plan-tile" onclick="regSelectPlan(\\''+k+'\\',this)">'
        + '<div class="name">'+p.label+'</div>'
        + '<div class="price">¥'+p.price+'</div>'
        + '<div class="info">'+p.days+'天 · '+p.max_accounts+'账号</div>'
        + '</div>';
    });
    grid.innerHTML = html || '<div style="grid-column:span 2;text-align:center;color:var(--muted);padding:10px;font-size:.8rem">暂无套餐</div>';
  }catch(e){console.warn(e);}
}

function regSelectPlan(k, el){
  _regSelectedPlan = k;
  document.querySelectorAll('.plan-tile').forEach(function(t){t.classList.remove('selected');});
  if(el) el.classList.add('selected');
}

async function doLogin(){
  var u=document.getElementById('inp-user').value.trim();
  var p=document.getElementById('inp-pass').value;
  var rem=document.getElementById('remember-me').checked;
  var err=document.getElementById('login-err');
  if(!u||!p){err.textContent='请填写账号和密码';return;}
  err.textContent='登录中...';err.style.color='var(--muted)';
  try{
    var d=await fetch('/api/login',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:u,password:p})}).then(r=>r.json());
    if(d.ok){
      if(rem){localStorage.setItem('saved_u',u);localStorage.setItem('saved_p',p);}
      else{localStorage.removeItem('saved_u');localStorage.removeItem('saved_p');}
      if(d.token)localStorage.setItem('u_token',d.token);
      location.href='/';
    }else{err.textContent=d.msg||'登录失败';err.style.color='var(--red)';}
  }catch(e){err.textContent='网络错误';err.style.color='var(--red)';}
}

async function doRegFree(){
  var u=document.getElementById('reg-user').value.trim();
  var p=document.getElementById('reg-pass').value;
  var err=document.getElementById('reg-err');
  if(!u||!p){err.textContent='请填写账号和密码';err.style.color='var(--red)';return;}
  err.textContent='注册中...';err.style.color='var(--muted)';
  try{
    var d=await fetch('/api/register/free',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:u,password:p})}).then(r=>r.json());
    if(d.ok){
      err.textContent='✅ '+d.msg+'  即将自动登录...';err.style.color='var(--green)';
      setTimeout(function(){
        document.getElementById('inp-user').value=u;
        document.getElementById('inp-pass').value=p;
        switchAuthTab('login');
        doLogin();
      },1500);
    }else{err.textContent=d.msg||'注册失败';err.style.color='var(--red)';}
  }catch(e){err.textContent='网络错误';err.style.color='var(--red)';}
}

async function doRegPaid(){
  var u=document.getElementById('reg-user').value.trim();
  var p=document.getElementById('reg-pass').value;
  var err=document.getElementById('reg-err');
  if(!u||!p){err.textContent='请填写账号和密码';err.style.color='var(--red)';return;}
  if(!_regSelectedPlan){err.textContent='请先选择套餐';err.style.color='var(--red)';return;}
  err.textContent='创建支付订单中...';err.style.color='var(--muted)';
  try{
    var d=await fetch('/api/register/paid',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:u,password:p,plan_key:_regSelectedPlan})}).then(r=>r.json());
    if(d.ok){
      err.textContent='✅ 订单已创建 '+d.out_trade_no+' · 跳转支付...';err.style.color='var(--green)';
      if(d.payurl){setTimeout(function(){window.open(d.payurl,'_blank');},400);}
    }else{err.textContent=d.msg||'下单失败';err.style.color='var(--red)';}
  }catch(e){err.textContent='网络错误';err.style.color='var(--red)';}
}

document.addEventListener('keydown',function(e){if(e.key==='Enter'){
  var inLogin = document.getElementById('auth-login').style.display !== 'none';
  if(inLogin) doLogin();
}});
</script></body></html>"""


def build_admin_login_html():
    return """<!DOCTYPE html>
<html lang="zh-CN"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>雷霆群控打金助手 · 管理端</title>
<style>
""" + COMMON_CSS + """
.login-wrap{min-height:100vh;display:flex;align-items:center;justify-content:center;background:var(--bg)}
.login-box{background:var(--card);border:1px solid var(--border);border-radius:16px;padding:40px 36px;width:360px;max-width:95vw}
.login-box h2{text-align:center;color:var(--yellow);margin-bottom:28px;font-size:1.4rem}
.login-box input{width:100%;padding:12px 14px;background:#12151e;border:1px solid var(--border);border-radius:8px;color:var(--text);font-size:1rem;margin-bottom:14px;outline:none}
.login-box input:focus{border-color:var(--accent)}
.login-box button{width:100%;padding:13px;border:none;border-radius:8px;background:var(--yellow);color:#000;font-size:1rem;font-weight:700;cursor:pointer;margin-top:6px}
.login-err{color:var(--red);font-size:.85rem;text-align:center;min-height:20px;margin-top:8px}
</style></head><body>
<div class="login-wrap">
  <div class="login-box">
    <h2>🔐 管理端</h2>
    <input id="inp-user" type="text" placeholder="账号" value="admin">
    <input id="inp-pass" type="password" placeholder="密码">
    <button onclick="doLogin()">登 录</button>
    <div class="login-err" id="login-err"></div>
  </div>
</div>
<script>
async function doLogin(){
  var u=document.getElementById('inp-user').value.trim();
  var p=document.getElementById('inp-pass').value;
  var err=document.getElementById('login-err');
  err.textContent='登录中...';
  try{
    var d=await fetch('""" + ADMIN_PATH + """/login',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({username:u,password:p})}).then(r=>r.json());
    if(d.ok){if(d.a_token)localStorage.setItem('a_token',d.a_token);location.href='""" + ADMIN_PATH + """';}
    else{err.textContent=d.msg||'登录失败';}
  }catch(e){err.textContent='网络错误';}
}
document.addEventListener('keydown',function(e){if(e.key==='Enter')doLogin();});
</script></body></html>"""




# ══════════════════════════════════════════════════════════════
#  Flask 单应用（端口17900）
# ══════════════════════════════════════════════════════════════
from functools import wraps

app = Flask("lejiting")
CORS(app)
app.secret_key = secrets.token_hex(32)

# ── Auth helpers ──
def get_current_user():
    # 支持 header 和 cookie 两种方式，header 优先（解决跨域/https cookie 问题）
    token = request.headers.get("X-User-Token") or request.cookies.get("u_token") or request.headers.get("X-Token")
    return _user_db.verify_session(token)

def login_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        username = get_current_user()
        if not username:
            if request.path.startswith("/api/"):
                # 诊断：看请求到底有没有带 token、带的是什么
                hdr_tok = request.headers.get("X-User-Token")
                cookie_tok = request.cookies.get("u_token")
                xtok = request.headers.get("X-Token")
                print(f"[auth] 401未登录 path={request.path} "
                      f"X-User-Token={'有' if hdr_tok else '无'} "
                      f"cookie_u_token={'有' if cookie_tok else '无'} "
                      f"X-Token={'有' if xtok else '无'} "
                      f"tok_head={(hdr_tok or cookie_tok or xtok or '')[:12]!r}")
                return jsonify({"ok": False, "msg": "未登录", "code": 401}), 401
            return Response(_platform_rewrite(build_login_html()), mimetype="text/html")
        return f(*args, username=username, **kwargs)
    return decorated

def admin_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        token = (request.headers.get("X-Admin-Token") or 
                 request.cookies.get("a_token"))
        if token != "admin_" + ADMIN_PASS:
            if request.path.startswith("/api/admin/"):
                return jsonify({"ok": False, "msg": "管理员未登录", "code": 401}), 401
            return Response(_platform_rewrite(build_admin_login_html()), mimetype="text/html")
        return f(*args, **kwargs)
    return decorated

# ══════════════════════════════════════════════════════════════
#  客户端路由
# ══════════════════════════════════════════════════════════════

@app.route("/")
def client_index():
    username = get_current_user()
    if not username:
        return Response(_platform_rewrite(build_login_html()), mimetype="text/html")
    u = _user_db.get_user(username)
    return Response(_platform_rewrite(build_client_html(username, u)), mimetype="text/html")

@app.route("/api/login", methods=["POST"])
def api_login():
    body = request.json or {}
    username = body.get("username","").strip()
    password = body.get("password","")
    ok, msg = _user_db.verify_password(username, password)
    if not ok:
        return jsonify({"ok": False, "msg": msg})
    token = _user_db.create_session(username)
    u = _user_db.get_user(username)
    resp = jsonify({"ok": True, "username": username, "expires_at": u.get("expires_at",""), "token": token})
    resp.set_cookie("u_token", token, max_age=86400, httponly=False, samesite="Lax")
    return resp

@app.route("/api/logout", methods=["POST"])
def api_logout():
    token = request.cookies.get("u_token")
    if token:
        _user_db.delete_session(token)
    resp = jsonify({"ok": True})
    resp.delete_cookie("u_token")
    return resp

@app.route("/api/me")
@login_required
def api_me(username):
    u = _user_db.get_user(username)
    return jsonify({"ok": True, "username": username, "expires_at": u.get("expires_at",""), "remark": u.get("remark","")})

# ── 开奖数据 ──
@app.route("/api/history")
def api_history():
    return jsonify({"ok": True, "data": state["history"], "fetch_time": state["fetch_time"]})

@app.route("/api/history60")
def api_history60():
    return jsonify({"ok": True, "data": state_60["history"], "last_qishu": state_60["last_qishu"]})

@app.route("/api/status")
def api_status():
    return jsonify({"ok": True, "countdown": state["countdown"], "last_qishu": state["last_qishu"],
                    "fetch_time": state["fetch_time"], "fast_mode": state["fast_mode"],
                    "notifications": state["notifications"], "countdown_60": state_60.get("countdown", 0)})

@app.route("/api/xiaomi_proxy")
def api_xiaomi_proxy():
    """开奖号码代理：只读主轮询线程刚刷新的内存缓存（state.history + _countdown_cache）。
    不再独立调 fetch_28vp，避免和主轮询线程同时写 _countdown_cache 造成倒计时跳变。
    返回归一化字段：data: [{qishu, sum, nums, time}], next_qishu, next_ts。
    """
    gid = str(request.args.get("game", "5"))
    try:
        n = min(int(request.args.get("n", "2")), 50)
    except Exception:
        n = 2
    style = 210 if gid in ("5", "210", "jnd28") else (60 if gid in ("67", "60", "btc28") else 210)
    game = "jnd28" if style == 210 else "btc28"
    hist = (state_60 if style == 60 else state).get("history", []) or []
    # 主轮询还没刷到内存 → 这里直接拉一次（同样走 fetch_28vp 统一路径）
    if not hist:
        try:
            res, _ = fetch_28vp(game)
            if res:
                hist = res
                if style == 60:
                    state_60["history"] = res[:200]
                else:
                    state["history"] = res[:200]
        except Exception as e:
            print(f"[xiaomi_proxy] fetch fallback err={e}")
    out = []
    for r in hist[:n]:
        out.append({
            "qishu": r.get("qishu"),
            "sum":   r.get("sum"),
            "nums":  r.get("nums") or [],
            "time":  r.get("time") or "",
        })
    nxt = None; next_qishu = None
    with _countdown_lock:
        c = _countdown_cache.get(game)
    if c:
        if c.get("next_ts"):    nxt = float(c["next_ts"])
        if c.get("next_qishu"): next_qishu = c["next_qishu"]
    if not out:
        return jsonify({"ok": False, "msg": "数据源暂无返回"}), 502
    return jsonify({"ok": True, "data": out, "next_qishu": next_qishu, "next_ts": nxt})

# ── 🔀 平台账号 ──
@app.route("/api/std/captcha")
@login_required
def api_std_captcha(username):
    """🔀 鲸鱼无验证码（返回 stub）；石头岛真验证码（/yzm/captcha）。"""
    if IS_JINGYU:
        return jsonify({"ok": True, "src": "", "uniqid": "no-captcha"})
    try:
        r = requests.post(f"{STD_API}/yzm/captcha", headers=std_headers(), timeout=8)
        d = r.json()
        if d.get("code") == 200:
            data = d.get("data") or {}
            return jsonify({"ok": True, "src": data.get("src",""), "uniqid": data.get("uniqid","")})
        return jsonify({"ok": False, "msg": d.get("msg","获取验证码失败")})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/api/std/login", methods=["POST"])
@login_required
def api_std_login(username):
    """🔀 平台账号登录：
    - 鲸鱼：tel + password 直接登（POST /pub/token）
    - 石头岛：tel + password + captcha + uniqid（POST /login/login）"""
    body = request.json or {}
    tel = (body.get("tel") or "").strip()
    password = (body.get("password") or "").strip()
    if not tel or not password:
        return jsonify({"ok": False, "msg": "请填写手机号和密码"})
    # 检查账号上限
    try:
        cur_n = len(_user_mgr.get_acc(username).accounts)
        max_n = _user_db.get_user_max_accounts(username)
        if max_n > 0 and cur_n >= max_n:
            return jsonify({"ok": False, "msg": f"已达账号上限 {max_n} 个，请联系管理员"})
    except Exception as e:
        print(f"[std_login max_check] {e}")

    if IS_JINGYU:
        # 🐋 鲸鱼登录
        try:
            r = requests.post(f"{STD_API}/pub/token", headers=std_headers(),
                              params={"tel": tel, "password": password}, timeout=8)
            d = r.json()
            if d.get("code") == 200 and d.get("token"):
                token = d["token"]
                info = std_get_user_info(token) or {}
                uid = tel  # 鲸鱼用 tel 当主键
                acc = _user_mgr.get_acc(username)
                acc.accounts[uid] = {"uid": uid, "tel": tel, "token": token,
                                     "password": password, "remark": ""}
                acc.save()
                _user_db.save_std_account(username, uid, tel, token, password=password)
                print(f"[jingyu_login] OK username={username!r} tel={tel} "
                      f"balance={info.get('balance')}")
                return jsonify({"ok": True, "uid": uid,
                                "balance": info.get("balance", 0),
                                "nick_name": info.get("nick_name", "")})
            print(f"[jingyu_login] FAIL username={username!r} tel={tel} "
                  f"code={d.get('code')} msg={d.get('msg')}")
            return jsonify({"ok": False, "msg": d.get("msg","登录失败")})
        except Exception as e:
            return jsonify({"ok": False, "msg": str(e)})

    # 🪨 石头岛登录
    captcha = (body.get("captcha") or "").strip()
    uniqid = (body.get("uniqid") or "").strip()
    if not captcha or not uniqid:
        return jsonify({"ok": False, "msg": "请输入验证码"})
    try:
        r = requests.post(f"{STD_API}/login/login", headers=std_headers(),
                          json={"tel": tel, "password": password,
                                "captcha": captcha, "uniqid": uniqid}, timeout=8)
        d = r.json()
        if d.get("code") == 200:
            data = d.get("data") or {}
            token = data.get("token","")
            user  = data.get("user") or {}
            uid = str(user.get("id") or user.get("Id") or tel)
            acc = _user_mgr.get_acc(username)
            acc.accounts[uid] = {"uid": uid, "tel": tel, "token": token,
                                 "password": password, "remark": ""}
            acc.save()
            _user_db.save_std_account(username, uid, tel, token, password=password)
            info = std_get_user_info(token) or {}
            print(f"[shitoud_login] OK username={username!r} tel={tel} uid={uid} "
                  f"silver={info.get('silver')}")
            return jsonify({"ok": True, "uid": uid,
                            "balance": info.get("silver", 0),
                            "silver": info.get("silver", 0),
                            "nick_name": info.get("nickname", ""),
                            "nickname": info.get("nickname", "")})
        print(f"[shitoud_login] FAIL username={username!r} tel={tel} "
              f"code={d.get('code')} msg={d.get('msg')}")
        return jsonify({"ok": False, "msg": d.get("msg","登录失败")})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/api/std/save_token", methods=["POST"])
@login_required
def api_std_save_token(username):
    """🪨 石头岛版（兼容用）：把 token 上报到服务器保存。"""
    body = request.json or {}
    tel = str(body.get("tel", "")).strip()
    uid = str(body.get("uid", "")).strip()
    token = str(body.get("token", "")).strip()
    password = str(body.get("password", "")).strip()
    if not token or not tel:
        print(f"[save_token] 参数不完整 username={username!r} tel={tel!r}")
        return jsonify({"ok": False, "msg": "参数不完整"})
    if not uid:
        uid = tel
    try:
        acc = _user_mgr.get_acc(username)
        acc.accounts[uid] = {"uid": uid, "tel": tel, "token": token,
                             "password": password, "remark": ""}
        acc.save()
        _user_db.save_std_account(username, uid, tel, token, password=password)
        return jsonify({"ok": True, "uid": uid})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/api/std/logout", methods=["POST"])
@login_required
def api_std_logout(username):
    body = request.json or {}
    uid = body.get("uid","")
    acc = _user_mgr.get_acc(username)
    acc.accounts.pop(uid, None)
    acc.save()
    _user_db.delete_std_account(username, uid)
    return jsonify({"ok": True})

@app.route("/api/std/tokens")
@login_required
def api_std_tokens(username):
    """返回当前用户的石头岛账号 token 列表（供前端浏览器直连备用）。"""
    acc = _user_mgr.get_acc(username)
    accs = [{"uid": uid, "tel": a.get("tel",""),
             "token": a.get("token",""), "remark": a.get("remark","")}
            for uid, a in acc.accounts.items() if a.get("token")]
    return jsonify({"ok": True, "accounts": accs})

@app.route("/api/std/accounts")
@login_required
def api_std_accounts(username):
    """🪨 石头岛：调 /user/getUserInfo 拿余额 + /game/getJoinRecordListNew + /game/stats。"""
    acc = _user_mgr.get_acc(username)
    items = list(acc.accounts.items())

    def _fetch_one(pair):
        uid, a = pair
        token = a.get("token") or ""
        tel = a.get("tel") or ""
        base = {"uid": uid, "tel": tel, "remark": a.get("remark",""),
                "nickname": tel, "last_check": now_cn().strftime("%H:%M:%S"),
                "records": [], "records60": [], "stats": {"today":0,"win_rate":0},
                "stats60": {"today":0,"win_rate":0}, "total_today": 0, "silver": 0}
        # 拿余额 + 昵称
        try:
            info = std_get_user_info(token)
            if info:
                base.update({"silver": int(info.get("silver") or 0),
                             "online": True,
                             "nickname": info.get("nickname") or tel})
            else:
                base.update({"online": False, "last_check": "--"})
        except Exception:
            base.update({"online": False, "last_check": "--"})
        # 拿两个游戏的下单记录 + 统计
        for style, skey, rkey in [(210, "stats", "records"), (60, "stats60", "records60")]:
            try:
                recs = std_get_records(token, limit=20, style=style)
                base[rkey] = recs[:10]
                stats = std_get_stats(token, style)
                base[skey] = stats
            except Exception as e:
                print(f"[std_accounts game{style}] uid={uid} {e}")
        base["total_today"] = base["stats"].get("today",0) + base["stats60"].get("today",0)
        return base

    result = []
    if items:
        max_workers = min(10, len(items))
        with ThreadPoolExecutor(max_workers=max_workers) as ex:
            result = list(ex.map(_fetch_one, items))
    return jsonify({"ok": True, "data": result})

@app.route("/api/std/orders")
@login_required
def api_std_orders(username):
    """🪨 石头岛：用 /game/getJoinRecordListNew 拿账号本游戏的下注+开奖记录。"""
    acc = _user_mgr.get_acc(username)
    uid = request.args.get("uid","")
    if uid not in acc.accounts:
        return jsonify({"ok": False, "msg": "账号不存在"})
    token = acc.accounts[uid]["token"]
    style = 60 if request.args.get("game","210") == "60" else 210
    try:
        recs = std_get_records(token, limit=50, style=style)
        orders = []
        for it in recs:
            bet   = int(it.get("CountBA") or it.get("output") or 0)
            prize = int(it.get("WinAmount") or it.get("income") or 0)
            orders.append({
                "qishu": str(it.get("Periods") or it.get("game_no") or ""),
                "createTime": it.get("OpenTime","") or "",
                "betAmount": bet,
                "winAmount": prize,
                "result": "中" if prize > 0 else "不中",
            })
        return jsonify({"ok": True, "data": orders[:50]})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

@app.route("/api/std/expect")
@login_required
def api_std_expect(username):
    style = int(request.args.get("style", 210))
    acc = _user_mgr.get_acc(username)
    if not acc.accounts:
        return jsonify({"ok": False, "msg": "请先登录石头岛账号"})
    token = list(acc.accounts.values())[0]["token"]
    expect = std_get_expect(token, style)
    if expect:
        return jsonify({"ok": True, "expect": expect})
    return jsonify({"ok": False, "msg": "获取期号失败"})

@app.route("/api/std/order", methods=["POST"])
@login_required
def api_std_order(username):
    body = request.json or {}
    press_str = body.get("press_str","")
    # amount 不再单独要求：press_str 里已含各位置实际金额，总额由它推导
    try:
        amount = int(body.get("amount", 0)) or sum(
            int(x) for x in str(press_str).split(",") if x.strip().lstrip("-").isdigit())
    except Exception:
        amount = 0
    style = int(body.get("style", 210))
    acc = _user_mgr.get_acc(username)
    print(f"[std_order] ENTER username={username!r} style={style} "
          f"amount={amount} 账号数={len(acc.accounts)} "
          f"accounts_keys={list(acc.accounts.keys())}")
    if not press_str or amount <= 0:
        return jsonify({"ok": False, "msg": "参数错误"})
    if not acc.accounts:
        print(f"[std_order] NO_ACCOUNT username={username!r} "
              f"→ DB查询: {[a.get('uid') for a in _user_db.get_std_accounts(username)]}")
        return jsonify({"ok": False, "msg": "请先登录石头岛账号"})
    # 获取当前期号
    token = list(acc.accounts.values())[0]["token"]
    expect = std_get_expect(token, style)
    if not expect:
        return jsonify({"ok": False, "msg": "获取期号失败"})
    results = []
    for uid, a in acc.accounts.items():
        try:
            if IS_JINGYU:
                # 🐋 鲸鱼下单：POST /pub/game/gameJoin?game_id=&game_no=&betNum=
                gid = JINGYU_GAME_ID.get(int(style), 2)
                endpoint = f"{STD_API}/pub/game/gameJoin"
                r = requests.post(endpoint, headers=std_headers(a["token"]),
                    params={"game_id": gid, "game_no": str(expect), "betNum": press_str},
                    timeout=15)
            else:
                # 🪨 石头岛下单：POST /game/createGameRecord JSON body
                endpoint = f"{STD_API}/game/createGameRecord"
                r = requests.post(endpoint, headers=std_headers(a["token"]),
                    json={"expect": str(expect), "style": str(style), "press": press_str},
                    timeout=15)
            raw = (r.text or "").strip()
            print(f"[{PLATFORM}_order] REQ uid={uid} style={style} "
                  f"http={r.status_code} body_head={raw[:120]!r}")
            if not raw:
                results.append({"uid": uid, "tel": a["tel"], "ok": False,
                    "expect": None, "msg": f"返回空 (HTTP {r.status_code})"})
                continue
            try:
                d = r.json()
            except ValueError:
                results.append({"uid": uid, "tel": a["tel"], "ok": False,
                    "expect": None, "msg": f"非JSON (HTTP {r.status_code}): {raw[:60]}"})
                continue
            code = d.get("code")
            msg = d.get("msg","") or ""
            ok = (code == 200) or ("已" in msg and ("参与" in msg or "下注" in msg or "投" in msg))
            # 鲸鱼 token 过期 → 自动续登重下；石头岛只能标记失效
            if not ok and code == -1:
                if IS_JINGYU and a.get("password"):
                    try:
                        rr = requests.post(f"{STD_API}/pub/token", headers=std_headers(),
                                           params={"tel": a["tel"], "password": a["password"]}, timeout=6)
                        dd = rr.json()
                        if dd.get("code") == 200 and dd.get("token"):
                            a["token"] = dd["token"]
                            acc.save()
                            _user_db.save_std_account(username, uid, a["tel"], dd["token"], password=a["password"])
                            r2 = requests.post(endpoint, headers=std_headers(a["token"]),
                                params={"game_id": JINGYU_GAME_ID.get(int(style), 2),
                                        "game_no": str(expect), "betNum": press_str},
                                timeout=8)
                            try:
                                d = r2.json()
                                code = d.get("code"); msg = d.get("msg","") or ""
                                ok = (code == 200) or ("已" in msg and ("参与" in msg or "下注" in msg or "投" in msg))
                            except Exception: pass
                    except Exception as e:
                        print(f"[{PLATFORM}_order relogin] {e}")
                elif IS_SHITOUD and ("登录" in msg or "失效" in msg or "未登录" in msg):
                    _mark_bad_token(a["token"])
                    msg = f"token失效，请重新登录: {msg}"
            if not ok:
                print(f"[{PLATFORM}_order] FAIL uid={uid} code={code} msg={msg}")
            results.append({"uid": uid, "tel": a["tel"], "ok": ok,
                "expect": expect if ok else None,
                "msg": msg if not ok else ""})
            # 保存下单记录
            try:
                bet_amount = sum(int(x) for x in press_str.split(",")
                                 if x.strip().lstrip("-").isdigit())
            except Exception:
                bet_amount = 0
            _sim_db.save_real_order(
                username, uid, a["tel"], style, expect,
                press_str, bet_amount, ok, msg if not ok else "")
        except requests.exceptions.RequestException as e:
            print(f"[jingyu_order] NETERR uid={uid} err={e}")
            results.append({"uid": uid, "tel": a["tel"], "ok": False,
                "msg": f"网络错误: {e}"})
        except Exception as e:
            print(f"[jingyu_order] EXC uid={uid} err={e}")
            results.append({"uid": uid, "tel": a["tel"], "ok": False, "msg": str(e)})
    return jsonify({"ok": True, "expect": expect, "results": results})

@app.route("/api/std/remove", methods=["POST"])
@login_required
def api_std_remove(username):
    body = request.json or {}
    uid = body.get("uid","")
    acc = _user_mgr.get_acc(username)
    acc.accounts.pop(uid, None)
    acc.save()
    _user_db.delete_std_account(username, uid)
    return jsonify({"ok": True})

@app.route("/api/std/recent_orders")
@login_required
def api_std_recent_orders(username):
    """返回该用户所有账号最近N期下单记录（默认 2，可通过 ?limit=30 调整）"""
    try:
        limit = max(1, min(int(request.args.get("limit", 2)), 100))
    except Exception:
        limit = 2
    acc = _user_mgr.get_acc(username)
    result = {}
    for uid in acc.accounts:
        result[uid] = {
            "210": _sim_db.get_recent_orders(username, uid, 210, limit),
            "60":  _sim_db.get_recent_orders(username, uid, 60, limit),
        }
    return jsonify({"ok": True, "data": result})

@app.route("/api/std/jingyu_orders")
@login_required
def api_std_jingyu_orders(username):
    """🪨 平台下单聚合：从石头岛 /game/getJoinRecordListNew 拉每个账号最近 N 期，
    并发拉所有账号；返回字段与 /api/real_orders 对齐。
    GET ?game=60|210
    """
    _t0 = time.time()
    try:
        game = int(request.args.get("game", 210))
        if game not in (60, 210):
            game = 210
    except Exception:
        game = 210
    acc = _user_mgr.get_acc(username)
    accounts = list(acc.accounts.items())
    print(f"[shitoud_orders] user={username} game={game} accounts={len(accounts)}")
    if not accounts:
        return jsonify({"ok": True, "data": []})

    def _fetch_one(uid, a):
        token = a.get("token","")
        if not token:
            return uid, a, []
        try:
            recs = std_get_records(token, limit=50, style=game)
            return uid, a, recs
        except Exception as e:
            print(f"[shitoud_orders fetch] uid={uid} err={e}")
            return uid, a, []

    out = []
    with ThreadPoolExecutor(max_workers=min(10, max(1, len(accounts)))) as ex:
        futs = [ex.submit(_fetch_one, uid, dict(a)) for uid, a in accounts]
        for f in futs:
            try:
                uid, a, lst = f.result(timeout=12)
            except Exception:
                continue
            tel = a.get("tel","")
            remark = a.get("remark","")
            for it in lst:
                qid = it.get("Periods") or it.get("game_no")
                bet = int(it.get("CountBA") or it.get("bet") or 0)
                if bet <= 0:
                    continue
                prize = int(it.get("WinAmount") or it.get("prize") or 0)
                # 石头岛字段 SumNum 是开奖合计号（鲸鱼用 num 兜底）
                sn = it.get("SumNum")
                if sn is None: sn = it.get("Num")
                if sn is None: sn = it.get("num")
                try: open_num = int(sn) if sn is not None and sn != "" else None
                except: open_num = None
                # 已开奖：SumNum 有值；未开奖：SumNum=None
                pending = (open_num is None)
                out.append({
                    "qishu": str(qid),
                    "uid":   uid,
                    "tel":   tel,
                    "remark": remark,
                    "betAmount": bet,
                    "winAmount": prize if not pending else 0,
                    "lossAmount": int(it.get("LossAmount") or 0),
                    "result": open_num if open_num is not None else "--",
                    "createTime": it.get("CreateTime","") or "",
                    "openTime":   it.get("OpenTime","") or "",
                    "ok":     True,
                    "pending": pending,
                    "press_str": it.get("Number","") or it.get("press_str","") or "",
                    "source": "shitoud",
                })
    try:
        out.sort(key=lambda x: int(x.get("qishu") or 0), reverse=True)
    except Exception:
        pass
    print(f"[shitoud_orders] user={username} game={game} done cost={time.time()-_t0:.2f}s out={len(out)}")
    return jsonify({"ok": True, "data": out})


@app.route("/api/std/platform_orders")
@login_required
def api_std_platform_orders(username):
    """🪨 平台参与记录：查本地 real_orders 表（脚本下到石头岛的全部真实下单记录）。
    支持按 game / date / uid / source 多维度筛选。严格按 username 隔离。

    GET ?game=210|60&date=YYYY-MM-DD&uid=&source=&limit=
    source 可选值：normal / sim_random / sim_map / sim_fix / sim_jump / miss / 空(全部)
    """
    try:
        game = int(request.args.get("game", 210))
        if game not in (60, 210):
            game = 210
    except Exception:
        game = 210
    date_str = (request.args.get("date") or "").strip()
    uid_filter = (request.args.get("uid") or "").strip()
    source_filter = (request.args.get("source") or "").strip()
    try:
        limit = max(1, min(5000, int(request.args.get("limit", 2000))))
    except Exception:
        limit = 2000

    # 账号下拉数据
    acc_mgr = _user_mgr.get_acc(username)
    acc_options = []
    for u, a in list(acc_mgr.accounts.items()):
        acc_options.append({
            "uid": u,
            "tel": a.get("tel", ""),
            "remark": a.get("remark", ""),
        })

    # 查 real_orders
    rows = []
    try:
        sql = ("SELECT id, uid, tel, qishu, press_str, bet_amount, ok, msg, "
               "created_at, source, result, win_amount, settled_at "
               "FROM real_orders WHERE username=? AND style=?")
        args = [username, int(game)]
        if date_str:
            sql += " AND substr(created_at,1,10)=?"
            args.append(date_str)
        if uid_filter:
            sql += " AND uid=?"
            args.append(uid_filter)
        if source_filter:
            if source_filter == "normal":
                # 手动下单：source 为 normal/manual/空/null
                sql += " AND (source='normal' OR source='manual' OR source IS NULL OR source='')"
            elif source_filter == "miss":
                # 遗漏：source 以 'miss' 开头（miss / miss_auto 等）
                sql += " AND source LIKE 'miss%'"
            elif source_filter == "dawei":
                # 打尾：source 以 'dawei' 开头（dawei_seq_1 / dawei_seq_2 等）
                sql += " AND source LIKE 'dawei%'"
            else:
                # sim_random / sim_map / sim_fix / sim_jump 等精确匹配
                sql += " AND source=?"
                args.append(source_filter)
        sql += " ORDER BY id DESC LIMIT ?"
        args.append(limit)
        with _sim_db.lock:
            with _sim_db._conn() as conn:
                cur = conn.execute(sql, args)
                cols = [c[0] for c in cur.description]
                for r in cur.fetchall():
                    rows.append(dict(zip(cols, r)))
    except Exception as e:
        print(f"[platform_orders] db err user={username} err={e}")
        return jsonify({"ok": False, "msg": f"查询失败: {e}"})

    # 整理输出
    out = []
    for r in rows:
        bet = int(r.get("bet_amount") or 0)
        result = r.get("result")
        win = r.get("win_amount")
        ok = bool(r.get("ok"))
        # pending：下单成功 且 还没开奖号
        pending = (ok and result is None)
        out.append({
            "id":         r.get("id"),
            "uid":        r.get("uid") or "",
            "tel":        r.get("tel") or "",
            "qishu":      str(r.get("qishu") or ""),
            "press_str":  r.get("press_str") or "",
            "betAmount":  bet,
            "winAmount":  int(win) if win is not None else 0,
            "result":     int(result) if result is not None else "--",
            "pending":    bool(pending),
            "ok":         ok,
            "msg":        r.get("msg") or "",
            "source":     r.get("source") or "",
            "createTime": r.get("created_at") or "",
            "settledAt":  r.get("settled_at") or "",
            "pnl":        (int(win) - bet) if (win is not None and ok) else 0,
        })

    stake = sum(o["betAmount"] for o in out if o["ok"])
    win = sum(o["winAmount"] for o in out if o["ok"] and not o["pending"])
    pnl_total = sum(o["pnl"] for o in out if o["ok"] and not o["pending"])
    won = sum(1 for o in out if o["ok"] and not o["pending"] and o["winAmount"] > 0)
    lost = sum(1 for o in out if o["ok"] and not o["pending"] and o["winAmount"] <= 0)
    pending_n = sum(1 for o in out if o["pending"])

    print(f"[platform_orders] user={username} game={game} date={date_str or '(all)'} uid={uid_filter or '(all)'} source={source_filter or '(all)'} rows={len(out)}")
    return jsonify({
        "ok": True,
        "data": out,
        "accounts": acc_options,
        "stats": {
            "count":   len(out),
            "stake":   stake,
            "win":     win,
            "pnl":     pnl_total,
            "won":     won,
            "lost":    lost,
            "pending": pending_n,
        }
    })


@app.route("/api/std/log_order", methods=["POST"])
@login_required
def api_std_log_order(username):
    """前端浏览器调石头岛接口下单后，把结果回传到服务器持久化记录。
    用途：保留 real_orders 表的盈亏统计、最近2期显示等功能不变。
    Body: {uid, tel, style, expect, press_str, bet_amount, ok, msg, source}
    source: normal | miss | sim (默认 normal)
    """
    body = request.json or {}
    uid = str(body.get("uid", ""))
    tel = str(body.get("tel", ""))
    style = int(body.get("style", 210))
    expect = str(body.get("expect", ""))
    press_str = str(body.get("press_str", ""))
    bet_amount = int(body.get("bet_amount", 0) or 0)
    ok = bool(body.get("ok", False))
    msg = str(body.get("msg", ""))
    source = str(body.get("source", "normal")) or "normal"
    if source not in ("normal", "miss", "sim"):
        source = "normal"
    if not uid or not expect:
        return jsonify({"ok": False, "msg": "参数不完整"})
    try:
        _sim_db.save_real_order(username, uid, tel, style, expect,
                                press_str, bet_amount, ok, msg, source)
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# 固定赔率表（用于后端计算 winAmount，跟前端一致）
# ⭐ 真实下单赔率 = 官方理论赔率 × 0.98（石头岛固定抽 2% 水）
_REAL_ORDER_ODDS = [
    979.99, 326.66, 163.33, 98.00, 65.32, 46.65, 34.99, 27.21,
    21.77, 17.81, 15.55, 14.20, 13.41, 13.03, 13.03, 13.41,
    14.20, 15.55, 17.81, 21.77, 27.21, 34.99, 46.65, 65.32,
    98.00, 163.33, 326.66, 979.99,
]

def _calc_win_from_open(press_str, open_num):
    """根据 press_str + 开奖号 计算 win_amount。"""
    try:
        on = int(open_num)
    except Exception:
        return 0
    if not (0 <= on <= 27):
        return 0
    try:
        parts = [int(x) for x in (press_str or "").split(",") if x.strip().lstrip("-").isdigit()]
        if len(parts) != 28:
            return 0
        stake = parts[on]
        if stake > 0:
            return int(round(stake * _REAL_ORDER_ODDS[on]))
    except Exception:
        pass
    return 0

def _lookup_open_num(qishu, style):
    """查指定期号的开奖号：先查内存 history，再查 DB（real_orders 已结算行）。
    ⭐ bug 2：历史期号被挤出内存 200 期窗口时，从 DB 已结算行兜底反查。"""
    try:
        hist = (state_60 if int(style) == 60 else state).get("history", []) or []
        for r in hist:
            if str(r.get("qishu","")) == str(qishu):
                s = r.get("sum")
                if s is not None and s != "" and s != "--":
                    try:
                        return int(s)
                    except Exception:
                        return None
                return None
    except Exception:
        pass
    # DB 兜底：同期号已有其他单子结算过 → 直接复用 result
    try:
        with _sim_db.lock:
            with _sim_db._conn() as conn:
                row = conn.execute(
                    "SELECT result FROM real_orders WHERE style=? AND qishu=? AND settled_at IS NOT NULL AND result IS NOT NULL LIMIT 1",
                    (int(style), str(qishu))
                ).fetchone()
                if row and row["result"] is not None:
                    return int(row["result"])
    except Exception:
        pass
    return None

def _settle_real_orders_for(style, qishu, open_num):
    """开奖一期就把 real_orders 表里这一期的未结算行全部回填 result/win_amount。"""
    try:
        on = int(open_num)
    except Exception:
        return 0
    now_str = now_cn().strftime("%Y-%m-%d %H:%M:%S")
    cnt = 0
    try:
        with _sim_db.lock:
            with _sim_db._conn() as conn:
                rows = conn.execute(
                    "SELECT id, press_str FROM real_orders WHERE style=? AND qishu=? AND (settled_at IS NULL OR settled_at='')",
                    (int(style), str(qishu))
                ).fetchall()
                for r in rows:
                    win = _calc_win_from_open(r["press_str"], on)
                    conn.execute(
                        "UPDATE real_orders SET result=?, win_amount=?, settled_at=? WHERE id=?",
                        (on, win, now_str, r["id"])
                    )
                    cnt += 1
                if cnt:
                    conn.commit()
    except Exception as e:
        print(f"[settle_real_orders] style={style} qishu={qishu} err={e}")
    return cnt

def _backfill_real_orders_loop():
    """后台线程：扫描 real_orders 里未结算的行，在内存 history / DB 里能查到开奖号就回填。
    ⭐ 同时给 SimEngine/MissEngine 的旧 pending 补结算（修复重启后 pending 卡死的 bug）。
    ⭐ bug 2：超 1 小时仍未结算的视为数据缺失，标记为 expired（settled_at=now, result=-1）
    避免「真实参与·待开奖」永远挂着历史脏数据。"""
    while True:
        try:
            with _sim_db.lock:
                with _sim_db._conn() as conn:
                    rows = conn.execute(
                        "SELECT DISTINCT style, qishu FROM real_orders WHERE (settled_at IS NULL OR settled_at='') AND ok=1 LIMIT 500"
                    ).fetchall()
            checked = 0; settled = 0
            # 记录回填成功的 (style, qishu, open_num) 一会儿给 SimEngine 也补结算
            broadcast_targets = []
            for r in rows:
                st = int(r["style"]); qs = str(r["qishu"])
                on = _lookup_open_num(qs, st)
                if on is not None:
                    n = _settle_real_orders_for(st, qs, on)
                    if n:
                        settled += n
                        broadcast_targets.append((st, qs, on))
                checked += 1
            # 给所有 user 引擎补结算（pending 期号匹配上就会被结算 + 推进 mul_idx）
            for st, qs, on in broadcast_targets:
                try: _user_mgr.broadcast_result(st, qs, on)
                except Exception as e: print(f"[backfill broadcast_result] style={st} qishu={qs} {e}")
                try:
                    for eng in _admin_sims + _admin_sims2:
                        eng.process_result(st, qs, on)
                        eng.settle_miss_bets(st, qs, on)
                except Exception as e: print(f"[backfill admin_sims] {e}")
                try: _admin_miss.process_result(st, qs, on)
                except Exception as e: print(f"[backfill admin_miss] {e}")
            if settled:
                print(f"[backfill] checked={checked} settled={settled} broadcast={len(broadcast_targets)}")
            # 超期清理：created_at 早于 1 小时前还没 settled → 标记 expired (result=-1)
            try:
                cutoff = (now_cn() - timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
                now_str = now_cn().strftime("%Y-%m-%d %H:%M:%S")
                with _sim_db.lock:
                    with _sim_db._conn() as conn:
                        cur = conn.execute(
                            "UPDATE real_orders SET result=-1, win_amount=0, settled_at=?, msg=COALESCE(msg,'')||' [expired]' "
                            "WHERE (settled_at IS NULL OR settled_at='') AND ok=1 AND created_at<?",
                            (now_str, cutoff)
                        )
                        if cur.rowcount:
                            conn.commit()
                            print(f"[backfill] expired {cur.rowcount} 行（超1小时未结算）")
            except Exception as e:
                print(f"[backfill expired] {e}")
        except Exception as e:
            print(f"[backfill_loop] {e}")
        time.sleep(10)

@app.route("/api/real_orders")
@login_required
def api_real_orders(username):
    """历史记录-真实下单：返回某游戏指定日期的所有下单记录（含开奖号码、中奖金额、盈亏）。
    GET ?game=60|210&date=YYYY-MM-DD&limit=200
    日期不传则不限定日期。
    开奖号码 + 中奖金额优先读 DB 持久化字段；DB 没有则尝试用内存 history 现算并写回。"""
    try:
        game = int(request.args.get("game", 210))
        if game not in (60, 210):
            game = 210
    except Exception:
        game = 210
    date_str = request.args.get("date", "").strip()
    try:
        limit = max(1, min(int(request.args.get("limit", 200)), 500))
    except Exception:
        limit = 200
    try:
        with _sim_db.lock:
            with _sim_db._conn() as conn:
                where_extra = ""
                params = [username, int(game)]
                if date_str:
                    where_extra = " AND date(created_at) = ?"
                    params.append(date_str)
                rows = conn.execute(
                    f"""SELECT id, qishu, uid, tel, press_str, bet_amount, ok, msg, created_at, source,
                               result, win_amount, settled_at
                        FROM real_orders
                        WHERE username=? AND style=?{where_extra}
                        ORDER BY id DESC LIMIT ?""",
                    params + [limit]).fetchall()
                orders_raw = [dict(r) for r in rows]
    except Exception as e:
        return jsonify({"ok": False, "msg": f"DB错误: {e}"})

    # 给 DB 里未结算的行尝试用内存 history 回填一次（同时写回 DB 持久化）
    backfill_pending = []
    for r in orders_raw:
        if r.get("settled_at"):
            continue
        if not r.get("ok"):
            continue
        on = _lookup_open_num(r["qishu"], game)
        if on is not None:
            backfill_pending.append((r["qishu"], on))
    # 去重批量写回
    for qs, on in set(backfill_pending):
        _settle_real_orders_for(game, qs, on)

    # 重新查（拿到刚回填的 result/win_amount）
    if backfill_pending:
        try:
            with _sim_db.lock:
                with _sim_db._conn() as conn:
                    where_extra = ""
                    params = [username, int(game)]
                    if date_str:
                        where_extra = " AND date(created_at) = ?"
                        params.append(date_str)
                    rows = conn.execute(
                        f"""SELECT id, qishu, uid, tel, press_str, bet_amount, ok, msg, created_at, source,
                                   result, win_amount, settled_at
                            FROM real_orders
                            WHERE username=? AND style=?{where_extra}
                            ORDER BY id DESC LIMIT ?""",
                        params + [limit]).fetchall()
                    orders_raw = [dict(r) for r in rows]
        except Exception:
            pass

    data = []
    for r in orders_raw:
        settled = bool(r.get("settled_at"))
        on = r.get("result")
        win = int(r.get("win_amount") or 0)
        data.append({
            "qishu": r["qishu"],
            "uid": r["uid"],
            "tel": r["tel"],
            "betAmount": r["bet_amount"],
            "winAmount": win if settled else 0,
            "result": on if settled else "--",
            "createTime": r["created_at"],
            "ok": bool(r["ok"]),
            "msg": r["msg"],
            "pending": (not settled) and bool(r["ok"]),
            "press_str": r["press_str"],
            "source": r.get("source") or "normal",
        })
    return jsonify({"ok": True, "data": data})

@app.route("/api/std/refresh", methods=["POST"])
@login_required
def api_std_refresh(username):
    # 触发账号刷新（前端会自动调 refreshAccounts）
    return jsonify({"ok": True})

@app.route("/api/std/remark", methods=["POST"])
@login_required
def api_std_remark(username):
    body = request.json or {}
    uid = body.get("uid","")
    remark = body.get("remark","")
    acc = _user_mgr.get_acc(username)
    if uid in acc.accounts:
        acc.accounts[uid]["remark"] = remark
        acc.save()
        _user_db.save_std_account(username, uid,
            acc.accounts[uid].get("tel",""), acc.accounts[uid].get("token",""),
            remark, password=acc.accounts[uid].get("password",""))
    return jsonify({"ok": True})

# ── 模拟下单（用户独立）──
@app.route("/api/sim/status")
@login_required
def api_sim_status(username):
    style = int(request.args.get("style", 210))
    slot  = int(request.args.get("slot", 1))
    eng = _user_mgr.get_sim(username, slot)
    return jsonify({"ok": True, "data": eng.get_status(style)})

@app.route("/api/sim/configure", methods=["POST"])
@login_required
def api_sim_configure(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    slot  = int(body.get("slot", 1))
    groups_text = body.get("groups_text","")
    muls_text   = body.get("multipliers_text","1")
    base_amount = int(body.get("base_amount", 10000))
    eng = _user_mgr.get_sim(username, slot)
    ok, msg = eng.configure(style, groups_text, muls_text, base_amount)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/sim/configure_map", methods=["POST"])
@login_required
def api_sim_configure_map(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    slot  = int(body.get("slot", 1))
    eng = _user_mgr.get_sim(username, slot)
    muls_text = body.get("multipliers_text","1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625")
    base_amount = int(body.get("base_amount", 10000))
    ok, msg = eng.configure_map(style, body.get("map_text",""), muls_text, base_amount)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/sim/configure_fix", methods=["POST"])
@login_required
def api_sim_configure_fix(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    slot  = int(body.get("slot", 1))
    eng = _user_mgr.get_sim(username, slot)
    muls_text = body.get("multipliers_text","1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625")
    base_amount = int(body.get("base_amount", 10000))
    ok, msg = eng.configure_fix(style, body.get("fix_text",""), muls_text, base_amount)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/sim/configure_jump", methods=["POST"])
@login_required
def api_sim_configure_jump(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    slot  = int(body.get("slot", 1))
    eng = _user_mgr.get_sim(username, slot)
    muls_text = body.get("multipliers_text","1-2.5-6.25-15.625-39.0625-97.65625-244.140625-610.3515625-1525.87890625")
    base_amount = int(body.get("base_amount", 10000))
    ok, msg = eng.configure_jump(style, body.get("jump_text",""), muls_text, base_amount)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/sim/fix_options", methods=["POST"])
@login_required
def api_sim_fix_options(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    slot  = int(body.get("slot", 1))
    eng = _user_mgr.get_sim(username, slot)
    ok, msg = eng.set_fix_options(
        style,
        stop_on_win    = body.get("stop_on_win"),
        stop_on_exhaust= body.get("stop_on_exhaust"),
    )
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/sim/start", methods=["POST"])
@login_required
def api_sim_start(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    mode  = body.get("mode","random")
    slot  = int(body.get("slot", 1))
    eng = _user_mgr.get_sim(username, slot)
    ok, msg = eng.start(style, mode)
    # ⭐ 启动模拟 = 用户主动操作 → 清除该用户所有爆仓标记
    if ok:
        _unban_all_for_user(username)
        # ⭐ bug 2：启动后立即在当前 next_qishu 下一注，避免用户等到下一期才看到下单
        try:
            game_key = "jnd28" if style == 210 else "btc28"
            with _countdown_lock:
                c = _countdown_cache.get(game_key) or {}
            cur_next = c.get("next_qishu")
            if cur_next:
                eng.place_bet(style, str(cur_next))
                print(f"[api_sim_start] 启动后立即下单 user={username} style={style} mode={mode} qishu={cur_next}")
        except Exception as e:
            print(f"[api_sim_start immediate place_bet] {e}")
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/sim/banned_accounts")
@login_required
def api_sim_banned_accounts(username):
    """前端 banner 查询：当前用户哪些账号爆仓了。"""
    return jsonify({"ok": True, "data": _get_banned_for_user(username)})

@app.route("/api/sim/stop", methods=["POST"])
@login_required
def api_sim_stop(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    mode  = body.get("mode","random")
    slot  = int(body.get("slot", 1))
    eng = _user_mgr.get_sim(username, slot)
    ok, msg = eng.stop(style, mode)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/sim/reset", methods=["POST"])
@login_required
def api_sim_reset(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    slot  = int(body.get("slot", 1))
    mode  = str(body.get("mode", "random"))
    if mode not in ("random", "map"):
        mode = "random"
    eng = _user_mgr.get_sim(username, slot)
    ok, msg = eng.reset(style, mode)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/sim/clear", methods=["POST"])
@login_required
def api_sim_clear(username):
    """清空指定 slot + style 的所有模拟数据（records/组日志/累计盈亏/倍率位置 + DB 历史）。
    配置（groups_text/muls_text/base_amount/stop_profit）保留。"""
    body = request.json or {}
    try:
        style = int(body.get("style", 210))
        slot  = int(body.get("slot", 1))
    except Exception:
        return jsonify({"ok": False, "msg": "参数错误"})
    eng = _user_mgr.get_sim(username, slot)
    ok, msg = eng.clear_all_data(style)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/real_orders/clear", methods=["POST"])
@login_required
def api_real_orders_clear(username):
    """删除当前登录用户的指定 style 全部参与记录。"""
    body = request.json or {}
    try:
        style = int(body.get("style", 210))
    except Exception:
        return jsonify({"ok": False, "msg": "参数错误"})
    n = _sim_db.delete_real_orders(username, style)
    return jsonify({"ok": True, "msg": f"已删除 {n} 条记录"})

# ── 真实参与开关（服务端持久化，浏览器关了也照跑）──────────────────────

@app.route("/api/sim/real/toggle", methods=["POST"])
@login_required
def api_sim_real_toggle(username):
    body = request.json or {}
    slot  = int(body.get("slot", 1))
    style = int(body.get("style", 210))
    mode  = str(body.get("mode", "random"))
    on    = bool(body.get("on"))
    if mode not in ("random", "map", "fix", "jump"):
        return jsonify({"ok": False, "msg": "mode 错误"})
    eng = _user_mgr.get_sim(username, slot)
    with eng.lock:
        s = eng._get_state(style)
        s[f"real_enabled_{mode}"] = on
        if on:
            # 打开开关 → 重置真实参与状态（从最低倍率开始，对账型）
            # fix/jump 不维护独立 real_mul_idx（跟模拟同步），但 last/settled 标记仍重置
            if mode in ("random", "map"):
                s[f"real_mul_idx_{mode}"] = 0
            s[f"real_last_qishu_{mode}"] = None
            s[f"real_settled_qishu_{mode}"] = None
    eng.save()
    return jsonify({"ok": True, "on": on})

@app.route("/api/miss/real/toggle", methods=["POST"])
@login_required
def api_miss_real_toggle(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    on    = bool(body.get("on"))
    eng = _user_mgr.get_miss(username)
    with eng.lock:
        eng.state[f"real_enabled_{style}"] = on
    eng.save()
    return jsonify({"ok": True, "on": on})

@app.route("/api/sim/real/migrate", methods=["POST"])
@login_required
def api_sim_real_migrate(username):
    """前端首次启动一次性把 localStorage 的开关推过来。
    body: {sim:[{slot,style,mode,on}], miss:[{style,on}]}
    """
    body = request.json or {}
    sim_list = body.get("sim") or []
    miss_list = body.get("miss") or []
    sim_done = 0; miss_done = 0
    for it in sim_list:
        try:
            slot  = int(it.get("slot"))
            style = int(it.get("style"))
            mode  = str(it.get("mode"))
            on    = bool(it.get("on"))
            if mode not in ("random", "map", "fix", "jump"):
                continue
            eng = _user_mgr.get_sim(username, slot)
            with eng.lock:
                s = eng._get_state(style)
                if bool(s.get(f"real_enabled_{mode}")) != on:
                    s[f"real_enabled_{mode}"] = on
                    if on:
                        if mode in ("random", "map"):
                            s[f"real_mul_idx_{mode}"] = 0
                        s[f"real_last_qishu_{mode}"] = None
                        s[f"real_settled_qishu_{mode}"] = None
            eng.save()
            sim_done += 1
        except Exception as e:
            print(f"[migrate sim] {e}")
    for it in miss_list:
        try:
            style = int(it.get("style"))
            on    = bool(it.get("on"))
            eng = _user_mgr.get_miss(username)
            with eng.lock:
                eng.state[f"real_enabled_{style}"] = on
            eng.save()
            miss_done += 1
        except Exception as e:
            print(f"[migrate miss] {e}")
    return jsonify({"ok": True, "sim": sim_done, "miss": miss_done})

@app.route("/api/sim/stop_profit", methods=["POST"])
@login_required
def api_sim_stop_profit(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    mode  = body.get("mode","random")
    # 兼容前端：amount（前端正在用）/ value（旧字段）都接受
    val   = int(body.get("amount", body.get("value", 0)) or 0)
    slot  = int(body.get("slot", 1))
    eng = _user_mgr.get_sim(username, slot)
    eng._get_state(style)[f"stop_profit_{mode}"] = val
    eng.save()
    msg = (f"止盈已设为 +{val:,}" if val > 0 else "止盈已关闭")
    return jsonify({"ok": True, "msg": msg, "value": val})

@app.route("/api/sim/history_db")
@login_required
def api_sim_history_db(username):
    style  = int(request.args.get("style", 210))
    mode   = request.args.get("mode","random")
    slot   = int(request.args.get("slot", 1))
    date_str = request.args.get("date", now_cn().strftime("%Y-%m-%d"))
    eng_name = f"user_{username}_s{slot}"
    groups = _sim_db.query_groups(eng_name, style, mode, date_str)
    dates  = _sim_db.get_dates(eng_name, style, mode)
    pnl    = _sim_db.daily_pnl(eng_name, style, mode, date_str)
    return jsonify({"ok": True, "groups": groups, "dates": dates, "daily_pnl": pnl, "date": date_str})

# ── 遗漏检测（用户独立）──
@app.route("/api/miss/configure", methods=["POST"])
@login_required
def api_miss_configure(username):
    body = request.json or {}
    eng = _user_mgr.get_miss(username)
    ok, msg = eng.configure(
        body.get("groups_text",""), body.get("random_text",""),
        body.get("muls_text","1"), int(body.get("base_amount",10000)),
        int(body.get("miss_n",5))
    )
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/miss/execute", methods=["POST"])
@login_required
def api_miss_execute(username):
    body = request.json or {}
    style = int(body.get("style", 0))
    history_210 = [{"sum": h["sum"], "qishu": h.get("qishu")} for h in state.get("history",[]) if h.get("sum") is not None]
    history_60  = fetch_60_history(None, 50)

    def get_fresh_next(style_int):
        try:
            if style_int == 210:
                _, nq = fetch_28vp(VP28_URL_210, "https://28vp.com/btc28.html")
                last = state.get("last_qishu")
            else:
                _, nq = fetch_28vp(VP28_URL_60, "https://28vp.com/btc28.html")
                last = state_60.get("last_qishu")
            if nq and str(nq) != str(last):
                return str(nq)
        except:
            pass
        return None

    eng = _user_mgr.get_miss(username)
    if style == 210:
        nq = get_fresh_next(210)
        if not nq:
            return jsonify({"ok": False, "msg": "暂无未开奖期号，请等待新期"})
        ok, msg, results = eng.execute(history_210, [], nq, None, None)
    elif style == 60:
        nq = get_fresh_next(60)
        if not nq:
            return jsonify({"ok": False, "msg": "暂无未开奖期号，请等待新期"})
        ok, msg, results = eng.execute([], history_60, None, nq, None)
    else:
        ok, msg, results = eng.execute(history_210, history_60,
            get_fresh_next(210), get_fresh_next(60), None)
    return jsonify({"ok": ok, "msg": msg, "results": results})

@app.route("/api/miss/auto", methods=["POST"])
@login_required
def api_miss_auto(username):
    body = request.json or {}
    style = int(body.get("style", 210))
    enabled = bool(body.get("enabled", False))
    eng = _user_mgr.get_miss(username)
    ok, msg = eng.set_auto(style, enabled)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/miss/reset", methods=["POST"])
@login_required
def api_miss_reset(username):
    body = request.json or {}
    style = body.get("style", None)
    eng = _user_mgr.get_miss(username)
    ok, msg = eng.reset(int(style) if style else None)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/miss/status")
@login_required
def api_miss_status(username):
    eng = _user_mgr.get_miss(username)
    return jsonify({"ok": True, "data": eng.get_status()})

# ── 🎯 打尾玩法 ──────────────────────────────────────────────
@app.route("/api/dawei/configure", methods=["POST"])
@login_required
def api_dawei_configure(username):
    body = request.json or {}
    slot  = int(body.get("slot", 1))
    style = int(body.get("style", 210))
    eng = _user_mgr.get_dawei(username, slot)
    ok, msg = eng.configure(
        style,
        body.get("tail_count", 5),
        body.get("detect_n", 30),
        body.get("base_amount", 1000),
        body.get("muls_text", "1"),
        body.get("pause_periods", 0),
    )
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/dawei/start", methods=["POST"])
@login_required
def api_dawei_start(username):
    body = request.json or {}
    slot  = int(body.get("slot", 1))
    style = int(body.get("style", 210))
    on    = bool(body.get("on"))
    eng = _user_mgr.get_dawei(username, slot)
    ok, msg = eng.set_running(style, on)
    return jsonify({"ok": ok, "msg": msg, "on": on})

@app.route("/api/dawei/reset", methods=["POST"])
@login_required
def api_dawei_reset(username):
    body = request.json or {}
    slot  = int(body.get("slot", 1))
    style = body.get("style", None)
    eng = _user_mgr.get_dawei(username, slot)
    ok, msg = eng.reset(int(style) if style else None)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/dawei/real/toggle", methods=["POST"])
@login_required
def api_dawei_real_toggle(username):
    body = request.json or {}
    slot  = int(body.get("slot", 1))
    style = int(body.get("style", 210))
    on    = bool(body.get("on"))
    eng = _user_mgr.get_dawei(username, slot)
    ok, msg = eng.set_real(style, on)
    return jsonify({"ok": ok, "on": on})

@app.route("/api/dawei/status")
@login_required
def api_dawei_status(username):
    slot = int(request.args.get("slot", 1))
    eng = _user_mgr.get_dawei(username, slot)
    return jsonify({"ok": True, "data": eng.get_status()})

# ── 📋 计划跟投（杀5余，仅欢乐210）──────────────────────────
@app.route("/api/plan/configure", methods=["POST"])
@login_required
def api_plan_configure(username):
    body = request.json or {}
    eng = _user_mgr.get_plan(username)
    ok, msg = eng.configure(
        body.get("base_amount", 1000),
        body.get("stop_profit", 0),
        body.get("min_lianzhong", 4),
        body.get("muls_text", None),
    )
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/plan/start", methods=["POST"])
@login_required
def api_plan_start(username):
    body = request.json or {}
    on = bool(body.get("on"))
    eng = _user_mgr.get_plan(username)
    ok, msg = eng.set_running(on)
    return jsonify({"ok": ok, "msg": msg, "on": on})

@app.route("/api/plan/reset", methods=["POST"])
@login_required
def api_plan_reset(username):
    eng = _user_mgr.get_plan(username)
    ok, msg = eng.reset()
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/plan/real/toggle", methods=["POST"])
@login_required
def api_plan_real_toggle(username):
    body = request.json or {}
    on = bool(body.get("on"))
    eng = _user_mgr.get_plan(username)
    ok, msg = eng.set_real(on)
    return jsonify({"ok": True, "on": on})

@app.route("/api/plan/status")
@login_required
def api_plan_status(username):
    eng = _user_mgr.get_plan(username)
    return jsonify({"ok": True, "data": eng.get_status()})

@app.route("/api/plan/preview")
@login_required
def api_plan_preview(username):
    """实时预览：当前 8 专家连对 + 冷号 + 选号（不下注，供前端展示）"""
    try:
        experts, pending = _fetch_wanjia_plans()
        _hist_210 = [{"sum": h["sum"], "qishu": h.get("qishu")} for h in state.get("history", []) if h.get("sum") is not None]
        cold_set, miss = _fetch_cold_numbers(_hist_210)
        eng = _user_mgr.get_plan(username)
        min_lz = int(eng.state.get("min_lianzhong", 4))
        sel = _plan_select(experts, min_lz, cold_set)
        experts_info = []
        for i, rows in enumerate(experts, 1):
            if not rows:
                experts_info.append({"id": i, "lianzhong": 0, "pred": None})
                continue
            experts_info.append({
                "id": i,
                "lianzhong": _plan_lianzhong(rows),
                "pred": rows[0][1],
            })
        return jsonify({"ok": True, "pending_qishu": pending,
                        "experts": experts_info, "selected": sel,
                        "cold": sorted(cold_set),
                        "cold_detail": {str(n): miss.get(n, 0) for n in range(8, 20)}})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ══════════════════════════════════════════════════════════════
#  管理端路由（/Admin123456 前缀）
# ══════════════════════════════════════════════════════════════

@app.route(f"{ADMIN_PATH}/login", methods=["GET","POST"])
def admin_login():
    if request.method == "GET":
        return Response(_platform_rewrite(build_admin_login_html()), mimetype="text/html")
    body = request.json or request.form
    if body.get("username") == ADMIN_USER and body.get("password") == ADMIN_PASS:
        a_token = f"admin_{ADMIN_PASS}"
        resp = jsonify({"ok": True, "a_token": a_token})
        resp.set_cookie("a_token", a_token, max_age=86400*7, httponly=False, samesite="Lax")
        return resp
    return jsonify({"ok": False, "msg": "账号或密码错误"})

@app.route(f"{ADMIN_PATH}/logout", methods=["POST"])
def admin_logout():
    resp = jsonify({"ok": True})
    resp.delete_cookie("a_token")
    return resp

@app.route(ADMIN_PATH)
@app.route(f"{ADMIN_PATH}/")
@admin_required
def admin_index():
    return Response(_platform_rewrite(build_admin_html()), mimetype="text/html")

# ── 管理端：用户管理 ──
# 🪨 admin/users 账号信息缓存，避免重复调石头岛接口（前端 5 秒一刷）
_admin_users_cache = {"ts": 0, "data": None}
_admin_users_cache_lock = threading.Lock()

@app.route("/api/admin/users")
@admin_required
def admin_list_users():
    # 命中 5 秒缓存 → 直接返回（修闪烁 + 避免重复打石头岛接口）
    with _admin_users_cache_lock:
        if _admin_users_cache["data"] and (time.time() - _admin_users_cache["ts"]) < 5:
            return jsonify({"ok": True, "data": _admin_users_cache["data"], "cached": True})

    users = _user_db.list_users()

    def _one_user(u):
        accs = _user_db.get_std_accounts(u["username"])

        def _fetch_acc(a):
            try:
                info = std_get_user_info(a["token"])
                if info:
                    return {"tel": a["tel"],
                            "balance": int(info.get("silver") or info.get("balance") or 0),
                            "nick_name": info.get("nickname") or info.get("nick_name","") or "",
                            "online": True}
                return {"tel": a["tel"], "online": False}
            except Exception:
                return {"tel": a["tel"], "online": False}

        if accs:
            with ThreadPoolExecutor(max_workers=min(8, len(accs))) as ex:
                acc_info = list(ex.map(_fetch_acc, accs))
        else:
            acc_info = []

        return {
            "username": u["username"],
            "expires_at": u.get("expires_at","") or "",
            "created_at": u.get("created_at","") or "",
            "remark": u.get("remark","") or "",
            "max_accounts": int(u.get("max_accounts") or 5),
            "current_accounts": len(accs),
            "std_accounts": acc_info,
        }

    if users:
        with ThreadPoolExecutor(max_workers=min(6, len(users))) as ex:
            result = list(ex.map(_one_user, users))
    else:
        result = []

    with _admin_users_cache_lock:
        _admin_users_cache["data"] = result
        _admin_users_cache["ts"] = time.time()
    return jsonify({"ok": True, "data": result})

@app.route("/api/admin/user_detail")
@admin_required
def admin_user_detail():
    """admin 端：查任一脚本用户的完整详情：基本信息 + 平台账号(含明文密码) + 下单记录。
    query: ?username=xxx&game=210|60|all&source=&date=&limit="""
    username = (request.args.get("username") or "").strip()
    if not username:
        return jsonify({"ok": False, "msg": "缺少 username"})
    u = _user_db.get_user(username)
    if not u:
        return jsonify({"ok": False, "msg": "用户不存在"})
    game = (request.args.get("game") or "all").strip()
    source_filter = (request.args.get("source") or "").strip()
    date_str = (request.args.get("date") or "").strip()
    try:
        limit = max(1, min(5000, int(request.args.get("limit", 500))))
    except Exception:
        limit = 500

    # 基本信息（含明文密码，老用户可能为空字符串）
    base = {
        "username":         u.get("username", ""),
        "password_plain":   u.get("password_plain", "") or "",
        "expires_at":       u.get("expires_at", "") or "",
        "created_at":       u.get("created_at", "") or "",
        "remark":           u.get("remark", "") or "",
        "max_accounts":     int(u.get("max_accounts") or 5),
    }

    # 平台账号（含明文密码 + token）
    std_accs = _user_db.get_std_accounts(username) or []
    accs = []
    for a in std_accs:
        accs.append({
            "uid":      a.get("uid", ""),
            "tel":      a.get("tel", ""),
            "remark":   a.get("remark", "") or "",
            "password": a.get("password", "") or "",
            "token":    (a.get("token", "") or "")[:24] + "..." if a.get("token") else "",
        })

    # 下单记录（查 real_orders 表，按筛选条件）
    orders = []
    try:
        sql = ("SELECT id, uid, tel, style, qishu, press_str, bet_amount, ok, msg, "
               "created_at, source, result, win_amount, settled_at "
               "FROM real_orders WHERE username=?")
        args = [username]
        if game in ("210", "60"):
            sql += " AND style=?"
            args.append(int(game))
        if date_str:
            sql += " AND substr(created_at,1,10)=?"
            args.append(date_str)
        if source_filter:
            if source_filter == "normal":
                sql += " AND (source='normal' OR source='manual' OR source IS NULL OR source='')"
            elif source_filter == "miss":
                sql += " AND source LIKE 'miss%'"
            else:
                sql += " AND source=?"
                args.append(source_filter)
        sql += " ORDER BY id DESC LIMIT ?"
        args.append(limit)
        with _sim_db.lock:
            with _sim_db._conn() as conn:
                cur = conn.execute(sql, args)
                cols = [c[0] for c in cur.description]
                for r in cur.fetchall():
                    d = dict(zip(cols, r))
                    bet = int(d.get("bet_amount") or 0)
                    res = d.get("result")
                    win = d.get("win_amount")
                    ok_v = bool(d.get("ok"))
                    pending = (ok_v and res is None)
                    orders.append({
                        "id":         d.get("id"),
                        "uid":        d.get("uid") or "",
                        "tel":        d.get("tel") or "",
                        "style":      int(d.get("style") or 0),
                        "qishu":      str(d.get("qishu") or ""),
                        "press_str":  d.get("press_str") or "",
                        "betAmount":  bet,
                        "winAmount":  int(win) if win is not None else 0,
                        "result":     int(res) if res is not None else "--",
                        "pending":    bool(pending),
                        "ok":         ok_v,
                        "msg":        d.get("msg") or "",
                        "source":     d.get("source") or "",
                        "createTime": d.get("created_at") or "",
                        "pnl":        (int(win) - bet) if (win is not None and ok_v) else 0,
                    })
    except Exception as e:
        print(f"[admin_user_detail orders] {e}")

    stake = sum(o["betAmount"] for o in orders if o["ok"])
    win_sum = sum(o["winAmount"] for o in orders if o["ok"] and not o["pending"])
    pnl_total = sum(o["pnl"] for o in orders if o["ok"] and not o["pending"])
    won_cnt = sum(1 for o in orders if o["ok"] and not o["pending"] and o["winAmount"] > 0)
    lost_cnt = sum(1 for o in orders if o["ok"] and not o["pending"] and o["winAmount"] <= 0)
    pending_cnt = sum(1 for o in orders if o["pending"])

    return jsonify({
        "ok": True,
        "user": base,
        "accounts": accs,
        "orders":   orders,
        "stats": {
            "count":   len(orders),
            "stake":   stake,
            "win":     win_sum,
            "pnl":     pnl_total,
            "won":     won_cnt,
            "lost":    lost_cnt,
            "pending": pending_cnt,
        }
    })


@app.route("/api/admin/users/create", methods=["POST"])
@admin_required
def admin_create_user():
    body = request.json or {}
    username = body.get("username","").strip()
    password = body.get("password","").strip()
    expires_at = body.get("expires_at","")
    remark = body.get("remark","")
    max_accounts = int(body.get("max_accounts") or 5)
    if not username or not password:
        return jsonify({"ok": False, "msg": "用户名和密码不能为空"})
    ok, msg = _user_db.create_user(username, password, expires_at or None, remark)
    if ok:
        _user_db.set_user_max_accounts(username, max_accounts)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/users/update", methods=["POST"])
@admin_required
def admin_update_user():
    body = request.json or {}
    username = body.get("username","")
    ok, msg = _user_db.update_user(
        username,
        password=body.get("password") or None,
        expires_at=body.get("expires_at"),
        remark=body.get("remark")
    )
    # 🪨 石头岛版：额外更新账号上限
    if "max_accounts" in body:
        try:
            _user_db.set_user_max_accounts(username, int(body.get("max_accounts") or 5))
        except Exception as e:
            print(f"[admin_update_user max_accounts] {e}")
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/users/delete", methods=["POST"])
@admin_required
def admin_delete_user():
    username = (request.json or {}).get("username","")
    ok, msg = _user_db.delete_user(username)
    if ok:
        _user_mgr.remove_user(username)
    return jsonify({"ok": ok, "msg": msg})

# ── 管理端：开奖监控（原有功能）──
@app.route("/api/admin/status")
@admin_required
def admin_status():
    return jsonify({"ok": True, "countdown": state["countdown"], "last_qishu": state["last_qishu"],
                    "fetch_time": state["fetch_time"], "fast_mode": state["fast_mode"],
                    "notifications": state["notifications"], "countdown_60": state_60.get("countdown",0)})

@app.route("/api/admin/history")
@admin_required
def admin_history():
    return jsonify({"ok": True, "data": state["history"], "fetch_time": state["fetch_time"]})

@app.route("/api/admin/history60")
@admin_required
def admin_history60():
    return jsonify({"ok": True, "data": state_60["history"], "last_qishu": state_60["last_qishu"]})

# ── 管理端：管理端自己的模拟下单（保留原有8套）──
@app.route("/api/admin/sim/status")
@admin_required
def admin_sim_status():
    style = int(request.args.get("style", 210))
    slot  = int(request.args.get("slot", 1))
    group = int(request.args.get("group", 1))
    return jsonify({"ok": True, "data": get_admin_sim(slot, group).get_status(style)})

@app.route("/api/admin/sim/configure", methods=["POST"])
@admin_required
def admin_sim_configure():
    body = request.json or {}
    style = int(body.get("style", 210))
    slot  = int(body.get("slot", 1))
    group = int(body.get("group", 1))
    ok, msg = get_admin_sim(slot, group).configure(style, body.get("groups_text",""), body.get("multipliers_text","1"), int(body.get("base_amount",10000)))
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/sim/configure_map", methods=["POST"])
@admin_required
def admin_sim_configure_map():
    body = request.json or {}
    style = int(body.get("style", 210))
    slot  = int(body.get("slot", 1))
    group = int(body.get("group", 1))
    ok, msg = get_admin_sim(slot, group).configure_map(style, body.get("map_text",""))
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/sim/start", methods=["POST"])
@admin_required
def admin_sim_start():
    body = request.json or {}
    ok, msg = get_admin_sim(int(body.get("slot",1)), int(body.get("group",1))).start(int(body.get("style",210)), body.get("mode","random"))
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/sim/stop", methods=["POST"])
@admin_required
def admin_sim_stop():
    body = request.json or {}
    ok, msg = get_admin_sim(int(body.get("slot",1)), int(body.get("group",1))).stop(int(body.get("style",210)), body.get("mode","random"))
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/sim/reset", methods=["POST"])
@admin_required
def admin_sim_reset():
    body = request.json or {}
    ok, msg = get_admin_sim(int(body.get("slot",1)), int(body.get("group",1))).reset(int(body.get("style",210)))
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/sim/stop_profit", methods=["POST"])
@admin_required
def admin_sim_stop_profit():
    body = request.json or {}
    style = int(body.get("style",210)); mode = body.get("mode","random")
    # 兼容 amount/value
    val = int(body.get("amount", body.get("value", 0)) or 0)
    slot = int(body.get("slot",1)); group = int(body.get("group",1))
    eng = get_admin_sim(slot, group)
    eng._get_state(style)[f"stop_profit_{mode}"] = val
    eng.save()
    msg = (f"止盈已设为 +{val:,}" if val > 0 else "止盈已关闭")
    return jsonify({"ok": True, "msg": msg, "value": val})

@app.route("/api/admin/sim/history_db")
@admin_required
def admin_sim_history_db():
    style  = int(request.args.get("style", 210))
    slot   = int(request.args.get("slot", 1))
    group  = int(request.args.get("group", 1))
    mode   = request.args.get("mode","random")
    date_str = request.args.get("date", now_cn().strftime("%Y-%m-%d"))
    eng = get_admin_sim(slot, group)
    groups = _sim_db.query_groups(eng.engine_name, style, mode, date_str)
    dates  = _sim_db.get_dates(eng.engine_name, style, mode)
    pnl    = _sim_db.daily_pnl(eng.engine_name, style, mode, date_str)
    return jsonify({"ok": True, "groups": groups, "dates": dates, "daily_pnl": pnl, "date": date_str})

@app.route("/api/admin/miss/configure", methods=["POST"])
@admin_required
def admin_miss_configure():
    body = request.json or {}
    ok, msg = _admin_miss.configure(body.get("groups_text",""), body.get("random_text",""),
        body.get("muls_text","1"), int(body.get("base_amount",10000)), int(body.get("miss_n",5)))
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/miss/execute", methods=["POST"])
@admin_required
def admin_miss_execute():
    body = request.json or {}
    style = int(body.get("style", 0))
    history_210 = [{"sum": h["sum"], "qishu": h.get("qishu")} for h in state.get("history",[]) if h.get("sum") is not None]
    history_60  = fetch_60_history(None, 50)
    def get_fresh_next(style_int):
        try:
            if style_int == 210:
                _, nq = fetch_28vp(VP28_URL_210, "https://28vp.com/btc28.html")
                last = state.get("last_qishu")
            else:
                _, nq = fetch_28vp(VP28_URL_60, "https://28vp.com/btc28.html")
                last = state_60.get("last_qishu")
            if nq and str(nq) != str(last): return str(nq)
        except: pass
        return None
    if style == 210:
        nq = get_fresh_next(210)
        if not nq: return jsonify({"ok": False, "msg": "暂无未开奖期号"})
        ok, msg, results = _admin_miss.execute(history_210, [], nq, None, None)
    elif style == 60:
        nq = get_fresh_next(60)
        if not nq: return jsonify({"ok": False, "msg": "暂无未开奖期号"})
        ok, msg, results = _admin_miss.execute([], history_60, None, nq, None)
    else:
        ok, msg, results = _admin_miss.execute(history_210, history_60, get_fresh_next(210), get_fresh_next(60), None)
    return jsonify({"ok": ok, "msg": msg, "results": results})

@app.route("/api/admin/miss/auto", methods=["POST"])
@admin_required
def admin_miss_auto():
    body = request.json or {}
    style = int(body.get("style", 210)); enabled = bool(body.get("enabled", False))
    ok, msg = _admin_miss.set_auto(style, enabled)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/miss/reset", methods=["POST"])
@admin_required
def admin_miss_reset():
    body = request.json or {}
    style = body.get("style", None)
    ok, msg = _admin_miss.reset(int(style) if style else None)
    return jsonify({"ok": ok, "msg": msg})

@app.route("/api/admin/miss/status")
@admin_required
def admin_miss_status():
    return jsonify({"ok": True, "data": _admin_miss.get_status()})






# ══════════════════════════════════════════════════════════════
#  广播用户引擎（在轮询线程里调用）
# ══════════════════════════════════════════════════════════════
def broadcast_user_engines(style, qishu, result_sum):
    _user_mgr.broadcast_result(style, qishu, result_sum)

def broadcast_user_place_bet(style, next_qishu):
    _user_mgr.broadcast_place_bet(style, next_qishu)

# ══════════════════════════════════════════════════════════════
#  💳 支付系统 API（管理端 + 客户端 + 回调）
# ══════════════════════════════════════════════════════════════

# ── 管理端：配置 CRUD ──
@app.route("/api/admin/payment/config", methods=["GET"])
@admin_required
def admin_pay_config_get():
    cfg = _pay_get_config(force_refresh=True) or {}
    # 不暴露 merchant_key 全文（前端编辑时只显示 ****），但管理员能看
    return jsonify({"ok": True, "data": cfg})

@app.route("/api/admin/payment/config", methods=["POST"])
@admin_required
def admin_pay_config_save():
    body = request.json or {}
    # 允许更新的字段
    upd = {}
    for k in ("api_url", "merchant_id", "merchant_key"):
        if k in body: upd[k] = str(body[k]).strip()
    for k in ("free_register_enabled", "free_register_days", "free_register_max_accounts"):
        if k in body:
            try: upd[k] = int(body[k])
            except Exception: pass
    if "plans" in body and isinstance(body["plans"], dict):
        upd["plans"] = body["plans"]
    _pay_save_config(upd)
    return jsonify({"ok": True, "msg": "已保存"})

# ── 管理端：订单查询（默认 15 天）──
@app.route("/api/admin/payment/orders", methods=["GET"])
@admin_required
def admin_pay_orders():
    try: days = max(1, min(int(request.args.get("days", 15)), 90))
    except Exception: days = 15
    cutoff = (now_cn() - timedelta(days=days)).strftime("%Y-%m-%d %H:%M:%S")
    status = (request.args.get("status") or "").strip()
    try: limit = max(1, min(int(request.args.get("limit", 500)), 2000))
    except Exception: limit = 500
    rows = []
    try:
        with _user_db._conn() as c:
            sql = ("SELECT * FROM payment_orders WHERE created_at >= ?"
                   + (" AND status=?" if status else "")
                   + " ORDER BY id DESC LIMIT ?")
            params = [cutoff] + ([status] if status else []) + [limit]
            for r in c.execute(sql, params):
                d = dict(r)
                # 不返回密码明文
                if d.get("register_password"):
                    d["register_password"] = "***"
                rows.append(d)
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})
    return jsonify({"ok": True, "data": rows, "days": days})

# ── 管理端：手动退款 ──
@app.route("/api/admin/payment/refund", methods=["POST"])
@admin_required
def admin_pay_refund():
    body = request.json or {}
    otn = (body.get("out_trade_no") or "").strip()
    if not otn:
        return jsonify({"ok": False, "msg": "缺少 out_trade_no"})
    try:
        with _user_db._conn() as c:
            row = c.execute("SELECT * FROM payment_orders WHERE out_trade_no=?", (otn,)).fetchone()
        if not row: return jsonify({"ok": False, "msg": "订单不存在"})
        order = dict(row)
        if order["status"] != "paid":
            return jsonify({"ok": False, "msg": f"订单状态={order['status']}，仅 paid 可退"})
        ok, msg = _pay_refund_order(otn, order["amount"], trade_no=order.get("trade_no"))
        if ok:
            with _user_db._conn() as c:
                c.execute("UPDATE payment_orders SET status='refunded', refunded_at=? WHERE out_trade_no=?",
                          (now_cn().strftime("%Y-%m-%d %H:%M:%S"), otn))
                c.commit()
        return jsonify({"ok": ok, "msg": msg})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})

# ── 客户端：拉套餐 ──
@app.route("/api/payment/plans", methods=["GET"])
def pay_plans():
    cfg = _pay_get_config() or {}
    plans = cfg.get("plans") or {}
    # 只返回 enabled 的
    out = {}
    for k, v in plans.items():
        if isinstance(v, dict) and v.get("enabled", True):
            out[k] = v
    return jsonify({
        "ok": True,
        "plans": out,
        "free_enabled": bool(cfg.get("free_register_enabled")),
        "free_days": int(cfg.get("free_register_days") or 3),
        "free_max_accounts": int(cfg.get("free_register_max_accounts") or 2),
    })

# ── 客户端：创建续费/加账号订单 ──
@app.route("/api/payment/create_order", methods=["POST"])
@login_required
def pay_create_order(username):
    body = request.json or {}
    plan_key = (body.get("plan_key") or "").strip()
    pay_type = (body.get("pay_type") or "cashier").strip()
    cfg = _pay_get_config() or {}
    plans = cfg.get("plans") or {}
    plan = plans.get(plan_key)
    if not plan or not plan.get("enabled", True):
        return jsonify({"ok": False, "msg": "套餐不存在或未启用"})
    if plan_key == "extra_account":
        plan_type = "extra_account"
        days = 0
        accounts = int(plan.get("accounts") or 1)
    else:
        plan_type = "renew"
        days = int(plan.get("days") or 0)
        accounts = int(plan.get("max_accounts") or 0)
    out_trade_no = _pay_make_out_trade_no("R")
    name = f"{plan.get('label','套餐')}-{username}"
    money = str(plan.get("price") or "0")
    base = request.host_url.rstrip("/")
    notify_url = f"{base}/api/payment/notify"
    return_url = f"{base}/api/payment/return"
    ok, info = _pay_create_order(out_trade_no, name, money, notify_url, return_url,
                                  pay_type=pay_type,
                                  client_ip=request.headers.get("X-Real-IP") or request.remote_addr or "127.0.0.1")
    if not ok:
        return jsonify({"ok": False, "msg": info})
    # 写订单（pending）
    try:
        with _user_db._conn() as c:
            c.execute("""INSERT INTO payment_orders
                (out_trade_no, trade_no, username, plan_type, plan_key, amount,
                 days, accounts, status, pay_type, pay_url, created_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'pending', ?, ?, ?)""",
                (out_trade_no, info.get("trade_no",""), username, plan_type, plan_key,
                 money, days, accounts, pay_type, info.get("payurl",""),
                 now_cn().strftime("%Y-%m-%d %H:%M:%S")))
            c.commit()
    except Exception as e:
        print(f"[pay_create_order INSERT] {e}")
    return jsonify({"ok": True, "out_trade_no": out_trade_no,
                    "payurl": info.get("payurl",""),
                    "qrcode": info.get("qrcode",""),
                    "amount": money,
                    "name": name})

# ── 注册：免费注册 ──
@app.route("/api/register/free", methods=["POST"])
def pay_register_free():
    body = request.json or {}
    uname = (body.get("username") or "").strip()
    pwd   = (body.get("password") or "").strip()
    if not uname or not pwd:
        return jsonify({"ok": False, "msg": "请填写账号和密码"})
    if len(uname) < 3 or len(uname) > 30:
        return jsonify({"ok": False, "msg": "账号长度 3-30"})
    if len(pwd) < 4:
        return jsonify({"ok": False, "msg": "密码至少 4 位"})
    cfg = _pay_get_config() or {}
    if not cfg.get("free_register_enabled"):
        return jsonify({"ok": False, "msg": "免费注册已关闭"})
    # 用户已存在？
    if _user_db.get_user(uname):
        return jsonify({"ok": False, "msg": "账号已存在"})
    days = int(cfg.get("free_register_days") or 3)
    max_acc = int(cfg.get("free_register_max_accounts") or 2)
    exp_at = (now_cn() + timedelta(days=days)).strftime("%Y-%m-%d %H:%M:%S")
    try:
        _user_db.create_user(uname, pwd, expires_at=exp_at, remark=f"免费注册 {days} 天")
        with _user_db._conn() as c:
            c.execute("UPDATE users SET max_accounts=? WHERE username=?", (max_acc, uname))
            c.commit()
    except Exception as e:
        return jsonify({"ok": False, "msg": f"注册失败: {e}"})
    return jsonify({"ok": True, "msg": f"注册成功！有效期到 {exp_at[:10]}，可登录 {max_acc} 个平台账号"})

# ── 注册：付费注册 ──
@app.route("/api/register/paid", methods=["POST"])
def pay_register_paid():
    body = request.json or {}
    uname = (body.get("username") or "").strip()
    pwd   = (body.get("password") or "").strip()
    plan_key = (body.get("plan_key") or "").strip()
    pay_type = (body.get("pay_type") or "cashier").strip()
    if not uname or not pwd:
        return jsonify({"ok": False, "msg": "请填写账号和密码"})
    if len(uname) < 3 or len(uname) > 30:
        return jsonify({"ok": False, "msg": "账号长度 3-30"})
    if len(pwd) < 4:
        return jsonify({"ok": False, "msg": "密码至少 4 位"})
    if _user_db.get_user(uname):
        return jsonify({"ok": False, "msg": "账号已存在，请直接登录或换一个"})
    cfg = _pay_get_config() or {}
    plans = cfg.get("plans") or {}
    plan = plans.get(plan_key)
    if not plan or plan_key == "extra_account":
        return jsonify({"ok": False, "msg": "套餐不存在或不可用于注册"})
    days = int(plan.get("days") or 0)
    max_acc = int(plan.get("max_accounts") or 0)
    money = str(plan.get("price") or "0")
    out_trade_no = _pay_make_out_trade_no("REG")
    name = f"{plan.get('label','套餐')}-注册-{uname}"
    base = request.host_url.rstrip("/")
    notify_url = f"{base}/api/payment/notify"
    return_url = f"{base}/api/payment/return"
    ok, info = _pay_create_order(out_trade_no, name, money, notify_url, return_url,
                                  pay_type=pay_type,
                                  client_ip=request.headers.get("X-Real-IP") or request.remote_addr or "127.0.0.1")
    if not ok:
        return jsonify({"ok": False, "msg": info})
    try:
        with _user_db._conn() as c:
            c.execute("""INSERT INTO payment_orders
                (out_trade_no, trade_no, username, plan_type, plan_key, amount,
                 days, accounts, status, pay_type, pay_url, register_password, created_at)
                VALUES (?, ?, ?, 'register', ?, ?, ?, ?, 'pending', ?, ?, ?, ?)""",
                (out_trade_no, info.get("trade_no",""), uname, plan_key,
                 money, days, max_acc, pay_type, info.get("payurl",""), pwd,
                 now_cn().strftime("%Y-%m-%d %H:%M:%S")))
            c.commit()
    except Exception as e:
        print(f"[pay_register_paid INSERT] {e}")
    return jsonify({"ok": True, "out_trade_no": out_trade_no,
                    "payurl": info.get("payurl",""),
                    "qrcode": info.get("qrcode",""),
                    "amount": money})

# ── 支付通知：异步 notify（核心业务逻辑）──
@app.route("/api/payment/notify", methods=["GET", "POST"])
def pay_notify():
    """支付平台异步通知，校验 sign 后做对应业务。返回纯文本 success（按 motionpay 文档）。"""
    params = dict(request.values)  # 兼容 GET / POST form
    cfg = _pay_get_config()
    if not cfg:
        print(f"[pay_notify] 配置缺失 params={params}")
        return "fail", 200
    if not _pay_verify_sign(params, cfg["merchant_key"]):
        print(f"[pay_notify] 验签失败 params={params}")
        return "fail", 200
    otn = params.get("out_trade_no", "")
    trade_status = params.get("trade_status", "")
    if not otn or trade_status != "TRADE_SUCCESS":
        print(f"[pay_notify] 跳过 otn={otn} status={trade_status}")
        return "success", 200
    try:
        with _user_db._conn() as c:
            row = c.execute("SELECT * FROM payment_orders WHERE out_trade_no=?", (otn,)).fetchone()
        if not row:
            print(f"[pay_notify] 订单不存在 otn={otn}")
            return "fail", 200
        order = dict(row)
        if order["status"] == "paid":
            print(f"[pay_notify] 订单已处理 otn={otn}")
            return "success", 200
        # 执行业务
        ok, msg = _pay_apply_business(order)
        new_status = "paid" if ok else "failed"
        with _user_db._conn() as c:
            c.execute("""UPDATE payment_orders SET status=?, trade_no=?, paid_at=?, notify_payload=? WHERE out_trade_no=?""",
                      (new_status, params.get("trade_no","") or order.get("trade_no",""),
                       now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                       json.dumps(params, ensure_ascii=False), otn))
            c.commit()
        print(f"[pay_notify] otn={otn} status={new_status} msg={msg}")
        return "success" if ok else "fail", 200
    except Exception as e:
        print(f"[pay_notify EXC] {e}")
        return "fail", 200

# ── 支付跳转回来 return_url（兼做业务派发兜底：notify 失败/没调时这里也能落账）──
@app.route("/api/payment/return", methods=["GET"])
def pay_return():
    params = dict(request.args)
    otn = (params.get("out_trade_no") or "").strip()
    status = (params.get("trade_status") or "").strip()
    ok_pay = (status == "TRADE_SUCCESS")
    # 业务派发：验签 + 找订单 + 派发（幂等：paid 状态跳过）
    if ok_pay and otn:
        cfg = _pay_get_config()
        if cfg and _pay_verify_sign(params, cfg["merchant_key"]):
            try:
                with _user_db._conn() as c:
                    row = c.execute("SELECT * FROM payment_orders WHERE out_trade_no=?", (otn,)).fetchone()
                if row:
                    order = dict(row)
                    if order["status"] != "paid":
                        ok, msg = _pay_apply_business(order)
                        new_status = "paid" if ok else "failed"
                        with _user_db._conn() as c:
                            c.execute("""UPDATE payment_orders SET status=?, trade_no=?, paid_at=?, notify_payload=? WHERE out_trade_no=?""",
                                      (new_status,
                                       params.get("trade_no","") or order.get("trade_no",""),
                                       now_cn().strftime("%Y-%m-%d %H:%M:%S"),
                                       json.dumps(params, ensure_ascii=False), otn))
                            c.commit()
                        print(f"[pay_return BUSINESS] otn={otn} status={new_status} msg={msg}")
                    else:
                        print(f"[pay_return] otn={otn} 已处理过，跳过")
                else:
                    print(f"[pay_return] otn={otn} 订单不存在")
            except Exception as e:
                print(f"[pay_return EXC] {e}")
        else:
            print(f"[pay_return] 验签失败或配置缺失 otn={otn}")
    # 简单 HTML 页面，3 秒后跳转回首页
    msg = "✅ 支付成功！" if ok_pay else "⏳ 支付状态未确认"
    sub = "正在为您开通..." if ok_pay else "如已支付请稍候 1 分钟，状态将自动更新"
    html = f"""<!DOCTYPE html><html><head><meta charset="UTF-8">
<title>支付结果</title>
<style>
body{{margin:0;background:#0c0e14;color:#e5e7eb;font-family:-apple-system,sans-serif;
     display:flex;align-items:center;justify-content:center;min-height:100vh}}
.card{{background:#12151e;border:1px solid #2a2f3e;border-radius:14px;padding:40px 60px;
      text-align:center;max-width:420px}}
.icon{{font-size:4rem;margin-bottom:14px}}
.title{{font-size:1.6rem;font-weight:800;margin-bottom:8px;color:{'#22c55e' if ok_pay else '#fbbf24'}}}
.sub{{font-size:.92rem;color:#94a3b8;margin-bottom:20px}}
.otn{{font-size:.75rem;color:#64748b;font-family:monospace;margin-bottom:18px}}
.btn{{display:inline-block;padding:10px 24px;background:#6366f1;color:#fff;border-radius:8px;
     text-decoration:none;font-weight:700}}
</style></head><body>
<div class="card">
<div class="icon">{'🎉' if ok_pay else '⏳'}</div>
<div class="title">{msg}</div>
<div class="sub">{sub}</div>
<div class="otn">订单号 {otn or '--'}</div>
<a class="btn" href="/">返回首页</a>
</div>
<script>setTimeout(function(){{location.href='/';}}, 4000);</script>
</body></html>"""
    return Response(html, mimetype="text/html")

# ══════════════════════════════════════════════════════════════
#  启动
# ══════════════════════════════════════════════════════════════
if __name__ == "__main__":
    os.makedirs(BASE_DIR, exist_ok=True)

    # ⭐ 服务启动后立即把所有用户的 SimEngine/MissEngine 实例都加载进内存
    # 否则停止前下的 pending 注会因为引擎未懒加载而漏掉开奖广播，永远不结算
    try:
        _user_mgr.ensure_all_loaded()
    except Exception as e:
        print(f"[startup ensure_all_loaded] {e}")

    # ⭐ 隐藏功能：账号到期自动静默关闭真实参与（防止账号过期还在烧钱下单）
    def _expired_users_loop():
        while True:
            try:
                now = now_cn()
                for u in (_user_db.list_users() or []):
                    exp_str = (u.get("expires_at") or "").strip()
                    if not exp_str:
                        continue
                    try:
                        exp = datetime.strptime(exp_str[:19], "%Y-%m-%d %H:%M:%S")
                    except Exception:
                        continue
                    if now > exp:
                        _user_mgr.disable_all_real_for_user(
                            u.get("username", ""), reason="账号已到期")
            except Exception as e:
                print(f"[expired_users_loop] {e}")
            time.sleep(60)
    threading.Thread(target=_expired_users_loop, daemon=True).start()

    # 启动轮询线程
    threading.Thread(target=poll_loop, daemon=True).start()
    threading.Thread(target=admin_acc_mgr.poll_loop, daemon=True).start()
    threading.Thread(target=central_poll_60, daemon=True).start()
    # ⭐ 启动 real_orders 后台回填线程（10秒一轮，扫描未结算行用内存 history 回填）
    threading.Thread(target=_backfill_real_orders_loop, daemon=True).start()

    print("🚀 app 启动 → http://0.0.0.0:17900")
    print(f"   客户端: http://0.0.0.0:17900/")
    print(f"   管理端: http://0.0.0.0:17900{ADMIN_PATH}")
    # 🚀 生产级 WSGI（waitress）：固定 32 线程池，慢请求不互相阻塞，去掉 dev server 警告
    try:
        from waitress import serve
        print("   WSGI: waitress (32 threads)")
        serve(app, host="0.0.0.0", port=17900, threads=32, ident="lejiting")
    except ImportError:
        print("   WSGI: Flask dev server（未装 waitress，fallback）")
        app.run(host="0.0.0.0", port=17900, debug=False, threaded=True)
