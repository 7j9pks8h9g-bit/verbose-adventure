#!/usr/bin/env python3
"""
Polymarket 5m Signals
Open + Now = Chainlink via Polymarket RTDS (wss://ws-live-data.polymarket.com)
Signals are produced ONLY from fresh Chainlink ticks (that is what Polymarket settles on).
If the Chainlink feed goes stale the coin is paused and the websocket is reconnected automatically.
"""

import os
import time
import math
import bisect
import json
import base64
import secrets
import asyncio
import logging
from datetime import datetime, timezone
from typing import Dict, Optional, List
from collections import deque

import httpx
import websockets
from starlette.applications import Starlette
from starlette.responses import HTMLResponse, JSONResponse, Response
from starlette.middleware import Middleware
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.routing import Route

SYMBOLS = [s.strip().upper() for s in os.getenv("SYMBOLS", "BTCUSDT,ETHUSDT,SOLUSDT,XRPUSDT").split(",")]
MIN_CONFIDENCE = float(os.getenv("MIN_CONFIDENCE", "0.78"))
WINDOW_SECONDS = 300
DASHBOARD_PASSWORD = os.getenv("DASHBOARD_PASSWORD", "").strip()
CONFIRM_AT = int(os.getenv("CONFIRM_AT", "125"))          # regular signal only after ~2 min
# Early signals (before CONFIRM_AT): only when the move is abnormally large for this coin's recent volatility.
# BOTH independent checks must agree: (1) counted reversals in the last hour, (2) random-walk model.
EARLY_ON = os.getenv("EARLY_SIGNALS", "true").strip().lower() == "true"
EARLY_FROM = int(os.getenv("EARLY_FROM", "40"))                       # seconds into the window
EARLY_MIN_LEAD_BPS = float(os.getenv("EARLY_MIN_LEAD_BPS", "5"))
EARLY_MAX_REVERSAL = float(os.getenv("EARLY_MAX_REVERSAL", "0.02"))   # max share of past intervals that reversed
EARLY_MIN_MODEL_P = float(os.getenv("EARLY_MIN_MODEL_P", "0.95"))
EARLY_MIN_SAMPLES = int(os.getenv("EARLY_MIN_SAMPLES", "300"))
EARLY_MIN_SPAN_MIN = int(os.getenv("EARLY_MIN_SPAN_MIN", "20"))       # minutes of recorded ticks required
PRICE_HISTORY_LEN = 60
# ---- 15-minute forecasts: the same analysis as for 5m, scaled to a 3x longer window ----
ENABLE_15M = os.getenv("ENABLE_15M", "true").strip().lower() == "true"
CONFIRM_AT_15 = int(os.getenv("CONFIRM_AT_15", str(CONFIRM_AT * 3)))             # 125 s -> 375 s
EARLY_FROM_15 = int(os.getenv("EARLY_FROM_15", str(EARLY_FROM * 3)))             # 40 s -> 120 s
EARLY_MIN_SPAN_MIN_15 = int(os.getenv("EARLY_MIN_SPAN_MIN_15", "40"))            # minutes of recorded ticks needed
HISTORY_KEEP = int(os.getenv("HISTORY_KEEP", "100"))                             # signals kept / shown in the history
CALIB_CPS = (30, 60, 90, 120, 150, 180, 240)                                     # calibration checkpoints (5m window)
CALIB_FILE = os.getenv("CALIB_FILE", "calib.json")
CALIB_FILE_15 = os.getenv("CALIB_FILE_15", "calib15.json")
MIN_LEAD_BPS = float(os.getenv("MIN_LEAD_BPS", "10.0"))        # lead filter (was 8 in older versions)
MIN_MOM_SHORT = float(os.getenv("MIN_MOM_SHORT", "4.0"))        # short momentum confirmation
MIN_MOM_MED = float(os.getenv("MIN_MOM_MED", "2.5"))          # medium momentum confirmation

# Chainlink symbol map for RTDS
CHAINLINK_SYM = {
    "BTCUSDT": "btc/usd",
    "ETHUSDT": "eth/usd",
    "SOLUSDT": "sol/usd",
    "XRPUSDT": "xrp/usd",
}
SYM_FROM_CL = {v: k for k, v in CHAINLINK_SYM.items()}

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
logger = logging.getLogger(__name__)


class WindowState:
    def __init__(self, symbol: str, series_len: int = 400):
        self.symbol = symbol
        self.price_to_beat: Optional[float] = None
        self.window_start: Optional[datetime] = None
        self.prices: deque = deque(maxlen=PRICE_HISTORY_LEN)
        self.last_price: Optional[float] = None
        self.signal_sent: bool = False
        self.last_signal: Optional[dict] = None
        self.last_update: Optional[datetime] = None
        self.last_error: Optional[str] = None
        self.source: str = ""
        self.open_confirmed: bool = False  # True when open taken from Polymarket
        self.series: deque = deque(maxlen=series_len)  # (seconds_in_window, price) for chart
        self.early: Optional[dict] = None       # early (low-confidence) forecast made right at window start
        self.prev_tail: list = []                # last prices of the previous window (trend before the start)
        self.calib_done: set = set()             # calibration checkpoints already handled in this window
        self.calib_pending: list = []            # calibration samples waiting for the window result

    def reset(self, price: float, start: datetime, source: str = ""):
        self.price_to_beat = price
        self.window_start = start
        self.prev_tail = list(self.prices)[-25:]
        self.early = None
        self.prices.clear()
        self.prices.append(price)
        self.series.clear()
        self.series.append((0.0, price))
        self.last_price = price
        self.signal_sent = False
        self.last_signal = None
        self.last_update = datetime.now(timezone.utc)
        self.last_error = None
        self.source = source
        self.open_confirmed = False
        self.calib_done = set()
        self.calib_pending = []


class TF:
    """Parameters + state of one market timeframe (5m / 15m).
    The 5m profile reproduces the original behaviour exactly (lead_scale = 1, time scale = 1).
    Longer windows scale the lead thresholds with sqrt(time) and the timings linearly."""

    def __init__(self, key: str, seconds: int, variant: str, confirm_at: int, early_from: int,
                 early_min_span: int, calib_file: str):
        self.key = key
        self.seconds = seconds
        self.variant = variant                 # `variant` parameter of polymarket.com/api/crypto/crypto-price
        self.confirm_at = confirm_at
        self.early_from = early_from
        self.early_min_span = early_min_span
        k = seconds / 300.0
        self.time_scale = k
        self.lead_scale = math.sqrt(k)
        self.cps = tuple(int(round(c * k)) for c in CALIB_CPS)
        self.state: Dict[str, WindowState] = {s: WindowState(s, int(400 * k)) for s in SYMBOLS}
        self.signal_history: List[dict] = []
        self.early_history: List[dict] = []    # results of early forecasts (tracked separately from real signals)
        self.error: Optional[str] = None
        self.calib: deque = deque(maxlen=30000)   # [coin, cp, lead_bps, up(1/0), win(1/0), ask|None, mom_bps, unix_ts]
        self.calib_file = calib_file
        self.calib_saved_at = 0.0


TF5 = TF("5m", 300, "fiveminute", CONFIRM_AT, EARLY_FROM, EARLY_MIN_SPAN_MIN, CALIB_FILE)
TF15 = TF("15m", 900, os.getenv("PM_VARIANT_15", "fifteen"), CONFIRM_AT_15, EARLY_FROM_15, EARLY_MIN_SPAN_MIN_15, CALIB_FILE_15)
TFS: Dict[str, TF] = {"5m": TF5, "15m": TF15}

# the original (5m) names keep working
state = TF5.state
signal_history = TF5.signal_history
early_history = TF5.early_history


def _tf_from(request) -> TF:
    """?tf=15m selects the 15-minute profile; anything else = 5m."""
    return TFS.get((request.query_params.get("tf") or "5m").lower(), TF5)
live_chainlink: Dict[str, float] = {}  # symbol -> last chainlink price


def momentum_bps(prices: deque, lookback: int = 12) -> float:
    if len(prices) < lookback + 1:
        return 0.0
    return (prices[-1] - prices[-lookback]) / prices[-lookback] * 10000


def generate_signal(price_to_beat: float, current_price: float, seconds_passed: int, prices: deque, tf: Optional["TF"] = None) -> dict:
    """
    Multi-factor signal inspired by jury-style bots:
    - Judge 1: Lead vs priceToBeat (Chainlink open)
    - Judge 2: Short momentum (last ~12 ticks)
    - Judge 3: Medium momentum (last ~25 ticks)
    Only fire when majority agree + strong enough edge.
    """
    tf = tf or TF5
    if seconds_passed < tf.confirm_at:
        return {"side": None, "confidence": 0.0, "reason": "too_early", "score": 0}

    lead_bps = ((current_price - price_to_beat) / price_to_beat) * 10000
    time_left = tf.seconds - seconds_passed
    abs_lead = abs(lead_bps)
    ls, k = tf.lead_scale, tf.time_scale          # both 1.0 for 5m
    min_lead = MIN_LEAD_BPS * ls

    if abs_lead < min_lead:
        return {"side": None, "confidence": 0.0, "reason": "too_small_lead", "score": 0, "lead_bps": round(lead_bps, 2)}

    mom_short = momentum_bps(prices, lookback=12)
    mom_med = momentum_bps(prices, lookback=25)

    side = "UP" if lead_bps > 0 else "DOWN"

    # Jury votes
    votes = 0
    # Judge 1: lead
    if abs_lead >= min_lead:
        votes += 1
    # Judge 2: short momentum same direction
    if (side == "UP" and mom_short >= MIN_MOM_SHORT) or (side == "DOWN" and mom_short <= -MIN_MOM_SHORT):
        votes += 1
    # Judge 3: medium momentum same direction
    if (side == "UP" and mom_med >= MIN_MOM_MED) or (side == "DOWN" and mom_med <= -MIN_MOM_MED):
        votes += 1

    if votes < 2:
        return {
            "side": None,
            "confidence": 0.0,
            "reason": f"jury_{votes}/3",
            "score": votes,
            "lead_bps": round(lead_bps, 2),
            "mom_short": round(mom_short, 2),
            "mom_med": round(mom_med, 2),
        }

    # Confidence curve: later + stronger lead = higher conf
    base = 0.72 + (votes - 2) * 0.06          # 2 votes → 0.72, 3 votes → 0.78
    lead_boost = min((abs_lead / ls) * 0.011, 0.14)
    time_boost = 0.0
    if time_left <= 45 * k:
        time_boost = 0.08
    elif time_left <= 70 * k:
        time_boost = 0.04

    confidence = min(base + lead_boost + time_boost, 0.96)

    return {
        "side": side,
        "confidence": round(confidence, 3),
        "lead_bps": round(lead_bps, 2),
        "time_left": time_left,
        "score": votes,
        "mom_short": round(mom_short, 2),
        "mom_med": round(mom_med, 2),
        "reason": f"jury_{votes}/3",
    }


def realized_sigma(series, max_pts: int = 80) -> Optional[float]:
    """Realized volatility per sqrt(second) from recent ticks (relative, drift-free)."""
    pts = list(series)[-max_pts:]
    if len(pts) < 8:
        return None
    s2, total = 0.0, 0.0
    for (t0, p0), (t1, p1) in zip(pts, pts[1:]):
        dt = t1 - t0
        if dt <= 0 or p0 <= 0 or p1 <= 0:
            continue
        r = math.log(p1 / p0)
        s2 += r * r
        total += dt
    if total <= 0:
        return None
    return max(math.sqrt(s2 / total), 3e-5)


def model_prob_up(open_px: Optional[float], price: float, t_now: float, series, T: Optional[float] = None) -> Optional[float]:
    """P(final 60s TWAP >= open) for a driftless random walk (idea: Black-Scholes style HFT bot, TWAP variant)."""
    if not open_px or not price:
        return None
    sig = realized_sigma(series)
    if sig is None:
        return None
    W, T = 60.0, float(T or WINDOW_SECONDS)
    sigma = sig * price
    if t_now <= T - W:
        a = (T - W) - t_now
        mean = price
        var = sigma * sigma * (a + W / 3.0)
    else:
        f = min(1.0, (t_now - (T - W)) / W)
        obs = [p for t, p in series if t >= T - W]
        m_obs = sum(obs) / len(obs) if obs else price
        r = max(T - t_now, 0.0)
        mean = f * m_obs + (1 - f) * price
        var = ((1 - f) ** 2) * sigma * sigma * (r / 3.0)
    var = max(var, (sigma * sigma) * 0.5)      # never claim certainty
    z = (mean - open_px) / math.sqrt(var)
    return 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))


def fee_per_share(p: float) -> float:
    return PAPER_FEE_RATE * (p * (1 - p)) ** 2


def is_strong_signal(signal: dict) -> bool:
    if signal.get("side") is None:
        return False
    return signal.get("confidence", 0) >= MIN_CONFIDENCE and signal.get("score", 0) >= 2


def get_window_start_unix(tf: Optional[TF] = None) -> int:
    secs = tf.seconds if tf else WINDOW_SECONDS
    now = int(datetime.now(timezone.utc).timestamp())
    return now - (now % secs)


def get_current_window_start(tf: Optional[TF] = None) -> datetime:
    return datetime.fromtimestamp(get_window_start_unix(tf), tz=timezone.utc)


def twap_last_seconds(series, seconds: float = 60.0) -> Optional[float]:
    """Average of the ticks in the last `seconds` of the series (Polymarket settles on a 60s Chainlink TWAP)."""
    if not series:
        return None
    t_end = series[-1][0]
    pts = [p for t, p in series if t >= t_end - seconds]
    return sum(pts) / len(pts) if pts else None


def twap_final_minute(series, secs: int = WINDOW_SECONDS) -> Optional[float]:
    """Average of the ticks in the final minute of the window (t in [secs-60, secs])."""
    pts = [p for t, p in series if t >= secs - 60]
    return sum(pts) / len(pts) if len(pts) >= 5 else None


async def fetch_polymarket_open(client: httpx.AsyncClient, symbol: str, start_unix: int, tf: Optional[TF] = None) -> Optional[float]:
    """Price to Beat straight from Polymarket (same endpoint the website uses)."""
    secs, variant = (tf.seconds, tf.variant) if tf else (WINDOW_SECONDS, "fiveminute")
    base = symbol.replace("USDT", "")
    start_iso = datetime.fromtimestamp(start_unix, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    end_iso = datetime.fromtimestamp(start_unix + secs, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    try:
        r = await client.get(
            "https://polymarket.com/api/crypto/crypto-price",
            params={
                "symbol": base,
                "eventStartTime": start_iso,
                "variant": variant,
                "endDate": end_iso,
            },
            timeout=3.0,
        )
        if r.status_code == 200:
            val = r.json().get("openPrice")
            if val is not None:
                return float(val)
    except Exception as e:
        logger.debug(f"polymarket open fetch {symbol}: {e}")
    return None


async def fetch_polymarket_close(client: httpx.AsyncClient, symbol: str, start_unix: int, tf: Optional[TF] = None) -> Optional[float]:
    """Final price of a finished window straight from Polymarket."""
    secs, variant = (tf.seconds, tf.variant) if tf else (WINDOW_SECONDS, "fiveminute")
    base = symbol.replace("USDT", "")
    start_iso = datetime.fromtimestamp(start_unix, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    end_iso = datetime.fromtimestamp(start_unix + secs, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    try:
        r = await client.get(
            "https://polymarket.com/api/crypto/crypto-price",
            params={"symbol": base, "eventStartTime": start_iso, "variant": variant, "endDate": end_iso},
            timeout=3.0,
        )
        if r.status_code == 200:
            val = r.json().get("closePrice")
            if val is not None:
                return float(val)
    except Exception as e:
        logger.debug(f"polymarket close fetch {symbol}: {e}")
    return None


# ====================== Virtual (paper) trading: 3 independent wallets ======================
PAPER_FILE = os.getenv("PAPER_FILE", "paper_state.json")
PAPER_FEE_RATE = 0.25      # approx. Polymarket crypto taker fee: fee = shares * 0.25 * (p*(1-p))**2
PAPER_COINS = ["BTC", "ETH", "SOL", "XRP"]
PAPER_MODEL_HAIRCUT = 0.02   # safety haircut on the model probability
PAPER_KELLY_CAP = 0.10       # never stake more than 10% of balance
PAPER_N = 3                  # number of virtual wallets (each has its own settings, balance and history)


def _paper_default(name: str = "") -> dict:
    return {
        "name": name,
        "enabled": False,
        "deposit": 1000.0,
        "balance": 1000.0,
        "stake_mode": "pct",      # "pct" = % of balance, "usd" = fixed $, "kelly" = fractional Kelly (% of full Kelly)
        "stake_value": 5.0,
        "min_edge": 0.0,          # % ; 0 = filter off
        "min_price": 0,           # cents ; crowd-confirmation filter (0 = off)
        "max_price": 99,          # cents ; do not buy above this
        "coins": {c: True for c in PAPER_COINS},
        "trades": [],
        "next_id": 1,
    }


wallets: List[dict] = [_paper_default(f"Гаманець {i + 1}") for i in range(PAPER_N)]
# Wallet 1 keeps the old name `paper`: real-money (live) trading mirrors ONLY this wallet.
paper: dict = wallets[0]


def paper_save():
    try:
        tmp = PAPER_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump({"version": 2, "wallets": wallets}, f)
        os.replace(tmp, PAPER_FILE)
    except Exception as e:
        logger.warning(f"paper save failed: {e}")


def _paper_apply(w: dict, data: dict, idx: int):
    base = _paper_default(f"Гаманець {idx + 1}")
    base.update({k: v for k, v in data.items() if k in base})
    base["coins"] = {c: bool((data.get("coins") or {}).get(c, True)) for c in PAPER_COINS}
    nm = str(base.get("name") or "").strip()[:24]
    base["name"] = nm or f"Гаманець {idx + 1}"
    w.clear()
    w.update(base)


def paper_load():
    try:
        with open(PAPER_FILE) as f:
            data = json.load(f)
        if isinstance(data, dict) and isinstance(data.get("wallets"), list):
            items = data["wallets"]
        else:
            items = [data]          # old single-wallet file -> becomes wallet 1, nothing is lost
        for i, w in enumerate(wallets):
            if i < len(items) and isinstance(items[i], dict):
                _paper_apply(w, items[i], i)
        logger.info("paper state loaded: " + ", ".join(
            f"{w['name']}: balance={w['balance']:.2f}, trades={len(w['trades'])}" for w in wallets))
    except FileNotFoundError:
        pass
    except Exception as e:
        logger.warning(f"paper load failed: {e}")


def _json_list(v):
    if isinstance(v, str):
        try:
            v = json.loads(v)
        except Exception:
            return []
    return v if isinstance(v, list) else []


async def paper_market_meta(client: httpx.AsyncClient, slug: str):
    """(conditionId, {token_id: 'Up'/'Down'}) for a 5m / 15m market."""
    meta = _cid_cache.get(slug)
    if meta:
        return meta
    r = await client.get("https://gamma-api.polymarket.com/events", params={"slug": slug}, timeout=5.0)
    data = r.json()
    ev = data[0] if isinstance(data, list) and data else None
    mk = (ev or {}).get("markets") or []
    if not mk:
        return None
    m0 = mk[0]
    tokens = _json_list(m0.get("clobTokenIds"))
    outs = _json_list(m0.get("outcomes"))
    meta = (m0.get("conditionId"), {str(t): str(o) for t, o in zip(tokens, outs)})
    if meta[0]:
        _cid_cache[slug] = meta
    return meta


_bg_tasks: set = set()


def spawn(coro):
    """create_task that keeps a reference (otherwise the task can be garbage-collected mid-flight)."""
    t = asyncio.create_task(coro)
    _bg_tasks.add(t)
    t.add_done_callback(_bg_tasks.discard)
    return t


def paper_skip(w: dict, coin: str, side: str, start_unix: int, reason: str):
    """Record why a signal was not traded (shown in the UI, not counted in stats)."""
    logger.info(f"paper[{w['name']}]: skipped {coin} {side}: {reason}")
    w["trades"].insert(0, {
        "id": w["next_id"], "ts": int(datetime.now(timezone.utc).timestamp()),
        "symbol": coin, "side": side, "window_start": start_unix,
        "entry": 0.0, "shares": 0.0, "cost": 0.0, "fee": 0.0,
        "status": "skip", "reason": reason, "pnl": 0.0, "settled_at": None, "balance_after": None,
    })
    w["next_id"] += 1
    paper_save()


async def _paper_get_asks(client: httpx.AsyncClient, coin: str, side: str, start_unix: int, tf: Optional[TF] = None):
    """Order-book asks for the side we want. Retries a few times. Returns (asks, reason)."""
    slug = f"{coin.lower()}-updown-{tf.key if tf else '5m'}-{start_unix}"
    reason = "невідома помилка"
    for attempt in range(3):
        try:
            meta = await paper_market_meta(client, slug)
            if not meta or not meta[0]:
                reason = "ринок не знайдено на Polymarket"
            else:
                want = "up" if side == "UP" else "down"
                token = next((tok for tok, o in meta[1].items() if o.lower() == want), None)
                if not token:
                    reason = "не знайдено токен ринку"
                else:
                    r = await client.get("https://clob.polymarket.com/book", params={"token_id": token}, timeout=5.0)
                    book = r.json()
                    asks = []
                    for x in (book.get("asks") or []):
                        try:
                            p, sz = float(x["price"]), float(x["size"])
                        except Exception:
                            continue
                        if 0 < p <= 0.99 and sz > 0:
                            asks.append((p, sz))
                    asks.sort()
                    if asks:
                        return asks, None
                    reason = "немає пропозицій дешевше 99¢"
        except Exception as e:
            reason = "помилка мережі Polymarket"
            logger.warning(f"paper book attempt {attempt + 1} for {coin}: {e}")
        await asyncio.sleep(0.7)
    return None, reason


def _paper_open_w(w: dict, client: httpx.AsyncClient, coin: str, side: str, start_unix: int,
                  p_model: Optional[float], mode: str, asks, reason):
    """Open a virtual position for ONE wallet at the real order book (walks the asks). No awaits: atomic."""
    try:
        # state may have changed while we were waiting for the network
        if not w["enabled"] or not w["coins"].get(coin):
            return
        if any(t["status"] == "open" and t["symbol"] == coin and t["window_start"] == start_unix
               for t in w["trades"]):
            return
        if not asks:
            paper_skip(w, coin, side, start_unix, reason or "немає даних")
            return
        bal = w["balance"]
        best = asks[0][0]
        if best * 100 < w.get("min_price", 0):
            paper_skip(w, coin, side, start_unix, f"ціна сторони {best*100:.0f}¢ нижча за мін. {w['min_price']}¢")
            return
        if best * 100 > w.get("max_price", 99):
            paper_skip(w, coin, side, start_unix, f"ціна {best*100:.0f}¢ вища за макс. {w['max_price']}¢")
            return
        p_eff = (p_model - PAPER_MODEL_HAIRCUT) if p_model is not None else None
        c_best = best + fee_per_share(best)
        edge_best = (p_eff - c_best) if p_eff is not None else None
        if w.get("min_edge", 0) > 0:
            if edge_best is None:
                paper_skip(w, coin, side, start_unix, "немає моделі для перевірки edge")
                return
            if edge_best * 100 < w["min_edge"]:
                paper_skip(w, coin, side, start_unix, f"edge {edge_best*100:.1f}% < мін. {w['min_edge']:.1f}%")
                return
        if w["stake_mode"] == "kelly":
            if edge_best is None or edge_best <= 0:
                paper_skip(w, coin, side, start_unix, "Kelly: edge ≤ 0 або немає моделі")
                return
            f_full = (p_eff - c_best) / (1.0 - c_best)
            stake = bal * min(f_full * w["stake_value"] / 100.0, PAPER_KELLY_CAP)
        elif w["stake_mode"] == "pct":
            stake = bal * w["stake_value"] / 100.0
        else:
            stake = w["stake_value"]
        stake = min(stake, bal)
        if stake < 1:
            paper_skip(w, coin, side, start_unix, "ставка менша за $1 (баланс або Kelly замалі)")
            return

        remaining, shares, cost = stake, 0.0, 0.0
        for p, sz in asks:
            take = min(sz, remaining / p)
            shares += take
            cost += take * p
            remaining -= take * p
            if remaining < 0.01:
                break
        if shares <= 0 or cost < 1:
            paper_skip(w, coin, side, start_unix, "замало ліквідності")
            return
        avg = cost / shares
        fee = shares * PAPER_FEE_RATE * (avg * (1 - avg)) ** 2
        total = cost + fee
        if total > w["balance"]:
            k = w["balance"] / total
            shares, cost, fee, total = shares * k, cost * k, fee * k, total * k
        w["balance"] -= total
        trade = {
            "id": w["next_id"],
            "ts": int(datetime.now(timezone.utc).timestamp()),
            "symbol": coin,
            "side": side,
            "window_start": start_unix,
            "entry": round(avg, 4),
            "shares": round(shares, 4),
            "cost": round(cost, 2),
            "fee": round(fee, 4),
            "model_p": (round(p_model, 3) if p_model is not None else None),
            "edge": (round((p_eff - (avg + fee_per_share(avg))) * 100, 1) if p_eff is not None else None),
            "status": "open",
            "pnl": 0.0,
            "settled_at": None,
            "balance_after": None,
        }
        w["next_id"] += 1
        w["trades"].insert(0, trade)
        if len(w["trades"]) > 400:
            keep_open = [t for t in w["trades"] if t["status"] == "open"]
            closed = [t for t in w["trades"] if t["status"] != "open"][:300]
            w["trades"] = sorted(keep_open + closed, key=lambda t: t["id"], reverse=True)
        paper_save()
        logger.info(f"PAPER[{w['name']}] BUY {coin} {side} {shares:.2f} sh @ {avg:.3f} cost ${cost:.2f} fee ${fee:.3f}")
        # real money mirrors wallet 1 only (its filters decide whether a live order is even attempted)
        if w is wallets[0] and live_rt["armed"] and (mode != "early" or LIVE_ALLOW_EARLY):
            spawn(live_buy(client, coin, side, start_unix, trade))
    except Exception as e:
        logger.warning(f"paper_open error [{w.get('name')}]: {e}")
        try:
            paper_skip(w, coin, side, start_unix, "внутрішня помилка")
        except Exception:
            pass


async def paper_open(client: httpx.AsyncClient, symbol: str, side: str, start_unix: int, p_model: Optional[float] = None,
                     mode: str = "confirm"):
    """A 5m signal fired: every enabled wallet decides on its own (own filters / stake). The order book is fetched once."""
    coin = symbol.replace("USDT", "")
    try:
        def wants(w):
            return bool(w["enabled"] and w["coins"].get(coin)) and not any(
                t["status"] == "open" and t["symbol"] == coin and t["window_start"] == start_unix for t in w["trades"])
        if not any(wants(w) for w in wallets):
            return
        asks, reason = await _paper_get_asks(client, coin, side, start_unix)
        for w in wallets:
            _paper_open_w(w, client, coin, side, start_unix, p_model, mode, asks, reason)
    except Exception as e:
        logger.warning(f"paper_open dispatcher error: {e}")


def paper_settle(coin: str, start_unix: int, actual: str) -> bool:
    live_settle(coin, start_unix, actual)
    done = False
    for w in wallets:
        for t in w["trades"]:
            if t["status"] == "open" and t["symbol"] == coin and t["window_start"] == start_unix:
                won = t["side"] == actual
                if won:
                    w["balance"] += t["shares"]
                    t["pnl"] = round(t["shares"] - t["cost"] - t["fee"], 2)
                    t["status"] = "win"
                else:
                    t["pnl"] = round(-(t["cost"] + t["fee"]), 2)
                    t["status"] = "loss"
                t["settled_at"] = int(datetime.now(timezone.utc).timestamp())
                t["balance_after"] = round(w["balance"], 2)
                paper_save()
                logger.info(f"PAPER[{w['name']}] {t['status'].upper()} {coin} {t['side']} pnl ${t['pnl']:.2f}")
                done = True
                break
    return done


def paper_void(w: dict, t: dict):
    w["balance"] += t["cost"] + t["fee"]
    t["status"] = "void"
    t["pnl"] = 0.0
    t["settled_at"] = int(datetime.now(timezone.utc).timestamp())
    t["balance_after"] = round(w["balance"], 2)
    paper_save()


async def paper_settle_orphans(client: httpx.AsyncClient, symbol: str, start_unix: int):
    """Settle positions whose window ended but the normal close step missed them (e.g. after a restart)."""
    coin = symbol.replace("USDT", "")
    starts = sorted({t["window_start"] for w in wallets for t in w["trades"]
                     if t["status"] == "open" and t["symbol"] == coin and t["window_start"] < start_unix})
    for ws_start in starts:
        o = await fetch_polymarket_open(client, symbol, ws_start)
        c = await fetch_polymarket_close(client, symbol, ws_start)
        if o is not None and c is not None:
            paper_settle(coin, ws_start, "UP" if c >= o else "DOWN")
        elif ws_start < start_unix - 1200:
            for w in wallets:
                for t in list(w["trades"]):
                    if t["status"] == "open" and t["symbol"] == coin and t["window_start"] == ws_start:
                        paper_void(w, t)
    for t in list(live["trades"]):
        if t["status"] != "open" or t["symbol"] != coin or t["window_start"] >= start_unix:
            continue
        o = await fetch_polymarket_open(client, symbol, t["window_start"])
        c = await fetch_polymarket_close(client, symbol, t["window_start"])
        if o is not None and c is not None:
            live_settle(coin, t["window_start"], "UP" if c >= o else "DOWN")
        elif t["window_start"] < start_unix - 1200:
            t["status"] = "unresolved"
            live_save()


paper_load()

# ====================== LIVE trading (REAL MONEY) ======================
# Mirrors the virtual trades (same filters: edge / price band / coins) with a FIXED small stake.
# Safety: off by default, needs LIVE_TRADING=true in the server env AND a manual switch in the UI after every restart,
# one attempt per coin per window (never retried), daily loss limit, max open positions, circuit breaker.
# Uses Polymarket's official unified Python SDK (pip: polymarket-client). CLOB V1 / py-clob-client no longer work.
LIVE_ENV = os.getenv("LIVE_TRADING", "false").strip().lower() == "true"
LIVE_PRIVATE_KEY = os.getenv("POLYMARKET_PRIVATE_KEY", "").strip()
LIVE_WALLET = os.getenv("POLYMARKET_WALLET_ADDRESS", "").strip()


def _env_float(name: str, default: float, lo: float, hi: float) -> float:
    try:
        v = float(os.getenv(name, str(default)))
    except ValueError:
        v = default
    return max(lo, min(hi, v))


LIVE_MAX_STAKE_USD = _env_float("LIVE_MAX_STAKE_USD", 5.0, 1.0, 100.0)          # hard cap per trade
LIVE_STAKE = min(_env_float("LIVE_STAKE_USD", 1.0, 1.0, 100.0), LIVE_MAX_STAKE_USD)
LIVE_DAILY_LOSS = _env_float("LIVE_DAILY_LOSS_USD", 5.0, 1.0, 10000.0)           # stop for the day at this loss
LIVE_MAX_OPEN = int(_env_float("LIVE_MAX_OPEN", 2, 1, 4))                        # coins are correlated: limit exposure
LIVE_MAX_SLIPPAGE = _env_float("LIVE_MAX_SLIPPAGE", 0.03, 0.0, 0.2)              # max avg price above the paper entry
LIVE_FILE = os.getenv("LIVE_FILE", "live_state.json")
LIVE_ALLOW_EARLY = os.getenv("LIVE_ALLOW_EARLY", "false").strip().lower() == "true"   # real money on EARLY signals: opt-in

live: dict = {"trades": [], "next_id": 1, "day": "", "day_pnl": 0.0}
live_rt: dict = {"armed": False, "disarm_reason": "", "consec_fail": 0, "last_error": None}   # never persisted
_live_attempted: dict = {}          # (coin, window_start) -> True ; at most ONE order attempt per coin/window
_live_client = None
_live_client_lock: Optional[asyncio.Lock] = None


def _mask(x) -> str:
    s = str(x)
    return s.replace(LIVE_PRIVATE_KEY, "***") if LIVE_PRIVATE_KEY else s


def live_save():
    try:
        tmp = LIVE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(live, f)
        os.replace(tmp, LIVE_FILE)
    except Exception as e:
        logger.warning(f"live save failed: {e}")


def live_load():
    try:
        with open(LIVE_FILE) as f:
            data = json.load(f)
        for k in ("trades", "next_id", "day", "day_pnl"):
            if k in data:
                live[k] = data[k]
        # anything still "open" after a restart will be settled by the orphan settler
    except FileNotFoundError:
        pass
    except Exception as e:
        logger.warning(f"live load failed: {e}")


live_load()


def _live_roll_day():
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    if live.get("day") != today:
        live["day"] = today
        live["day_pnl"] = 0.0


def live_disarm(reason: str):
    if live_rt["armed"]:
        logger.warning(f"LIVE DISARMED: {reason}")
    live_rt["armed"] = False
    live_rt["disarm_reason"] = reason


def live_missing() -> list:
    import importlib.util
    m = []
    if not LIVE_ENV:
        m.append("LIVE_TRADING=true")
    if not LIVE_PRIVATE_KEY:
        m.append("POLYMARKET_PRIVATE_KEY")
    if not (LIVE_WALLET.startswith("0x") and len(LIVE_WALLET) == 42):
        m.append("POLYMARKET_WALLET_ADDRESS")
    if not DASHBOARD_PASSWORD:
        m.append("DASHBOARD_PASSWORD")
    if importlib.util.find_spec("polymarket") is None:
        m.append("SDK polymarket-client (не встановлено)")
    return m


async def live_client():
    """Authenticated SDK client (created once). Raises if the key / wallet / SDK are not usable."""
    global _live_client, _live_client_lock
    if _live_client is not None:
        return _live_client
    if _live_client_lock is None:
        _live_client_lock = asyncio.Lock()
    async with _live_client_lock:
        if _live_client is None:
            from polymarket import AsyncSecureClient
            _live_client = await asyncio.wait_for(
                AsyncSecureClient.create(private_key=LIVE_PRIVATE_KEY, wallet=LIVE_WALLET), timeout=30)
    return _live_client


def _live_open_count() -> int:
    return sum(1 for t in live["trades"] if t["status"] == "open")


def _live_record(coin: str, side: str, start_unix: int, status: str, stake: float = 0.0, **extra) -> dict:
    t = {
        "id": live["next_id"], "ts": int(time.time()), "symbol": coin, "side": side, "window_start": start_unix,
        "status": status, "stake": round(stake, 2), "pnl": 0.0, "settled_at": None,
    }
    t.update(extra)
    live["next_id"] += 1
    live["trades"].insert(0, t)
    del live["trades"][300:]
    live_save()
    return t


def _live_skip(coin: str, side: str, start_unix: int, reason: str):
    logger.info(f"live: skipped {coin} {side}: {reason}")
    _live_record(coin, side, start_unix, "skip", reason=reason)


def _pick_outcome(market, side: str):
    outs = getattr(market, "outcomes", None)
    names = ("up", "yes") if side == "UP" else ("down", "no")
    for n in names:
        o = getattr(outs, n, None)
        if o is not None:
            return o
    try:
        for o in outs:
            lab = str(getattr(o, "label", getattr(o, "name", ""))).lower()
            if lab in names:
                return o
    except TypeError:
        pass
    return None


async def _live_token(client: httpx.AsyncClient, sdk, coin: str, side: str, start_unix: int):
    """Trading token for the side. Gamma gives the Up/Down -> token mapping (same as virtual trading);
    the SDK is used as a cross-check. Returns (token, reason_if_refused)."""
    slug = f"{coin.lower()}-updown-5m-{start_unix}"
    meta = await paper_market_meta(client, slug)
    if not meta or not meta[0]:
        return None, "ринок не знайдено"
    want = "up" if side == "UP" else "down"
    token = next((tok for tok, o in meta[1].items() if o.lower() == want), None)
    if not token:
        return None, "не знайдено токен ринку"
    try:
        market = await asyncio.wait_for(sdk.get_market(slug=slug), timeout=8)
        if str(getattr(market, "version", "")).lower() == "v2":
            return None, "ринок Polymarket Protocol V2: бот поки не вміє торгувати такі ринки"
        o = _pick_outcome(market, side)
        st = str(getattr(o, "token_id", "") or "") if o is not None else ""
        if st and st != str(token):
            return None, "токен ринку не збігається з SDK (захист від ставки не в той бік)"
    except Exception as e:
        logger.warning(f"live: SDK market cross-check unavailable for {slug}: {_mask(e)[:120]}")
    return str(token), None


async def live_buy(client: httpx.AsyncClient, coin: str, side: str, start_unix: int, ptrade: Optional[dict]):
    """Place ONE real market buy for the same side as the virtual trade. Never retried."""
    try:
        if not (LIVE_ENV and live_rt["armed"]):
            return
        key = (coin, start_unix)
        if key in _live_attempted:
            return
        _live_attempted[key] = True
        while len(_live_attempted) > 500:
            _live_attempted.pop(next(iter(_live_attempted)))

        _live_roll_day()
        if live["day_pnl"] <= -LIVE_DAILY_LOSS:
            live_disarm(f"денний ліміт збитку ${LIVE_DAILY_LOSS:g} досягнуто")
            return
        if _live_open_count() >= LIVE_MAX_OPEN:
            _live_skip(coin, side, start_unix, f"вже відкрито {LIVE_MAX_OPEN} реальних позицій (ліміт)")
            return
        if time.time() > start_unix + WINDOW_SECONDS - 10:
            _live_skip(coin, side, start_unix, "замало часу до кінця вікна")
            return

        asks, reason = await _paper_get_asks(client, coin, side, start_unix)
        if not asks:
            _live_skip(coin, side, start_unix, reason or "немає даних книги")
            return
        remaining, shares, cost = LIVE_STAKE, 0.0, 0.0
        for p, sz in asks:
            take = min(sz, remaining / p)
            shares += take
            cost += take * p
            remaining -= take * p
            if remaining < 0.01:
                break
        if shares <= 0 or cost < LIVE_STAKE * 0.98:
            _live_skip(coin, side, start_unix, "замало ліквідності на повну ставку")
            return
        avg = cost / shares
        limit = min(paper.get("max_price", 99) / 100.0, ((ptrade or {}).get("entry") or avg) + LIVE_MAX_SLIPPAGE, 0.97)
        if avg > limit + 1e-9:
            _live_skip(coin, side, start_unix, f"ціна {avg*100:.0f}¢ вища за ліміт {limit*100:.0f}¢")
            return

        sdk = await live_client()
        token, why = await _live_token(client, sdk, coin, side, start_unix)
        if not token:
            _live_skip(coin, side, start_unix, why or "токен недоступний")
            return
        if not live_rt["armed"]:
            return          # switched off while we were checking

        est_fee = shares * PAPER_FEE_RATE * (avg * (1 - avg)) ** 2
        try:
            resp = await asyncio.wait_for(
                sdk.place_market_order(asset_id=token, side="BUY", amount=f"{LIVE_STAKE:.2f}"), timeout=20)
        except asyncio.TimeoutError:
            _live_record(coin, side, start_unix, "unknown", LIVE_STAKE, est_entry=round(avg, 4),
                         msg="таймаут: невідомо, чи виконано. Перевір акаунт Polymarket")
            live_disarm("таймаут ордера: стан невідомий, перевір акаунт Polymarket")
            return
        except Exception as e:
            live_rt["consec_fail"] += 1
            msg = _mask(e)[:200]
            live_rt["last_error"] = msg
            _live_record(coin, side, start_unix, "failed", LIVE_STAKE, msg=msg)
            logger.warning(f"live order error {coin} {side}: {msg}")
            if live_rt["consec_fail"] >= 3:
                live_disarm("3 помилки ордерів поспіль")
            return

        if not bool(getattr(resp, "ok", False)):
            live_rt["consec_fail"] += 1
            msg = _mask(getattr(resp, "message", "") or "ордер відхилено")[:200]
            live_rt["last_error"] = msg
            _live_record(coin, side, start_unix, "failed", LIVE_STAKE, msg=msg)
            logger.warning(f"live order rejected {coin} {side}: {msg}")
            if live_rt["consec_fail"] >= 3:
                live_disarm("3 відхилені ордери поспіль")
            return

        live_rt["consec_fail"] = 0
        live_rt["last_error"] = None
        _live_record(coin, side, start_unix, "open", LIVE_STAKE, est_entry=round(avg, 4),
                     est_shares=round(shares, 4), est_fee=round(est_fee, 4),
                     order_id=str(getattr(resp, "order_id", "") or ""))
        logger.info(f"LIVE BUY {coin} {side} ${LIVE_STAKE:.2f} @~{avg:.3f} order={getattr(resp, 'order_id', '')}")
    except asyncio.CancelledError:
        raise
    except Exception as e:
        logger.error(f"live_buy crashed: {_mask(e)[:200]}")
        live_rt["last_error"] = _mask(e)[:200]


def live_settle(coin: str, start_unix: int, actual: str) -> bool:
    """Book the result of a real position (ESTIMATE from the book price; the exact numbers are in your Polymarket account)."""
    for t in live["trades"]:
        if t["status"] == "open" and t["symbol"] == coin and t["window_start"] == start_unix:
            fee = t.get("est_fee", 0.0)
            if t["side"] == actual:
                t["pnl"] = round(t["est_shares"] - t["stake"] - fee, 2)
                t["status"] = "win"
            else:
                t["pnl"] = round(-(t["stake"] + fee), 2)
                t["status"] = "loss"
            t["settled_at"] = int(time.time())
            _live_roll_day()
            live["day_pnl"] = round(live["day_pnl"] + t["pnl"], 2)
            if live_rt["armed"] and live["day_pnl"] <= -LIVE_DAILY_LOSS:
                live_disarm(f"денний ліміт збитку ${LIVE_DAILY_LOSS:g} досягнуто")
            live_save()
            logger.info(f"LIVE {t['status'].upper()} {coin} {t['side']} est.pnl ${t['pnl']:.2f}")
            return True
    return False


def _live_payload() -> dict:
    _live_roll_day()
    w = LIVE_WALLET
    return {
        "missing": live_missing(),
        "armed": live_rt["armed"],
        "disarm_reason": live_rt["disarm_reason"],
        "last_error": live_rt["last_error"],
        "wallet_short": (w[:6] + "…" + w[-4:]) if len(w) > 12 else "",
        "stake": LIVE_STAKE,
        "daily_loss_limit": LIVE_DAILY_LOSS,
        "day_pnl": round(live["day_pnl"], 2),
        "open": _live_open_count(),
        "max_open": LIVE_MAX_OPEN,
        "paper_enabled": paper["enabled"],
        "allow_early": LIVE_ALLOW_EARLY,
        "trades": live["trades"][:30],
    }


async def api_live(request):
    return JSONResponse(_live_payload())


async def api_live_arm(request):
    # custom header: a foreign website cannot set it (CSRF protection for a real-money switch)
    if request.headers.get("x-requested-with") != "signals":
        return JSONResponse({"error": "forbidden"}, status_code=403)
    try:
        b = await request.json()
    except Exception:
        b = {}
    if not b.get("armed"):
        live_disarm("вимкнено вручну")
        return JSONResponse(_live_payload())
    miss = live_missing()
    if miss:
        live_rt["last_error"] = "Не готово: " + ", ".join(miss)
        return JSONResponse(_live_payload())
    if not paper["enabled"]:
        live_rt["last_error"] = "Спочатку увімкни «Торгувати віртуально» у Гаманці 1: live повторює його угоди та фільтри"
        return JSONResponse(_live_payload())
    try:
        await live_client()          # preflight: authenticates key + wallet, places NO order
    except Exception as e:
        live_rt["last_error"] = "Не вдалося підключитись: " + _mask(e)[:200]
        return JSONResponse(_live_payload())
    live_rt.update(armed=True, disarm_reason="", consec_fail=0, last_error=None)
    logger.warning("LIVE ARMED by user")
    return JSONResponse(_live_payload())



# ====================== Calibration: where is the REAL edge? (facts only) ======================
# At fixed seconds of every window the bot records: the current leader (side with price above/below open), the lead in bps,
# the real Polymarket best ask for that side, and later the real result. The table then shows, per moment in the window,
# how often the leader really won, what the market charged for it, and the average real result per share after fees.
CALIB_THRS = (0.0, 3.0, 6.0, 10.0)               # min |lead| in bps for the table filters


def calib_load(tf: TF):
    try:
        with open(tf.calib_file) as f:
            for row in json.load(f):
                if isinstance(row, list) and len(row) == 8:
                    tf.calib.append(row)
        logger.info(f"calibration {tf.key} loaded: {len(tf.calib)} samples")
    except FileNotFoundError:
        pass
    except Exception as e:
        logger.warning(f"calib load failed: {e}")


def calib_save(tf: TF, force: bool = False):
    if not force and time.time() - tf.calib_saved_at < 120:
        return
    tf.calib_saved_at = time.time()
    try:
        tmp = tf.calib_file + ".tmp"
        with open(tmp, "w") as f:
            json.dump(list(tf.calib), f, separators=(",", ":"))
        os.replace(tmp, tf.calib_file)
    except Exception as e:
        logger.warning(f"calib save failed: {e}")


calib_load(TF5)
calib_load(TF15)


async def calib_fill_ask(client: httpx.AsyncClient, symbol: str, start_unix: int, sample: dict, tf: Optional[TF] = None):
    """Best ask (what the market charges) for the leader side at the checkpoint. Best effort, single request."""
    tf = tf or TF5
    try:
        coin = symbol.replace("USDT", "")
        meta = await paper_market_meta(client, f"{coin.lower()}-updown-{tf.key}-{start_unix}")
        if not meta:
            return
        want = "up" if sample["side"] == "UP" else "down"
        token = next((tok for tok, o in meta[1].items() if o.lower() == want), None)
        if not token:
            return
        r = await client.get("https://clob.polymarket.com/book", params={"token_id": token}, timeout=4.0)
        prices = []
        for x in (r.json().get("asks") or []):
            try:
                p = float(x["price"])
            except Exception:
                continue
            if 0 < p < 1:
                prices.append(p)
        if prices:
            sample["ask"] = min(prices)
    except Exception as e:
        logger.debug(f"calib ask {symbol}: {e}")


def _own_final_price(symbol: str, start_unix: int, secs: int = WINDOW_SECONDS) -> Optional[float]:
    """Last recorded Chainlink tick at the end of the window (the same feed Polymarket settles on).
    Used only when Polymarket does not return the exact close price; None if our ticks do not reach the window end."""
    end = start_unix + secs
    for t, p in reversed(tick_hist.get(symbol, ())):
        if t <= end:
            return p if end - t <= 8 else None
    return None


async def calib_settle(client: httpx.AsyncClient, symbol: str, start_unix: int, pending: list, open_px: Optional[float],
                       tf: Optional[TF] = None):
    """Attach the real result to the samples of a finished window.
    1) the exact close price from Polymarket (it can appear a while after the window ends, so be patient: ~3 min);
    2) otherwise our own last Chainlink tick of the window; 3) otherwise the samples are dropped (and counted)."""
    tf = tf or TF5
    try:
        final, src_name = None, ""
        for i in range(14):
            final = await fetch_polymarket_close(client, symbol, start_unix, tf)
            if final is not None:
                src_name = "exact"
                break
            await asyncio.sleep(4 if i < 2 else 15)
        if final is None:
            final = _own_final_price(symbol, start_unix, tf.seconds)
            src_name = "own_ticks"
        if final is None or not open_px:
            diag["calib"]["dropped"] += len(pending)
            logger.info(f"calib {tf.key} {symbol}: no result for window {start_unix}, {len(pending)} samples dropped")
            return
        outcome = "UP" if final >= open_px else "DOWN"
        for s_ in pending:
            tf.calib.append([s_["coin"], s_["cp"], s_["lead"], 1 if s_["side"] == "UP" else 0,
                             1 if s_["side"] == outcome else 0, s_.get("ask"), s_["mom"], s_["ts"]])
        diag["calib"][src_name] += len(pending)
        calib_save(tf)
    except asyncio.CancelledError:
        raise
    except Exception as e:
        logger.warning(f"calib settle {symbol}: {e}")


def calib_stats(tf: Optional[TF] = None) -> dict:
    tf = tf or TF5
    acc = {thr: {cp: [0, 0, 0, 0.0, 0.0] for cp in tf.cps} for thr in CALIB_THRS}   # n, wins, n_ask, sum_ask, sum_pnl
    for coin, cp, lead, up, win, ask, mom, ts in tf.calib:
        if cp not in acc[0.0]:
            continue
        for thr in CALIB_THRS:
            if abs(lead) >= thr:
                a = acc[thr][cp]
                a[0] += 1
                a[1] += win
                if ask is not None and 0 < ask < 1:
                    a[2] += 1
                    a[3] += ask
                    a[4] += (1.0 if win else 0.0) - ask - fee_per_share(ask)
    out = {}
    for thr in CALIB_THRS:
        rows = []
        for cp in tf.cps:
            n, w, na, sa, sp = acc[thr][cp]
            rows.append({
                "cp": cp, "n": n,
                "wr": round(w / n * 100, 1) if n else None,
                "ask": round(sa / na * 100, 1) if na else None,
                "pnl": round(sp / na * 100, 2) if na else None,
                "n_ask": na,
            })
        out[str(int(thr))] = rows
    return out


async def api_calib(request):
    tf = _tf_from(request)
    return JSONResponse({"total": len(tf.calib), "thresholds": [int(t) for t in CALIB_THRS], "rows": calib_stats(tf)})


# ====================== Reversal reserve (facts from real ticks) ======================
TICK_HIST_MAXLEN = 3000      # ~75 min at 1.5s ticks
tick_hist: Dict[str, deque] = {s: deque(maxlen=TICK_HIST_MAXLEN) for s in SYMBOLS}   # (unix_time, chainlink_price)


def reversal_stats(symbol: str, lead_bps: float, horizon_sec: float) -> Optional[dict]:
    """
    How often did the REAL Chainlink price (as recorded by this bot) move against the current leader
    by at least |lead| bps within `horizon_sec` seconds? Pure counting over recorded ticks, no model.
    """
    if horizon_sec <= 0:
        return None
    h = list(tick_hist[symbol])
    n = len(h)
    if n < 50:
        return {"samples": 0, "hits": 0, "span_min": 0}
    times = [t for t, _ in h]
    span = times[-1] - times[0]
    cushion = abs(lead_bps)
    leader = "UP" if lead_bps >= 0 else "DOWN"
    samples = hits = 0
    j = 0
    for i in range(n):
        target = times[i] + horizon_sec
        if target > times[-1]:
            break
        j = bisect.bisect_left(times, target, max(j, i))
        if j >= n:
            break
        if times[j] - target > 3.0:      # data gap (reconnect / pause) -> do not count this interval
            continue
        d = (h[j][1] - h[i][1]) / h[i][1] * 10000
        samples += 1
        if (leader == "UP" and d <= -cushion) or (leader == "DOWN" and d >= cushion):
            hits += 1
    if span < horizon_sec + 120:
        samples = 0
    return {"samples": samples, "hits": hits, "span_min": int(span // 60)}


def early_signal(symbol: str, ws, price: float, seconds_passed: int, tf: Optional[TF] = None) -> Optional[dict]:
    """Signal BEFORE the regular confirmation time. Returns None unless the evidence is strong:
    a big lead, momentum not reversing, >= 20 min of recorded ticks, (almost) no reversals of this size in that
    history for the time left, AND the random-walk model agrees."""
    tf = tf or TF5
    if not ws.price_to_beat or ws.price_to_beat <= 0:
        return None
    lead = (price - ws.price_to_beat) / ws.price_to_beat * 10000
    if abs(lead) < EARLY_MIN_LEAD_BPS * tf.lead_scale:
        return None
    side = "UP" if lead > 0 else "DOWN"
    mom = momentum_bps(ws.prices, lookback=12)
    if (side == "UP" and mom < 0) or (side == "DOWN" and mom > 0):
        return None                                   # price is already moving back toward open
    time_left = tf.seconds - seconds_passed
    st = reversal_stats(symbol, lead, time_left)
    if not st or st["samples"] < EARLY_MIN_SAMPLES or st["span_min"] < tf.early_min_span:
        return None
    rate = st["hits"] / st["samples"]
    if rate > EARLY_MAX_REVERSAL:
        return None
    p_up = model_prob_up(ws.price_to_beat, price, seconds_passed, ws.series, tf.seconds)
    if p_up is None:
        return None
    p_side = p_up if side == "UP" else 1.0 - p_up
    if p_side < EARLY_MIN_MODEL_P:
        return None
    return {
        "side": side,
        "confidence": round(min(1.0 - rate, p_side), 3),   # the weaker of the two independent estimates
        "lead_bps": round(lead, 2),
        "time_left": time_left,
        "score": 0,
        "mom_short": round(mom, 2),
        "mom_med": round(momentum_bps(ws.prices, lookback=25), 2),
        "reason": "early",
        "rev_hits": st["hits"], "rev_samples": st["samples"], "rev_span_min": st["span_min"],
    }


async def _attach_mkt_price(client: httpx.AsyncClient, entry: dict, coin: str, side: str, start_unix: int,
                            tf: Optional[TF] = None):
    """Remember what the crowd was paying (best ask) when the signal fired."""
    try:
        asks, _ = await _paper_get_asks(client, coin, side, start_unix, tf)
        entry["mkt_price"] = round(asks[0][0], 3) if asks else None
    except Exception as e:
        logger.debug(f"mkt price: {e}")


# ====================== Volatility monitor ======================
# Compares how fast the REAL Chainlink price moved over the last ~45 s with the coin's own normal level
# (median of per-minute realized volatility over the recorded history). Ratio x1.0 = normal.
# An "event" starts when the ratio stays >= VOL_ON for a few seconds and ends when it stays < VOL_OFF for ~30 s.
# This is display only: it does NOT change signals or trades.
VOL_SHORT_SEC = float(os.getenv("VOL_SHORT_SEC", "45"))
VOL_ON = float(os.getenv("VOL_ON", "2.0"))
VOL_OFF = float(os.getenv("VOL_OFF", "1.4"))
VOL_HIGH = float(os.getenv("VOL_HIGH", "3.0"))
VOL_EXTREME = float(os.getenv("VOL_EXTREME", "4.5"))
VOL_START_HOLD = 8.0       # seconds the ratio must stay above VOL_ON before an event is declared (start time = first moment above)
VOL_END_HOLD = 30.0        # seconds below VOL_OFF before the event is declared over (end time = first moment below)
VOL_MIN_HISTORY_SEC = 600  # need >= 10 min of recorded ticks to know what "normal" is
VOL_LEVELS = {0: "спокійно", 1: "помірна", 2: "висока", 3: "екстремальна"}

vol_state: Dict[str, dict] = {s: {"active": False, "first_above": None, "below_since": None, "ratio": None, "level": 0,
                                  "warm": True, "now_bps": None, "typ_bps": None, "range_bps": None, "event": None}
                              for s in SYMBOLS}
vol_events: List[dict] = []      # newest first; a running event stays in this list and is updated in place
_vol_seq = 0


def _vol_level(r: float) -> int:
    return 3 if r >= VOL_EXTREME else 2 if r >= VOL_HIGH else 1 if r >= VOL_ON else 0


def vol_measure(symbol: str) -> Optional[dict]:
    pts = list(tick_hist[symbol])
    if len(pts) < 60:
        return None
    t_end = pts[-1][0]
    if t_end - pts[0][0] < VOL_MIN_HISTORY_SEC:
        return {"warm": True}
    cut = t_end - VOL_SHORT_SEC
    s2_short = dt_short = 0.0
    buckets: Dict[int, list] = {}
    lo = hi = pts[-1][1]
    for (t0, p0), (t1, p1) in zip(pts, pts[1:]):
        dt = t1 - t0
        if dt <= 0 or dt > 5.0 or p0 <= 0 or p1 <= 0:      # skip data gaps (reconnects)
            continue
        r = math.log(p1 / p0)
        if t1 >= cut:
            s2_short += r * r
            dt_short += dt
            lo, hi = min(lo, p1), max(hi, p1)
        elif t1 < cut - 30:                                # the baseline never includes the window being judged
            b = buckets.setdefault(int(t1 // 60), [0.0, 0.0])
            b[0] += r * r
            b[1] += dt
    base_list = sorted(math.sqrt(b[0] / b[1]) for b in buckets.values() if b[1] >= 30)
    if len(base_list) < 6 or dt_short < 15:
        return {"warm": True}
    base = max(base_list[len(base_list) // 2], 5e-6)
    short = math.sqrt(s2_short / dt_short)
    k = math.sqrt(VOL_SHORT_SEC) * 10000.0                  # per-sqrt-second -> bps over VOL_SHORT_SEC
    price = pts[-1][1]
    return {"warm": False, "ratio": short / base, "now_bps": short * k, "typ_bps": base * k,
            "range_bps": (hi - lo) / price * 10000.0, "price": price}


def vol_update(symbol: str):
    global _vol_seq
    st = vol_state[symbol]
    now = time.time()
    m = vol_measure(symbol)
    if m is None or m.get("warm"):
        st.update(warm=True, ratio=None, level=0, now_bps=None, typ_bps=None, range_bps=None)
        return
    ratio, price = m["ratio"], m["price"]
    st.update(warm=False, ratio=round(ratio, 2), level=_vol_level(ratio), now_bps=round(m["now_bps"], 2),
              typ_bps=round(m["typ_bps"], 2), range_bps=round(m["range_bps"], 2))
    coin = symbol.replace("USDT", "")
    if not st["active"]:
        if ratio >= VOL_ON:
            if st["first_above"] is None:
                st["first_above"] = (now, price)
            elif now - st["first_above"][0] >= VOL_START_HOLD:
                _vol_seq += 1
                t0, p0 = st["first_above"]
                ev = {"id": _vol_seq, "symbol": coin, "start": int(t0), "end": None, "active": True,
                      "peak_ratio": round(ratio, 2), "peak_level": _vol_level(ratio),
                      "start_price": p0, "last_price": price, "hi": max(p0, price), "lo": min(p0, price)}
                st.update(active=True, event=ev, below_since=None)
                vol_events.insert(0, ev)
                del vol_events[60:]
                logger.info(f"VOLATILITY START {coin} x{ratio:.1f}")
        else:
            st["first_above"] = None
        return
    ev = st["event"]
    ev["last_price"] = price
    ev["hi"], ev["lo"] = max(ev["hi"], price), min(ev["lo"], price)
    if ratio > ev["peak_ratio"]:
        ev["peak_ratio"], ev["peak_level"] = round(ratio, 2), _vol_level(ratio)
    if ratio < VOL_OFF:
        if st["below_since"] is None:
            st["below_since"] = (now, price)
        elif now - st["below_since"][0] >= VOL_END_HOLD:
            ev["end"], ev["last_price"], ev["active"] = int(st["below_since"][0]), st["below_since"][1], False
            st.update(active=False, event=None, first_above=None, below_since=None)
            logger.info(f"VOLATILITY END {coin} peak x{ev['peak_ratio']}")
    else:
        st["below_since"] = None


def _vol_event_view(ev: dict) -> dict:
    p0 = ev["start_price"] or 1.0
    end = ev["end"] or int(time.time())
    return {"id": ev["id"], "symbol": ev["symbol"], "start": ev["start"], "end": ev["end"], "active": ev["active"],
            "dur": max(0, end - ev["start"]), "peak_ratio": ev["peak_ratio"], "peak_level": ev["peak_level"],
            "move_bps": round((ev["last_price"] - p0) / p0 * 10000.0, 1),
            "range_bps": round((ev["hi"] - ev["lo"]) / p0 * 10000.0, 1)}


def _vol_payload() -> dict:
    coins = {}
    for sym, st in vol_state.items():
        ev = st["event"] if st["active"] else None
        coins[sym.replace("USDT", "")] = {
            "warm": st["warm"], "ratio": st["ratio"], "level": st["level"], "label": VOL_LEVELS[st["level"]],
            "active": st["active"], "since": ev["start"] if ev else None,
            "peak_ratio": ev["peak_ratio"] if ev else None, "peak_label": VOL_LEVELS[ev["peak_level"]] if ev else None,
            "now_bps": st["now_bps"], "typ_bps": st["typ_bps"], "range_bps": st["range_bps"],
        }
    return {"short_sec": int(VOL_SHORT_SEC), "on": VOL_ON, "off": VOL_OFF, "high": VOL_HIGH, "extreme": VOL_EXTREME,
            "coins": coins, "events": [_vol_event_view(e) for e in vol_events[:30]]}


# ====================== RTDS Chainlink ======================
RTDS_URL = "wss://ws-live-data.polymarket.com"
CL_FRESH_SEC = 15.0           # Chainlink tick older than this = stale -> coin is paused (no signals)
RTDS_DEAD_SEC = 15.0          # no Chainlink price at all for this long -> reconnect
RTDS_SYMBOL_DEAD_SEC = 30.0   # a coin that was updating and then went silent this long -> reconnect
live_chainlink_ts: Dict[str, float] = {}   # symbol -> time.monotonic() of the last tick
diag: dict = {"rtds_reconnects": 0, "last_reconnect": "", "last_reconnect_at": None,
              "calib": {"exact": 0, "own_ticks": 0, "dropped": 0}}


async def rtds_session():
    """One websocket session. Raises (-> reconnect) when the connection is dead OR silently stopped sending prices."""
    async with websockets.connect(RTDS_URL, ping_interval=None, close_timeout=5, open_timeout=10) as ws:
        # one subscription for ALL chainlink symbols (no filters) - most reliable
        subs = [{"topic": "crypto_prices_chainlink", "type": "*", "filters": ""}]
        await ws.send(json.dumps({"action": "subscribe", "subscriptions": subs}))
        logger.info("RTDS subscribed to Chainlink prices")

        t_conn = time.monotonic()
        last_ping = t_conn
        last_data = t_conn          # last time a real Chainlink PRICE arrived (PONG does not count)
        while True:
            try:
                raw = await asyncio.wait_for(ws.recv(), timeout=2.0)
            except asyncio.TimeoutError:
                raw = None
            now = time.monotonic()

            if now - last_ping >= 5.0:
                await asyncio.wait_for(ws.send("PING"), timeout=5.0)
                last_ping = now

            # watchdogs: a socket can stay "open" while the data stream is dead
            if now - last_data > RTDS_DEAD_SEC:
                raise RuntimeError(f"no Chainlink prices for {now - last_data:.0f}s")
            for sym, ts in list(live_chainlink_ts.items()):
                if now - max(ts, t_conn) > RTDS_SYMBOL_DEAD_SEC:
                    raise RuntimeError(f"{sym} silent for {now - max(ts, t_conn):.0f}s")

            if raw is None or raw == "PONG":
                continue
            try:
                msg = json.loads(raw)
            except Exception:
                continue
            if not isinstance(msg, dict):
                continue
            topic = msg.get("topic") or ""
            if "chainlink" not in topic:
                continue
            payload = msg.get("payload") or {}
            sym = (payload.get("symbol") or "").lower()
            val = payload.get("value")
            if val is None and isinstance(payload.get("data"), list) and payload["data"]:
                val = payload["data"][-1].get("value")  # initial snapshot
            if val is None:
                continue
            usdt = SYM_FROM_CL.get(sym)
            if not usdt:
                continue
            try:
                price = float(val)
            except Exception:
                continue
            if price <= 0:
                continue
            if usdt not in live_chainlink:
                logger.info(f"RTDS first chainlink price {usdt}={price}")
            live_chainlink[usdt] = price
            live_chainlink_ts[usdt] = now
            last_data = now


async def rtds_loop():
    while True:
        try:
            await rtds_session()
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.warning(f"RTDS reconnect in 2s: {e!r}")
            diag["rtds_reconnects"] += 1
            diag["last_reconnect"] = repr(e)[:150]
            diag["last_reconnect_at"] = datetime.now(timezone.utc).isoformat()
        await asyncio.sleep(2)


async def process_symbol(client: httpx.AsyncClient, symbol: str, start_unix: int, window_start: datetime,
                         tf: Optional[TF] = None) -> bool:
    """One tick for one coin. Returns False if there is no fresh Chainlink price (coin paused).
    tf = timeframe profile (5m by default). Only the 5m profile feeds virtual / live trading and the tick history."""
    tf = tf or TF5
    is5 = tf is TF5
    signal_history = tf.signal_history
    early_history = tf.early_history
    ws = tf.state[symbol]
    price = live_chainlink.get(symbol)
    tick = live_chainlink_ts.get(symbol)
    if price is None or tick is None or time.monotonic() - tick > CL_FRESH_SEC:
        ws.last_error = "chainlink stale"
        return False
    ws.last_error = None

    # close previous window: mark history outcomes ONLY when the window has ended
    if (ws.window_start is not None and ws.window_start != window_start
            and ws.last_signal and ws.price_to_beat and ws.last_price):
        prev_start_unix = int(ws.window_start.timestamp())
        final = await fetch_polymarket_close(client, symbol, prev_start_unix, tf)
        if final is None:
            final = twap_final_minute(ws.series, tf.seconds) or ws.last_price
        open_p = ws.price_to_beat
        actual = "UP" if final >= open_p else "DOWN"
        predicted = ws.last_signal.get("side")
        if is5:
            paper_settle(symbol.replace("USDT", ""), prev_start_unix, actual)
        for h in signal_history:
            if h.get("window_start") == ws.window_start.isoformat() and h.get("symbol") == symbol.replace("USDT", ""):
                h["result"] = "win" if predicted == actual else "loss"
                h["final"] = final
                h["actual"] = actual
                h["move"] = round(final - open_p, 6)
                break

    if (ws.window_start is not None and ws.window_start != window_start
            and ws.early and ws.early.get("side") and ws.price_to_beat and ws.last_price):
        try:
            fin = await fetch_polymarket_close(client, symbol, int(ws.window_start.timestamp()), tf)
            if fin is None:
                fin = twap_final_minute(ws.series, tf.seconds) or ws.last_price
            act = "UP" if fin >= ws.price_to_beat else "DOWN"
            early_history.insert(0, {
                "symbol": symbol.replace("USDT", ""), "side": ws.early["side"], "actual": act,
                "result": "win" if ws.early["side"] == act else "loss",
                "time": ws.early["time"], "move": round(fin - ws.price_to_beat, 6),
            })
            del early_history[300:]
        except Exception as e:
            logger.warning(f"early eval error: {e}")

    # calibration: samples of the finished window get their real result in the background
    if ws.window_start is not None and ws.window_start != window_start and ws.calib_pending:
        pending, ws.calib_pending = ws.calib_pending, []
        spawn(calib_settle(client, symbol, int(ws.window_start.timestamp()), pending, ws.price_to_beat, tf))

    # new window
    if ws.window_start is None or ws.window_start != window_start:
        if is5:
            await paper_settle_orphans(client, symbol, start_unix)
        pm_open = await fetch_polymarket_open(client, symbol, start_unix, tf)
        if pm_open is not None:
            open_px, open_src = pm_open, "polymarket"
        else:
            open_px, open_src = live_chainlink.get(symbol, price), "chainlink"
        ws.reset(open_px, window_start, source=open_src)
        ws.open_confirmed = pm_open is not None
        logger.info(f"[{symbol}/{tf.key}] New window open={open_px:.4f} ({open_src})")
        return True

    # Polymarket open not available at window start yet -> keep retrying
    if not ws.open_confirmed:
        pm_open = await fetch_polymarket_open(client, symbol, start_unix, tf)
        if pm_open is not None:
            ws.price_to_beat = pm_open
            ws.open_confirmed = True
            ws.source = "polymarket"
            logger.info(f"[{symbol}] Open set from Polymarket: {pm_open:.4f}")

    # network calls above may have taken a while: re-read time and price
    now_utc = datetime.now(timezone.utc)
    seconds_passed = int((now_utc - window_start).total_seconds())
    if seconds_passed >= tf.seconds:
        return True        # window just ended; the next tick will open the new one
    price = live_chainlink.get(symbol, price)

    # update live
    ws.prices.append(price)
    ws.last_price = price
    if is5:            # one shared tick history: only the 5m loop writes it (otherwise ticks would be doubled)
        tick_hist[symbol].append((time.time(), price))
        vol_update(symbol)

    # calibration checkpoints (only with the confirmed Polymarket open, only the first tick right after the checkpoint)
    if ws.open_confirmed and ws.price_to_beat:
        for cp in tf.cps:
            if cp in ws.calib_done or seconds_passed < cp:
                continue
            ws.calib_done.add(cp)
            if seconds_passed - cp > 5:
                continue
            lead_c = (price - ws.price_to_beat) / ws.price_to_beat * 10000
            if lead_c == 0:
                continue
            sample = {"coin": symbol.replace("USDT", ""), "cp": cp, "lead": round(lead_c, 2),
                      "side": "UP" if lead_c > 0 else "DOWN", "mom": round(momentum_bps(ws.prices, 12), 2),
                      "ts": int(time.time()), "ask": None}
            ws.calib_pending.append(sample)
            spawn(calib_fill_ask(client, symbol, start_unix, sample, tf))

    # early forecast: trend of the last ~25 ticks (incl. the end of the previous window)
    if ws.early is None and seconds_passed >= 3:
        seq = list(ws.prev_tail) + list(ws.prices)
        side_e, mom_e = None, 0.0
        if len(seq) >= 12:
            ref = seq[-min(len(seq), 25)]
            mom_e = (seq[-1] - ref) / ref * 10000
            if abs(mom_e) >= 0.5:
                side_e = "UP" if mom_e > 0 else "DOWN"
        ws.early = {"side": side_e, "mom_bps": round(mom_e, 2), "time": now_utc.isoformat()}
    ws.series.append((round((now_utc - ws.window_start).total_seconds(), 1), price))
    ws.last_update = now_utc

    if ws.signal_sent:
        return True
    signal, mode = None, "confirm"
    if seconds_passed >= tf.confirm_at:
        signal = generate_signal(ws.price_to_beat, price, seconds_passed, ws.prices, tf)
        if not is_strong_signal(signal):
            signal = None
    elif EARLY_ON and seconds_passed >= tf.early_from:
        signal, mode = early_signal(symbol, ws, price, seconds_passed, tf), "early"
    if signal:
        ws.signal_sent = True
        entry = {
            **signal,
            "mode": mode,
            "fired_at": seconds_passed,
            "symbol": symbol.replace("USDT", ""),
            "momentum_bps": signal.get("mom_short", 0),
            "price": price,
            "open": ws.price_to_beat,
            "time": now_utc.isoformat(),
            "window_start": window_start.isoformat(),
        }
        p_up = model_prob_up(ws.price_to_beat, price, seconds_passed, ws.series, tf.seconds)
        p_side = None if p_up is None else (p_up if signal["side"] == "UP" else 1.0 - p_up)
        entry["model_p"] = round(p_side, 3) if p_side is not None else None
        ws.last_signal = entry
        signal_history.insert(0, entry)
        if is5:            # virtual wallets (and live, via wallet 1) trade only 5m signals
            spawn(paper_open(client, symbol, signal["side"], start_unix, p_side, mode))
        spawn(_attach_mkt_price(client, entry, symbol.replace("USDT", ""), signal["side"], start_unix, tf))
        if len(signal_history) > HISTORY_KEEP:
            del signal_history[HISTORY_KEEP:]
        logger.info(
            f"SIGNAL[{tf.key}/{mode}@{seconds_passed}s] {symbol} {signal['side']} conf={signal['confidence']} "
            f"score={signal.get('score')} lead={signal.get('lead_bps')} "
            f"mom={signal.get('mom_short')}"
        )
    return True


async def price_loop(tf: Optional[TF] = None):
    """One loop per timeframe, each with its own HTTP client: a problem in the 15m loop cannot slow down the 5m one."""
    tf = tf or TF5
    async with httpx.AsyncClient(headers={"User-Agent": "Mozilla/5.0"}) as client:
        while True:
            try:
                start_unix = get_window_start_unix(tf)
                window_start = get_current_window_start(tf)
                # all coins in parallel: a slow Polymarket call for one coin must not delay the others
                results = await asyncio.wait_for(
                    asyncio.gather(*(process_symbol(client, s, start_unix, window_start, tf) for s in SYMBOLS),
                                   return_exceptions=True),
                    timeout=20.0,
                )
                any_ok = False
                for s, r in zip(SYMBOLS, results):
                    if isinstance(r, BaseException):
                        logger.error(f"process {s}: {r!r}")
                    elif r:
                        any_ok = True
                tf.error = None if any_ok else "Chainlink: немає свіжих цін"
                await asyncio.sleep(1.5)      # keep 1.5s: momentum thresholds are tuned for this tick spacing
            except asyncio.CancelledError:
                raise
            except Exception as e:
                tf.error = str(e) or type(e).__name__
                logger.error(f"Loop[{tf.key}]: {tf.error}")
                await asyncio.sleep(5)


async def supervise(name: str, fn):
    """Restart a background loop if it ever dies."""
    while True:
        try:
            await fn()
            return
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.error(f"{name} crashed, restarting in 2s: {e!r}")
            await asyncio.sleep(2)


async def keepalive_loop():
    """Render free sleeps after 15 min without inbound HTTP. Ping our own public URL so it never sleeps."""
    base = os.getenv("RENDER_EXTERNAL_URL", "").strip().rstrip("/")
    if not base:
        return
    logger.info(f"keepalive -> {base}/health every 4 min")
    async with httpx.AsyncClient(timeout=10.0) as c:
        while True:
            await asyncio.sleep(240)
            try:
                await c.get(base + "/health")
            except Exception as e:
                logger.debug(f"keepalive: {e}")


def _flip_info(symbol: str, ws, current: float, lead_bps: float, time_left: int) -> Optional[dict]:
    if not ws.signal_sent or not ws.last_signal or time_left <= 0:
        return None
    st = reversal_stats(symbol, lead_bps, time_left)
    if st is None:
        return None
    return {
        "leader": "UP" if lead_bps >= 0 else "DOWN",
        "signal_side": ws.last_signal.get("side"),
        "cushion_bps": round(abs(lead_bps), 2),
        "cushion_usd": round(abs(current - ws.price_to_beat), 6),
        "horizon": time_left,
        **st,
    }


async def api_status(request):
    tf = _tf_from(request)                     # ?tf=15m -> 15-minute forecasts, default 5m
    signal_history = tf.signal_history
    early_history = tf.early_history
    window_start = get_current_window_start(tf)
    seconds_passed = int((datetime.now(timezone.utc) - window_start).total_seconds())
    time_left = max(0, tf.seconds - seconds_passed)

    markets = {}
    for symbol, ws in tf.state.items():
        name = symbol.replace("USDT", "")
        if ws.price_to_beat is None:
            markets[name] = {"status": "waiting", "error": ws.last_error}
            continue
        current = ws.last_price or ws.price_to_beat
        lead = ((current - ws.price_to_beat) / ws.price_to_beat) * 10000
        live = generate_signal(ws.price_to_beat, current, max(seconds_passed, tf.confirm_at), ws.prices, tf)
        markets[name] = {
            "open": round(ws.price_to_beat, 4),
            "current": round(current, 4),
            "lead_bps": round(lead, 2),
            "signal_sent": ws.signal_sent,
            "signal": ws.last_signal,
            "live_side": live.get("side"),
            "live_confidence": live.get("confidence", 0),
            "live_score": live.get("score", 0),
            "live_reason": live.get("reason"),
            "early": ws.early,
            "model_p_up": (lambda p: round(p, 3) if p is not None else None)(model_prob_up(ws.price_to_beat, current, seconds_passed, ws.series, tf.seconds)),
            "source": ws.source,
            "flip": _flip_info(symbol, ws, current, lead, time_left),
            "stale": bool(ws.last_error),
            "series": [[t, round(p, 4)] for t, p in ws.series],
            "twap60": (round(twap_last_seconds(ws.series), 4) if ws.series else None),
            "updated": ws.last_update.isoformat() if ws.last_update else None,
        }

    # simple win-rate from resolved history
    resolved = [h for h in signal_history if h.get("result") in ("win", "loss")]
    wins = sum(1 for h in resolved if h["result"] == "win")
    losses = sum(1 for h in resolved if h["result"] == "loss")
    total_r = wins + losses
    win_rate = round(wins / total_r * 100, 1) if total_r else None

    timing = []
    mid = int(round(tf.seconds * 2 / 3))      # 200 s for 5m (as before), 600 s for 15m
    for label, lo, hi in (("ранні (до %d с)" % tf.confirm_at, 0, tf.confirm_at), ("%d–%d с" % (tf.confirm_at, mid), tf.confirm_at, mid), ("після %d с" % mid, mid, 10**6)):
        grp = [h for h in resolved if lo <= h.get("fired_at", tf.confirm_at) < hi]
        px = [h["mkt_price"] for h in signal_history if h.get("mkt_price") is not None and lo <= h.get("fired_at", tf.confirm_at) < hi]
        if grp or px:
            timing.append({"label": label, "n": len(grp), "wins": sum(1 for h in grp if h["result"] == "win"),
                           "avg_mkt": round(sum(px) / len(px), 3) if px else None})

    return JSONResponse({
        "server_time": datetime.now(timezone.utc).isoformat(),
        "timing": timing,
        "window_start": window_start.isoformat(),
        "seconds_passed": seconds_passed,
        "time_left": time_left,
        "confirm_at": tf.confirm_at,
        "tf": tf.key,
        "window": tf.seconds,
        "error": tf.error,
        "vol": _vol_payload(),
        "chainlink_live": {k.replace("USDT",""): v for k,v in live_chainlink.items()},
        "markets": markets,
        "history": signal_history[:HISTORY_KEEP],
        "early_stats": {
            "wins": sum(1 for e in early_history if e["result"] == "win"),
            "losses": sum(1 for e in early_history if e["result"] == "loss"),
        },
        "stats": {
            "signals": len(signal_history),
            "resolved": total_r,
            "wins": wins,
            "losses": losses,
            "win_rate": win_rate,
        },
    })


async def health(request):
    now = time.monotonic()
    return JSONResponse({"ok": True, "chainlink": list(live_chainlink.keys()),
                         "paused": [s.replace("USDT", "") for s, w in state.items() if w.last_error],
                         "rtds": diag,
                         "tf15": {"on": ENABLE_15M, "confirm_at": CONFIRM_AT_15, "early_from": EARLY_FROM_15,
                                  "error": TF15.error, "paused": [s.replace("USDT", "") for s, w in TF15.state.items() if w.last_error]},
                         "thresholds": {"min_lead_bps": MIN_LEAD_BPS, "min_mom_short": MIN_MOM_SHORT,
                                        "min_mom_med": MIN_MOM_MED, "confirm_at": CONFIRM_AT, "min_confidence": MIN_CONFIDENCE,
                                        "early": {"on": EARLY_ON, "from": EARLY_FROM, "min_lead_bps": EARLY_MIN_LEAD_BPS,
                                                  "max_reversal": EARLY_MAX_REVERSAL, "min_model_p": EARLY_MIN_MODEL_P}},
                         "tick_age_sec": {k.replace("USDT", ""): round(now - v, 1) for k, v in live_chainlink_ts.items()}})


# HTML — same dashboard (compact)
HTML_PAGE = """<!DOCTYPE html>
<html lang="uk">
<head>
<meta charset="UTF-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, viewport-fit=cover"/>
<meta name="apple-mobile-web-app-capable" content="yes"/>
<title>5m Signals</title>
<style>
:root{--bg:#0b0b0c;--card:#141415;--border:#232326;--text:#ececee;--muted:#8a8a93;--up:#22c55e;--down:#ef4444;--accent:#8b8bff}
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;background:var(--bg);color:var(--text);min-height:100vh;padding:14px;padding-bottom:40px}
header{display:flex;justify-content:space-between;align-items:center;margin-bottom:14px}
h1{font-size:1.15rem;font-weight:700}
.badge{font-size:.72rem;background:#1c1c1f;color:var(--muted);padding:4px 10px;border-radius:999px;border:1px solid var(--border)}
.badge.ok{color:var(--up);border-color:rgba(34,197,94,.3)}
.top{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-bottom:14px}
.ac{background:var(--card);border:1px solid var(--border);border-radius:14px;padding:12px 14px}
.an{font-size:.72rem;color:var(--muted)}.ap{font-size:1.05rem;font-weight:700;font-variant-numeric:tabular-nums}
.ach{font-size:.78rem;font-weight:600}.pos{color:var(--up)}.neg{color:var(--down)}
.panel{background:var(--card);border:1px solid var(--border);border-radius:16px;padding:14px;margin-bottom:12px}
.pt{font-size:.8rem;color:var(--muted);margin-bottom:10px;display:flex;justify-content:space-between}
.mrow{display:grid;grid-template-columns:50px 1fr 1fr 90px;gap:6px;padding:9px 0;border-bottom:1px solid var(--border);font-size:.88rem;align-items:center}
.mrow.h{color:var(--muted);font-size:.7rem;text-transform:uppercase;border:none}
.bs{padding:3px 8px;border-radius:6px;font-size:.72rem;font-weight:700}
.bu{background:rgba(34,197,94,.15);color:var(--up)}.bd{background:rgba(239,68,68,.15);color:var(--down)}.bw{background:#1c1c1f;color:var(--muted)}
.timer{font-size:2rem;font-weight:700;font-variant-numeric:tabular-nums;margin:6px 0 12px}
.btns{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-bottom:10px}
.bup,.bdn{padding:13px;border-radius:12px;border:none;font-weight:700;font-size:.9rem;text-align:center;opacity:.45;transition:.2s}
.bup{background:rgba(34,197,94,.18);color:var(--up)}.bdn{background:rgba(239,68,68,.18);color:var(--down)}
.bup.on,.bdn.on{opacity:1;box-shadow:0 0 0 2px currentColor}
.conf{height:6px;background:#1c1c1f;border-radius:4px;overflow:hidden;margin-top:6px}
.conf i{display:block;height:100%;background:var(--accent);width:0;transition:width .4s}
.ct{font-size:.85rem;color:var(--muted);margin-top:4px}
.lr{display:flex;justify-content:space-between;padding:5px 0;font-size:.85rem;border-bottom:1px solid var(--border)}
.hrow{display:grid;grid-template-columns:60px 40px 30px 40px 1fr;gap:4px;padding:7px 0;border-bottom:1px solid var(--border);font-size:.78rem;align-items:center}
.stats{display:flex;gap:12px;font-size:.78rem;color:var(--muted);margin-bottom:8px;flex-wrap:wrap}
.stats b{color:var(--text)}
.ctabs{display:flex;gap:6px;margin-bottom:10px}
.ctabs button{flex:1;background:#1c1c1f;color:var(--muted);border:1px solid var(--border);border-radius:8px;padding:7px 0;font-size:.78rem;font-weight:600}
.ctabs button.on{color:var(--text);border-color:var(--accent)}
.cnums{display:flex;gap:18px;margin-bottom:8px}
.cnums small{display:block;font-size:.68rem;color:var(--muted)}
.cnums b{font-size:1.05rem;font-variant-numeric:tabular-nums}
.bnav{position:fixed;left:0;right:0;bottom:0;display:flex;background:#101012;border-top:1px solid var(--border);padding-bottom:env(safe-area-inset-bottom);z-index:40}
.bnav button{flex:1;background:none;border:0;color:var(--muted);padding:9px 0 8px;font-size:1.25rem;display:flex;flex-direction:column;align-items:center;gap:2px}
.bnav button span{font-size:.68rem;font-weight:600;letter-spacing:.04em}
.bnav button.on{color:var(--text)}
.sheet{position:fixed;left:0;right:0;top:0;bottom:calc(58px + env(safe-area-inset-bottom));background:var(--bg);display:none;z-index:30;flex-direction:column;padding:14px 16px 0}
.sheet.open{display:flex}
header{padding-right:52px}
.vfab{position:fixed;top:calc(10px + env(safe-area-inset-top));right:14px;z-index:55;width:40px;height:40px;border-radius:50%;background:#1c1c1f;border:1px solid var(--border);color:var(--muted);font-size:1.15rem;display:flex;align-items:center;justify-content:center;padding:0}
.vfab .vn{position:absolute;top:-5px;right:-5px;min-width:17px;height:17px;border-radius:9px;background:var(--down);color:#fff;font-size:.65rem;font-weight:700;display:none;align-items:center;justify-content:center;padding:0 4px}
.vfab.l1{color:#eab308;border-color:#eab308}.vfab.l2{color:#f97316;border-color:#f97316}.vfab.l3{color:var(--down);border-color:var(--down)}
.vfab.act{animation:vpulse 1.3s infinite}
@keyframes vpulse{0%,100%{box-shadow:0 0 0 0 rgba(249,115,22,.55)}50%{box-shadow:0 0 0 8px rgba(249,115,22,0)}}
.vpop{position:fixed;left:0;right:0;top:0;bottom:0;background:rgba(0,0,0,.6);z-index:60;display:none;align-items:flex-end}
.vpop.open{display:flex}
.vbox{width:100%;max-height:82vh;overflow-y:auto;background:var(--bg);border-top:1px solid var(--border);border-radius:16px 16px 0 0;padding:16px 16px calc(16px + env(safe-area-inset-bottom))}
.vclose{width:100%;margin-top:14px;padding:11px;border-radius:10px;border:1px solid var(--border);background:#1c1c1f;color:var(--text);font-size:.9rem}
.sheet h3{margin:0 0 10px;font-size:1rem}
.sheet .scroll{flex:1;overflow-y:auto;-webkit-overflow-scrolling:touch;padding-bottom:12px}
.subtabs{display:flex;gap:6px;margin:10px 0 4px;overflow-x:auto}
.subtabs button{flex:none;padding-left:14px!important;padding-right:14px!important;white-space:nowrap;background:#1c1c1f;color:var(--muted);border:1px solid var(--border);border-radius:8px;padding:8px 0;font-size:.74rem;font-weight:600}
.subtabs button.on{color:var(--text);border-color:var(--accent)}
.vbar{display:flex;height:10px;border-radius:6px;overflow:hidden;margin:8px 0 4px;background:#232326}
.wrow{padding:9px 0;border-bottom:1px solid var(--border);font-size:.82rem}
.wrow a{color:var(--text);text-decoration:none;font-family:ui-monospace,Menlo,monospace}
.wrow .sub{color:var(--muted);font-size:.74rem;margin-top:2px}
.sec{font-size:.7rem;letter-spacing:.12em;color:var(--muted);margin:14px 0 4px;text-transform:uppercase}
.pbtn{background:#1c1c1f;color:var(--muted);border:1px solid var(--border);border-radius:999px;padding:7px 16px;font-size:.8rem;font-weight:700}
.pbtn.on{color:#0b0b0c;background:var(--up);border-color:var(--up)}
.inp{background:#1c1c1f;border:1px solid var(--border);color:var(--text);border-radius:10px;padding:10px;font-size:1rem;width:100%;box-sizing:border-box}
.prow{display:flex;gap:8px;align-items:center;margin:10px 0}
.prow label{font-size:.78rem;color:var(--muted);min-width:78px}
.pgrid{display:grid;grid-template-columns:1fr 1fr;gap:12px}
.pgrid small{display:block;font-size:.68rem;color:var(--muted)}
.pgrid b{font-size:1.05rem;font-variant-numeric:tabular-nums}
.pgo{background:var(--accent);color:#0b0b0c;border:0;border-radius:10px;padding:10px 16px;font-weight:700;font-size:.85rem;white-space:nowrap}
.pgh{background:#1c1c1f;color:var(--text);border:1px solid var(--border);border-radius:10px;padding:10px 14px;font-size:.8rem;font-weight:600;white-space:nowrap}
</style>
</head>
<body>
<header>
  <h1>⚡ 5m Signals</h1>
  <div id="badge" class="badge">…</div>
</header>
<!--P5-->
<div style="height:90px"></div>
<button id="vfab" class="vfab" aria-label="Волатильність">⚡<span id="vfn" class="vn"></span></button>
<div id="vpop" class="vpop"><div class="vbox">
  <div class="pt"><span>⚡ Волатильність</span><span id="volt"></span></div>
  <div id="vol"></div>
  <div class="sec" style="margin:12px 0 2px">Останні періоди</div>
  <div id="volh" style="font-size:.78rem"></div>
  <div id="volnote" style="font-size:.68rem;color:var(--muted);line-height:1.45;margin-top:8px"></div>
  <button id="vclose" class="vclose">Закрити</button>
</div></div>
<div class="sheet" id="sheet">
  <h3>Угоди на Polymarket (поточне вікно)</h3>
  <div class="ctabs" id="wtabs"><button data-s="BTC">BTC</button><button data-s="ETH">ETH</button><button data-s="SOL">SOL</button><button data-s="XRP">XRP</button></div>
  <div id="wsum"></div>
  <div class="subtabs" id="wsub"><button data-t="feed">Стрічка</button><button data-t="buy">Купівлі</button><button data-t="sell">Продажі</button><button data-t="up">Up</button><button data-t="down">Down</button><button data-t="top">Гаманці</button></div>
  <div class="scroll" id="wbody" style="color:var(--muted);font-size:.85rem">Завантаження…</div>
</div>
<div class="sheet" id="vtop">
  <h3>Найуспішніші трейдери · крипто (за прибутком)</h3>
  <div class="ctabs" id="ttabs" style="margin-top:4px"><button data-p="day">Сьогодні</button><button data-p="week">Тиждень</button><button data-p="month">Місяць</button></div>
  <div class="scroll" id="tbody" style="color:var(--muted);font-size:.85rem;margin-top:10px">Завантаження…</div>
</div>
<div class="sheet" id="v15">
  <h3>Прогнози на 15 хв</h3>
  <div class="scroll"><!--P15-->
<div style="height:30px"></div></div>
</div>
<div class="sheet" id="vpap">
  <h3>Віртуальні гаманці та live</h3>
  <div class="scroll">
    <div class="ctabs" id="pwtabs"></div>
    <div class="panel" id="lpan" style="border:1px solid #7f1d1d"></div>
    <div class="panel">
      <div class="prow"><label>Назва</label><input class="inp" id="pname" maxlength="24" type="text"></div>
      <div class="prow" style="justify-content:space-between"><span>Торгувати віртуально</span><button class="pbtn" id="pen">ВИМК</button></div>
      <div style="font-size:.72rem;color:var(--muted);margin-bottom:6px">Монети, якими торгувати:</div>
      <div class="ctabs" id="pcoins"><button data-c="BTC">BTC</button><button data-c="ETH">ETH</button><button data-c="SOL">SOL</button><button data-c="XRP">XRP</button></div>
      <div class="prow"><label>Ставка</label><select class="inp" id="pmode" style="flex:1.2"><option value="pct">% від балансу</option><option value="usd">$ фіксована</option><option value="kelly">Kelly (% від повного)</option></select><input class="inp" id="pval" type="number" inputmode="decimal" style="flex:1"></div>
      <div style="font-size:.72rem;color:var(--muted);margin:10px 0 2px">Фільтри входу (0 = вимкнено):</div>
      <div class="prow"><label>Мін. edge %</label><input class="inp" id="pedge" type="number" inputmode="decimal"></div>
      <div class="prow"><label>Ціна ¢ від</label><input class="inp" id="pminp" type="number" inputmode="numeric" style="flex:1"><label style="min-width:30px;text-align:center">до</label><input class="inp" id="pmaxp" type="number" inputmode="numeric" style="flex:1"></div>
      <div class="prow"><button class="pgo" id="psave">Зберегти</button><span id="pmsg" style="font-size:.78rem;color:var(--up)"></span></div>
      <div class="prow" style="margin-top:14px"><label>Депозит $</label><input class="inp" id="pdep" type="number" inputmode="decimal" style="flex:1"><button class="pgh" id="preset">Скинути рахунок</button></div>
      <div style="font-size:.7rem;color:var(--muted)">Зміни депозит і натисни «Зберегти» (або «Скинути рахунок»): баланс стане рівним депозиту, історія віртуальних угод буде стерта.</div>
    </div>
    <div class="panel"><div id="pacc"></div><div id="pspark" style="margin-top:10px"></div></div>
    <div class="panel"><div class="pt"><span>Віртуальні угоди</span></div><div id="plist"></div></div>
  </div>
</div>
<div class="sheet" id="vchart">
  <div class="ctabs" id="ktabs"><button data-s="BTC">BTC</button><button data-s="ETH">ETH</button><button data-s="SOL">SOL</button><button data-s="XRP">XRP</button></div>
  <div id="tvbox" style="flex:1;min-height:0;margin-bottom:8px;border-radius:12px;overflow:hidden;background:#0b0b0c"></div>
  <div style="font-size:.68rem;color:var(--muted);margin-bottom:8px">TradingView · Bitstamp, 5 хв. Це не Chainlink: ціна може відрізнятись на кілька bps від тієї, за якою рахується Polymarket.</div>
</div>
<nav class="bnav"><button id="nv1" class="on">📈<span>Сигнали</span></button><button id="nv6">⏱️<span>15 хв</span></button><button id="nv2">🐋<span>Гаманці</span></button><button id="nv3">🏆<span>Трейдери</span></button><button id="nv4">💰<span>Віртуал</span></button><button id="nv5">📊<span>Графік</span></button></nav>
<script>
const S=["BTC","ETH","SOL","XRP"];
function f(n,d=2){return n==null?"—":Number(n).toFixed(d)}
// two views share the same code: "" = 5m (main page), "15" = 15m sheet. Element ids carry the suffix.
const VS={"":{cs:"BTC",cm:"c",d:null,thr:"6",tf:"5m"},"15":{cs:"BTC",cm:"c",d:null,thr:"6",tf:"15m"}};
const E=(id,sx)=>document.getElementById(id+sx);
const escH=x=>String(x).replace(/[&<>]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;"}[c]));
const hms=ts=>new Date(ts*1000).toLocaleTimeString([],{hour:"2-digit",minute:"2-digit",second:"2-digit"});
const fdur=s=>{s=Math.max(0,Math.round(s));const m=Math.floor(s/60);return m?m+"хв "+(s%60)+"с":s+"с"};
const VCOL=["var(--up)","#eab308","#f97316","var(--down)"];
function drawChart(d,sx){
  const V=VS[sx];V.d=d;
  const n=V.cs,mode=V.cm;
  document.querySelectorAll("#ctabs"+sx+" button").forEach(b=>{b.className=b.dataset.s===n?"on":""});
  document.querySelectorAll("#cmode"+sx+" button").forEach(b=>{b.className=b.dataset.m===mode?"on":""});
  const box=E("chart",sx);
  const m=d.markets[n];
  if(!m||!m.series||m.series.length<2){box.innerHTML="<div style='color:var(--muted);font-size:.85rem'>Збираю дані…</div>";return}
  const WS=d.window||300,NC=Math.round(WS/60);
  const dec=n==="XRP"?4:2,ser=m.series,open=m.open,last=ser[ser.length-1][1];
  E("cpb",sx).textContent="$"+f(open,dec);
  const pn=E("cpn",sx);pn.textContent="$"+f(last,dec);pn.style.color=last>=open?"var(--up)":"var(--down)";
  const tw=E("ctw",sx);if(m.twap60!=null){tw.textContent="$"+f(m.twap60,dec);tw.style.color=m.twap60>=open?"var(--up)":"var(--down)"}else{tw.textContent="—"}
  E("cwin",sx).textContent=(d.time_left||0)+"s left";
  // 1-minute candles
  const cd=[];
  for(const p of ser){
    const k=Math.min(NC-1,Math.floor(p[0]/60));
    if(!cd[k])cd[k]={o:p[1],h:p[1],l:p[1],c:p[1]};
    else{const c=cd[k];c.h=Math.max(c.h,p[1]);c.l=Math.min(c.l,p[1]);c.c=p[1]}
  }
  const vals=mode==="c"?cd.filter(Boolean).flatMap(c=>[c.h,c.l]):ser.map(p=>p[1]);
  let lo=Math.min(open,...vals),hi=Math.max(open,...vals);
  let pad=(hi-lo)*0.2;if(!pad)pad=hi*0.0005;lo-=pad;hi+=pad;
  const W=340,H=200,L=4,R=60,T=10,B=20,PW=W-L-R;
  const X=t=>L+Math.min(t,WS)/WS*PW,Y=p=>T+(hi-p)/(hi-lo)*(H-T-B);
  let g="";
  for(let i=0;i<4;i++){
    const p=hi-(hi-lo)*i/3,y=Y(p);
    g+="<line x1='"+L+"' x2='"+(W-R)+"' y1='"+y+"' y2='"+y+"' stroke='#232326' stroke-width='1'/><text x='"+(W-R+4)+"' y='"+(y+3)+"' fill='#8a8a93' font-size='9'>"+f(p,dec)+"</text>";
  }
  for(let i=1;i<NC;i++){const xx=L+PW*i/NC;g+="<line x1='"+xx+"' x2='"+xx+"' y1='"+T+"' y2='"+(H-B)+"' stroke='#1a1a1d' stroke-width='1'/>"}
  const yo=Y(open),xc=X(d.confirm_at||0);
  g+="<line x1='"+L+"' x2='"+(W-R)+"' y1='"+yo+"' y2='"+yo+"' stroke='#8a8a93' stroke-width='1' stroke-dasharray='4 3'/>";
  g+="<text x='"+(W-R+4)+"' y='"+(yo-4)+"' fill='#e8e8ea' font-size='9'>open</text>";
  g+="<line x1='"+xc+"' x2='"+xc+"' y1='"+T+"' y2='"+(H-B)+"' stroke='#8b8bff' stroke-width='1' stroke-dasharray='2 3'/>";
  g+="<text x='"+(xc+3)+"' y='"+(H-B-4)+"' fill='#8b8bff' font-size='9'>conf</text>";
  if(mode==="c"){
    const cw=PW/NC*0.6;
    cd.forEach((c,i)=>{
      if(!c)return;
      const col=c.c>=c.o?"#22c55e":"#ef4444",xx=L+PW*(i+0.5)/NC;
      const yt=Math.min(Y(c.o),Y(c.c)),hh=Math.max(1.5,Math.abs(Y(c.o)-Y(c.c)));
      g+="<line x1='"+xx+"' x2='"+xx+"' y1='"+Y(c.h)+"' y2='"+Y(c.l)+"' stroke='"+col+"' stroke-width='1.5'/>";
      g+="<rect x='"+(xx-cw/2)+"' y='"+yt+"' width='"+cw+"' height='"+hh+"' fill='"+col+"' rx='1'/>";
    });
  }else{
    const col=last>=open?"#22c55e":"#ef4444";
    let path="";
    ser.forEach((p,i)=>{path+=(i?"L":"M")+X(p[0]).toFixed(1)+" "+Y(p[1]).toFixed(1)+" "});
    g+="<path d='"+path+"' fill='none' stroke='"+col+"' stroke-width='2' stroke-linejoin='round'/>";
    g+="<circle cx='"+X(ser[ser.length-1][0])+"' cy='"+Y(last)+"' r='3.5' fill='"+col+"'/>";
  }
  const step=NC>5?3:1;
  for(let i=0;i<=NC;i+=step){const xx=L+PW*i/NC;g+="<text x='"+(xx-(i?8:0))+"' y='"+(H-4)+"' fill='#8a8a93' font-size='9'>"+i+":00</text>"}
  box.innerHTML="<svg viewBox='0 0 "+W+" "+H+"' width='100%' style='display:block'>"+g+"</svg>";
}
function drawVol(d){
  const v=d.vol;if(!v)return;
  const now=Math.floor(new Date(d.server_time).getTime()/1000);
  let h="",nAct=0,maxL=0,warm=0;
  for(const n of S){
    const c=v.coins[n];if(!c)continue;
    let st,sub="";
    if(c.warm){
      warm++;
      st="<span class='bs bw'>збираю дані</span>";
      sub="потрібно ~10 хв історії тіків, щоб знати, що для цієї монети «норма»";
    }else{
      const col=VCOL[c.level];
      st="<span class='bs' style='background:rgba(255,255,255,.06);color:"+col+"'>"+(c.level?"⚡ ":"")+escH(c.label)+" ×"+f(c.ratio,1)+"</span>";
      sub="зараз "+f(c.now_bps,1)+" bps за "+v.short_sec+" с · норма "+f(c.typ_bps,1)+" · розмах "+f(c.range_bps,1);
      if(c.active&&c.since){
        nAct++;maxL=Math.max(maxL,c.level,1);
        sub="<b style='color:"+VCOL[Math.max(1,c.level)]+"'>Триває з "+hms(c.since)+" ("+fdur(now-c.since)+"), пік ×"+f(c.peak_ratio,1)+" ("+escH(c.peak_label)+")</b><br>"+sub;
      }
    }
    h+="<div class='wrow'><div style='display:flex;justify-content:space-between;align-items:center'><b>"+n+"</b>"+st+"</div><div class='sub'>"+sub+"</div></div>";
  }
  document.getElementById("vol").innerHTML=h;
  document.getElementById("volt").textContent=nAct?("⚡ зараз: "+nAct):(warm===S.length?"збираю дані":"спокійно");
  let eh="";
  for(const e of (v.events||[]).slice(0,10)){
    const col=VCOL[Math.max(1,e.peak_level)];
    eh+="<div class='wrow' style='padding:6px 0'><b>"+escH(e.symbol)+"</b> · "+hms(e.start)+" → "+(e.active?"<b style='color:"+col+"'>триває</b>":hms(e.end))+" ("+fdur(e.dur)+") · <span style='color:"+col+"'>пік ×"+f(e.peak_ratio,1)+"</span><div class='sub'>розмах "+f(e.range_bps,1)+" bps · рух від старту "+(e.move_bps>=0?"+":"")+f(e.move_bps,1)+" bps</div></div>";
  }
  document.getElementById("volh").innerHTML=eh||"<div style='color:var(--muted)'>Поки не було</div>";
  document.getElementById("volnote").innerHTML="<b>×N</b> = наскільки різкіше ціна рухається за останні "+v.short_sec+" с порівняно зі звичайним рівнем цієї монети (медіана за останню годину; ×1 = норма). Період починається, коли ≥×"+v.on+" тримається кілька секунд, і закінчується, коли &lt;×"+v.off+" тримається ~30 с. Рівні: помірна ≥×"+v.on+", висока ≥×"+v.high+", екстремальна ≥×"+v.extreme+". Під час такої волатильності ціна ринку може швидко йти до крайніх значень і розвертатись. Це лише індикація: на сигнали та угоди вона не впливає.";
  // the single icon: colour = strongest level among the coins, badge = how many coins are volatile right now
  const fab=document.getElementById("vfab"),vn=document.getElementById("vfn");
  fab.className="vfab"+(nAct?" l"+maxL+" act":"");
  vn.style.display=nAct?"flex":"none";vn.textContent=nAct;
}
function render(d,sx){
  drawChart(d,sx);
  if(sx===""){
    drawVol(d);
    const badge=document.getElementById("badge");
    if(d.error){badge.textContent=d.error;badge.className="badge"}
    else{badge.textContent="live · "+(d.seconds_passed||0)+"s";badge.className="badge ok"}
  }
  E("tmr",sx).textContent=(d.time_left||0)+"s left · conf@"+d.confirm_at+"s"+(sx&&d.error?" · "+d.error:"");
  let top="";
  for(const n of S){
    const m=d.markets[n];
    if(!m||m.status==="waiting"){top+=`<div class="ac"><div class="an">${n}</div><div class="ap">—</div></div>`;continue}
    const c=m.lead_bps>=0?"pos":"neg";
    top+=`<div class="ac"><div class="an">${n} · ${m.source||""}</div><div class="ap">$${f(m.current,n==="XRP"?4:2)}</div><div class="ach ${c}">${m.lead_bps>=0?"+":""}${m.lead_bps} bps</div></div>`;
  }
  E("top",sx).innerHTML=top;
  let body="",anyFlip=false;
  const now=Math.floor(new Date(d.server_time).getTime()/1000);
  for(const n of S){
    const m=d.markets[n];
    if(!m||m.status==="waiting"){body+=`<div class="mrow"><div>${n}</div><div>—</div><div>—</div><div class="bs bw">…</div></div>`;continue}
    let sh=`<span class="bs bw">очікування</span>`;
    if(m.stale){
      sh=`<span class="bs bw" title="Chainlink не оновлюється, чекаю на перепідключення">нема даних</span>`;
    }else if(m.signal_sent&&m.signal){
      const s=m.signal.side;
      const sc=m.signal.score?` ${m.signal.score}/3`:"";
      const cf=m.signal.mode==="early"?"ранній":(m.signal.confidence*100).toFixed(0)+"%";
      sh=`<span class="bs ${s==="UP"?"bu":"bd"}">${s==="UP"?"ВГОРУ":"ВНИЗ"} ${cf}${sc}${m.signal.model_p!=null?` · P${Math.round(m.signal.model_p*100)}`:""}</span>`;
    }else if(d.seconds_passed>=d.confirm_at&&m.live_side){
      sh=`<span class="bs bw">${m.live_side} ~${(m.live_confidence*100).toFixed(0)}%${m.model_p_up!=null?` · P${Math.round((m.live_side==="UP"?m.model_p_up:1-m.model_p_up)*100)}`:""}</span>`;
    }else if(d.seconds_passed>=d.confirm_at&&m.live_reason){
      const rs=m.live_reason,rt=rs==="too_small_lead"?"малий відрив":rs.startsWith("jury_")?"журі "+rs.slice(5):rs;
      sh=`<span class="bs bw" title="чому немає сигналу">${rt}</span>`;
    }else if(m.early&&m.early.side){
      sh=`<span class="bs bw" title="ранній прогноз, низька впевненість">ранній ${m.early.side==="UP"?"↑":"↓"}</span>`;
    }
    body+=`<div class="mrow"><div style="font-weight:600">${n}</div><div>${f(m.open,n==="XRP"?4:2)}</div><div>${f(m.current,n==="XRP"?4:2)}</div><div>${sh}</div></div>`;
    const fl=m.flip;
    if(fl&&!m.stale){
      const dir=fl.leader==="UP"?"ВНИЗ":"ВГОРУ",dec=n==="XRP"?4:2;
      let t="";
      if(fl.signal_side&&fl.signal_side!==fl.leader)t+=`<b class="neg">Ціна вже по інший бік від open — прогноз зараз програє.</b> `;
      if(fl.samples){
        const none=fl.hits===0;
        t+=`Щоб вікно закрилось ${dir}, ціні треба пройти ${fl.cushion_bps} bps ($${f(fl.cushion_usd,dec)}) за ${fl.horizon} с. За останні ${fl.span_min} хв такий хід за такий час був у <b class="${none?"pos":"neg"}">${fl.hits} з ${fl.samples}</b> інтервалів${none?" — не траплялось":""}.`;
      }else{
        t+=`Щоб вікно закрилось ${dir}, ціні треба пройти ${fl.cushion_bps} bps ($${f(fl.cushion_usd,dec)}) за ${fl.horizon} с. Історії тіків ще замало для підрахунку (бот працює ~${fl.span_min} хв).`;
      }
      body+=`<div style="font-size:.74rem;color:var(--muted);line-height:1.4;margin:-2px 0 8px;padding:0 4px">${n}: ${t}</div>`;
      anyFlip=true;
    }
  }
  if(anyFlip)body+=`<div style="font-size:.68rem;color:var(--muted);margin-top:4px">Це підрахунок фактичних тіків Chainlink, які записав бот, а не прогноз: розворот можливий, поки вікно не закрилось.</div>`;
  const es=d.early_stats||{wins:0,losses:0},et=es.wins+es.losses;
  body+=`<div style="font-size:.74rem;color:var(--muted);margin-top:10px;line-height:1.4">Ранній прогноз (одразу на старті вікна, низька впевненість, окрема статистика): <b>${es.wins}</b> / <b>${es.losses}</b>${et?` · ${(es.wins/et*100).toFixed(0)}%`:""}</div>`;
  E("mkt",sx).innerHTML=body;
  const st=d.stats||{};
  if(st.win_rate!=null){
    E("stats",sx).innerHTML=`<span>Сигналів: <b>${st.signals||0}</b></span><span>Вирішено: <b>${st.resolved||0}</b></span><span>Win: <b class="pos">${st.wins||0}</b></span><span>Loss: <b class="neg">${st.losses||0}</b></span><span>WR: <b>${st.win_rate}%</b></span>`;
  }
  const tm=d.timing||[];
  const tel=E("timing",sx);
  if(tel)tel.innerHTML=tm.length?("<b>Коли видано сигнал</b> (останні сигнали): "+tm.map(x=>x.label+": "+(x.n?`<b>${x.wins}/${x.n}</b>`:"—")+(x.avg_mkt!=null?` · ринок ~${Math.round(x.avg_mkt*100)}¢`:"")).join(" · ")):"";
  const h=d.history||[];
  if(h.length){
    let x="";
    for(const e of h){
      const t=e.time?new Date(e.time).toLocaleTimeString():"—";
      const res=e.result==="win"?"✓":e.result==="loss"?"✗":"";
      const rc=e.result==="win"?"pos":e.result==="loss"?"neg":"";
      const sc=e.score?` ${e.score}/3`:"";
      const mv=e.move==null?null:e.move;
      x+=`<div class="hrow"><div>${t}</div><div>${e.symbol||"—"}</div><div style="color:${e.side==="UP"?"var(--up)":"var(--down)"}">${e.side==="UP"?"↑":"↓"}</div><div>${e.mode==="early"?"ранній":(e.confidence*100).toFixed(0)+"%"+sc}${e.mkt_price!=null?` <span style="color:var(--muted)">${Math.round(e.mkt_price*100)}¢</span>`:""}</div><div class="${mv==null?"":mv>=0?"pos":"neg"}">${mv==null?"…":(mv>=0?"+":"-")+Math.abs(mv).toFixed(e.symbol==='XRP'?4:2)} <span class="${rc}">${res}</span></div></div>`;
    }
    E("hist",sx).innerHTML=x;
  }
}
async function loadCal(sx){
  sx=sx||"";const V=VS[sx];
  try{
    const d=await(await fetch("/api/calib?tf="+V.tf)).json();
    document.querySelectorAll("#calThr"+sx+" button").forEach(b=>{b.className=b.dataset.t===V.thr?"on":""});
    E("calN",sx).textContent="записано "+d.total;
    const rows=(d.rows&&d.rows[V.thr])||[];
    let h="<div style='display:grid;grid-template-columns:.9fr .8fr .9fr .9fr 1fr;gap:4px;color:var(--muted);font-size:.68rem;margin:6px 0 2px'><div>Секунда</div><div>Випадків</div><div>WR</div><div>Ціна</div><div>PnL/акцію</div></div>";
    for(const r of rows){
      const few=r.n<30,col=few?"var(--muted)":"inherit";
      const pc=r.pnl==null?"var(--muted)":(few?"var(--muted)":(r.pnl>0?"var(--up)":"var(--down)"));
      h+="<div style='display:grid;grid-template-columns:.9fr .8fr .9fr .9fr 1fr;gap:4px;padding:3px 0;border-top:1px solid #1f1f22;color:"+col+"'><div>"+r.cp+"с</div><div>"+r.n+"</div><div>"+(r.wr==null?"—":r.wr.toFixed(0)+"%")+"</div><div>"+(r.ask==null?"—":r.ask.toFixed(0)+"¢")+"</div><div style='color:"+pc+"'>"+(r.pnl==null?"—":(r.pnl>0?"+":"")+r.pnl.toFixed(1)+"¢")+"</div></div>";
    }
    if(!d.total)h+="<div style='color:var(--muted);margin-top:6px'>Збираю дані: перші результати через одне вікно, надійні висновки після доби роботи.</div>";
    E("calBody",sx).innerHTML=h;
  }catch(e){}
}
async function refresh(sx){
  sx=(typeof sx==="string")?sx:"";
  try{render(await(await fetch("/api/status?tf="+VS[sx].tf)).json(),sx)}
  catch(e){if(sx==="")document.getElementById("badge").textContent="offline"}
}
document.getElementById("vfab").onclick=()=>document.getElementById("vpop").classList.add("open");
document.getElementById("vclose").onclick=()=>document.getElementById("vpop").classList.remove("open");
document.getElementById("vpop").onclick=e=>{if(e.target.id==="vpop")e.target.classList.remove("open")};
for(const sx of ["","15"]){
  E("ctabs",sx).onclick=function(e){const s=e.target.dataset&&e.target.dataset.s;if(s){VS[sx].cs=s;if(VS[sx].d)drawChart(VS[sx].d,sx)}};
  E("cmode",sx).onclick=function(e){const s=e.target.dataset&&e.target.dataset.m;if(s){VS[sx].cm=s;if(VS[sx].d)drawChart(VS[sx].d,sx)}};
  E("calThr",sx).onclick=function(e){const t=e.target.dataset&&e.target.dataset.t;if(t!==undefined&&t!==""){VS[sx].thr=t;loadCal(sx)}};
}
(function(){
  let sym='BTC',sub='feed',tper='day',timer=null,data=null;
  const esc=x=>String(x).replace(/[&<>]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;'}[c]));
  const short=a=>a?a.slice(0,6)+'…'+a.slice(-4):'—';
  const usd=x=>'$'+Math.abs(x).toLocaleString('en-US',{maximumFractionDigits:0});
  const tm=ts=>ts?new Date(ts*1000).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit',second:'2-digit'}):'';
  function who(w){
    const link='https://polymarket.com/profile/'+esc(w.wallet);
    return "<a href='"+link+"' target='_blank' rel='noopener'>"+(w.name?esc(w.name)+' · ':'')+short(w.wallet)+"</a>";
  }
  function tradeRow(t){
    const c=t.outcome==='Up'?'var(--up)':'var(--down)';
    return "<div class='wrow'>"+who(t)+"<div class='sub'>"+(t.side==='BUY'?'купив':'продав')+" <span style='color:"+c+"'>"+esc(t.outcome)+"</span> · "+usd(t.usd)+" @ "+Math.round(t.price*100)+"¢ · "+tm(t.ts)+"</div></div>";
  }
  function draw(){
    document.querySelectorAll('#wtabs button').forEach(x=>{x.className=x.dataset.s===sym?'on':''});
    document.querySelectorAll('#wsub button').forEach(x=>{x.className=x.dataset.t===sub?'on':''});
    const b=document.getElementById('wbody'),sm=document.getElementById('wsum');
    if(!data){b.innerHTML='Завантаження…';return}
    if(!data.ok){sm.innerHTML='';b.innerHTML=esc(data.error||'Помилка');return}
    const up=data.totals.Up,dn=data.totals.Down,tot=up+dn||1;
    sm.innerHTML="<div style='display:flex;justify-content:space-between;font-size:.85rem'><span style='color:var(--up)'>Up "+usd(up)+"</span><span style='color:var(--down)'>Down "+usd(dn)+"</span></div><div class='vbar'><div style='width:"+(up/tot*100)+"%;background:#22c55e'></div><div style='flex:1;background:#ef4444'></div></div><div style='font-size:.72rem;color:var(--muted)'>Завантажено угод: "+(data.count||0)+" (куплено, у $)</div>";
    let x='';
    if(sub==='top'){
      for(const w of data.wallets){
        x+="<div class='wrow'>"+who(w)+"<div class='sub'>Купив: <span style='color:var(--up)'>Up "+usd(w.bUp)+"</span> · <span style='color:var(--down)'>Down "+usd(w.bDown)+"</span></div><div class='sub'>Продав: <span style='color:var(--up)'>Up "+usd(w.sUp)+"</span> · <span style='color:var(--down)'>Down "+usd(w.sDown)+"</span> · угод: "+w.n+" · "+tm(w.last)+"</div></div>";
      }
    }else{
      const list=data.trades.filter(t=>sub==='feed'||(sub==='buy'&&t.side==='BUY')||(sub==='sell'&&t.side==='SELL')||(sub==='up'&&t.outcome==='Up')||(sub==='down'&&t.outcome==='Down'));
      for(const t of list)x+=tradeRow(t);
    }
    b.innerHTML=x||"<div style='color:var(--muted)'>Поки порожньо</div>";
  }
  async function load(){
    try{
      const r=await fetch('/api/trades?symbol='+sym);
      data=await r.json();
    }catch(e){data={ok:false,error:'Не вдалося завантажити'}}
    draw();
  }
  let ttimer=null;
  async function loadT(){
    clearTimeout(ttimer);
    document.querySelectorAll('#ttabs button').forEach(x=>{x.className=x.dataset.p===tper?'on':''});
    const b=document.getElementById('tbody');
    try{
      const r=await fetch('/api/top?period='+tper);
      const d=await r.json();
      if(!d.ok){b.innerHTML=esc(d.error||'Помилка');return}
      let x='';
      for(const w of d.rows){
        const c=w.pnl>=0?'var(--up)':'var(--down)';
        x+="<div class='wrow'><div style='display:flex;justify-content:space-between;align-items:center'><span><span style='color:var(--muted)'>#"+w.rank+"</span> "+who(w)+"</span><b style='color:"+c+"'>"+(w.pnl>=0?'+':'-')+usd(w.pnl)+"</b></div></div>";
      }
      b.innerHTML=x||'Поки порожньо';
    }catch(e){b.innerHTML='Не вдалося завантажити'}
  }
  let pinit=false,pen=false,pcoins={},pdepSrv=0,pw=0,ctimer=null;
  const money=x=>(x<0?'-':'')+'$'+Math.abs(x).toLocaleString('en-US',{minimumFractionDigits:2,maximumFractionDigits:2});
  function drawCfg(){
    const e=document.getElementById('pen');e.textContent=pen?'УВІМК':'ВИМК';e.className='pbtn'+(pen?' on':'');
    document.querySelectorAll('#pcoins button').forEach(b=>{b.className=pcoins[b.dataset.c]?'on':''});
  }
  function fillCfg(c){
    pen=c.enabled;pcoins=Object.assign({},c.coins);pdepSrv=c.deposit;
    document.getElementById('pname').value=c.name||'';
    document.getElementById('pmode').value=c.stake_mode;
    document.getElementById('pval').value=c.stake_value;
    document.getElementById('pdep').value=c.deposit;
    document.getElementById('pedge').value=c.min_edge;
    document.getElementById('pminp').value=c.min_price;
    document.getElementById('pmaxp').value=c.max_price;
    drawCfg();
  }
  function drawAcc(d){
    const a=d.account,c=a.pnl>=0?'var(--up)':'var(--down)';
    document.getElementById('pacc').innerHTML="<div class='pgrid'><div><small>Баланс (вільний)</small><b>"+money(a.balance)+"</b></div><div><small>Разом з відкритими</small><b>"+money(a.equity)+"</b></div><div><small>Прибуток</small><b style='color:"+c+"'>"+(a.pnl>=0?'+':'')+money(a.pnl)+" ("+a.pnl_pct.toFixed(1)+"%)</b></div><div><small>Win rate</small><b>"+a.winrate.toFixed(0)+"% ("+a.wins+"/"+(a.wins+a.losses)+")</b></div></div>";
    const cv=d.curve;
    if(cv.length>1){
      const lo=Math.min(...cv),hi=Math.max(...cv),W=320,H=64,sp=(hi-lo)||1;
      const pts=cv.map((v,i)=>(i/(cv.length-1)*W).toFixed(1)+','+(H-4-(v-lo)/sp*(H-8)).toFixed(1)).join(' ');
      const col=cv[cv.length-1]>=cv[0]?'#22c55e':'#ef4444';
      document.getElementById('pspark').innerHTML="<svg viewBox='0 0 "+W+" "+H+"' width='100%' style='display:block'><polyline points='"+pts+"' fill='none' stroke='"+col+"' stroke-width='2'/></svg>";
    }else document.getElementById('pspark').innerHTML="<div style='font-size:.78rem;color:var(--muted)'>Графік з'явиться після перших закритих угод</div>";
    let x='';
    for(const t of d.trades){
      const sc=t.side==='UP'?'var(--up)':'var(--down)';
      let st;
      if(t.status==='open')st="<span style='color:var(--muted)'>очікує…</span>";
      else if(t.status==='void')st="<span style='color:var(--muted)'>скасовано</span>";
      else if(t.status==='skip')st="<span style='color:var(--muted)'>пропущено</span>";
      else st="<b style='color:"+(t.pnl>=0?'var(--up)':'var(--down)')+"'>"+(t.status==='win'?'✓ ':'✕ ')+(t.pnl>=0?'+':'')+money(t.pnl)+"</b>";
      const tmm=new Date(t.ts*1000).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});
      if(t.status==='skip'){
        x+="<div class='wrow'><div style='display:flex;justify-content:space-between'><span>"+t.symbol+" <span style='color:"+sc+"'>"+t.side+"</span></span>"+st+"</div><div class='sub'>"+new Date(t.ts*1000).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'})+" · "+(t.reason||'')+"</div></div>";
        continue;
      }
      x+="<div class='wrow'><div style='display:flex;justify-content:space-between'><span>"+t.symbol+" <span style='color:"+sc+"'>"+t.side+"</span></span>"+st+"</div><div class='sub'>"+tmm+" · вхід "+Math.round(t.entry*100)+"¢ · ставка "+money(t.cost)+" · комісія "+money(t.fee)+(t.model_p!=null?" · модель "+Math.round(t.model_p*100)+"%":"")+(t.edge!=null?" · edge "+(t.edge>=0?'+':'')+t.edge+"%":"")+"</div></div>";
    }
    document.getElementById('plist').innerHTML=x||"<div style='color:var(--muted);font-size:.85rem'>Ще немає угод. Бот відкриє віртуальну угоду на наступному сигналі.</div>";
  }
  function drawL(d){
    const el=document.getElementById('lpan');
    let h="<div class='pt'><span>⚠️ Реальна торгівля (live)</span></div>";
    if(d.missing&&d.missing.length){
      h+="<div style='font-size:.78rem;color:var(--muted);line-height:1.5'>Вимкнено на сервері. Щоб підключити, додай у Render → Environment: <b>"+d.missing.map(esc).join(', ')+"</b></div>";
    }else{
      h+="<div class='prow' style='justify-content:space-between'><span>Реальні ставки</span><button class='pbtn"+(d.armed?" on":"")+"' id='larm'>"+(d.armed?"УВІМК":"ВИМК")+"</button></div>";
      h+="<div style='font-size:.75rem;color:var(--muted);line-height:1.5'>Акаунт "+esc(d.wallet_short)+" · ставка $"+d.stake+" · ліміт збитку за день $"+d.daily_loss_limit+" · сьогодні "+(d.day_pnl>=0?'+':'')+"$"+d.day_pnl+" (оцінка) · відкрито "+d.open+"/"+d.max_open+"<br>Повторює угоди Гаманця 1 (його фільтри теж діють)"+(d.allow_early?", у тому числі за ранніми сигналами":", крім ранніх сигналів")+". Після кожного перезапуску сервера треба вмикати знову.</div>";
    }
    if(d.disarm_reason&&!d.armed)h+="<div style='font-size:.78rem;color:var(--down);margin-top:6px'>Вимкнено: "+esc(d.disarm_reason)+"</div>";
    if(d.last_error)h+="<div style='font-size:.78rem;color:var(--down);margin-top:6px'>"+esc(d.last_error)+"</div>";
    let x='';
    for(const t of d.trades||[]){
      const sc=t.side==='UP'?'var(--up)':'var(--down)';
      const tm=new Date(t.ts*1000).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});
      let st;
      if(t.status==='open')st="<span style='color:var(--muted)'>очікує…</span>";
      else if(t.status==='win'||t.status==='loss')st="<b style='color:"+(t.pnl>=0?'var(--up)':'var(--down)')+"'>"+(t.status==='win'?'✓ ':'✕ ')+(t.pnl>=0?'+':'')+"$"+t.pnl.toFixed(2)+"</b>";
      else if(t.status==='failed')st="<b style='color:var(--down)'>помилка</b>";
      else if(t.status==='unknown')st="<b style='color:var(--down)'>перевір акаунт!</b>";
      else st="<span style='color:var(--muted)'>"+(t.status==='skip'?'пропущено':t.status)+"</span>";
      const sub=t.reason||t.msg||(t.stake?("ставка $"+t.stake.toFixed(2)+(t.est_entry?" · ~"+Math.round(t.est_entry*100)+"¢":"")):"");
      x+="<div class='wrow'><div style='display:flex;justify-content:space-between'><span>"+esc(t.symbol)+" <span style='color:"+sc+"'>"+t.side+"</span></span>"+st+"</div><div class='sub'>"+tm+" · "+esc(sub)+"</div></div>";
    }
    if(x)h+="<div style='margin-top:10px'>"+x+"</div>";
    el.innerHTML=h;
    const b=document.getElementById('larm');
    if(b)b.onclick=()=>armL(!d.armed);
  }
  async function armL(on){
    if(on&&!confirm('Увімкнути РЕАЛЬНІ ставки? Бот сам купуватиме на гроші з твого акаунта Polymarket. Максимальний збиток обмежений лімітом за день, але ринок може піти проти тебе.'))return;
    try{
      const r=await fetch('/api/live/arm',{method:'POST',headers:{'Content-Type':'application/json','X-Requested-With':'signals'},body:JSON.stringify({armed:on})});
      drawL(await r.json());
    }catch(e){}
  }
  async function loadL(){
    try{drawL(await (await fetch('/api/live')).json())}catch(e){}
  }
  function drawWT(ws){
    if(!ws)return;
    let h='';
    ws.forEach((w,i)=>{
      const c=w.pnl>=0?'var(--up)':'var(--down)';
      h+="<button data-w='"+i+"' class='"+(i===pw?'on':'')+"'><span style='color:"+(w.enabled?'var(--up)':'var(--muted)')+"'>●</span> "+esc(w.name)+"<br><small style='color:"+c+"'>"+(w.pnl>=0?'+':'-')+'$'+Math.abs(w.pnl).toFixed(2)+(w.open?' · '+w.open+' відкр.':'')+"</small></button>";
    });
    document.getElementById('pwtabs').innerHTML=h;
  }
  async function loadP(){
    document.getElementById('lpan').style.display=pw===0?'':'none';   // real money mirrors wallet 1 only
    if(pw===0)loadL();
    try{
      const d=await (await fetch('/api/paper?w='+pw)).json();
      if(d.w!==pw)return;
      drawWT(d.wallets);
      if(!pinit){fillCfg(d.config);pinit=true}
      drawAcc(d);
    }catch(e){}
  }
  async function postP(url,body){
    body.w=pw;
    const r=await fetch(url,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
    return r.json();
  }
  document.getElementById('pwtabs').onclick=e=>{
    const b=e.target.closest&&e.target.closest('button');
    if(b&&b.dataset.w!==undefined){pw=+b.dataset.w;pinit=false;document.getElementById('plist').innerHTML='';document.getElementById('pacc').innerHTML='';loadP()}
  };
  async function saveCfg(explicit){
    const body={enabled:pen,coins:pcoins};
    if(explicit){
      body.name=document.getElementById('pname').value;
      body.stake_mode=document.getElementById('pmode').value;
      body.stake_value=parseFloat(document.getElementById('pval').value);
      body.min_edge=parseFloat(document.getElementById('pedge').value)||0;
      body.min_price=parseFloat(document.getElementById('pminp').value)||0;
      body.max_price=parseFloat(document.getElementById('pmaxp').value)||99;
      const dep=parseFloat(document.getElementById('pdep').value);
      if(dep>0&&Math.abs(dep-pdepSrv)>1e-9){
        if(!confirm('Депозит змінено на '+money(dep)+'. Скинути рахунок і стерти історію віртуальних угод?')){document.getElementById('pdep').value=pdepSrv;return}
        body.deposit=dep;
      }
    }
    const d=await postP('/api/paper/config',body);
    if(d.w!==pw)return;
    if(explicit)fillCfg(d.config);else{pdepSrv=d.config.deposit;drawCfg()}
    drawWT(d.wallets);
    drawAcc(d);
    if(explicit){const m=document.getElementById('pmsg');m.textContent='Збережено ✓';setTimeout(()=>{m.textContent=''},1800)}
  }
  document.getElementById('pen').onclick=()=>{pen=!pen;drawCfg();saveCfg(false)};
  document.getElementById('pcoins').onclick=e=>{const c=e.target.dataset&&e.target.dataset.c;if(c){pcoins[c]=!pcoins[c];drawCfg();saveCfg(false)}};
  document.getElementById('psave').onclick=()=>saveCfg(true);
  document.getElementById('preset').onclick=async()=>{
    if(!confirm('Скинути віртуальний рахунок і стерти історію угод?'))return;
    const d=await postP('/api/paper/reset',{deposit:parseFloat(document.getElementById('pdep').value)});
    if(d.w!==pw)return;
    fillCfg(d.config);drawWT(d.wallets);drawAcc(d);
  };
  let csym='BTC',cbuilt='';
  const TVS={BTC:'BITSTAMP:BTCUSD',ETH:'BITSTAMP:ETHUSD',SOL:'BITSTAMP:SOLUSD',XRP:'BITSTAMP:XRPUSD'};
  function loadChart(){
    document.querySelectorAll('#ktabs button').forEach(x=>{x.className=x.dataset.s===csym?'on':''});
    if(cbuilt===csym)return;
    cbuilt=csym;
    const box=document.getElementById('tvbox');
    box.innerHTML='<div class="tradingview-widget-container" style="height:100%;width:100%"><div class="tradingview-widget-container__widget" style="height:100%;width:100%"></div></div>';
    const s=document.createElement('script');
    s.src='https://s3.tradingview.com/external-embedding/embed-widget-advanced-chart.js';
    s.async=true;
    let tz='Etc/UTC';try{tz=Intl.DateTimeFormat().resolvedOptions().timeZone||tz}catch(e){}
    s.text=JSON.stringify({autosize:true,symbol:TVS[csym],interval:'5',timezone:tz,theme:'dark',style:'1',locale:'uk',
      backgroundColor:'#0b0b0c',gridColor:'rgba(255,255,255,0.06)',hide_side_toolbar:true,allow_symbol_change:false,
      save_image:false,calendar:false,details:false,hotlist:false,withdateranges:false,support_host:'https://www.tradingview.com'});
    box.firstChild.appendChild(s);
  }
  function show(v){
    document.getElementById('sheet').classList.toggle('open',v==='wal');
    document.getElementById('vtop').classList.toggle('open',v==='top');
    document.getElementById('vpap').classList.toggle('open',v==='pap');
    document.getElementById('vchart').classList.toggle('open',v==='chart');
    document.getElementById('v15').classList.toggle('open',v==='t15');
    document.getElementById('nv6').className=v==='t15'?'on':'';
    document.getElementById('nv1').className=v==='main'?'on':'';
    document.getElementById('nv2').className=v==='wal'?'on':'';
    document.getElementById('nv3').className=v==='top'?'on':'';
    document.getElementById('nv4').className=v==='pap'?'on':'';
    document.getElementById('nv5').className=v==='chart'?'on':'';
    clearInterval(timer);clearTimeout(ttimer);clearInterval(ctimer);
    if(v==='wal'){data=null;draw();load();timer=setInterval(load,5000)}
    else if(v==='top'){loadT();timer=setInterval(loadT,60000)}
    else if(v==='pap'){loadP();timer=setInterval(loadP,4000)}
    else if(v==='chart'){loadChart()}
    else if(v==='t15'){refresh('15');loadCal('15');timer=setInterval(()=>refresh('15'),2000);ctimer=setInterval(()=>loadCal('15'),30000)}
    else window.scrollTo(0,0);
  }
  document.getElementById('nv1').onclick=()=>show('main');
  document.getElementById('nv2').onclick=()=>show('wal');
  document.getElementById('nv3').onclick=()=>show('top');
  document.getElementById('nv4').onclick=()=>show('pap');
  document.getElementById('nv5').onclick=()=>show('chart');
  document.getElementById('nv6').onclick=()=>show('t15');
  document.getElementById('ktabs').onclick=e=>{const s=e.target.dataset&&e.target.dataset.s;if(s){csym=s;loadChart()}};
  document.getElementById('wtabs').onclick=e=>{const s=e.target.dataset&&e.target.dataset.s;if(s){sym=s;data=null;draw();load()}};
  document.getElementById('wsub').onclick=e=>{const t=e.target.dataset&&e.target.dataset.t;if(t){sub=t;draw()}};
  document.getElementById('ttabs').onclick=e=>{const p=e.target.dataset&&e.target.dataset.p;if(p){tper=p;loadT()}};
})();
refresh();setInterval(refresh,2000);
loadCal();setInterval(loadCal,30000);
</script>
</body>
</html>"""


_PANELS = r"""<div class="top" id="top@@"></div>
<div class="panel">
  <div class="pt"><span>Ринки</span><span id="tmr@@"></span></div>
  <div class="mrow h"><div>Актив</div><div>Open</div><div>Now</div><div>Сигнал</div></div>
  <div id="mkt@@"></div>
</div>
<div class="panel">
  <div class="pt"><span>Графік @T@ (Chainlink / Polymarket)</span><span id="cwin@@"></span></div>
  <div class="ctabs" id="ctabs@@"><button data-s="BTC">BTC</button><button data-s="ETH">ETH</button><button data-s="SOL">SOL</button><button data-s="XRP">XRP</button></div>
  <div class="ctabs" id="cmode@@"><button data-m="c">Свічки 1хв</button><button data-m="l">Лінія</button></div>
  <div class="cnums"><div><small>Price to beat</small><b id="cpb@@">—</b></div><div><small>Поточна ціна</small><b id="cpn@@">—</b></div><div><small>TWAP 60с</small><b id="ctw@@">—</b></div></div>
  <div id="chart@@"></div>
</div>
<div class="panel">
  <div class="pt"><span>Історія</span><span id="st@@"></span></div>
  <div class="stats" id="stats@@"></div>
  <div class="hrow" style="color:var(--muted);font-size:.65rem"><div>Час</div><div>Акт</div><div>Стор</div><div>Conf</div><div>Lead</div></div>
  <div id="timing@@" style="font-size:.74rem;color:var(--muted);line-height:1.5;margin:6px 0 8px"></div>
  <div id="hist@@"></div>
</div>
<div class="panel">
  <div class="pt"><span>Де є реальна перевага</span><span id="calN@@"></span></div>
  <div class="ctabs" id="calThr@@"><button data-t="0">всі</button><button data-t="3">≥3 bps</button><button data-t="6">≥6 bps</button><button data-t="10">≥10 bps</button></div>
  <div id="calBody@@" style="font-size:.78rem"></div>
  <div style="font-size:.68rem;color:var(--muted);line-height:1.45;margin-top:8px">Рядок = секунда вікна. <b>WR</b> = як часто сторона, що вела на той момент, справді виграла вікно. <b>Ціна</b> = середня ціна покупки цієї сторони на Polymarket. <b>PnL</b> = середній реальний результат однієї акції після комісії (у центах). Це підрахунок записаних фактів, не прогноз. Надійно, коли в рядку ≥30 випадків.</div>
</div>
"""
HTML_PAGE = (HTML_PAGE.replace("<!--P5-->", _PANELS.replace("@@", "").replace("@T@", "5m"))
             .replace("<!--P15-->", _PANELS.replace("@@", "15").replace("@T@", "15m")))


async def dashboard(request):
    return HTMLResponse(HTML_PAGE)


async def on_startup():
    spawn(supervise("rtds", rtds_loop))
    spawn(supervise("price", lambda: price_loop(TF5)))
    if ENABLE_15M:
        spawn(supervise("price15", lambda: price_loop(TF15)))
    spawn(keepalive_loop())
    logger.info("RTDS + price loops started")


_cid_cache: Dict[str, tuple] = {}
_trades_cache: Dict[str, tuple] = {}
MAX_TRADE_PAGES = 4


async def api_trades(request):
    """Who is trading the current 5m market on Polymarket (public data: wallets, sizes)."""
    sym = (request.query_params.get("symbol") or "BTC").upper()
    if sym not in ("BTC", "ETH", "SOL", "XRP"):
        sym = "BTC"
    now = int(datetime.now(timezone.utc).timestamp())
    start = now - now % WINDOW_SECONDS
    slug = f"{sym.lower()}-updown-5m-{start}"

    cached = _trades_cache.get(slug)
    if cached and now - cached[0] < 4:
        return JSONResponse(cached[1])

    def g(t, *keys, default=None):
        for k in keys:
            if k in t and t[k] is not None:
                return t[k]
        return default

    def to_ts(v):
        if v is None:
            return 0
        try:
            x = int(float(v))
        except Exception:
            try:
                return int(datetime.fromisoformat(str(v).replace("Z", "+00:00")).timestamp())
            except Exception:
                return 0
        return x // 1000 if x > 10**11 else x

    def as_list(v):
        if isinstance(v, str):
            try:
                v = json.loads(v)
            except Exception:
                return []
        return v if isinstance(v, list) else []

    raw: list = []
    try:
        async with httpx.AsyncClient(timeout=8.0) as c:
            meta = _cid_cache.get(slug)
            if not meta:
                r = await c.get("https://gamma-api.polymarket.com/events", params={"slug": slug})
                data = r.json()
                ev = data[0] if isinstance(data, list) and data else None
                mk = (ev or {}).get("markets") or []
                if mk:
                    m0 = mk[0]
                    tokens = as_list(m0.get("clobTokenIds"))
                    outs = as_list(m0.get("outcomes"))
                    tmap = {str(t): str(o) for t, o in zip(tokens, outs)}
                    meta = (m0.get("conditionId"), tmap)
                    if meta[0]:
                        _cid_cache[slug] = meta
            if not meta or not meta[0]:
                return JSONResponse({"ok": False, "error": "Ринок ще не знайдено, спробуй за кілька секунд", "slug": slug})
            cid, tmap = meta

            # first page (try a few param variants), then follow the cursor
            body = None
            last_err = ""
            for params in (
                {"condition": cid, "limit": 500, "taker_only": "false"},
                {"condition": cid, "limit": 200, "taker_only": "false"},
                {"condition": cid, "taker_only": "false"},
                {"condition": cid},
            ):
                r = await c.get("https://data-api.polymarket.com/v2/trades", params=params)
                try:
                    b = r.json()
                except Exception:
                    b = None
                if r.status_code == 200 and b is not None:
                    body = b
                    break
                last_err = f"{r.status_code} {str(b)[:150]}"
                logger.warning(f"data-api v2/trades {params}: {last_err}")
            if body is None:
                return JSONResponse({"ok": False, "error": f"Polymarket: {last_err}", "slug": slug})

            pages = 0
            while True:
                rows = body.get("data") if isinstance(body, dict) else body
                if isinstance(rows, list):
                    raw.extend(rows)
                pages += 1
                pg = (body.get("pagination") or {}) if isinstance(body, dict) else {}
                cur = pg.get("next_cursor")
                if not cur or pages >= MAX_TRADE_PAGES or pg.get("has_more") is False:
                    break
                r = await c.get("https://data-api.polymarket.com/v2/trades", params={"condition": cid, "cursor": cur})
                if r.status_code != 200:
                    break
                try:
                    body = r.json()
                except Exception:
                    break
    except Exception as e:
        logger.warning(f"api_trades error: {e}")
        if not raw:
            return JSONResponse({"ok": False, "error": "Не вдалося отримати дані з Polymarket", "slug": slug})

    trades = []
    wallets: Dict[str, dict] = {}
    totals = {"Up": 0.0, "Down": 0.0}
    seen = set()
    for t in raw:
        if not isinstance(t, dict):
            continue
        try:
            addr = g(t, "proxy_wallet", "proxyWallet", "wallet", default="")
            side = str(g(t, "side", default="")).upper()
            size = float(g(t, "size", default=0))
            price = float(g(t, "price", default=0))
            ts = to_ts(g(t, "timestamp", "created_at", "createdAt"))
        except Exception:
            continue
        outcome = g(t, "outcome", default="")
        if outcome not in ("Up", "Down"):
            tok = str(g(t, "token_id", "asset", "assetId", "asset_id", default=""))
            outcome = tmap.get(tok, outcome)
        if outcome not in ("Up", "Down"):
            idx = g(t, "outcome_index", "outcomeIndex")
            if idx in (0, 1, "0", "1"):
                outcome = "Up" if int(idx) == 0 else "Down"
        txh = g(t, "transaction_hash", "transactionHash", default="")
        key = (txh, addr, side, outcome, size, price, ts) if txh else None
        if key is not None:
            if key in seen:
                continue
            seen.add(key)
        usd = size * price
        name = g(t, "name", "pseudonym", default="")
        trades.append({"wallet": addr, "name": name, "side": side, "outcome": outcome,
                       "usd": round(usd, 2), "price": round(price, 3), "ts": ts})
        if outcome in totals and side == "BUY":
            totals[outcome] += usd
        w = wallets.setdefault(addr, {"wallet": addr, "name": name, "bUp": 0.0, "bDown": 0.0,
                                      "sUp": 0.0, "sDown": 0.0, "n": 0, "last": 0})
        if outcome in ("Up", "Down"):
            w[("b" if side == "BUY" else "s") + outcome] += usd
        w["n"] += 1
        w["last"] = max(w["last"], ts)

    trades.sort(key=lambda x: x["ts"], reverse=True)
    top = sorted(wallets.values(), key=lambda w: w["bUp"] + w["bDown"] + w["sUp"] + w["sDown"], reverse=True)[:40]
    for w in top:
        for k in ("bUp", "bDown", "sUp", "sDown"):
            w[k] = round(w[k], 2)

    payload = {
        "ok": True,
        "symbol": sym,
        "slug": slug,
        "window_start": start,
        "count": len(trades),
        "totals": {"Up": round(totals["Up"], 2), "Down": round(totals["Down"], 2)},
        "wallets": top,
        "trades": trades[:500],
    }
    _trades_cache[slug] = (now, payload)
    if len(_trades_cache) > 40:
        for k in sorted(_trades_cache, key=lambda k: _trades_cache[k][0])[:20]:
            _trades_cache.pop(k, None)
    return JSONResponse(payload)


_top_cache: Dict[str, tuple] = {}


async def api_top(request):
    """Best traders by profit (Polymarket leaderboard, crypto category)."""
    period = (request.query_params.get("period") or "day").lower()
    if period not in ("day", "week", "month"):
        period = "day"
    now = int(datetime.now(timezone.utc).timestamp())
    cached = _top_cache.get(period)
    if cached and now - cached[0] < 60:
        return JSONResponse(cached[1])

    def g(t, *keys, default=None):
        for k in keys:
            if k in t and t[k] is not None:
                return t[k]
        return default

    attempts = [
        ("https://data-api.polymarket.com/v2/leaderboard",
         {"time_period": period, "category": "crypto", "sort_by": "PNL", "limit": 25}),
        ("https://data-api.polymarket.com/v1/leaderboard",
         {"timePeriod": period.upper(), "category": "CRYPTO", "orderBy": "PNL", "limit": 25}),
    ]
    rows = None
    last_err = ""
    try:
        async with httpx.AsyncClient(timeout=8.0) as c:
            for url, params in attempts:
                r = await c.get(url, params=params)
                try:
                    body = r.json()
                except Exception:
                    body = None
                if r.status_code == 200 and body is not None:
                    data = body.get("data") if isinstance(body, dict) else body
                    if isinstance(data, dict):
                        data = next((v for v in data.values() if isinstance(v, list)), [])
                    if isinstance(data, list):
                        rows = data
                        break
                last_err = f"{r.status_code} {str(body)[:150]}"
                logger.warning(f"leaderboard {url}: {last_err}")
    except Exception as e:
        logger.warning(f"api_top error: {e}")
        return JSONResponse({"ok": False, "error": "Не вдалося отримати дані з Polymarket"})
    if rows is None:
        return JSONResponse({"ok": False, "error": f"Polymarket: {last_err}"})

    out = []
    for i, t in enumerate(rows):
        if not isinstance(t, dict):
            continue
        try:
            pnl = float(g(t, "pnl", "profit", default=0))
        except Exception:
            pnl = 0.0
        out.append({
            "rank": g(t, "rank", default=i + 1),
            "wallet": g(t, "user_id", "proxy_wallet", "proxyWallet", "address", "wallet", default=""),
            "name": g(t, "user_name", "userName", "name", "pseudonym", default=""),
            "pnl": round(pnl, 2),
        })
    payload = {"ok": True, "period": period, "rows": out}
    _top_cache[period] = (now, payload)
    return JSONResponse(payload)


def _wallet_idx(v) -> int:
    try:
        return max(0, min(PAPER_N - 1, int(v)))
    except (TypeError, ValueError):
        return 0


def _wallet_summary(w: dict) -> dict:
    closed = [t for t in w["trades"] if t["status"] in ("win", "loss")]
    return {"name": w["name"], "enabled": w["enabled"], "pnl": round(sum(t["pnl"] for t in closed), 2),
            "open": sum(1 for t in w["trades"] if t["status"] == "open")}


async def _paper_payload(idx: int = 0):
    w = wallets[idx]
    trades = w["trades"]
    closed = [t for t in trades if t["status"] in ("win", "loss")]
    wins = sum(1 for t in closed if t["status"] == "win")
    losses = len(closed) - wins
    open_trades = [t for t in trades if t["status"] == "open"]
    open_cost = sum(t["cost"] + t["fee"] for t in open_trades)
    pnl = sum(t["pnl"] for t in closed)
    curve = [round(w["deposit"], 2)]
    run = w["deposit"]
    for t in sorted([t for t in trades if t["status"] in ("win", "loss", "void") and t["settled_at"]],
                    key=lambda t: (t["settled_at"], t["id"])):
        run += t["pnl"]
        curve.append(round(run, 2))
    return {
        "w": idx,
        "wallets": [_wallet_summary(x) for x in wallets],
        "config": {
            "name": w["name"],
            "enabled": w["enabled"],
            "coins": w["coins"],
            "stake_mode": w["stake_mode"],
            "stake_value": w["stake_value"],
            "min_edge": w["min_edge"],
            "min_price": w["min_price"],
            "max_price": w["max_price"],
            "deposit": w["deposit"],
        },
        "account": {
            "balance": round(w["balance"], 2),
            "equity": round(w["balance"] + open_cost, 2),
            "pnl": round(pnl, 2),
            "pnl_pct": round(pnl / w["deposit"] * 100, 2) if w["deposit"] else 0.0,
            "wins": wins,
            "losses": losses,
            "open": len(open_trades),
            "winrate": round(wins / len(closed) * 100, 1) if closed else 0.0,
        },
        "curve": curve[-200:],
        "trades": trades[:100],
    }


async def api_paper(request):
    return JSONResponse(await _paper_payload(_wallet_idx(request.query_params.get("w"))))


async def api_paper_config(request):
    try:
        b = await request.json()
    except Exception:
        b = {}
    idx = _wallet_idx(b.get("w"))
    w = wallets[idx]
    if "name" in b:
        nm = str(b["name"] or "").strip()[:24]
        if nm:
            w["name"] = nm
    if "enabled" in b:
        w["enabled"] = bool(b["enabled"])
    coins = b.get("coins")
    if isinstance(coins, dict):
        for c in PAPER_COINS:
            if c in coins:
                w["coins"][c] = bool(coins[c])
    mode = b.get("stake_mode")
    if mode in ("pct", "usd", "kelly"):
        w["stake_mode"] = mode
    try:
        v = float(b.get("stake_value"))
        if w["stake_mode"] in ("pct", "kelly"):
            v = max(0.1, min(100.0, v))
        else:
            v = max(1.0, min(1e7, v))
        w["stake_value"] = round(v, 2)
    except (TypeError, ValueError):
        pass
    for key, lo, hi, cast in (("min_edge", 0.0, 50.0, float), ("min_price", 0, 99, int), ("max_price", 1, 99, int)):
        if key in b:
            try:
                w[key] = cast(max(lo, min(hi, float(b[key]))))
            except (TypeError, ValueError):
                pass
    if w["min_price"] > w["max_price"]:
        w["min_price"] = 0
    if "deposit" in b:
        try:
            dep = float(b["deposit"])
            if abs(dep - w["deposit"]) > 1e-9:
                _paper_reset(w, dep)
        except (TypeError, ValueError):
            pass
    paper_save()
    return JSONResponse(await _paper_payload(idx))


def _paper_reset(w: dict, dep: float):
    dep = max(1.0, min(1e9, dep))
    w["deposit"] = round(dep, 2)
    w["balance"] = round(dep, 2)
    w["trades"] = []
    paper_save()


async def api_paper_reset(request):
    idx = 0
    try:
        b = await request.json()
        idx = _wallet_idx(b.get("w"))
        dep = float(b.get("deposit"))
    except Exception:
        return JSONResponse(await _paper_payload(idx))
    _paper_reset(wallets[idx], dep)
    return JSONResponse(await _paper_payload(idx))


class PasswordMiddleware(BaseHTTPMiddleware):
    """Password for the dashboard (browser login window). Off if DASHBOARD_PASSWORD is not set."""
    async def dispatch(self, request, call_next):
        if not DASHBOARD_PASSWORD or request.url.path == "/health":
            return await call_next(request)
        auth = request.headers.get("authorization", "")
        if auth.startswith("Basic "):
            try:
                decoded = base64.b64decode(auth[6:]).decode("utf-8")
                pwd = decoded.split(":", 1)[1] if ":" in decoded else ""
                if secrets.compare_digest(pwd.encode(), DASHBOARD_PASSWORD.encode()):
                    return await call_next(request)
            except Exception:
                pass
        return Response("Unauthorized", status_code=401,
                        headers={"WWW-Authenticate": 'Basic realm="Signals"'})


app = Starlette(
    routes=[
        Route("/", dashboard),
        Route("/api/status", api_status),
        Route("/api/trades", api_trades),
        Route("/api/top", api_top),
        Route("/api/paper", api_paper),
        Route("/api/paper/config", api_paper_config, methods=["POST"]),
        Route("/api/paper/reset", api_paper_reset, methods=["POST"]),
        Route("/api/live", api_live),
        Route("/api/calib", api_calib),
        Route("/api/live/arm", api_live_arm, methods=["POST"]),
        Route("/health", health),
    ],
    on_startup=[on_startup],
    middleware=[Middleware(PasswordMiddleware)],
)
