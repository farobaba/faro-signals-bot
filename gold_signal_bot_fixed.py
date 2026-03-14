"""
====================================================
  @FaroSignal_bot — ULTIMATE VERSION
  RSI + MA + MACD + SMC + Price Action
  Multi-Timeframe | Risk Calculator | Performance
  Economic Calendar | Daily Summary | Dashboard
  Trailing Stop | Real Forex Prices
====================================================

Requirements (add to requirements.txt):
  python-telegram-bot>=20.0
  pandas
  numpy
  requests
  ta
  ccxt
  pytz
  matplotlib
====================================================
"""

import logging
import ccxt
import pandas as pd
import numpy as np
import requests
import ta
import tempfile, os
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes
from datetime import datetime, timezone, timedelta
import pytz

# ============================================================
#   CONFIGURATION
# ============================================================

TELEGRAM_TOKEN     = "8369749647:AAGxrU79EQojd-lAEw5b73TbcTMZUwR-SHQ"
CHAT_ID            = "6533190483"
TWELVE_DATA_KEY    = "b7fad4cbdcf9493ab7944a06ae002e0d"  # Twelve Data key 1
TWELVE_DATA_KEY_2  = "145ad17fa12b4251b26711e70f73dfaf"                       # Twelve Data key 2 (register free)
ALPHA_VANTAGE_KEY  = "65X604SALOA865O0"                         # Alpha Vantage fallback

# Key rotation state
_td_key_index = 0

def _td_key():
    keys = [TWELVE_DATA_KEY, TWELVE_DATA_KEY_2]
    return keys[_td_key_index % 2]

def _td_rotate():
    global _td_key_index
    _td_key_index += 1
    logger.warning(f"🔄 Rotated to TD key {(_td_key_index % 2) + 1}")

# Cache for API responses
_cache = {}
CACHE_TTL = {"1m":60,"5m":180,"15m":600,"30m":900,"1h":1800,"4h":3600,"1d":86400}

def _get_cache(key, interval):
    entry = _cache.get(f"{key}_{interval}")
    if not entry: return None
    df, ts = entry
    if time.time() - ts < CACHE_TTL.get(interval, 900):
        return df
    return None

def _set_cache(key, interval, df):
    _cache[f"{key}_{interval}"] = (df, time.time())

SYMBOLS = {
    # Forex
    "XAU/USD":   {"display": "XAUUSD",  "type": "forex",  "sl": 15,   "source": "twelvedata", "td_symbol": "XAU/USD",   "binance": None},
    # Crypto — Top performers
    "BTC/USDT":  {"display": "BTCUSD",  "type": "crypto", "sl": 300,  "source": "binance",    "td_symbol": "BTC/USD",   "binance": "BTC/USDT"},
    "ETH/USDT":  {"display": "ETHUSD",  "type": "crypto", "sl": 20,   "source": "binance",    "td_symbol": "ETH/USD",   "binance": "ETH/USDT"},
    "SOL/USDT":  {"display": "SOLUSDT", "type": "crypto", "sl": 5,    "source": "binance",    "td_symbol": "SOL/USD",   "binance": "SOL/USDT"},
    "BNB/USDT":  {"display": "BNBUSDT", "type": "crypto", "sl": 8,    "source": "binance",    "td_symbol": "BNB/USD",   "binance": "BNB/USDT"},
    "XRP/USDT":  {"display": "XRPUSDT", "type": "crypto", "sl": 0.05, "source": "binance",    "td_symbol": "XRP/USD",   "binance": "XRP/USDT"},
    "DOGE/USDT": {"display": "DOGEUSDT","type": "crypto", "sl": 0.02, "source": "binance",    "td_symbol": "DOGE/USD",  "binance": "DOGE/USDT"},
    "AVAX/USDT": {"display": "AVAXUSDT","type": "crypto", "sl": 2,    "source": "binance",    "td_symbol": "AVAX/USD",  "binance": "AVAX/USDT"},
    "LINK/USDT": {"display": "LINKUSDT","type": "crypto", "sl": 0.5,  "source": "binance",    "td_symbol": "LINK/USD",  "binance": "LINK/USDT"},
}

# Multi-Timeframe settings
TIMEFRAMES = {
    "30m": {"interval": "30m",  "period": "5d",  "label": "30 Min",  "weight": 1},
    "1h":  {"interval": "60m",  "period": "7d",  "label": "1 Hour",  "weight": 2},
    "4h":  {"interval": "1h",   "period": "30d", "label": "4 Hour",  "weight": 3},
}
PRIMARY_TF        = "30m"
MTF_AGREEMENT     = 2        # Min timeframes that must agree

RISK_REWARD       = 2.0
MIN_CONFIRMATIONS = 3
CHECK_INTERVAL    = 1800

RSI_PERIOD         = 14
RSI_OVERSOLD       = 30
RSI_OVERBOUGHT     = 70
MA_SHORT           = 9
MA_LONG            = 21
MACD_FAST          = 12
MACD_SLOW          = 26
MACD_SIGNAL_PERIOD = 9

OB_LOOKBACK        = 20
FVG_THRESHOLD      = 0.001
STRUCTURE_LOOKBACK = 10
SR_LOOKBACK        = 30
SR_ZONE_PCT        = 0.002

NEWS_BLACKOUT_TIMES = [
    (7,  45,  8, 30),
    (13,  0, 14,  0),
    (18, 45, 19, 30),
]

# Daily summary time (UTC)
DAILY_SUMMARY_HOUR   = 7
DAILY_SUMMARY_MINUTE = 0

# Trailing stop trigger — when TP is X% reached, suggest moving SL
TRAILING_TRIGGER_PCT  = 0.5    # 50% to TP → suggest trailing stop
BREAKEVEN_TRIGGER_PCT = 1.0    # 100% of SL distance in profit → move to breakeven
SIGNAL_EXPIRY_CANDLES = 2      # Signal expires after this many candles
REENTRY_BUFFER_PCT    = 0.003  # 0.3% pullback = re-entry zone

# ============================================================
#   IN-MEMORY STORAGE
# ============================================================

signal_history   = []

# ── User-entered trades (manual trade tracking) ───────────────
user_active_trades  = []   # Active monitored trades
pending_signals     = {}   # Short ID → full signal data (for callback_data size limit)
pending_signal_seq  = 0    # Auto-increment ID
open_trades      = []
performance      = {
    "total": 0, "wins": 0, "losses": 0, "pending": 0,
    "total_pips": 0, "best_signal": None, "worst_signal": None
}

SCAN_MODES = {
    "5m":  {"interval": "5m",  "period": "1d",  "label": "5 Minutes",  "seconds": 300,   "emoji": "⚡"},
    "15m": {"interval": "15m", "period": "2d",  "label": "15 Minutes", "seconds": 900,   "emoji": "🔥"},
    "30m": {"interval": "30m", "period": "5d",  "label": "30 Minutes", "seconds": 1800,  "emoji": "✅"},
    "1h":  {"interval": "60m", "period": "7d",  "label": "1 Hour",     "seconds": 3600,  "emoji": "🕐"},
    "4h":  {"interval": "1h",  "period": "30d", "label": "4 Hours",    "seconds": 14400, "emoji": "📊"},
    "1d":  {"interval": "1d",  "period": "60d", "label": "1 Day",      "seconds": 86400, "emoji": "🌙"},
}
active_scan = {"tf": "30m", "seconds": 1800, "job": None}

# Market mode — which assets to scan
MARKET_MODES = {
    "forex":  {"label": "Forex",   "emoji": "💱", "symbols": ["XAU/USD"]},
    "crypto": {"label": "Crypto",  "emoji": "🪙", "symbols": ["BTC/USDT","ETH/USDT","SOL/USDT","BNB/USDT","XRP/USDT","DOGE/USDT","AVAX/USDT","LINK/USDT"]},
    "all":    {"label": "All",     "emoji": "🌍", "symbols": ["XAU/USD","BTC/USDT","ETH/USDT","SOL/USDT","BNB/USDT","XRP/USDT","DOGE/USDT","AVAX/USDT","LINK/USDT"]},
    "binary": {"label": "Binary",  "emoji": "⚡", "symbols": []},  # Binary uses get_active_binary_symbols() — not this list
}

# ── Pocket Option Binary Settings ────────────────────────────
# ── All pairs shared by both brokers ─────────────────────────
# Pocket Option = regular pairs (weekdays)
# Quotex        = OTC versions only (always available)
BINARY_PAIRS = {
    # Key           display         td_symbol      po_pay  qx_pay
    "EUR/USD":  {"display": "EURUSD",  "td": "EUR/USD",  "po": 92, "qx": 90},
    "GBP/USD":  {"display": "GBPUSD",  "td": "GBP/USD",  "po": 88, "qx": 86},
    "USD/JPY":  {"display": "USDJPY",  "td": "USD/JPY",  "po": 88, "qx": 86},
    "USD/CAD":  {"display": "USDCAD",  "td": "USD/CAD",  "po": 85, "qx": 83},
    "AUD/USD":  {"display": "AUDUSD",  "td": "AUD/USD",  "po": 85, "qx": 83},
    "NZD/USD":  {"display": "NZDUSD",  "td": "NZD/USD",  "po": 85, "qx": 83},
    "EUR/JPY":  {"display": "EURJPY",  "td": "EUR/JPY",  "po": 85, "qx": 83},
    "GBP/AUD":  {"display": "GBPAUD",  "td": "GBP/AUD",  "po": 83, "qx": 81},
    "GBP/NZD":  {"display": "GBPNZD",  "td": "GBP/NZD",  "po": 83, "qx": 81},
    "EUR/CHF":  {"display": "EURCHF",  "td": "EUR/CHF",  "po": 82, "qx": 80},
    "EUR/CAD":  {"display": "EURCAD",  "td": "EUR/CAD",  "po": 82, "qx": 80},
    "EUR/AUD":  {"display": "EURAUD",  "td": "EUR/AUD",  "po": 82, "qx": 80},
    "NZD/CHF":  {"display": "NZDCHF",  "td": "NZD/CHF",  "po": 80, "qx": 78},
    "NZD/JPY":  {"display": "NZDJPY",  "td": "NZD/JPY",  "po": 80, "qx": 78},
    "GBP/CHF":  {"display": "GBPCHF",  "td": "GBP/CHF",  "po": 80, "qx": 78},
    "CAD/CHF":  {"display": "CADCHF",  "td": "CAD/CHF",  "po": 80, "qx": 78},
    "CHF/JPY":  {"display": "CHFJPY",  "td": "CHF/JPY",  "po": 80, "qx": 78},
    "USD/MXN":  {"display": "USDMXN",  "td": "USD/MXN",  "po": 88, "qx": 86},
    "USD/BDT":  {"display": "USDBDT",  "td": "USD/BDT",  "po": 85, "qx": 83},
    "USD/COP":  {"display": "USDCOP",  "td": "USD/COP",  "po": 85, "qx": 83},
    "USD/ARS":  {"display": "USDARS",  "td": "USD/ARS",  "po": 85, "qx": 83},
    "USD/PKR":  {"display": "USDPKR",  "td": "USD/PKR",  "po": 85, "qx": 83},
    "BRL/USD":  {"display": "BRLUSD",  "td": "BRL/USD",  "po": 88, "qx": 86},
}

# ── Build broker-specific symbol lists ────────────────────────
# Pocket Option = regular pairs + OTC pairs
# Quotex        = OTC pairs ONLY (all same assets)
POCKET_OPTION_SYMBOLS = {}
QUOTEX_SYMBOLS        = {}

# Top 10 pairs for auto/manual queue (reduces API calls)
TOP_BINARY_PAIRS = [
    "EUR/USD", "GBP/USD", "USD/JPY", "AUD/USD", "USD/CAD",
    "EUR/GBP", "GBP/JPY", "EUR/JPY", "USD/CHF", "NZD/USD",
]

for key, val in BINARY_PAIRS.items():
    # Regular pair — Pocket Option weekdays
    POCKET_OPTION_SYMBOLS[key] = {
        "display": val["display"],
        "td":      val.get("td"),
        "binance": val.get("binance"),
        "payout":  val["po"],
        "otc":     False,
        "broker":  "Pocket Option",
    }
    # OTC version — both brokers
    otc_key = key + "-OTC"
    otc_display = val["display"] + "-OTC"
    POCKET_OPTION_SYMBOLS[otc_key] = {
        "display": otc_display,
        "td":      val.get("td"),
        "binance": val.get("binance"),
        "payout":  min(val["po"] + 5, 98),  # OTC pays MORE — up to 98%
        "otc":     True,
        "broker":  "Pocket Option OTC",
    }
    QUOTEX_SYMBOLS[otc_key] = {
        "display": otc_display,
        "td":      val.get("td"),
        "binance": val.get("binance"),
        "payout":  val["qx"],
        "otc":     True,
        "broker":  "Quotex",
    }

# Legacy BINARY_SYMBOLS kept for compatibility
BINARY_SYMBOLS = POCKET_OPTION_SYMBOLS

# ── Broker config ─────────────────────────────────────────────
BROKERS = {
    "po_regular": {"label": "PO Regular", "emoji": "💰", "otc": False,  "broker": "Pocket Option"},
    "po_otc":     {"label": "PO OTC",     "emoji": "💎", "otc": True,   "broker": "Pocket Option"},
    "quotex":     {"label": "Quotex OTC", "emoji": "📊", "otc": True,   "broker": "Quotex"},
}
active_broker = "po_otc"   # Default to OTC — higher payouts

BINARY_EXPIRIES = {
    "1m":  {"label": "1 Minute",  "seconds": 60,   "emoji": "⚡", "candles": "1m",  "lookback": 30},
    "2m":  {"label": "2 Minutes", "seconds": 120,  "emoji": "🔥", "candles": "1m",  "lookback": 40},
    "5m":  {"label": "5 Minutes", "seconds": 300,  "emoji": "✅", "candles": "5m",  "lookback": 50},
    "15m": {"label": "15 Minutes","seconds": 900,  "emoji": "📊", "candles": "15m", "lookback": 50},
}

active_binary_expiry = "5m"    # Default expiry
binary_results       = []      # Track binary trade results
binary_performance   = {"total": 0, "wins": 0, "losses": 0, "pending": 0}
binary_asset_stats   = {}      # Per-asset: {display: {wins, losses, total}}
binary_streak        = {"current": 0, "type": None, "best_win": 0, "worst_loss": 0}
active_binary_trades = []      # Pending expiry checks

active_market = "all"   # Currently active market mode

# ── User timezone ─────────────────────────────────────────────
user_timezone  = "UTC"   # Default until user sets it
user_tz_object = pytz.utc

TIMEZONE_REGIONS = {
    "americas": {
        "label": "🌎 Americas",
        "zones": {
            "America/New_York":    "New York (EST/EDT)",
            "America/Chicago":     "Chicago (CST/CDT)",
            "America/Denver":      "Denver (MST/MDT)",
            "America/Los_Angeles": "Los Angeles (PST/PDT)",
            "America/Sao_Paulo":   "São Paulo (BRT)",
            "America/Mexico_City": "Mexico City (CST)",
        }
    },
    "europe": {
        "label": "🌍 Europe/Africa",
        "zones": {
            "Europe/London":   "London (GMT/BST)",
            "Europe/Paris":    "Paris (CET/CEST)",
            "Europe/Berlin":   "Berlin (CET/CEST)",
            "Africa/Lagos":    "Lagos (WAT)",
            "Africa/Nairobi":  "Nairobi (EAT)",
            "Africa/Cairo":    "Cairo (EET)",
        }
    },
    "asia": {
        "label": "🌏 Asia/Pacific",
        "zones": {
            "Asia/Dubai":      "Dubai (GST)",
            "Asia/Karachi":    "Karachi (PKT)",
            "Asia/Dhaka":      "Dhaka (BST)",
            "Asia/Kolkata":    "India (IST)",
            "Asia/Tokyo":      "Tokyo (JST)",
            "Asia/Singapore":  "Singapore (SGT)",
            "Australia/Sydney":"Sydney (AEST)",
        }
    },
}

# ── Symbol rotation queue ─────────────────────────────────────
# Instead of scanning all symbols at once, rotate one per interval
symbol_queue    = []   # Ordered list of symbols to scan
symbol_queue_idx = 0   # Current position in queue

# ============================================================
#   LOGGING
# ============================================================

logging.basicConfig(format="%(asctime)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)

# ============================================================
#   MARKET HOURS
# ============================================================

def get_utc_now():
    return datetime.now(timezone.utc)

def is_forex_open():
    now     = get_utc_now()
    weekday = now.weekday()
    hour    = now.hour
    if weekday == 5:
        return False, "Weekend — Forex closed Saturday"
    if weekday == 4 and hour >= 22:
        return False, "Forex closed — reopens Sunday 22:00 UTC"
    if weekday == 6 and hour < 22:
        return False, f"Forex closed — opens in ~{22 - hour}h (Sun 22:00 UTC)"
    return True, "Forex market is open"

def get_active_sessions():
    now     = get_utc_now()
    current = now.hour * 60 + now.minute
    active  = []
    ranges  = {
        "Sydney":   (22*60, 7*60 + 24*60),
        "Tokyo":    (0*60,  9*60),
        "London":   (8*60,  17*60),
        "New York": (13*60, 22*60),
    }
    for name, (start, end) in ranges.items():
        if start > end:
            if current >= start or current <= end % (24*60):
                active.append(name)
        else:
            if start <= current <= end:
                active.append(name)
    return active

def is_best_trading_time():
    now     = get_utc_now()
    current = now.hour * 60 + now.minute
    if 13*60 <= current <= 17*60:
        return True, "London + New York overlap"
    return False, None

def is_news_blackout():
    now     = get_utc_now()
    current = now.hour * 60 + now.minute
    for sh, sm, eh, em in NEWS_BLACKOUT_TIMES:
        if sh*60+sm <= current <= eh*60+em:
            return True, f"{sh:02d}:{sm:02d}—{eh:02d}:{em:02d} UTC"
    return False, None

# ============================================================
#   FETCH DATA
# ============================================================

# ── Binance exchange instance (for crypto) ───────────────────
binance_ex = ccxt.binance({"enableRateLimit": True})

def fetch_data_twelvedata(td_symbol: str, interval: str = "30min", outputsize: int = 100) -> pd.DataFrame:
    """Fetch OHLCV from Twelve Data — used for Gold (real Forex price)."""
    try:
        # Map our interval format to Twelve Data format
        interval_map = {
            "1m": "1min", "5m": "5min", "15m": "15min", "30m": "30min",
            "60m": "1h",  "1h": "1h",   "4h":  "4h",    "1d": "1day"
        }
        td_interval = interval_map.get(interval, "30min")

        url    = "https://api.twelvedata.com/time_series"
        params = {
            "symbol":     td_symbol,
            "interval":   td_interval,
            "outputsize": outputsize,
            "apikey":     TWELVE_DATA_KEY,
            "format":     "JSON",
        }
        r    = requests.get(url, params=params, timeout=15)
        data = r.json()

        if "values" not in data:
            msg = data.get("message", "Unknown error")
            logger.error(f"Twelve Data error for {td_symbol}: {msg}")
            # Rate limit hit — wait briefly and retry once
            if "rate limit" in msg.lower() or "429" in str(msg):
                import time; time.sleep(12)
                r2   = requests.get(url, params=params, timeout=15)
                data = r2.json()
                if "values" not in data:
                    return None
            else:
                return None

        rows = []
        for v in reversed(data["values"]):   # oldest first
            rows.append({
                "open":   float(v["open"]),
                "high":   float(v["high"]),
                "low":    float(v["low"]),
                "close":  float(v["close"]),
                # Gold/Forex from TD often has volume=0 — use 1 as placeholder
                # so volume_ratio = 1.0 (neutral, won't block signal)
                "volume": float(v.get("volume", 1)) or 1.0,
            })

        df = pd.DataFrame(rows)
        logger.info(f"✅ Twelve Data: {len(df)} candles for {td_symbol}")
        return df

    except Exception as e:
        logger.error(f"Twelve Data fetch error {td_symbol}: {e}")
        return None


def fetch_data_binance(binance_symbol: str, interval: str = "30m", limit: int = 100) -> pd.DataFrame:
    """Fetch OHLCV from Binance — used for BTC and ETH."""
    try:
        interval_map = {
            "5m": "5m", "15m": "15m", "30m": "30m",
            "60m": "1h", "1h": "1h",  "4h": "4h",  "1d": "1d"
        }
        bi_interval = interval_map.get(interval, "30m")
        ohlcv = binance_ex.fetch_ohlcv(binance_symbol, bi_interval, limit=limit)
        df    = pd.DataFrame(ohlcv, columns=["timestamp", "open", "high", "low", "close", "volume"])
        df    = df[["open", "high", "low", "close", "volume"]].copy()
        logger.info(f"✅ Binance: {len(df)} candles for {binance_symbol}")
        return df
    except Exception as e:
        logger.error(f"Binance fetch error {binance_symbol}: {e}")
        return None


def fetch_data(symbol: str, interval: str = "30m", period: str = "5d") -> pd.DataFrame:
    """Route data fetching: crypto → Binance, forex/gold → TD → Alpha Vantage."""
    info = SYMBOLS.get(symbol)
    if not info:
        return None

    if info["source"] == "twelvedata":
        df = fetch_data_twelvedata(info["td_symbol"], interval=interval)
        if df is None or len(df) < 10:
            logger.warning(f"TD failed for {symbol} — trying Alpha Vantage")
            df = fetch_data_alpha_vantage(info["td_symbol"], interval=interval)
        return df
    else:
        return fetch_data_binance(info["binance"], interval=interval)


def get_current_price_td(td_symbol: str):
    """Get current price from Twelve Data for any pair."""
    try:
        url    = "https://api.twelvedata.com/price"
        params = {"symbol": td_symbol, "apikey": TWELVE_DATA_KEY}
        r      = requests.get(url, params=params, timeout=10)
        data   = r.json()
        if "price" not in data:
            return None
        price = float(data["price"])
        url2    = "https://api.twelvedata.com/quote"
        params2 = {"symbol": td_symbol, "apikey": TWELVE_DATA_KEY}
        r2      = requests.get(url2, params=params2, timeout=10)
        data2   = r2.json()
        change  = float(data2.get("percent_change", 0))
        return {"price": price, "change": change,
                "high": float(data2.get("high", price)),
                "low":  float(data2.get("low", price))}
    except Exception as e:
        logger.error(f"TD price error {td_symbol}: {e}")
        return None


def get_current_price(symbol: str):
    """Get current price — Twelve Data for Gold, Binance for crypto."""
    info = SYMBOLS.get(symbol)
    if not info:
        return None

    try:
        if info["source"] == "twelvedata":
            # Twelve Data real-time price
            url    = "https://api.twelvedata.com/price"
            params = {"symbol": info["td_symbol"], "apikey": TWELVE_DATA_KEY}
            r      = requests.get(url, params=params, timeout=10)
            data   = r.json()
            if "price" not in data:
                logger.error(f"Twelve Data price error: {data}")
                return None
            price = float(data["price"])

            # Get 24h change from quote endpoint
            url2    = "https://api.twelvedata.com/quote"
            params2 = {"symbol": info["td_symbol"], "apikey": TWELVE_DATA_KEY}
            r2      = requests.get(url2, params=params2, timeout=10)
            data2   = r2.json()
            change  = float(data2.get("percent_change", 0))
            high    = float(data2.get("high", price))
            low     = float(data2.get("low",  price))

            logger.info(f"✅ Twelve Data price for {info['display']}: {price}")
            return {"price": price, "change": change, "high": high, "low": low}

        else:
            # Binance real-time price
            ticker = binance_ex.fetch_ticker(info["binance"])
            return {
                "price":  ticker["last"],
                "change": ticker["percentage"],
                "high":   ticker["high"],
                "low":    ticker["low"],
            }

    except Exception as e:
        logger.error(f"Price error {symbol}: {e}")
        return None

# ============================================================
#   ECONOMIC CALENDAR
# ============================================================

def get_upcoming_news() -> list:
    """
    Returns upcoming high-impact news events.
    Uses a scheduled list of known recurring high-impact events.
    """
    now     = get_utc_now()
    weekday = now.weekday()   # 0=Mon
    events  = []

    # Weekly recurring high-impact events (approximate UTC times)
    weekly_events = [
        {"day": 4, "hour": 13, "minute": 30, "name": "Non-Farm Payrolls (NFP)",     "impact": "🔴 VERY HIGH",  "frequency": "First Friday"},
        {"day": 4, "hour": 13, "minute": 30, "name": "US Unemployment Rate",        "impact": "🔴 VERY HIGH",  "frequency": "Monthly"},
        {"day": 2, "hour": 13, "minute": 30, "name": "US CPI Inflation",            "impact": "🔴 VERY HIGH",  "frequency": "Monthly"},
        {"day": 3, "hour": 19, "minute": 0,  "name": "FOMC Interest Rate Decision", "impact": "🔴 VERY HIGH",  "frequency": "Every 6 weeks"},
        {"day": 1, "hour": 9,  "minute": 30, "name": "UK GDP Data",                 "impact": "🟠 HIGH",       "frequency": "Monthly"},
        {"day": 0, "hour": 9,  "minute": 0,  "name": "German Manufacturing PMI",    "impact": "🟠 HIGH",       "frequency": "Monthly"},
        {"day": 4, "hour": 13, "minute": 30, "name": "US Retail Sales",             "impact": "🟠 HIGH",       "frequency": "Monthly"},
        {"day": 2, "hour": 14, "minute": 30, "name": "US PPI Data",                 "impact": "🟡 MEDIUM",     "frequency": "Monthly"},
        {"day": 3, "hour": 13, "minute": 30, "name": "US GDP Preliminary",          "impact": "🟠 HIGH",       "frequency": "Quarterly"},
    ]

    # Find events in next 24 hours
    for event in weekly_events:
        event_time = now.replace(hour=event["hour"], minute=event["minute"], second=0, microsecond=0)
        # Check if event is today or tomorrow
        days_ahead = (event["day"] - weekday) % 7
        event_date = now + timedelta(days=days_ahead)
        event_dt   = event_date.replace(hour=event["hour"], minute=event["minute"], second=0, microsecond=0)

        minutes_until = (event_dt - now).total_seconds() / 60

        if 0 < minutes_until <= 1440:   # Within next 24 hours
            events.append({
                "name":         event["name"],
                "impact":       event["impact"],
                "time":         event_dt.strftime("%a %H:%M UTC"),
                "minutes_away": int(minutes_until),
                "frequency":    event["frequency"],
            })

    events.sort(key=lambda x: x["minutes_away"])
    return events[:5]   # Return next 5 events

def check_imminent_news() -> tuple:
    """Check if high-impact news is within 30 minutes."""
    events = get_upcoming_news()
    for event in events:
        if event["minutes_away"] <= 30 and "VERY HIGH" in event["impact"]:
            return True, event
    return False, None

# ============================================================
#   STANDARD INDICATORS
# ============================================================

def calculate_indicators(df: pd.DataFrame) -> pd.DataFrame:
    df["rsi"]      = ta.momentum.RSIIndicator(df["close"], window=RSI_PERIOD).rsi()
    df["ma_short"] = ta.trend.SMAIndicator(df["close"], window=MA_SHORT).sma_indicator()
    df["ma_long"]  = ta.trend.SMAIndicator(df["close"], window=MA_LONG).sma_indicator()
    df["ema_fast"] = ta.trend.EMAIndicator(df["close"], window=8).ema_indicator()
    df["ema_slow"] = ta.trend.EMAIndicator(df["close"], window=21).ema_indicator()
    df["ema_200"]  = ta.trend.EMAIndicator(df["close"], window=50).ema_indicator()

    macd = ta.trend.MACD(df["close"], window_fast=MACD_FAST, window_slow=MACD_SLOW, window_sign=MACD_SIGNAL_PERIOD)
    df["macd"]        = macd.macd()
    df["macd_signal"] = macd.macd_signal()
    df["macd_hist"]   = macd.macd_diff()

    df["atr"]        = ta.volatility.AverageTrueRange(df["high"], df["low"], df["close"], window=14).average_true_range()
    df["volume_ma"]  = df["volume"].rolling(20).mean()
    df["body"]       = abs(df["close"] - df["open"])
    df["candle_ma"]  = df["body"].rolling(20).mean()
    df["upper_wick"] = df["high"] - df[["open", "close"]].max(axis=1)
    df["lower_wick"] = df[["open", "close"]].min(axis=1) - df["low"]

    # Bollinger Bands
    bb = ta.volatility.BollingerBands(df["close"], window=20, window_dev=2)
    df["bb_upper"] = bb.bollinger_hband()
    df["bb_lower"] = bb.bollinger_lband()
    df["bb_mid"]   = bb.bollinger_mavg()
    df["bb_width"] = (df["bb_upper"] - df["bb_lower"]) / df["bb_mid"]
    df["bb_pct"]   = bb.bollinger_pband()   # 0=lower band, 1=upper band

    # ADX — market regime detection
    adx_ind        = ta.trend.ADXIndicator(df["high"], df["low"], df["close"], window=14)
    df["adx"]      = adx_ind.adx()
    df["adx_pos"]  = adx_ind.adx_pos()   # +DI
    df["adx_neg"]  = adx_ind.adx_neg()   # -DI

    # Volume ratio vs 20-period average
    df["volume_ratio"] = df["volume"] / df["volume_ma"].replace(0, 1)

    return df

# ============================================================
#   MULTI-TIMEFRAME ANALYSIS
# ============================================================

def analyze_timeframe(symbol: str, tf_key: str) -> dict:
    """Analyze a single timeframe and return its bias."""
    tf     = TIMEFRAMES[tf_key]
    df     = fetch_data(symbol, interval=tf["interval"])
    result = {"tf": tf["label"], "bias": "NEUTRAL", "rsi": 50, "trend": "NEUTRAL", "reasons": []}

    if df is None or len(df) < 30:
        return result

    df  = calculate_indicators(df)
    latest = df.iloc[-1]
    prev   = df.iloc[-2]

    buy_votes  = 0
    sell_votes = 0

    rsi = latest["rsi"]
    result["rsi"] = round(rsi, 1)

    if rsi < RSI_OVERSOLD:
        buy_votes += 1; result["reasons"].append(f"RSI {rsi:.0f} oversold")
    elif rsi > RSI_OVERBOUGHT:
        sell_votes += 1; result["reasons"].append(f"RSI {rsi:.0f} overbought")

    if latest["ma_short"] > latest["ma_long"]:
        buy_votes += 1; result["reasons"].append("MA bullish")
    else:
        sell_votes += 1; result["reasons"].append("MA bearish")

    if latest["ema_fast"] > latest["ema_slow"]:
        buy_votes += 1; result["reasons"].append("EMA bullish")
    else:
        sell_votes += 1; result["reasons"].append("EMA bearish")

    if latest["macd"] > latest["macd_signal"]:
        buy_votes += 1; result["reasons"].append("MACD bullish")
    else:
        sell_votes += 1; result["reasons"].append("MACD bearish")

    if latest["close"] > latest["ema_200"]:
        buy_votes += 1; result["reasons"].append("Above EMA50")
    else:
        sell_votes += 1; result["reasons"].append("Below EMA50")

    if buy_votes > sell_votes:
        result["bias"]  = "BUY"
        result["trend"] = "BULLISH"
    elif sell_votes > buy_votes:
        result["bias"]  = "SELL"
        result["trend"] = "BEARISH"

    return result

def multi_timeframe_analysis(symbol: str) -> dict:
    """Run analysis across all timeframes and check alignment."""
    results   = {}
    buy_count = 0
    sell_count = 0

    for tf_key in TIMEFRAMES:
        r = analyze_timeframe(symbol, tf_key)
        results[tf_key] = r
        if r["bias"] == "BUY":
            buy_count += TIMEFRAMES[tf_key]["weight"]
        elif r["bias"] == "SELL":
            sell_count += TIMEFRAMES[tf_key]["weight"]

    total_weight = sum(tf["weight"] for tf in TIMEFRAMES.values())

    if buy_count >= sell_count and buy_count >= MTF_AGREEMENT * 2:
        overall = "BUY"
        alignment = round((buy_count / total_weight) * 100)
    elif sell_count > buy_count and sell_count >= MTF_AGREEMENT * 2:
        overall = "SELL"
        alignment = round((sell_count / total_weight) * 100)
    else:
        overall   = "NEUTRAL"
        alignment = 0

    return {
        "overall":   overall,
        "alignment": alignment,
        "timeframes": results,
        "buy_count":  buy_count,
        "sell_count": sell_count,
    }

# ============================================================
#   SMC FUNCTIONS
# ============================================================

def detect_order_blocks(df):
    result = {"bullish_ob": None, "bearish_ob": None, "price_in_ob": False, "ob_type": None}
    latest_close = df["close"].iloc[-1]
    lookback     = df.iloc[-OB_LOOKBACK:]

    for i in range(len(lookback) - 4, 0, -1):
        candle = lookback.iloc[i]
        next_3 = lookback.iloc[i+1:i+4]
        if candle["close"] < candle["open"] and len(next_3) >= 2:
            if next_3["close"].max() - candle["low"] > candle["atr"] * 1.5:
                ob = {"high": candle["high"], "low": candle["low"], "mid": (candle["high"] + candle["low"]) / 2}
                result["bullish_ob"] = ob
                if ob["low"] <= latest_close <= ob["high"]:
                    result["price_in_ob"] = True
                    result["ob_type"]     = "BULLISH"
                break

    for i in range(len(lookback) - 4, 0, -1):
        candle = lookback.iloc[i]
        next_3 = lookback.iloc[i+1:i+4]
        if candle["close"] > candle["open"] and len(next_3) >= 2:
            if candle["high"] - next_3["close"].min() > candle["atr"] * 1.5:
                ob = {"high": candle["high"], "low": candle["low"], "mid": (candle["high"] + candle["low"]) / 2}
                result["bearish_ob"] = ob
                if ob["low"] <= latest_close <= ob["high"] and result["ob_type"] is None:
                    result["price_in_ob"] = True
                    result["ob_type"]     = "BEARISH"
                break

    return result

def detect_market_structure(df):
    result   = {"bos": None, "choch": None, "trend": "NEUTRAL", "swing_high": None, "swing_low": None}
    lookback = df.iloc[-STRUCTURE_LOOKBACK-5:-1]
    if len(lookback) < 10:
        return result

    highs = lookback["high"].values
    lows  = lookback["low"].values
    swing_highs = []
    swing_lows  = []

    for i in range(2, len(highs) - 2):
        if highs[i] > highs[i-1] and highs[i] > highs[i-2] and highs[i] > highs[i+1] and highs[i] > highs[i+2]:
            swing_highs.append(highs[i])
        if lows[i] < lows[i-1] and lows[i] < lows[i-2] and lows[i] < lows[i+1] and lows[i] < lows[i+2]:
            swing_lows.append(lows[i])

    if not swing_highs or not swing_lows:
        return result

    latest_close = df["close"].iloc[-1]
    last_sh      = swing_highs[-1]
    last_sl      = swing_lows[-1]
    result["swing_high"] = last_sh
    result["swing_low"]  = last_sl

    ema_fast = df["ema_fast"].iloc[-1]
    ema_slow = df["ema_slow"].iloc[-1]
    result["trend"] = "BULLISH" if ema_fast > ema_slow else "BEARISH"

    if latest_close > last_sh and result["trend"] == "BULLISH":
        result["bos"] = {"direction": "BULLISH", "level": last_sh}
    elif latest_close < last_sl and result["trend"] == "BEARISH":
        result["bos"] = {"direction": "BEARISH", "level": last_sl}
    elif latest_close > last_sh and result["trend"] == "BEARISH":
        result["choch"] = {"direction": "BULLISH", "level": last_sh}
    elif latest_close < last_sl and result["trend"] == "BULLISH":
        result["choch"] = {"direction": "BEARISH", "level": last_sl}

    return result

def detect_fair_value_gaps(df):
    result = {"bullish_fvg": None, "bearish_fvg": None, "price_in_fvg": False, "fvg_type": None}
    latest_close = df["close"].iloc[-1]
    lookback     = df.iloc[-15:]

    for i in range(1, len(lookback) - 1):
        prev = lookback.iloc[i-1]
        curr = lookback.iloc[i]
        nxt  = lookback.iloc[i+1]

        gap = nxt["low"] - prev["high"]
        if gap > 0 and gap / curr["close"] > FVG_THRESHOLD:
            fvg = {"high": nxt["low"], "low": prev["high"], "mid": (nxt["low"] + prev["high"]) / 2}
            result["bullish_fvg"] = fvg
            if fvg["low"] <= latest_close <= fvg["high"]:
                result["price_in_fvg"] = True
                result["fvg_type"]     = "BULLISH"

        gap = prev["low"] - nxt["high"]
        if gap > 0 and gap / curr["close"] > FVG_THRESHOLD:
            fvg = {"high": prev["low"], "low": nxt["high"], "mid": (prev["low"] + nxt["high"]) / 2}
            result["bearish_fvg"] = fvg
            if fvg["low"] <= latest_close <= fvg["high"] and result["fvg_type"] is None:
                result["price_in_fvg"] = True
                result["fvg_type"]     = "BEARISH"

    return result

def detect_liquidity_sweep(df):
    result   = {"sweep": None, "direction": None, "level": None}
    lookback = df.iloc[-10:-1]
    latest   = df.iloc[-1]

    recent_high = lookback["high"].max()
    recent_low  = lookback["low"].min()

    if latest["high"] > recent_high and latest["close"] < recent_high:
        wick = latest["high"] - max(latest["open"], latest["close"])
        if wick > latest["atr"] * 0.3:
            result["sweep"] = "BEARISH"; result["direction"] = "Swept highs"; result["level"] = recent_high
    elif latest["low"] < recent_low and latest["close"] > recent_low:
        wick = min(latest["open"], latest["close"]) - latest["low"]
        if wick > latest["atr"] * 0.3:
            result["sweep"] = "BULLISH"; result["direction"] = "Swept lows"; result["level"] = recent_low

    return result

def detect_candle_patterns(df):
    latest   = df.iloc[-1]
    prev     = df.iloc[-2]
    prev2    = df.iloc[-3]
    patterns = []
    atr      = latest["atr"]

    body       = latest["body"]
    upper_wick = latest["upper_wick"]
    lower_wick = latest["lower_wick"]
    is_bull    = latest["close"] > latest["open"]
    is_bear    = latest["close"] < latest["open"]

    if is_bull and prev["close"] < prev["open"]:
        if latest["close"] > prev["open"] and latest["open"] < prev["close"]:
            patterns.append({"name": "Bullish Engulfing", "direction": "BUY", "strength": "strong"})
    if is_bear and prev["close"] > prev["open"]:
        if latest["close"] < prev["open"] and latest["open"] > prev["close"]:
            patterns.append({"name": "Bearish Engulfing", "direction": "SELL", "strength": "strong"})
    if lower_wick > body * 2 and lower_wick > upper_wick * 2 and body > 0:
        patterns.append({"name": "Bullish Pin Bar", "direction": "BUY", "strength": "strong"})
    if upper_wick > body * 2 and upper_wick > lower_wick * 2 and body > 0:
        patterns.append({"name": "Bearish Pin Bar", "direction": "SELL", "strength": "strong"})
    if (prev2["close"] < prev2["open"] and prev["body"] < prev2["body"] * 0.5 and
            is_bull and latest["close"] > prev2["open"] * 0.5):
        patterns.append({"name": "Morning Star", "direction": "BUY", "strength": "very strong"})
    if (prev2["close"] > prev2["open"] and prev["body"] < prev2["body"] * 0.5 and
            is_bear and latest["close"] < prev2["open"] * 0.5):
        patterns.append({"name": "Evening Star", "direction": "SELL", "strength": "very strong"})
    if body > atr * 1.5 and is_bull and lower_wick < body * 0.3:
        patterns.append({"name": "Strong Bullish Momentum", "direction": "BUY", "strength": "strong"})
    if body > atr * 1.5 and is_bear and upper_wick < body * 0.3:
        patterns.append({"name": "Strong Bearish Momentum", "direction": "SELL", "strength": "strong"})

    return patterns

def detect_support_resistance(df):
    result   = {"near_resistance": False, "near_support": False, "resistance": None, "support": None}
    lookback = df.iloc[-SR_LOOKBACK:]
    price    = df["close"].iloc[-1]
    atr      = df["atr"].iloc[-1]
    zone     = price * SR_ZONE_PCT

    resistances = []
    supports    = []

    for i in range(2, len(lookback) - 2):
        h = lookback["high"].iloc[i]
        l = lookback["low"].iloc[i]
        if all(h > lookback["high"].iloc[i+j] for j in [-2,-1,1,2]):
            resistances.append(h)
        if all(l < lookback["low"].iloc[i+j] for j in [-2,-1,1,2]):
            supports.append(l)

    if resistances:
        r = min(resistances, key=lambda x: abs(x - price))
        result["resistance"] = r
        if abs(price - r) <= zone + atr * 0.5:
            result["near_resistance"] = True
    if supports:
        s = min(supports, key=lambda x: abs(x - price))
        result["support"] = s
        if abs(price - s) <= zone + atr * 0.5:
            result["near_support"] = True

    return result

def detect_trend_structure(df):
    result   = {"structure": "NEUTRAL", "description": "No clear structure"}
    lookback = df.iloc[-20:]
    highs    = []
    lows     = []

    for i in range(2, len(lookback) - 2):
        h = lookback["high"].iloc[i]
        l = lookback["low"].iloc[i]
        if h > lookback["high"].iloc[i-1] and h > lookback["high"].iloc[i+1]:
            highs.append(h)
        if l < lookback["low"].iloc[i-1] and l < lookback["low"].iloc[i+1]:
            lows.append(l)

    if len(highs) >= 2 and len(lows) >= 2:
        hh = highs[-1] > highs[-2]
        hl = lows[-1]  > lows[-2]
        lh = highs[-1] < highs[-2]
        ll = lows[-1]  < lows[-2]

        if hh and hl:
            result["structure"]   = "BULLISH"
            result["description"] = "HH + HL — Strong uptrend"
        elif lh and ll:
            result["structure"]   = "BEARISH"
            result["description"] = "LH + LL — Strong downtrend"
        elif lh and hl:
            result["structure"]   = "NEUTRAL"
            result["description"] = "Consolidating — Breakout pending"

    return result


# ============================================================
#   RSI DIVERGENCE
# ============================================================

def detect_rsi_divergence(df: pd.DataFrame) -> dict:
    """
    Bullish Divergence:  Price makes Lower Low, RSI makes Higher Low  → BUY
    Bearish Divergence:  Price makes Higher High, RSI makes Lower High → SELL
    """
    result   = {"type": None, "description": None}
    lookback = df.iloc[-30:]

    price_vals = lookback["close"].values
    rsi_vals   = lookback["rsi"].values

    # Find swing lows in price and RSI (for bullish divergence)
    price_lows = []
    rsi_lows   = []
    for i in range(2, len(price_vals) - 2):
        if price_vals[i] < price_vals[i-1] and price_vals[i] < price_vals[i-2] and            price_vals[i] < price_vals[i+1] and price_vals[i] < price_vals[i+2]:
            price_lows.append((i, price_vals[i], rsi_vals[i]))
        if rsi_vals[i] < rsi_vals[i-1] and rsi_vals[i] < rsi_vals[i+1]:
            rsi_lows.append((i, rsi_vals[i]))

    # Find swing highs in price and RSI (for bearish divergence)
    price_highs = []
    rsi_highs   = []
    for i in range(2, len(price_vals) - 2):
        if price_vals[i] > price_vals[i-1] and price_vals[i] > price_vals[i-2] and            price_vals[i] > price_vals[i+1] and price_vals[i] > price_vals[i+2]:
            price_highs.append((i, price_vals[i], rsi_vals[i]))
        if rsi_vals[i] > rsi_vals[i-1] and rsi_vals[i] > rsi_vals[i+1]:
            rsi_highs.append((i, rsi_vals[i]))

    # Bullish divergence — last 2 price lows
    if len(price_lows) >= 2:
        p1, p2 = price_lows[-2], price_lows[-1]
        if p2[1] < p1[1] and p2[2] > p1[2]:   # Price LL, RSI HL
            result["type"]        = "BULLISH"
            result["description"] = f"Bullish RSI Divergence — Price LL, RSI HL"

    # Bearish divergence — last 2 price highs
    if len(price_highs) >= 2 and result["type"] is None:
        p1, p2 = price_highs[-2], price_highs[-1]
        if p2[1] > p1[1] and p2[2] < p1[2]:   # Price HH, RSI LH
            result["type"]        = "BEARISH"
            result["description"] = f"Bearish RSI Divergence — Price HH, RSI LH"

    return result

# ============================================================
#   FIBONACCI LEVELS
# ============================================================

def detect_fibonacci_levels(df: pd.DataFrame) -> dict:
    """
    Calculate Fibonacci retracement levels from recent swing high/low.
    Check if current price is near key Fib levels (0.382, 0.5, 0.618).
    """
    result   = {"near_fib": False, "fib_level": None, "fib_direction": None,
                "levels": {}, "swing_high": None, "swing_low": None}
    lookback = df.iloc[-50:]
    price    = df["close"].iloc[-1]
    atr      = df["atr"].iloc[-1]

    swing_high = lookback["high"].max()
    swing_low  = lookback["low"].min()
    diff       = swing_high - swing_low

    if diff == 0:
        return result

    result["swing_high"] = swing_high
    result["swing_low"]  = swing_low

    # Key Fibonacci levels
    fibs = {
        "0.236": swing_high - diff * 0.236,
        "0.382": swing_high - diff * 0.382,
        "0.500": swing_high - diff * 0.500,
        "0.618": swing_high - diff * 0.618,
        "0.786": swing_high - diff * 0.786,
    }
    result["levels"] = fibs

    # Check if price is near a key Fib level (within 0.5 ATR)
    key_fibs = ["0.382", "0.500", "0.618"]
    for level_name in key_fibs:
        level_price = fibs[level_name]
        if abs(price - level_price) <= atr * 0.5:
            result["near_fib"]      = True
            result["fib_level"]     = level_name
            result["fib_price"]     = level_price
            # Direction — price at fib support = BUY, fib resistance = SELL
            trend = df["ema_fast"].iloc[-1] > df["ema_slow"].iloc[-1]
            result["fib_direction"] = "BUY" if trend else "SELL"
            break

    return result

# ============================================================
#   BOLLINGER BANDS ANALYSIS
# ============================================================

def detect_bollinger_signals(df: pd.DataFrame) -> dict:
    """
    BB Squeeze:   Very narrow bands = big move coming
    BB Touch Low: Price touches lower band = potential BUY
    BB Touch High: Price touches upper band = potential SELL
    BB Breakout:  Price closes outside band = strong momentum
    """
    result  = {"signal": None, "description": None, "squeeze": False}
    latest  = df.iloc[-1]
    prev    = df.iloc[-2]
    price   = latest["close"]

    bb_upper = latest["bb_upper"]
    bb_lower = latest["bb_lower"]
    bb_mid   = latest["bb_mid"]
    bb_pct   = latest["bb_pct"]
    bb_width = latest["bb_width"]

    # BB Squeeze — width very narrow (below 20-period average width)
    avg_width = df["bb_width"].rolling(20).mean().iloc[-1]
    if bb_width < avg_width * 0.5:
        result["squeeze"] = True

    # Price at lower band — bullish signal
    if bb_pct <= 0.05:
        result["signal"]      = "BUY"
        result["description"] = "Price at BB lower band — oversold zone"
    # Price at upper band — bearish signal
    elif bb_pct >= 0.95:
        result["signal"]      = "SELL"
        result["description"] = "Price at BB upper band — overbought zone"
    # Bullish breakout above upper band with momentum
    elif price > bb_upper and prev["close"] <= prev["bb_upper"]:
        result["signal"]      = "BUY"
        result["description"] = "BB bullish breakout — strong momentum"
    # Bearish breakdown below lower band
    elif price < bb_lower and prev["close"] >= prev["bb_lower"]:
        result["signal"]      = "SELL"
        result["description"] = "BB bearish breakdown — strong momentum"

    return result

# ============================================================
#   SIGNAL GENERATION
# ============================================================

def detect_market_regime(df: pd.DataFrame) -> dict:
    """
    Detect market regime using ADX.
    Relaxed thresholds — crypto naturally has lower ADX.
    """
    try:
        adx    = df["adx"].iloc[-1]
        di_pos = df["adx_pos"].iloc[-1]
        di_neg = df["adx_neg"].iloc[-1]
    except Exception:
        return {"regime": "unknown", "adx": 0, "label": "❓ Unknown", "min_score": 6}

    if adx >= 20:
        regime    = "trending"
        label     = "📈 Trending"
        min_score = 6    # Normal threshold
    elif adx >= 15:
        regime    = "caution"
        label     = "⚠️ Caution"
        min_score = 9    # Slightly higher bar
    else:
        regime    = "ranging"
        label     = "📊 Ranging"
        min_score = 999  # Block only truly dead markets

    direction = "bullish" if di_pos > di_neg else "bearish"
    return {
        "regime":    regime,
        "adx":       round(adx, 1),
        "label":     label,
        "min_score": min_score,
        "direction": direction,
    }


def check_volume_quality(df: pd.DataFrame) -> dict:
    """
    Check volume quality for signal confirmation.
    Returns score bonus + label.
    """
    try:
        ratio = df["volume_ratio"].iloc[-1]
    except Exception:
        return {"ratio": 1.0, "bonus": 0, "label": "❓ Unknown", "valid": True}

    if ratio >= 1.5:
        return {"ratio": round(ratio, 2), "bonus": 2, "label": "🔥 High Volume", "valid": True}
    elif ratio >= 1.2:
        return {"ratio": round(ratio, 2), "bonus": 1, "label": "✅ Good Volume", "valid": True}
    elif ratio >= 0.1:
        return {"ratio": round(ratio, 2), "bonus": 0, "label": "⚪ Low Volume", "valid": True}
    else:
        return {"ratio": round(ratio, 2), "bonus": -1, "label": "❌ Dead Volume", "valid": False}


def check_mtf_alignment(mtf: dict) -> dict:
    """
    Check how many timeframes agree.
    Returns alignment count + grade.
    """
    tfs     = mtf.get("timeframes", {})
    total   = len(tfs)
    overall = mtf.get("overall", "HOLD")

    if overall == "HOLD" or total == 0:
        return {"count": 0, "total": total, "grade": "❌", "bonus": 0, "label": "No MTF alignment"}

    agree = sum(1 for tf in tfs.values() if tf.get("bias") == overall)

    if agree == total:
        return {"count": agree, "total": total, "grade": "🔥", "bonus": 3, "label": f"All {total}/{total} TF aligned"}
    elif agree >= total * 0.66:
        return {"count": agree, "total": total, "grade": "✅", "bonus": 2, "label": f"{agree}/{total} TF aligned"}
    elif agree >= total * 0.33:
        return {"count": agree, "total": total, "grade": "⚠️", "bonus": 1, "label": f"{agree}/{total} TF aligned"}
    else:
        return {"count": agree, "total": total, "grade": "❌", "bonus": 0, "label": f"Only {agree}/{total} TF aligned"}


def score_signal(signal: str, df, ob, structure, fvg, sweep, patterns, sr,
                 trend_str, divergence, fib, bb_signal, mtf_align, vol, prev, latest) -> tuple:
    """
    Weighted scoring engine. Returns (buy_score, sell_score, reasons_buy, reasons_sell).
    Weights reflect real signal importance.
    """
    buy_score = 0; sell_score = 0
    reasons_buy = []; reasons_sell = []
    rsi = latest["rsi"]

    # ── HIGH WEIGHT (3 pts) — Strong confirmations ────────────
    # SMC Order Block
    if ob["price_in_ob"] and ob["ob_type"] == "BULLISH":
        buy_score += 3; reasons_buy.append("🏦 Bullish Order Block (3pts)")
    if ob["price_in_ob"] and ob["ob_type"] == "BEARISH":
        sell_score += 3; reasons_sell.append("🏦 Bearish Order Block (3pts)")

    # Break of Structure
    if structure["bos"] and structure["bos"]["direction"] == "BULLISH":
        buy_score += 3; reasons_buy.append(f"💥 BOS Bullish — broke {structure['bos']['level']:.2f} (3pts)")
    if structure["bos"] and structure["bos"]["direction"] == "BEARISH":
        sell_score += 3; reasons_sell.append(f"💥 BOS Bearish — broke {structure['bos']['level']:.2f} (3pts)")

    # RSI Divergence
    if divergence["type"] == "BULLISH":
        buy_score += 3; reasons_buy.append(f"🔀 Bullish RSI Divergence (3pts)")
    elif divergence["type"] == "BEARISH":
        sell_score += 3; reasons_sell.append(f"🔀 Bearish RSI Divergence (3pts)")

    # ── MEDIUM WEIGHT (2 pts) ─────────────────────────────────
    # CHoCH
    if structure["choch"] and structure["choch"]["direction"] == "BULLISH":
        buy_score += 2; reasons_buy.append("🔄 CHoCH Bullish reversal (2pts)")
    if structure["choch"] and structure["choch"]["direction"] == "BEARISH":
        sell_score += 2; reasons_sell.append("🔄 CHoCH Bearish reversal (2pts)")

    # FVG
    if fvg["price_in_fvg"] and fvg["fvg_type"] == "BULLISH":
        buy_score += 2; reasons_buy.append("📦 Filling Bullish FVG (2pts)")
    if fvg["price_in_fvg"] and fvg["fvg_type"] == "BEARISH":
        sell_score += 2; reasons_sell.append("📦 Filling Bearish FVG (2pts)")

    # Liquidity sweep
    if sweep["sweep"] == "BULLISH":
        buy_score += 2; reasons_buy.append(f"💧 Liq. Sweep lows {sweep['level']:.2f} (2pts)")
    if sweep["sweep"] == "BEARISH":
        sell_score += 2; reasons_sell.append(f"💧 Liq. Sweep highs {sweep['level']:.2f} (2pts)")

    # MACD crossover
    if prev["macd"] <= prev["macd_signal"] and latest["macd"] > latest["macd_signal"]:
        buy_score += 2; reasons_buy.append("📊 MACD Bullish crossover (2pts)")
    elif prev["macd"] >= prev["macd_signal"] and latest["macd"] < latest["macd_signal"]:
        sell_score += 2; reasons_sell.append("📊 MACD Bearish crossover (2pts)")

    # Fibonacci
    if fib["near_fib"] and fib["fib_direction"] == "BUY":
        buy_score += 2; reasons_buy.append(f"📐 Fib {fib['fib_level']} support (2pts)")
    elif fib["near_fib"] and fib["fib_direction"] == "SELL":
        sell_score += 2; reasons_sell.append(f"📐 Fib {fib['fib_level']} resistance (2pts)")

    # ── LOW WEIGHT (1 pt) ─────────────────────────────────────
    # RSI extreme
    if rsi < RSI_OVERSOLD:
        buy_score += 1; reasons_buy.append(f"📉 RSI {rsi:.1f} oversold (1pt)")
    elif rsi > RSI_OVERBOUGHT:
        sell_score += 1; reasons_sell.append(f"📈 RSI {rsi:.1f} overbought (1pt)")

    # MA cross
    if prev["ma_short"] <= prev["ma_long"] and latest["ma_short"] > latest["ma_long"]:
        buy_score += 1; reasons_buy.append(f"✨ Golden Cross MA{MA_SHORT}/MA{MA_LONG} (1pt)")
    elif prev["ma_short"] >= prev["ma_long"] and latest["ma_short"] < latest["ma_long"]:
        sell_score += 1; reasons_sell.append(f"✨ Death Cross MA{MA_SHORT}/MA{MA_LONG} (1pt)")

    # Support/Resistance
    if sr["near_support"]:
        buy_score += 1; reasons_buy.append(f"🧱 Near support {sr['support']:.2f} (1pt)")
    if sr["near_resistance"]:
        sell_score += 1; reasons_sell.append(f"🧱 Near resistance {sr['resistance']:.2f} (1pt)")

    # Trend structure
    if trend_str["structure"] == "BULLISH":
        buy_score += 1; reasons_buy.append(f"📈 {trend_str['description']} (1pt)")
    if trend_str["structure"] == "BEARISH":
        sell_score += 1; reasons_sell.append(f"📉 {trend_str['description']} (1pt)")

    # Bollinger Bands
    if bb_signal["signal"] == "BUY":
        buy_score += 1; reasons_buy.append(f"🎯 BB: {bb_signal['description']} (1pt)")
    elif bb_signal["signal"] == "SELL":
        sell_score += 1; reasons_sell.append(f"🎯 BB: {bb_signal['description']} (1pt)")

    # Candle patterns — strong patterns get 2pts
    buy_patterns  = [p for p in patterns if p["direction"] == "BUY"]
    sell_patterns = [p for p in patterns if p["direction"] == "SELL"]
    strong_patterns = {"Engulfing", "Pin Bar", "Hammer", "Shooting Star", "Morning Star", "Evening Star"}
    if buy_patterns:
        pts = 2 if buy_patterns[0]["name"] in strong_patterns else 1
        buy_score += pts; reasons_buy.append(f"🕯 PA: {buy_patterns[0]['name']} ({pts}pts)")
    if sell_patterns:
        pts = 2 if sell_patterns[0]["name"] in strong_patterns else 1
        sell_score += pts; reasons_sell.append(f"🕯 PA: {sell_patterns[0]['name']} ({pts}pts)")

    # ── OB + FVG CONFLUENCE BONUS ─────────────────────────────
    # When Order Block and FVG are both active — very strong
    if ob["price_in_ob"] and fvg["price_in_fvg"]:
        if ob["ob_type"] == "BULLISH" and fvg["fvg_type"] == "BULLISH":
            buy_score += 2; reasons_buy.append("🔥 OB + FVG Confluence (+2pts)")
        elif ob["ob_type"] == "BEARISH" and fvg["fvg_type"] == "BEARISH":
            sell_score += 2; reasons_sell.append("🔥 OB + FVG Confluence (+2pts)")

    # ── MTF ALIGNMENT BONUS ───────────────────────────────────
    if mtf_align["bonus"] > 0:
        if buy_score > sell_score:
            buy_score += mtf_align["bonus"]
            reasons_buy.append(f"🕐 {mtf_align['label']} (+{mtf_align['bonus']}pts)")
        elif sell_score > buy_score:
            sell_score += mtf_align["bonus"]
            reasons_sell.append(f"🕐 {mtf_align['label']} (+{mtf_align['bonus']}pts)")

    # ── VOLUME BONUS/PENALTY ──────────────────────────────────
    if vol["bonus"] != 0:
        if buy_score > sell_score:
            buy_score += vol["bonus"]
            reasons_buy.append(f"📊 {vol['label']} ({'+' if vol['bonus']>0 else ''}{vol['bonus']}pts)")
        elif sell_score > buy_score:
            sell_score += vol["bonus"]
            reasons_sell.append(f"📊 {vol['label']} ({'+' if vol['bonus']>0 else ''}{vol['bonus']}pts)")

    return buy_score, sell_score, reasons_buy, reasons_sell


def get_signal_grade(score: int, regime: dict, vol: dict, mtf_align: dict) -> str:
    """Stricter grading — only strong setups get A/A+."""
    adx       = regime["adx"]
    vol_ratio = vol["ratio"]
    mtf_count = mtf_align["count"]
    mtf_total = mtf_align["total"]

    if score >= 12 and adx >= 25 and vol_ratio >= 1.0 and mtf_count == mtf_total:
        return "🔥 A+ — Premium Setup"
    elif score >= 8 and adx >= 18 and vol_ratio >= 0.5:
        return "💪 A — Strong Setup"
    elif score >= 5 and adx >= 12:
        return "✅ B — Good Setup"
    elif score >= 3:
        return "⚠️ C — Weak Setup"
    else:
        return "❌ Blocked"


def generate_signal(df: pd.DataFrame, mtf: dict) -> dict:
    """
    Weighted signal engine with:
    - Weighted scoring (not equal counts)
    - Market regime filter (ADX)
    - Volume confirmation
    - MTF alignment bonus
    - Signal grade (A+/A/B/C)
    """
    latest = df.iloc[-1]
    prev   = df.iloc[-2]
    price  = latest["close"]
    rsi    = latest["rsi"]

    # ── Quality filters ────────────────────────────────────────
    regime    = detect_market_regime(df)
    vol       = check_volume_quality(df)
    mtf_align = check_mtf_alignment(mtf)

    # Block ranging market entirely
    if regime["regime"] == "ranging":
        logger.info(f"⏸ Signal blocked — ranging market (ADX {regime['adx']})")
        return {"signal": "HOLD", "conf": 0, "reasons": [f"Ranging market (ADX {regime['adx']}) — waiting for trend"],
                "price": price, "rsi": rsi, "prob": None, "analysis": {},
                "regime": regime, "volume": vol, "mtf_align": mtf_align, "grade": "❌ Blocked — Ranging"}

    # Volume filter — only block truly dead volume
    if vol["ratio"] < 0.1:
        logger.info(f"⏸ Signal blocked — dead volume ({vol['ratio']}x avg)")
        return {"signal": "HOLD", "conf": 0, "reasons": [f"Dead volume ({vol['ratio']}x avg)"],
                "price": price, "rsi": rsi, "prob": None, "analysis": {},
                "regime": regime, "volume": vol, "mtf_align": mtf_align, "grade": "❌ Blocked — Dead Volume"}

    # ── Detect all signals ─────────────────────────────────────
    ob        = detect_order_blocks(df)
    structure = detect_market_structure(df)
    fvg       = detect_fair_value_gaps(df)
    sweep     = detect_liquidity_sweep(df)
    patterns  = detect_candle_patterns(df)
    sr        = detect_support_resistance(df)
    trend_str = detect_trend_structure(df)
    divergence = detect_rsi_divergence(df)
    fib       = detect_fibonacci_levels(df)
    bb_signal = detect_bollinger_signals(df)

    buy_score, sell_score, reasons_buy, reasons_sell = score_signal(
        "BUY", df, ob, structure, fvg, sweep, patterns, sr,
        trend_str, divergence, fib, bb_signal, mtf_align, vol, prev, latest
    )

    analysis = {
        "ob": ob, "structure": structure, "fvg": fvg, "sweep": sweep,
        "patterns": patterns, "sr": sr, "trend_str": trend_str, "mtf": mtf,
        "divergence": divergence, "fib": fib, "bb": bb_signal,
    }

    min_score = regime["min_score"]

    if buy_score > sell_score and buy_score >= min_score:
        grade = get_signal_grade(buy_score, regime, vol, mtf_align)
        prob  = calculate_probability(df, "BUY", analysis)
        return {"signal": "BUY", "conf": buy_score, "reasons": reasons_buy,
                "price": price, "rsi": rsi, "prob": prob, "analysis": analysis,
                "regime": regime, "volume": vol, "mtf_align": mtf_align, "grade": grade}

    elif sell_score > buy_score and sell_score >= min_score:
        grade = get_signal_grade(sell_score, regime, vol, mtf_align)
        prob  = calculate_probability(df, "SELL", analysis)
        return {"signal": "SELL", "conf": sell_score, "reasons": reasons_sell,
                "price": price, "rsi": rsi, "prob": prob, "analysis": analysis,
                "regime": regime, "volume": vol, "mtf_align": mtf_align, "grade": grade}

    else:
        return {"signal": "HOLD", "conf": 0, "reasons": [],
                "price": price, "rsi": rsi, "prob": None, "analysis": analysis,
                "regime": regime, "volume": vol, "mtf_align": mtf_align, "grade": "⏸ HOLD"}

# ============================================================
#   PROBABILITY SCORE
# ============================================================

def calculate_probability(df, signal, analysis):
    latest  = df.iloc[-1]
    prev    = df.iloc[-2]
    score   = 0
    factors = []

    ob        = analysis["ob"]
    structure = analysis["structure"]
    fvg       = analysis["fvg"]
    sweep     = analysis["sweep"]
    patterns  = analysis["patterns"]
    sr        = analysis["sr"]
    trend_str = analysis["trend_str"]
    mtf       = analysis["mtf"]

    is_best, _ = is_best_trading_time()
    if is_best:
        score += 5; factors.append("London+NY overlap ⚡")

    # MTF alignment
    if mtf["overall"] == signal:
        if mtf["alignment"] >= 80:
            score += 20; factors.append(f"All timeframes aligned {signal} 🔥")
        elif mtf["alignment"] >= 60:
            score += 12; factors.append(f"Most timeframes aligned {signal}")
        else:
            score += 6;  factors.append(f"Some timeframes aligned {signal}")

    if signal == "BUY":
        rsi = latest["rsi"]
        if rsi < 20:   score += 18; factors.append(f"RSI {rsi:.0f} — extremely oversold 🔥")
        elif rsi < 30: score += 10; factors.append(f"RSI {rsi:.0f} — oversold")
        elif rsi < 40: score += 5;  factors.append(f"RSI {rsi:.0f} — approaching oversold")

        hist = latest["macd_hist"]
        if hist > 0 and hist > prev["macd_hist"]:
            score += 8; factors.append("MACD growing bullish")
        elif hist > 0:
            score += 4; factors.append("MACD positive")

        if ob["price_in_ob"] and ob["ob_type"] == "BULLISH":
            score += 15; factors.append("🏦 Price at Bullish OB 🔥")
        if structure["bos"] and structure["bos"]["direction"] == "BULLISH":
            score += 10; factors.append("📈 BOS Bullish confirmed")
        if structure["choch"] and structure["choch"]["direction"] == "BULLISH":
            score += 8;  factors.append("🔄 CHoCH — bullish reversal")
        if fvg["price_in_fvg"] and fvg["fvg_type"] == "BULLISH":
            score += 8;  factors.append("⚡ Bullish FVG fill")
        if sweep["sweep"] == "BULLISH":
            score += 10; factors.append("💧 Liquidity swept — smart money buying 🔥")

        buy_patterns = [p for p in patterns if p["direction"] == "BUY"]
        for p in buy_patterns:
            pts = 12 if p["strength"] == "very strong" else 8 if p["strength"] == "strong" else 4
            score += pts; factors.append(f"🕯 {p['name']}")

        if sr["near_support"]:
            score += 7; factors.append(f"🛡 At key support {sr['support']:.2f}")
        if trend_str["structure"] == "BULLISH":
            score += 6; factors.append(f"📐 {trend_str['description']}")
        if latest["volume"] > latest["volume_ma"] * 1.5:
            score += 5; factors.append("📊 Volume surge")

        # Divergence bonus
        div = analysis.get("divergence", {})
        if div.get("type") == "BULLISH":
            score += 15; factors.append("🔀 Bullish RSI Divergence 🔥")

        # Fibonacci bonus
        fib = analysis.get("fib", {})
        if fib.get("near_fib") and fib.get("fib_direction") == "BUY":
            score += 10; factors.append(f"📐 Fib {fib.get('fib_level','?')} support zone")

        # Bollinger Bands bonus
        bb = analysis.get("bb", {})
        if bb.get("signal") == "BUY":
            score += 8;  factors.append(f"📊 {bb.get('description','BB signal')}")
        if bb.get("squeeze"):
            score += 5;  factors.append("🔔 BB Squeeze — explosive move pending")

    elif signal == "SELL":
        rsi = latest["rsi"]
        if rsi > 80:   score += 18; factors.append(f"RSI {rsi:.0f} — extremely overbought 🔥")
        elif rsi > 70: score += 10; factors.append(f"RSI {rsi:.0f} — overbought")
        elif rsi > 60: score += 5;  factors.append(f"RSI {rsi:.0f} — approaching overbought")

        hist = latest["macd_hist"]
        if hist < 0 and hist < prev["macd_hist"]:
            score += 8; factors.append("MACD growing bearish")
        elif hist < 0:
            score += 4; factors.append("MACD negative")

        if ob["price_in_ob"] and ob["ob_type"] == "BEARISH":
            score += 15; factors.append("🏦 Price at Bearish OB 🔥")
        if structure["bos"] and structure["bos"]["direction"] == "BEARISH":
            score += 10; factors.append("📉 BOS Bearish confirmed")
        if structure["choch"] and structure["choch"]["direction"] == "BEARISH":
            score += 8;  factors.append("🔄 CHoCH — bearish reversal")
        if fvg["price_in_fvg"] and fvg["fvg_type"] == "BEARISH":
            score += 8;  factors.append("⚡ Bearish FVG fill")
        if sweep["sweep"] == "BEARISH":
            score += 10; factors.append("💧 Liquidity swept — smart money selling 🔥")

        sell_patterns = [p for p in patterns if p["direction"] == "SELL"]
        for p in sell_patterns:
            pts = 12 if p["strength"] == "very strong" else 8 if p["strength"] == "strong" else 4
            score += pts; factors.append(f"🕯 {p['name']}")

        if sr["near_resistance"]:
            score += 7; factors.append(f"🧱 At key resistance {sr['resistance']:.2f}")
        if trend_str["structure"] == "BEARISH":
            score += 6; factors.append(f"📐 {trend_str['description']}")
        if latest["volume"] > latest["volume_ma"] * 1.5:
            score += 5; factors.append("📊 Volume surge")

        # Divergence bonus
        div = analysis.get("divergence", {})
        if div.get("type") == "BEARISH":
            score += 15; factors.append("🔀 Bearish RSI Divergence 🔥")

        # Fibonacci bonus
        fib = analysis.get("fib", {})
        if fib.get("near_fib") and fib.get("fib_direction") == "SELL":
            score += 10; factors.append(f"📐 Fib {fib.get('fib_level','?')} resistance zone")

        # Bollinger Bands bonus
        bb = analysis.get("bb", {})
        if bb.get("signal") == "SELL":
            score += 8;  factors.append(f"📊 {bb.get('description','BB signal')}")
        if bb.get("squeeze"):
            score += 5;  factors.append("🔔 BB Squeeze — explosive move pending")

    score = min(score, 100)

    if score >= 85:   label = "🔥 VERY HIGH — Premium Setup"
    elif score >= 70: label = "💪 HIGH — Strong Setup"
    elif score >= 55: label = "✅ MODERATE — Decent Setup"
    else:             label = "⚠️ LOW — Weak Setup"

    return {"score": score, "label": label, "factors": factors}

# ============================================================
#   SIGNAL CHART GENERATOR
# ============================================================

def format_signal_message(result, symbol, display):
    """Clean, compact signal message."""
    signal   = result["signal"]
    price    = result["price"]
    conf     = result["conf"]
    prob     = result["prob"]
    reasons  = result["reasons"]
    analysis = result["analysis"]
    grade    = result.get("grade", "")
    regime   = result.get("regime", {})
    vol      = result.get("volume", {})
    mtf_align= result.get("mtf_align", {})

    sl_usd = SYMBOLS[symbol]["sl"]
    tp_usd = sl_usd * RISK_REWARD

    if signal == "BUY":
        emoji    = "🟢"
        sl_price = round(price - sl_usd, 5)
        tp_price = round(price + tp_usd, 5)
        action   = "📥 PLACE A BUY ORDER"
    else:
        emoji    = "🔴"
        sl_price = round(price + sl_usd, 5)
        tp_price = round(price - tp_usd, 5)
        action   = "📤 PLACE A SELL ORDER"

    # Pip distances
    pip_sl = round(abs(price - sl_price), 5)
    pip_tp = round(abs(price - tp_price), 5)
    rr     = round(tp_usd / sl_usd, 1) if sl_usd > 0 else 2.0

    adx_val   = regime.get("adx", 0)
    vol_ratio = vol.get("ratio", 1.0)
    mtf_label = mtf_align.get("label", "")
    score     = prob["score"] if prob else 0

    # Session
    try:
        sessions    = get_active_sessions()
        session_txt = " + ".join(sessions) if sessions else "Off-hours"
        is_best, _  = is_best_trading_time()
        peak_tag    = " 🔥" if is_best else ""
    except Exception:
        session_txt = ""; peak_tag = ""

    # MTF summary — compact
    mtf = analysis.get("mtf", {})
    mtf_lines = ""
    for tf_key, tf_data in mtf.get("timeframes", {}).items():
        tf_e = "🟢" if tf_data["bias"] == "BUY" else "🔴" if tf_data["bias"] == "SELL" else "⚪"
        mtf_lines += f"   {tf_e} {tf_data['tf']}: {tf_data['bias']} (RSI {tf_data['rsi']})\n"

    # SMC + PA compact
    ob        = analysis.get("ob", {})
    structure = analysis.get("structure", {})
    fvg       = analysis.get("fvg", {})
    sweep     = analysis.get("sweep", {})
    smc_tags  = []
    if ob.get("price_in_ob"):     smc_tags.append("OB")
    if structure.get("bos"):      smc_tags.append("BOS")
    if fvg.get("price_in_fvg"):   smc_tags.append("FVG")
    if sweep.get("sweep"):        smc_tags.append("Liq.Sweep")
    smc_line  = " | ".join(smc_tags) if smc_tags else "—"

    pa_list  = [p["name"] for p in analysis.get("patterns", []) if p["direction"] == signal]
    pa_line  = ", ".join(pa_list[:2]) if pa_list else "—"

    # Top 3 reasons only
    top_reasons = "\n   • ".join(reasons[:3]) if reasons else "—"

    # Signal strength bar
    filled   = int(score / 10)
    prob_bar = "█" * filled + "░" * (10 - filled)

    nl = "\n"
    msg = (
        f"{emoji}{emoji} *{display} — {signal} NOW* {emoji}{emoji}\n"
        f"{grade}\n\n"
        f"{action}\n\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"💰 *Entry:*       `{price}`\n"
        f"🛑 *Stop Loss:*   `{sl_price}` ({pip_sl})\n"
        f"🎯 *Take Profit:* `{tp_price}` ({pip_tp})\n"
        f"⚖️ *R/R:* `1:{rr}`\n"
        f"━━━━━━━━━━━━━━━━━━━━\n\n"
        f"📊 *Score:* {prob_bar} `{score}%` | *{conf} pts*\n"
        f"📐 ADX `{adx_val}` | Vol `{vol_ratio}x` | {mtf_label}\n"
        f"⏱ `30M` | 🌍 {session_txt}{peak_tag}\n\n"
        f"📐 *MTF Alignment:*\n{mtf_lines}\n"
        f"🏦 *SMC:* `{smc_line}`\n"
        f"🕯 *PA:* `{pa_line}`\n\n"
        f"💡 *Top Reasons:*\n"
        f"   • {top_reasons}\n\n"
        f"🕐 `{to_user_datetime()}`\n"
        f"⚠️ _Always use Stop Loss._"
    )
    return msg.strip()


def send_message(message: str):
    try:
        url     = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
        payload = {"chat_id": CHAT_ID, "text": message, "parse_mode": "Markdown"}
        r       = requests.post(url, data=payload, timeout=10)
        if r.status_code == 200:
            logger.info("✅ Telegram message sent")
        else:
            logger.error(f"Telegram error: {r.text}")
    except Exception as e:
        logger.error(f"Telegram error: {e}")

# ============================================================
#   PERFORMANCE TRACKING
# ============================================================

def save_to_history(signal, display, symbol, price, prob_score, sl, tp, conf):
    global signal_history, performance
    entry = {
        "id":       len(signal_history) + 1,
        "time":     datetime.now().strftime("%m/%d %H:%M"),
        "symbol":   display,
        "yf_sym":   symbol,
        "signal":   signal,
        "price":    price,
        "sl":       sl,
        "tp":       tp,
        "prob":     prob_score,
        "conf":     conf,
        "outcome":  "PENDING",   # PENDING / WIN / LOSS
        "pips":     0,
    }
    signal_history.insert(0, entry)
    if len(signal_history) > 50:
        signal_history = signal_history[:50]

    performance["total"]   += 1
    performance["pending"] += 1

    # Track as open trade for trailing stop
    now_ts = datetime.now(timezone.utc).timestamp()
    open_trades.append({
        "id":                  entry["id"],
        "symbol":              symbol,
        "display":             display,
        "signal":              signal,
        "price":               price,
        "sl":                  sl,
        "tp":                  tp,
        "sl_usd":              SYMBOLS[symbol]["sl"],
        "tp_usd":              SYMBOLS[symbol]["sl"] * RISK_REWARD,
        "trailing_notified":   False,
        "breakeven_notified":  False,
        "reentry_notified":    False,
        "candles_passed":      0,
        "expired":             False,
        "entry_time":          now_ts,
        "entry_expiry_time":   now_ts + 900,   # 15 minutes to enter
        "entry_triggered":     False,          # True once price moves into trade
        "entry_missed_noted":  False,          # True once MISSED notification sent
    })

def update_signal_outcomes():
    """Check open trades — TP/SL hits, breakeven, trailing stop, expiry, re-entry."""
    global performance
    closed = []
    nl = chr(10)

    # Skip ALL trade monitoring when in binary-only mode
    if active_market == "binary":
        return

    for trade in open_trades:
        # Skip already expired trades completely
        if trade.get("expired"):
            continue

        data = get_current_price(trade["symbol"])
        if not data:
            continue

        current = data["price"]
        signal  = trade["signal"]
        tp      = trade["tp"]
        sl      = trade["sl"]
        entry   = trade["price"]
        sl_usd  = trade["sl_usd"]
        tp_usd  = trade["tp_usd"]

        hit_tp = (signal == "BUY"  and current >= tp) or (signal == "SELL" and current <= tp)
        hit_sl = (signal == "BUY"  and current <= sl) or (signal == "SELL" and current >= sl)

        # ── TP / SL hit ───────────────────────────────────────
        if hit_tp or hit_sl:
            outcome = "WIN" if hit_tp else "LOSS"
            pips    = tp_usd if hit_tp else -sl_usd

            for h in signal_history:
                if h["id"] == trade["id"]:
                    h["outcome"] = outcome
                    h["pips"]    = pips
                    break

            performance["pending"] -= 1
            if hit_tp:
                performance["wins"]       += 1
                performance["total_pips"] += pips
                send_message(
                    "✅ *TRADE CLOSED — WIN!*" + nl + nl +
                    "🎯 " + trade["display"] + " " + signal + " hit Take Profit!" + nl +
                    "Entry: `" + str(round(entry,2)) + "` → TP: `" + str(round(tp,2)) + "`" + nl +
                    "Profit: `+$" + str(round(pips,0)) + "` per lot 💰"
                )
            else:
                performance["losses"]     += 1
                performance["total_pips"] += pips
                send_message(
                    "❌ *TRADE CLOSED — LOSS*" + nl + nl +
                    "🛑 " + trade["display"] + " " + signal + " hit Stop Loss." + nl +
                    "Entry: `" + str(round(entry,2)) + "` → SL: `" + str(round(sl,2)) + "`" + nl +
                    "Loss: `-$" + str(abs(round(pips,0))) + "` per lot" + nl +
                    "_Next signal coming — stick to the plan!_"
                )
            closed.append(trade)
            continue

        # Progress toward TP (0.0 to 1.0)
        if signal == "BUY":
            total    = tp - entry
            progress = (current - entry) / total if total > 0 else 0
            profit_distance = current - entry
        else:
            total    = entry - tp
            progress = (entry - current) / total if total > 0 else 0
            profit_distance = entry - current

        # ── Breakeven alert (skip if expired) ────────────────
        if trade.get("expired"):
            continue

        if not trade.get("breakeven_notified") and profit_distance >= sl_usd:
            trade["breakeven_notified"] = True
            send_message(
                "🔐 *MOVE SL TO BREAKEVEN!*" + nl + nl +
                trade["display"] + " " + signal + " is " + str(round(profit_distance,2)) + " in profit!" + nl + nl +
                "💡 *Move your Stop Loss to entry:*" + nl +
                "New SL: `" + str(round(entry, 2)) + "` ← your entry price" + nl +
                "This makes it a *zero risk trade!*" + nl + nl +
                "Current price: `" + str(round(current,2)) + "`" + nl +
                "Target TP: `" + str(round(tp,2)) + "`"
            )

        # ── Trailing stop suggestion ──────────────────────────
        elif not trade.get("trailing_notified") and progress >= TRAILING_TRIGGER_PCT:
            trade["trailing_notified"] = True
            if signal == "BUY":
                new_sl = round(entry + sl_usd * 0.5, 2)
            else:
                new_sl = round(entry - sl_usd * 0.5, 2)
            send_message(
                "📈 *TRAILING STOP SUGGESTION*" + nl + nl +
                trade["display"] + " " + signal + " is " + str(int(progress*100)) + "% to TP!" + nl + nl +
                "Suggested SL: `" + str(new_sl) + "` _(locks partial profit)_" + nl +
                "Current: `" + str(round(current,2)) + "` | TP: `" + str(round(tp,2)) + "`"
            )

        # ── Signal expiry check ───────────────────────────────
        if not trade.get("expired"):
            candles_passed = trade.get("candles_passed", 0) + 1
            trade["candles_passed"] = candles_passed
            if candles_passed >= SIGNAL_EXPIRY_CANDLES * 3 and abs(current - entry) < sl_usd * 0.3:
                trade["expired"] = True
                send_message(
                    "⏰ *SIGNAL EXPIRED*" + nl + nl +
                    trade["display"] + " " + signal + " signal has not moved significantly." + nl +
                    "Entry: `" + str(round(entry,2)) + "` | Current: `" + str(round(current,2)) + "`" + nl + nl +
                    "Consider closing this trade and waiting for a fresh signal."
                )

        # ── Re-entry alert ────────────────────────────────────
        # Track peak progress toward TP (must reach 0.15 = 15% toward TP before qualifying)
        if progress > trade.get("peak_progress_ot", 0):
            trade["peak_progress_ot"] = progress

        peak_reached = trade.get("peak_progress_ot", 0)
        # Only alert if: price moved meaningfully toward TP first, THEN pulled back to entry zone
        if (not trade.get("reentry_notified")
                and peak_reached >= 0.15          # was at least 15% toward TP
                and progress < 0                   # now behind entry
                and abs(progress) <= REENTRY_BUFFER_PCT):  # within 0.3% of entry
            trade["reentry_notified"] = True
            send_message(
                "🔄 *RE-ENTRY OPPORTUNITY!*" + nl + nl +
                "If you missed the " + trade["display"] + " " + signal + " signal," + nl +
                "price moved toward TP then pulled back to entry zone!" + nl + nl +
                "Original entry: `" + str(round(entry,2)) + "`" + nl +
                "Current price:  `" + str(round(current,2)) + "`" + nl +
                "SL: `" + str(round(sl,2)) + "` | TP: `" + str(round(tp,2)) + "`" + nl + nl +
                "_Same SL and TP apply — manage risk!_"
            )

    for t in closed:
        open_trades.remove(t)

# ============================================================
#   RISK/REWARD CALCULATOR
# ============================================================

def calculate_lot_size(balance: float, symbol: str) -> dict:
    """Calculate recommended lot size based on 2% risk rule."""
    risk_amount = balance * 0.02              # 2% of balance
    sl_usd      = SYMBOLS[symbol]["sl"]
    tp_usd      = sl_usd * RISK_REWARD

    # For Gold: 1 standard lot = $100 per $1 move
    # For BTC/ETH: varies — approximate
    pip_values = {
        "GC=F":    100,   # Gold: $100 per lot per $1
        "BTC-USD": 1,     # BTC: $1 per unit
        "ETH-USD": 1,     # ETH: $1 per unit
    }

    pip_val  = pip_values.get(symbol, 1)
    lot_size = round(risk_amount / (sl_usd * pip_val), 2)
    lot_size = max(0.01, lot_size)

    potential_profit = lot_size * tp_usd * pip_val
    potential_loss   = lot_size * sl_usd * pip_val

    return {
        "balance":          balance,
        "risk_amount":      risk_amount,
        "lot_size":         lot_size,
        "potential_profit": potential_profit,
        "potential_loss":   potential_loss,
        "sl_usd":           sl_usd,
        "tp_usd":           tp_usd,
    }

# ============================================================
#   DAILY SUMMARY
# ============================================================

async def send_daily_summary(context):
    """Daily performance report — sent at configured time (default 8PM Lagos = 19:00 UTC)."""
    now = get_utc_now()
    # Send at 19:00 UTC (8PM Lagos WAT)
    if now.hour != 19 or now.minute > 5:
        return

    nl = chr(10)

    # ── Forex/Crypto Performance ──────────────────────────────
    total_fx  = performance["total"]
    wins_fx   = performance["wins"]
    losses_fx = performance["losses"]
    pending_fx= performance["pending"]
    pips_fx   = round(performance.get("total_pips", 0), 2)
    wr_fx     = round(wins_fx / max(wins_fx + losses_fx, 1) * 100, 1)

    # Best and worst trade
    best_trade  = "—"
    worst_trade = "—"
    if signal_history:
        closed = [s for s in signal_history if s["outcome"] in ["WIN","LOSS"]]
        if closed:
            best  = max(closed, key=lambda x: x.get("pips", 0))
            worst = min(closed, key=lambda x: x.get("pips", 0))
            if best["pips"] > 0:
                best_trade = f"{best['symbol']} {best['signal']} +${abs(round(best['pips'],0))}"
            if worst["pips"] < 0:
                worst_trade = f"{worst['symbol']} {worst['signal']} -${abs(round(worst['pips'],0))}"

    # ── Binary Performance ────────────────────────────────────
    total_bin   = binary_performance.get("total", 0)
    wins_bin    = binary_performance.get("wins", 0)
    losses_bin  = binary_performance.get("losses", 0)
    pending_bin = binary_performance.get("pending", 0)
    streak      = binary_performance.get("streak", 0)
    wr_bin      = round(wins_bin / max(wins_bin + losses_bin, 1) * 100, 1)

    # Best binary pair
    best_pair = "—"
    if binary_asset_stats:
        sorted_pairs = sorted(
            binary_asset_stats.items(),
            key=lambda x: x[1].get("wins", 0),
            reverse=True
        )
        if sorted_pairs:
            pair, stats = sorted_pairs[0]
            w = stats.get("wins", 0)
            l = stats.get("losses", 0)
            if w > 0:
                best_pair = f"{pair} ({w}W/{l}L)"

    # ── Combined ──────────────────────────────────────────────
    total_all = wins_fx + losses_fx + wins_bin + losses_bin
    wins_all  = wins_fx + wins_bin
    wr_all    = round(wins_all / max(total_all, 1) * 100, 1)

    # Streak emoji
    streak_txt = ""
    if streak >= 3:
        streak_txt = nl + "🔥 Binary streak: *" + str(streak) + " wins in a row!*"

    # Session info
    sessions    = get_active_sessions()
    session_txt = ", ".join(sessions) if sessions else "Off-hours"

    msg = (
        "📊 *DAILY PERFORMANCE REPORT*" + nl +
        "📅 `" + now.strftime("%A, %B %d %Y") + "`" + nl +
        "━━━━━━━━━━━━━━━━━━━━" + nl + nl +

        "🔷 *Forex / Crypto Signals*" + nl +
        "Signals: `" + str(total_fx) + "` | "
        "✅ `" + str(wins_fx) + "W` "
        "❌ `" + str(losses_fx) + "L` "
        "⏳ `" + str(pending_fx) + " open`" + nl +
        "Win Rate: `" + str(wr_fx) + "%`" + nl +
        ("💰 Pips: `" + str(pips_fx) + "`" + nl if total_fx > 0 else "") +
        ("🏆 Best: " + best_trade + nl if best_trade != "—" else "") +
        ("📉 Worst: " + worst_trade + nl if worst_trade != "—" else "") +
        nl +

        "🔷 *Binary Options*" + nl +
        "Signals: `" + str(total_bin) + "` | "
        "✅ `" + str(wins_bin) + "W` "
        "❌ `" + str(losses_bin) + "L` "
        "⏳ `" + str(pending_bin) + " open`" + nl +
        "Win Rate: `" + str(wr_bin) + "%`" + nl +
        ("🏆 Best pair: " + best_pair + nl if best_pair != "—" else "") +
        streak_txt + nl + nl +

        "━━━━━━━━━━━━━━━━━━━━" + nl +
        "🏆 *Overall: " + str(wins_all) + "W / " + str(total_all - wins_all) + "L — " + str(wr_all) + "%*" + nl + nl +
        "🌍 Active sessions: " + session_txt + nl +
        "🕐 `" + now.strftime("%H:%M UTC") + "`" + nl + nl +
        "_Keep following the signals — consistency wins! 💪_"
    )

    send_message(msg)


# ============================================================
#   SCAN
# ============================================================

# ============================================================
#   BINARY OPTIONS — ANALYSIS ENGINE (Pocket Option)
# ============================================================

def calculate_stochastic(df: pd.DataFrame, k_period=14, d_period=3) -> pd.DataFrame:
    """Stochastic Oscillator — key for binary options."""
    low_min  = df["low"].rolling(window=k_period).min()
    high_max = df["high"].rolling(window=k_period).max()
    df["stoch_k"] = 100 * (df["close"] - low_min) / (high_max - low_min + 1e-10)
    df["stoch_d"] = df["stoch_k"].rolling(window=d_period).mean()
    return df


def calculate_momentum(df: pd.DataFrame, period=10) -> pd.DataFrame:
    """Price momentum — how fast price is moving."""
    df["momentum"] = df["close"] - df["close"].shift(period)
    df["mom_ma"]   = df["momentum"].rolling(5).mean()
    return df


def auto_select_expiry(df: pd.DataFrame, confidence: int) -> str:
    """
    Auto-select binary expiry based on ATR volatility + signal confidence.
    Returns expiry key: '1m', '2m', or '5m'
    """
    try:
        atr    = df["atr"].iloc[-1] if "atr" in df.columns else None
        price  = df["close"].iloc[-1]

        if atr is None:
            atr_pct = 0.003
        else:
            atr_pct = atr / price  # ATR as % of price

        # High volatility + high confidence → fast expiry
        if atr_pct > 0.005 and confidence >= 78:
            return "1m"
        # Medium volatility or good confidence → 2 min
        elif atr_pct > 0.003 or confidence >= 65:
            return "2m"
        # Low volatility / lower confidence → 5 min
        else:
            return "5m"
    except Exception:
        return "5m"   # safe default


def analyze_binary_signal(df: pd.DataFrame, expiry_key: str) -> dict:
    """
    Full binary options analysis.
    Returns CALL, PUT, or WAIT with confidence score.
    """
    result = {
        "direction": "WAIT",
        "confidence": 0,
        "reasons":    [],
        "expiry":     BINARY_EXPIRIES[expiry_key]["label"],
        "payout":     0,
    }

    if df is None or len(df) < 20:
        return result

    # Calculate all indicators
    df = calculate_indicators(df)
    df = calculate_stochastic(df)
    df = calculate_momentum(df)

    latest   = df.iloc[-1]
    prev     = df.iloc[-2]
    call_pts = 0
    put_pts  = 0

    # ── RSI ───────────────────────────────────────────────────
    rsi = latest["rsi"]
    if rsi < 30:
        call_pts += 20
        result["reasons"].append(f"RSI {rsi:.0f} — oversold 🔥")
    elif rsi < 40:
        call_pts += 10
        result["reasons"].append(f"RSI {rsi:.0f} — approaching oversold")
    elif rsi > 70:
        put_pts += 20
        result["reasons"].append(f"RSI {rsi:.0f} — overbought 🔥")
    elif rsi > 60:
        put_pts += 10
        result["reasons"].append(f"RSI {rsi:.0f} — approaching overbought")

    # ── Stochastic ────────────────────────────────────────────
    stoch_k = latest["stoch_k"]
    stoch_d = latest["stoch_d"]
    if stoch_k < 20 and stoch_d < 20:
        call_pts += 20
        result["reasons"].append(f"Stochastic {stoch_k:.0f} — oversold zone")
    elif stoch_k > 80 and stoch_d > 80:
        put_pts += 20
        result["reasons"].append(f"Stochastic {stoch_k:.0f} — overbought zone")

    # Stochastic crossover
    if prev["stoch_k"] <= prev["stoch_d"] and latest["stoch_k"] > latest["stoch_d"] and stoch_k < 50:
        call_pts += 15
        result["reasons"].append("Stochastic bullish cross ⬆️")
    elif prev["stoch_k"] >= prev["stoch_d"] and latest["stoch_k"] < latest["stoch_d"] and stoch_k > 50:
        put_pts += 15
        result["reasons"].append("Stochastic bearish cross ⬇️")

    # ── Bollinger Bands ───────────────────────────────────────
    bb_pct = latest["bb_pct"]
    if bb_pct <= 0.05:
        call_pts += 15
        result["reasons"].append("Price at BB lower band — bounce zone")
    elif bb_pct >= 0.95:
        put_pts += 15
        result["reasons"].append("Price at BB upper band — rejection zone")

    # BB squeeze breakout direction
    bb_width   = latest["bb_width"]
    avg_width  = df["bb_width"].rolling(20).mean().iloc[-1]
    if bb_width < avg_width * 0.5:
        # Squeeze — use momentum to predict direction
        if latest["momentum"] > 0:
            call_pts += 10
            result["reasons"].append("BB Squeeze + bullish momentum 🔔")
        else:
            put_pts += 10
            result["reasons"].append("BB Squeeze + bearish momentum 🔔")

    # ── MACD ──────────────────────────────────────────────────
    if prev["macd"] <= prev["macd_signal"] and latest["macd"] > latest["macd_signal"]:
        call_pts += 15
        result["reasons"].append("MACD bullish crossover")
    elif prev["macd"] >= prev["macd_signal"] and latest["macd"] < latest["macd_signal"]:
        put_pts += 15
        result["reasons"].append("MACD bearish crossover")
    elif latest["macd_hist"] > 0 and latest["macd_hist"] > prev["macd_hist"]:
        call_pts += 8
        result["reasons"].append("MACD histogram growing bullish")
    elif latest["macd_hist"] < 0 and latest["macd_hist"] < prev["macd_hist"]:
        put_pts += 8
        result["reasons"].append("MACD histogram growing bearish")

    # ── EMA trend ─────────────────────────────────────────────
    if latest["ema_fast"] > latest["ema_slow"]:
        call_pts += 8
        result["reasons"].append("EMA trend: Bullish")
    else:
        put_pts += 8
        result["reasons"].append("EMA trend: Bearish")

    # ── Momentum ──────────────────────────────────────────────
    if latest["momentum"] > 0 and latest["mom_ma"] > 0:
        call_pts += 8
        result["reasons"].append("Price momentum: Bullish")
    elif latest["momentum"] < 0 and latest["mom_ma"] < 0:
        put_pts += 8
        result["reasons"].append("Price momentum: Bearish")

    # ── Candle patterns (fast binary patterns) ────────────────
    patterns = detect_candle_patterns(df)
    for p in patterns:
        if p["direction"] == "BUY":
            call_pts += 10
            result["reasons"].append("🕯 " + p["name"])
        elif p["direction"] == "SELL":
            put_pts += 10
            result["reasons"].append("🕯 " + p["name"])

    # ── Support & Resistance ──────────────────────────────────
    sr = detect_support_resistance(df)
    if sr["near_support"]:
        call_pts += 10
        result["reasons"].append(f"At key support {sr['support']:.2f}")
    if sr["near_resistance"]:
        put_pts += 10
        result["reasons"].append(f"At key resistance {sr['resistance']:.2f}")

    # ── Decision ──────────────────────────────────────────────
    total = call_pts + put_pts
    if total == 0:
        return result

    if call_pts > put_pts:
        confidence = min(int((call_pts / total) * 100), 100)
        if confidence >= 52:
            result["direction"]  = "CALL"
            result["confidence"] = confidence
    elif put_pts > call_pts:
        confidence = min(int((put_pts / total) * 100), 100)
        if confidence >= 52:
            result["direction"]  = "PUT"
            result["confidence"] = confidence

    # Auto-select expiry + quality info (no blocking — let scan_binary decide)
    vol    = check_volume_quality(df)
    regime = detect_market_regime(df)
    result["auto_expiry"] = auto_select_expiry(df, result["confidence"]) if result["direction"] in ["CALL","PUT"] else "5m"
    result["volume"]  = vol
    result["regime"]  = regime
    result["grade"]   = get_signal_grade(
        int(result["confidence"] / 10), regime, vol,
        {"count": 1, "total": 1, "label": "Binary"}
    )

    return result


def format_binary_signal(result: dict, symbol: str, display: str, expiry_key: str = None, broker_tag: str = "") -> str:
    """Format binary signal message — auto expiry based on ATR + confidence."""
    direction  = result["direction"]
    confidence = result["confidence"]
    # Use auto-selected expiry from analysis, fallback to passed key or default
    auto_key   = result.get("auto_expiry", expiry_key or "5m")
    expiry     = BINARY_EXPIRIES[auto_key]
    payout     = POCKET_OPTION_SYMBOLS.get(symbol, {}).get("payout", 80)
    reasons    = result["reasons"]

    # ── Time calculations ─────────────────────────────────────
    now          = datetime.now(timezone.utc)
    valid_window = 2   # minutes to place the trade
    valid_until  = now + timedelta(minutes=valid_window)
    expiry_at    = now + timedelta(seconds=expiry["seconds"] + valid_window * 60)

    place_time   = to_user_time(now)
    valid_time   = to_user_time(valid_until)
    expiry_time  = to_user_time(expiry_at)
    time_now_str = to_user_time(now)

    emoji      = "🟢" if direction == "CALL" else "🔴"
    de         = "⬆️" if direction == "CALL" else "⬇️"
    action     = "CALL (UP ⬆️)" if direction == "CALL" else "PUT (DOWN ⬇️)"
    filled     = int(confidence / 10)
    conf_bar   = "█" * filled + "░" * (10 - filled)
    reasons_txt = chr(10) + "   • ".join(reasons[:6])

    if confidence >= 80:
        conf_label = "🔥 VERY HIGH — Strong setup"
    elif confidence >= 70:
        conf_label = "💪 HIGH — Good setup"
    elif confidence >= 60:
        conf_label = "✅ MODERATE — Decent setup"
    else:
        conf_label = "⚠️ LOW — Be careful"

    nl = chr(10)
    msg = (
        emoji + emoji + " *" + display + " — " + action + "* " + emoji + emoji + nl + nl +

        "━━━━━━━━━━━━━━━━━━━━" + nl +
        "📊 *" + display + "*" + nl +
        "⏰ *Place trade at:*  `" + place_time + " UTC`" + nl +
        "⌛ *Valid until:*     `" + valid_time + " UTC`  ← deadline!" + nl +
        "⌛ *Expiry at:*       `" + expiry_time + " UTC`" + nl +
        "🔴 *Direction:*      *" + direction + " " + de + "*" + nl +
        "━━━━━━━━━━━━━━━━━━━━" + nl + nl +

        "⏱ *Expiry:* " + expiry["emoji"] + " `" + expiry["label"] + "` _(auto-selected)_" + nl +
        "💵 *Payout:*         `+" + str(payout) + "%` profit if correct" + nl + nl +

        "📊 *Confidence:* " + conf_bar + " *" + str(confidence) + "%*" + nl +
        conf_label + nl + nl +

        "⚠️ *PLACE BEFORE " + valid_time + " — signal expires after!*" + nl + nl +

        "📋 *Why " + direction + "?*" + nl +
        "   • " + reasons_txt + nl + nl +

        (broker_tag + nl + nl if broker_tag else "") +
        "📱 *Steps:*" + nl +
        "   1️⃣ Open your broker app NOW" + nl +
        "   2️⃣ Select *" + display + "*" + nl +
        "   3️⃣ Set timer: *" + expiry["label"] + "*" + nl +
        "   4️⃣ Tap *" + direction + "* " + de + nl +
        "   5️⃣ Enter your stake" + nl + nl +

        "🕐 Signal sent: `" + time_now_str + "`" + nl +
        "⚠️ _Never stake more than 2-5% of your balance per trade_"
    )
    return msg


def is_weekend_otc():
    """True if forex market is closed — use OTC pairs."""
    now = get_utc_now()
    # Friday 21:00 UTC to Sunday 23:59 UTC = weekend OTC mode
    if now.weekday() == 4 and now.hour >= 21:   return True
    if now.weekday() == 5:                       return True
    if now.weekday() == 6:                       return True
    return False


def get_active_symbols() -> list:
    """
    Return the correct symbol list for the current market mode.
    Binary mode uses get_active_binary_symbols() keys.
    All other modes use MARKET_MODES symbols list.
    """
    if active_market == "binary":
        return list(get_active_binary_symbols().keys())
    return MARKET_MODES[active_market]["symbols"]


def get_active_binary_symbols():
    """
    Return symbol dict based on selected broker mode.
    - po_regular: live market pairs (weekdays only — auto-switch to OTC on weekend)
    - po_otc:     synthetic OTC pairs (higher payout, available anytime)
    - quotex:     Quotex OTC pairs (always available)
    """
    weekend = is_weekend_otc()

    if active_broker == "quotex":
        # Quotex — OTC only, always
        return {k: v for k, v in QUOTEX_SYMBOLS.items()}

    elif active_broker == "po_otc":
        # Pocket Option OTC — higher payouts, anytime
        return {k: v for k, v in POCKET_OPTION_SYMBOLS.items() if v["otc"]}

    elif active_broker == "po_regular":
        if weekend:
            # Market closed — auto-switch to PO OTC silently
            logger.info("⚠️ Weekend detected — auto-switching PO Regular → PO OTC")
            return {k: v for k, v in POCKET_OPTION_SYMBOLS.items() if v["otc"]}
        else:
            # Weekday — regular live pairs
            return {k: v for k, v in POCKET_OPTION_SYMBOLS.items() if not v["otc"]}

    # Fallback
    return {k: v for k, v in POCKET_OPTION_SYMBOLS.items() if v["otc"]}


def get_broker_tag(symbol_key: str) -> str:
    """Return broker tag for signal — shows broker, type and payout info."""
    otc     = symbol_key.endswith("-OTC")
    weekend = is_weekend_otc()
    info    = POCKET_OPTION_SYMBOLS.get(symbol_key) or QUOTEX_SYMBOLS.get(symbol_key, {})
    payout  = info.get("payout", 80)

    if active_broker == "po_regular":
        mode = "🌙 Auto-switched to OTC (weekend)" if weekend else "📅 Regular Market"
        return "💰 *Broker:* Pocket Option | " + mode + " | Payout: `" + str(payout) + "%`"
    elif active_broker == "po_otc":
        return "💎 *Broker:* Pocket Option OTC | Higher Payout: `" + str(payout) + "%`"
    elif active_broker == "quotex":
        qx_info = QUOTEX_SYMBOLS.get(symbol_key, {})
        qx_pay  = qx_info.get("payout", payout)
        return "📊 *Broker:* Quotex OTC | Payout: `" + str(qx_pay) + "%`"
    return "💰 *Broker:* Pocket Option | Payout: `" + str(payout) + "%`"


def sort_symbols_by_trend(symbols: dict) -> list:
    """
    Return symbol keys in standard order.
    No API calls here — avoids burning rate limit before the actual scan.
    Major pairs (EUR, GBP, USD) go first as they tend to be most active.
    """
    priority = ["EUR/USD", "GBP/USD", "USD/JPY", "AUD/USD", "USD/CAD",
                "EUR/USD-OTC", "GBP/USD-OTC", "USD/JPY-OTC", "AUD/USD-OTC"]
    result = []
    # Prioritised pairs first
    for key in priority:
        if key in symbols:
            result.append(key)
    # Rest in original order
    for key in symbols:
        if key not in result:
            result.append(key)
    return result


async def scan_binary_signals(context, manual: bool = False):
    """
    Binary scan — sends ONLY the single best signal per cycle.
    Scans TOP_BINARY_PAIRS only to save API calls.
    Manual: triggered by user. Auto: runs every 5 minutes.
    """
    in_blackout, window = is_news_blackout()
    if in_blackout and not manual:
        logger.info(f"⏸ Binary scan paused — news blackout: {window}")
        return

    expiry_key  = active_binary_expiry
    expiry      = BINARY_EXPIRIES[expiry_key]
    all_symbols = get_active_binary_symbols()
    weekend     = is_weekend_otc()
    broker      = BROKERS[active_broker]
    nl          = chr(10)
    send_time   = datetime.now(timezone.utc)

    if not all_symbols:
        if manual:
            send_message("⚡ *Binary Scan*" + nl + "No assets available for " + broker["label"])
        return

    # Use only top 10 pairs (fewer API calls, faster scan)
    otc_suffix = "-OTC" if weekend else ""
    scan_keys  = []
    for pair in TOP_BINARY_PAIRS:
        key = pair + otc_suffix
        if key in all_symbols:
            scan_keys.append(key)
        elif pair in all_symbols:
            scan_keys.append(pair)
    if not scan_keys:
        scan_keys = list(all_symbols.keys())[:10]

    logger.info(f"⚡ Binary scan: {len(scan_keys)} pairs | broker={active_broker} | otc={weekend}")

    if manual:
        send_message(
            "🔍 *Binary Scan Started*" + nl + nl +
            broker["emoji"] + " Broker: *" + broker["label"] + "*" + nl +
            ("🌙 OTC Mode" if weekend else "📅 Regular Mode") + nl +
            "⚡ Expiry: " + expiry["label"] + nl +
            "⏱ Checking " + str(len(scan_keys)) + " pairs..." + nl +
            "🕐 " + to_user_time()
        )

    # Scan all pairs — collect signals with confidence
    candidates = []

    for symbol in scan_keys:
        try:
            info      = all_symbols[symbol]
            base_key  = symbol.replace("-OTC", "")
            base_info = BINARY_PAIRS.get(base_key, {})
            td_sym    = base_info.get("td") or info.get("td")
            display   = info.get("display", base_key)
            candle_tf = expiry["candles"]

            logger.info(f"Binary scanning: {display}")

            # Fetch data
            df = None
            if base_key in SYMBOLS:
                df = fetch_data(base_key, interval=candle_tf)
            elif td_sym:
                time.sleep(0.5)
                df = fetch_data_twelvedata(td_sym, interval=candle_tf)

            # Alpha Vantage fallback
            if (df is None or len(df) < 20) and td_sym:
                logger.warning(f"TD failed for binary {display} — trying Alpha Vantage")
                df = fetch_data_alpha_vantage(td_sym, interval=candle_tf)

            if df is None or len(df) < 20:
                logger.warning(f"Binary: no data for {display}")
                continue

            result = analyze_binary_signal(df, expiry_key)
            logger.info(f"Binary {display}: {result['direction']} | {result['confidence']}%")

            if result["direction"] in ["CALL", "PUT"]:
                candidates.append({
                    "symbol":   symbol,
                    "base_key": base_key,
                    "display":  display,
                    "result":   result,
                    "info":     info,
                    "td_sym":   td_sym,
                })

        except Exception as e:
            logger.error(f"Binary scan error {symbol}: {e}")
            continue

    # Pick BEST signal — highest confidence
    if not candidates:
        if manual:
            send_message(
                "📊 *Binary Scan — No Signals*" + nl + nl +
                "No confident setups found in top 10 pairs." + nl +
                broker["emoji"] + " " + broker["label"] + " | " +
                ("🌙 OTC" if weekend else "📅 Regular") + nl +
                "⚡ Expiry: " + expiry["label"] + nl +
                "🕐 " + to_user_time()
            )
        return

    # Sort by confidence — take the best one
    candidates.sort(key=lambda x: x["result"]["confidence"], reverse=True)
    best = candidates[0]

    # Only send if confidence >= 65%
    MIN_BINARY_CONF = 55
    if best["result"]["confidence"] < MIN_BINARY_CONF:
        if manual:
            best_conf = best["result"]["confidence"]
            send_message(
                "📊 *Binary Scan — No Signals*" + nl + nl +
                "Best setup: " + best["display"] + " at " + str(best_conf) + "% conf" + nl +
                "Minimum required: " + str(MIN_BINARY_CONF) + "%" + nl + nl +
                "⏳ Waiting for stronger setup..." + nl +
                "🕐 " + to_user_time()
            )
        return

    # Send the single best signal
    symbol   = best["symbol"]
    base_key = best["base_key"]
    display  = best["display"]
    result   = best["result"]
    info     = best["info"]
    td_sym   = best["td_sym"]

    broker_tag = get_broker_tag(symbol)
    auto_key   = result.get("auto_expiry", expiry_key)
    exp_used   = BINARY_EXPIRIES[auto_key]
    msg        = format_binary_signal(result, symbol, display, auto_key, broker_tag)

    send_message(msg)

    # Get entry price
    if base_key in SYMBOLS:
        price_data = get_current_price(base_key)
    elif td_sym:
        price_data = get_current_price_td(td_sym)
    else:
        price_data = None
    entry_price = price_data["price"] if price_data else 0

    active_binary_trades.append({
        "symbol":      symbol,
        "base_key":    base_key,
        "display":     display,
        "direction":   result["direction"],
        "entry":       entry_price,
        "expiry_s":    exp_used["seconds"],
        "payout":      info.get("payout", 80),
        "open_time":   send_time.timestamp(),
        "valid_until": (send_time + timedelta(minutes=2)).timestamp(),
        "valid_str":   (send_time + timedelta(minutes=2)).strftime("%H:%M UTC"),
        "notified":    False,
        "broker_tag":  broker_tag,
    })
    binary_performance["total"]   += 1
    binary_performance["pending"] += 1

    dir_emoji = "🟢" if result["direction"] == "CALL" else "🔴"
    logger.info(f"✅ Binary signal sent: {display} {result['direction']} {result['confidence']}%")


async def auto_binary_queue_scan(context):
    """Auto binary queue — runs every 5 minutes, sends best signal if conf >= 65%."""
    global active_scan
    # Only run if binary market mode is active or all mode
    if active_market not in ["binary", "all"]:
        return
    logger.info("⚡ Auto binary queue scan running...")
    await scan_binary_signals(context, manual=False)


async def check_binary_results(context):
    """Check if binary trades have expired and notify result."""
    now    = datetime.now(timezone.utc).timestamp()
    closed = []

    for trade in active_binary_trades:
        elapsed = now - trade["open_time"]
        if elapsed < trade["expiry_s"]:
            # Not expired yet — send reminder at halfway point
            if not trade.get("halfway_notified") and elapsed >= trade["expiry_s"] * 0.5:
                remaining   = int(trade["expiry_s"] - elapsed)
                expiry_at   = datetime.fromtimestamp(
                    trade["open_time"] + trade["expiry_s"], tz=timezone.utc
                ).strftime("%H:%M:%S")
                nl = chr(10)
                send_message(
                    "⏳ *" + trade["display"] + " " + trade["direction"] + " — Halfway!*" + nl + nl +
                    "⌛ Time remaining: `" + str(remaining) + " seconds`" + nl +
                    "🏁 Expires at: `" + expiry_at + " UTC`" + nl + nl +
                    "👀 Watch your Pocket Option trade..."
                )
                trade["halfway_notified"] = True
            continue

        # Check if entry window expired (user missed it)
        if not trade.get("window_expired_notified"):
            valid_until = trade.get("valid_until", trade["open_time"] + 120)
            if now > valid_until and elapsed < trade["expiry_s"]:
                trade["window_expired_notified"] = True
                send_message(
                    "⏰ *Signal Window Expired!*" + chr(10) + chr(10) +
                    trade["display"] + " " + trade["direction"] + " signal is now invalid." + chr(10) +
                    "If you placed the trade — keep holding until `" + trade.get("valid_str","expiry") + "`" + chr(10) +
                    "If you missed it — _wait for the next signal!_"
                )

        # Trade expired — check result
        # Use correct price source: forex binary pairs need Twelve Data
        base_key   = trade.get("base_key", trade["symbol"].replace("-OTC",""))
        base_info  = BINARY_PAIRS.get(base_key, {})
        td_sym     = base_info.get("td")

        if base_key in SYMBOLS:
            price_data = get_current_price(base_key)
        elif td_sym:
            price_data = get_current_price_td(td_sym)
        else:
            price_data = None

        if not price_data:
            continue

        current = price_data["price"]
        entry   = trade["entry"]
        nl      = chr(10)

        won = (trade["direction"] == "CALL" and current > entry) or               (trade["direction"] == "PUT"  and current < entry)

        binary_performance["pending"] -= 1
        if won:
            binary_performance["wins"] += 1
            send_message(
                "✅ *BINARY WIN!* 🎉" + nl + nl +
                trade["display"] + " " + trade["direction"] + " expired!" + nl +
                "Entry: `" + str(round(entry, 5)) + "`" + nl +
                "Close: `" + str(round(current, 5)) + "`" + nl +
                "Payout: `+" + str(trade["payout"]) + "%` profit 💰" + nl + nl +
                "Win rate: `" + str(round(binary_performance["wins"] / max(binary_performance["total"] - binary_performance["pending"], 1) * 100, 1)) + "%`"
            )
        else:
            binary_performance["losses"] += 1
            send_message(
                "❌ *BINARY LOSS*" + nl + nl +
                trade["display"] + " " + trade["direction"] + " expired against us." + nl +
                "Entry: `" + str(round(entry, 5)) + "`" + nl +
                "Close: `" + str(round(current, 5)) + "`" + nl + nl +
                "_Stay disciplined — next signal coming!_"
            )

        closed.append(trade)
        binary_results.insert(0, {
            "symbol":    trade["display"],
            "direction": trade["direction"],
            "result":    "WIN" if won else "LOSS",
            "entry":     entry,
            "close":     current,
            "time":      datetime.now().strftime("%m/%d %H:%M"),
        })
        if len(binary_results) > 50:
            binary_results.pop()

    for t in closed:
        active_binary_trades.remove(t)


def to_user_time(dt=None) -> str:
    """Convert UTC datetime to user's local time string."""
    if dt is None:
        dt = datetime.now(timezone.utc)
    elif dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    local = dt.astimezone(user_tz_object)
    return local.strftime("%H:%M") + " " + user_timezone.split("/")[-1]


def to_user_datetime(dt=None) -> str:
    """Full datetime in user timezone."""
    if dt is None:
        dt = datetime.now(timezone.utc)
    elif dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    local = dt.astimezone(user_tz_object)
    return local.strftime("%Y-%m-%d %H:%M") + " " + user_timezone.split("/")[-1]


def make_tz_region_keyboard():
    """Keyboard to pick timezone region."""
    rows = []
    for key, val in TIMEZONE_REGIONS.items():
        rows.append([InlineKeyboardButton(val["label"], callback_data="tz_region_" + key)])
    rows.append([InlineKeyboardButton("🕐 UTC (default)", callback_data="tz_set_UTC")])
    return InlineKeyboardMarkup(rows)


def make_tz_zone_keyboard(region_key: str):
    """Keyboard to pick specific timezone within a region."""
    region = TIMEZONE_REGIONS[region_key]
    rows   = []
    for tz_key, tz_label in region["zones"].items():
        rows.append([InlineKeyboardButton(tz_label, callback_data="tz_set_" + tz_key)])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="tz_back")])
    return InlineKeyboardMarkup(rows)


def rebuild_symbol_queue():
    """Rebuild the rotation queue based on active market mode."""
    global symbol_queue, symbol_queue_idx
    mode_symbols  = get_active_symbols()
    forex_open, _ = is_forex_open()
    new_queue     = []
    for symbol in mode_symbols:
        if active_market == "binary":
            new_queue.append(symbol)
            continue
        info = SYMBOLS.get(symbol)
        if not info:
            continue
        if info["type"] == "forex" and not forex_open:
            continue
        new_queue.append(symbol)
    # Only reset index if queue changed
    if new_queue != symbol_queue:
        symbol_queue     = new_queue
        symbol_queue_idx = 0
        logger.info(f"🔄 Queue rebuilt: {[SYMBOLS[s]['display'] for s in symbol_queue]}")


async def scan_all_symbols(context, manual: bool = False):
    """
    Manual scan — scans ALL symbols in active market at once.
    Binary mode delegates to scan_binary_signals.
    Auto scan uses check_signals() with rotation instead.
    """
    global symbol_queue, symbol_queue_idx
    in_blackout, bw  = is_news_blackout()
    nl               = chr(10)

    if in_blackout and not manual:
        return

    # ── Binary mode — use dedicated binary scanner ────────────
    if active_market == "binary":
        await scan_binary_signals(context, manual=True)
        return

    forex_open, _  = is_forex_open()
    mode_symbols   = get_active_symbols()
    signals_found  = 0
    scan_report    = []   # Per-symbol result summary

    send_message(
        "🔍 *Manual Scan Started*" + nl + nl +
        MARKET_MODES[active_market]["emoji"] + " Mode: *" + MARKET_MODES[active_market]["label"] + "*" + nl +
        "⏱ Checking all " + str(len(mode_symbols)) + " symbols..." + nl +
        "🕐 " + to_user_time()
    )

    for symbol in mode_symbols:
        info = SYMBOLS.get(symbol)
        if not info:
            continue
        display     = info["display"]
        symbol_type = info["type"]

        if symbol_type == "forex" and not forex_open:
            logger.info(f"⏸ Skipping {display} — Forex closed")
            continue

        try:
            mode_cfg = SCAN_MODES[active_scan["tf"]]
            df = fetch_data(symbol, interval=mode_cfg["interval"])
            if df is None or len(df) < 50:
                logger.warning(f"Not enough data for {display}")
                scan_report.append("❓ " + display + " — No data")
                continue

            df  = calculate_indicators(df)
            mtf = multi_timeframe_analysis(symbol)
            sig = generate_signal(df, mtf)

            regime = sig.get("regime", {})
            vol    = sig.get("volume", {})
            adx    = regime.get("adx", 0)
            vr     = vol.get("ratio", 1.0)

            if sig["signal"] in ["BUY", "SELL"]:
                sl_price = sig["price"] - info["sl"] if sig["signal"] == "BUY" else sig["price"] + info["sl"]
                tp_price = sig["price"] + info["sl"] * RISK_REWARD if sig["signal"] == "BUY" else sig["price"] - info["sl"] * RISK_REWARD
                msg      = format_signal_message(sig, symbol, display)

                send_signal_with_enter_button(
                    sig["signal"], symbol, display,
                    sig["price"], round(sl_price, 5), round(tp_price, 5),
                    msg
                )

                signals_found += 1
                grade = sig.get("grade", "")
                scan_report.append(
                    ("🟢" if sig["signal"] == "BUY" else "🔴") +
                    " " + display + " — " + sig["signal"] + " | " + grade
                )
                save_to_history(
                    sig["signal"], display, symbol, sig["price"],
                    sig["prob"]["score"], sl_price, tp_price, sig["conf"]
                )
            else:
                # Show WHY signal was blocked
                reason = sig["grade"] if sig.get("grade") else "HOLD"
                adx_str = " ADX " + str(adx) if adx else ""
                vol_str = " Vol " + str(vr) + "x" if vr else ""
                scan_report.append("⚪ " + display + " — " + reason + adx_str + vol_str)
                logger.info(f"📊 {display}: {reason}")

        except Exception as e:
            import traceback
            logger.error("Manual scan error %s: %s\n%s", display, e, traceback.format_exc())
            scan_report.append("⚠️ " + display + " — Error: " + str(e)[:60])

    # Build scan summary report
    report_lines = chr(10).join(scan_report)
    if signals_found == 0:
        send_message(
            "📊 *Scan Report — No Signals*" + nl + nl +
            report_lines + nl + nl +
            "🔍 *Why no signals?*" + nl +
            "   • ⏸ Blocked = ranging market (ADX < 20)" + nl +
            "   • ❌ Blocked = low volume" + nl +
            "   • ⚪ HOLD = score too low" + nl + nl +
            "🕐 " + to_user_time()
        )
    else:
        send_message(
            "✅ *Scan Complete — " + str(signals_found) + " Signal(s)*" + nl + nl +
            report_lines + nl + nl +
            "🕐 " + to_user_time()
        )

# ============================================================
#   USER TRADE MONITOR
# ============================================================

def send_signal_with_enter_button(signal: str, symbol: str, display: str,
                                   entry: float, sl: float, tp: float,
                                   msg: str):
    """
    Send signal message with an inline "I Entered This Trade" button.
    Stores full trade data in pending_signals dict and uses short numeric ID
    in callback_data to stay within Telegram's 64-char limit.
    """
    global pending_signal_seq
    pending_signal_seq += 1
    sid = pending_signal_seq   # short numeric ID

    # Store full data — callback only carries the short ID
    pending_signals[sid] = {
        "signal":  signal,
        "symbol":  symbol,
        "display": display,
        "entry":   entry,
        "sl":      sl,
        "tp":      tp,
    }

    # Trim old entries (keep last 50)
    if len(pending_signals) > 50:
        oldest = sorted(pending_signals.keys())[0]
        del pending_signals[oldest]

    cb_data  = f"trade_enter_{sid}"   # Max ~18 chars — well within 64 limit
    keyboard = {
        "inline_keyboard": [[
            {"text": "✅ I Entered This Trade", "callback_data": cb_data},
        ]]
    }


    # Fallback: text only
    url  = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
    import json
    resp = requests.post(url, json={
        "chat_id":      CHAT_ID,
        "text":         msg,
        "parse_mode":   "Markdown",
        "reply_markup": keyboard,
    }, timeout=10)
    return resp.json().get("result", {}).get("message_id")


def calc_pnl(direction: str, entry: float, current: float, symbol: str) -> dict:
    """
    Calculate P&L using correct metric per asset type.
    - Forex/Gold: pips
    - Crypto:     USD change + %
    """
    info      = SYMBOLS.get(symbol, {})
    asset_type = info.get("type", "crypto")

    if direction == "BUY":
        raw_pnl = current - entry
    else:
        raw_pnl = entry - current

    pct_pnl  = (raw_pnl / entry) * 100
    positive = raw_pnl > 0

    if asset_type == "forex":
        # Forex: pips (gold = 0.01 pip, others = 0.0001)
        pip_size = 0.01 if symbol == "XAU/USD" else 0.0001
        pips     = raw_pnl / pip_size
        pnl_str  = ("+" if positive else "") + str(round(pips, 1)) + " pips"
        short    = ("+" if positive else "") + str(round(pips, 1)) + " pips"
    else:
        # Crypto: dollar value change + %
        usd_change = raw_pnl   # per unit (e.g. per BTC)
        pnl_str    = ("+" if positive else "") + "$" + "{:,.2f}".format(abs(usd_change)) + " per coin"
        short      = ("+" if positive else "-") + "$" + "{:,.2f}".format(abs(usd_change))

    pct_str = ("+" if positive else "") + str(round(pct_pnl, 3)) + "%"

    return {
        "pnl_raw":  raw_pnl,
        "pnl_pct":  round(pct_pnl, 3),
        "pnl_str":  pnl_str,
        "pct_str":  pct_str,
        "short":    short,
        "positive": positive,
        "type":     asset_type,
    }


def update_trailing_stop(trade: dict, current_price: float) -> dict:
    """
    Update trailing stop based on price movement.
    Trail by 50% of initial SL distance.
    Returns updated trade dict.
    """
    direction = trade["direction"]
    entry     = trade["entry"]
    sl_init   = trade["sl_initial"]
    trail_gap = abs(trade["tp"] - entry) * 0.3   # Trail at 30% of TP distance

    if direction == "BUY":
        # Track highest price seen
        if current_price > trade.get("extreme", entry):
            trade["extreme"] = current_price
            # Move SL up — but never below original SL
            new_sl = current_price - trail_gap
            if new_sl > trade["trail_sl"]:
                trade["trail_sl"] = round(new_sl, 5)
                return trade, True   # SL moved
    else:
        # Track lowest price seen
        if current_price < trade.get("extreme", entry):
            trade["extreme"] = current_price
            # Move SL down — but never above original SL
            new_sl = current_price + trail_gap
            if new_sl < trade["trail_sl"]:
                trade["trail_sl"] = round(new_sl, 5)
                return trade, True   # SL moved

    return trade, False   # No change


def analyze_trade_health(trade: dict, current_price: float, symbol: str, df=None) -> dict:
    """
    Analyze whether an open trade should be held or exited.
    Fetches fresh data and re-runs signal engine against the trade direction.
    Returns: {level, headline, reasons, recommendation}
    Levels: "ok" | "warning" | "danger"
    """
    direction = trade["direction"]
    entry     = trade["entry"]
    sl        = trade["trail_sl"]
    tp        = trade["tp"]

    reasons  = []
    score    = 0   # Negative = bearish for BUY trade, positive = bearish for SELL

    try:
        # Fetch fresh candle data
        info     = SYMBOLS.get(symbol, {})
        interval = SCAN_MODES[active_scan["tf"]]["interval"]
        df       = fetch_data(symbol, interval=interval)
        if df is None or len(df) < 30:
            return {"level": "ok", "headline": "", "reasons": [], "recommendation": "Hold"}
        df = calculate_indicators(df)
    except Exception:
        return {"level": "ok", "headline": "", "reasons": [], "recommendation": "Hold"}

    latest = df.iloc[-1]
    prev   = df.iloc[-2]
    rsi    = latest["rsi"]

    # ── 1. Trend structure reversed ───────────────────────────
    try:
        trend = detect_trend_structure(df)
        if direction == "BUY" and trend["structure"] == "BEARISH":
            score += 2; reasons.append("Trend structure turned BEARISH")
        elif direction == "SELL" and trend["structure"] == "BULLISH":
            score += 2; reasons.append("Trend structure turned BULLISH")
    except Exception:
        pass

    # ── 2. Break of Structure against trade ──────────────────
    try:
        structure = detect_market_structure(df)
        if direction == "BUY" and structure["bos"] and structure["bos"]["direction"] == "BEARISH":
            score += 3; reasons.append("BOS broke BEARISH — structure changed against BUY")
        elif direction == "SELL" and structure["bos"] and structure["bos"]["direction"] == "BULLISH":
            score += 3; reasons.append("BOS broke BULLISH — structure changed against SELL")
        # CHoCH (stronger reversal signal)
        if direction == "BUY" and structure["choch"] and structure["choch"]["direction"] == "BEARISH":
            score += 3; reasons.append("CHoCH — potential trend reversal against your BUY")
        elif direction == "SELL" and structure["choch"] and structure["choch"]["direction"] == "BULLISH":
            score += 3; reasons.append("CHoCH — potential trend reversal against your SELL")
    except Exception:
        pass

    # ── 3. RSI divergence forming against trade ───────────────
    try:
        divergence = detect_rsi_divergence(df)
        if direction == "BUY" and divergence["type"] == "BEARISH":
            score += 3; reasons.append("Bearish RSI divergence forming — momentum weakening")
        elif direction == "SELL" and divergence["type"] == "BULLISH":
            score += 3; reasons.append("Bullish RSI divergence forming — momentum weakening")
    except Exception:
        pass

    # ── 4. RSI extreme against trade ─────────────────────────
    if direction == "BUY" and rsi > 75:
        score += 1; reasons.append(f"RSI {rsi:.1f} — extremely overbought, reversal risk")
    elif direction == "SELL" and rsi < 25:
        score += 1; reasons.append(f"RSI {rsi:.1f} — extremely oversold, reversal risk")

    # ── 5. MACD cross against trade ───────────────────────────
    if direction == "BUY" and prev["macd"] >= prev["macd_signal"] and latest["macd"] < latest["macd_signal"]:
        score += 2; reasons.append("MACD crossed bearish — momentum shifting down")
    elif direction == "SELL" and prev["macd"] <= prev["macd_signal"] and latest["macd"] > latest["macd_signal"]:
        score += 2; reasons.append("MACD crossed bullish — momentum shifting up")

    # ── 6. Price approaching SL ───────────────────────────────
    sl_dist_total = abs(entry - trade["sl_initial"])
    sl_dist_now   = abs(current_price - sl)
    if sl_dist_total > 0:
        pct_to_sl = 1 - (sl_dist_now / sl_dist_total)
        if pct_to_sl >= 0.75:
            score += 2; reasons.append(f"Price is {int(pct_to_sl*100)}% of the way to SL — high risk zone")
        elif pct_to_sl >= 0.5:
            score += 1; reasons.append(f"Price is {int(pct_to_sl*100)}% of the way to SL — monitor closely")

    # ── 7. MTF alignment flipped ─────────────────────────────
    try:
        mtf = multi_timeframe_analysis(symbol)
        opposite = "SELL" if direction == "BUY" else "BUY"
        if mtf["overall"] == opposite:
            score += 2; reasons.append(f"Higher timeframes now aligned {opposite} against your {direction}")
    except Exception:
        pass

    # ── 8. Profit reversal detection ─────────────────────────
    # How far price has moved from entry toward TP (0.0 = at entry, 1.0 = at TP)
    tp_dist_total = abs(tp - entry)
    if tp_dist_total > 0:
        if direction == "BUY":
            progress_now  = (current_price - entry) / tp_dist_total   # current % toward TP
            peak_progress = (trade.get("extreme", entry) - entry) / tp_dist_total  # best % reached
        else:
            progress_now  = (entry - current_price) / tp_dist_total
            peak_progress = (entry - trade.get("extreme", entry)) / tp_dist_total

        # Was in profit zone and now reversing
        if peak_progress >= 0.7 and progress_now < 0.4:
            score += 3
            pct_lost = round((peak_progress - progress_now) * 100)
            reasons.append(
                f"Was {int(peak_progress*100)}% to TP — now pulled back {pct_lost}% of gains"
            )
        elif peak_progress >= 0.5 and progress_now < 0.2:
            score += 3
            reasons.append(
                f"Was {int(peak_progress*100)}% to TP — most profits now erased"
            )

        # Price crossed back through entry — profit turned to loss
        if peak_progress >= 0.3 and progress_now < 0:
            score += 4
            reasons.append(
                "⚠️ Trade was in profit but has now crossed back to a loss — consider exiting"
            )

        # Store peak progress in trade for next check
        if peak_progress > trade.get("peak_progress", 0):
            trade["peak_progress"] = round(peak_progress, 3)

    # ── Determine alert level ─────────────────────────────────
    # Choose contextual headline based on whether in profit or loss
    in_profit = (direction == "BUY" and current_price > entry) or                 (direction == "SELL" and current_price < entry)

    if score >= 6:
        if in_profit:
            headline = "Profits reversing fast — lock in gains now"
            rec      = "Exit now or at minimum move SL to lock in profits"
        else:
            headline = "Strong reversal — high risk of SL hit"
            rec      = "Exit or move SL to breakeven immediately"
        return {
            "level":          "danger",
            "headline":       headline,
            "reasons":        reasons,
            "recommendation": rec,
        }
    elif score >= 3:
        if in_profit:
            headline = "Reversal forming while in profit — consider securing gains"
            rec      = "Move SL to breakeven or take partial profits"
        else:
            headline = "Trend weakening against your trade"
            rec      = "Consider partial exit or tighten SL"
        return {
            "level":          "warning",
            "headline":       headline,
            "reasons":        reasons,
            "recommendation": rec,
        }
    else:
        return {
            "level":          "ok",
            "headline":       "",
            "reasons":        reasons,
            "recommendation": "Hold — no major reversal signals",
        }


async def check_user_trades(context):
    """
    Background job — monitor all user-entered trades.
    Checks P&L, trailing stop, TP/SL hits every minute.
    """
    # Skip in binary mode
    if active_market == "binary":
        return

    global user_active_trades
    if not user_active_trades:
        return

    nl       = chr(10)
    to_close = []

    for trade in user_active_trades:
        symbol  = trade["symbol"]
        display = trade["display"]

        # Get current price
        price_data = get_current_price(symbol)
        if not price_data:
            continue
        current = price_data["price"]

        direction = trade["direction"]
        tp        = trade["tp"]
        sl        = trade["trail_sl"]   # Use trailing SL

        pnl = calc_pnl(direction, trade["entry"], current, symbol)

        # ── Check TP hit ─────────────────────────────────────
        tp_hit = (direction == "BUY" and current >= tp) or                  (direction == "SELL" and current <= tp)

        # ── Check SL hit ─────────────────────────────────────
        sl_hit = (direction == "BUY" and current <= sl) or                  (direction == "SELL" and current >= sl)

        if tp_hit:
            emoji = "🎯"
            pnl_str = pnl["pnl_str"] + " (" + pnl["pct_str"] + ")"
            send_message(
                emoji + " *TAKE PROFIT HIT!* " + emoji + nl + nl +
                "💱 *" + display + "* — " + direction + nl +
                "📥 Entry:   `" + str(trade["entry"]) + "`" + nl +
                "🎯 TP:      `" + str(tp) + "`" + nl +
                "📊 Current: `" + str(round(current, 5)) + "`" + nl + nl +
                "💰 *Result: " + pnl_str + "*" + nl +
                "🕐 " + to_user_time()
            )
            to_close.append(trade["id"])

        elif sl_hit:
            was_trailing = trade["trail_sl"] != trade["sl_initial"]
            emoji = "🛑"
            pnl_str = pnl["pnl_str"] + " (" + pnl["pct_str"] + ")"
            sl_type = "Trailing SL" if was_trailing else "Stop Loss"
            send_message(
                emoji + " *" + sl_type.upper() + " HIT* " + emoji + nl + nl +
                "💱 *" + display + "* — " + direction + nl +
                "📥 Entry:   `" + str(trade["entry"]) + "`" + nl +
                "🛑 SL:      `" + str(sl) + "`" + nl +
                "📊 Current: `" + str(round(current, 5)) + "`" + nl + nl +
                "📊 *Result: " + pnl_str + "*" + nl +
                ("✅ _Protected by trailing stop_" + nl if was_trailing and pnl["positive"] else "") +
                "🕐 " + to_user_time()
            )
            to_close.append(trade["id"])

        else:
            # Trade still open — update trailing stop, health check, periodic update
            trade, sl_moved = update_trailing_stop(trade, current)
            trade["check_count"] = trade.get("check_count", 0) + 1

            # ── Smart Trade Health Check ──────────────────────
            # Run every 5 checks (~5 min) to detect trend reversals
            health_warn = None
            if trade["check_count"] % 5 == 0:
                health_warn = analyze_trade_health(trade, current, symbol, df=None)

            if sl_moved:
                send_message(
                    "📈 *Trailing Stop Updated!*" + nl +
                    "💱 *" + display + "* — " + direction + nl +
                    "🛡 New SL: `" + str(trade["trail_sl"]) + "` _(moved in your favor)_" + nl +
                    "📊 Current: `" + str(round(current, 5)) + "`" + nl +
                    "P&L: " + pnl["short"] + " (" + pnl["pct_str"] + ")" + nl +
                    "🕐 " + to_user_time()
                )

            elif health_warn and health_warn["level"] in ["warning", "danger"]:
                # Send health warning with Hold/Exit buttons
                level_emoji = "🚨" if health_warn["level"] == "danger" else "⚠️"
                reasons_txt = chr(10) + "   • ".join(health_warn["reasons"])
                pnl_emoji   = "📈" if pnl["positive"] else "📉"

                exit_kb = InlineKeyboardMarkup([[
                    InlineKeyboardButton("❌ Exit Now",  callback_data="trade_exit_" + str(trade["id"])),
                    InlineKeyboardButton("✋ Hold Trade", callback_data="trade_hold_" + str(trade["id"])),
                ]])

                url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
                import json
                requests.post(url, json={
                    "chat_id":      CHAT_ID,
                    "text": (
                        level_emoji + " *Trade Alert — " + display + "*" + nl + nl +
                        "💱 " + direction + " | Entry: `" + str(trade["entry"]) + "`" + nl +
                        "📊 Current: `" + str(round(current, 5)) + "`" + nl +
                        pnl_emoji + " P&L: `" + pnl["short"] + " (" + pnl["pct_str"] + ")`" + nl + nl +
                        level_emoji + " *" + health_warn["headline"] + "*" + nl +
                        "   • " + reasons_txt + nl + nl +
                        "_Recommendation: " + health_warn["recommendation"] + "_" + nl +
                        "🕐 " + to_user_time()
                    ),
                    "parse_mode":   "Markdown",
                    "reply_markup": {"inline_keyboard": [[
                        {"text": "❌ Exit Now",   "callback_data": "trade_exit_" + str(trade["id"])},
                        {"text": "✋ Hold Trade", "callback_data": "trade_hold_" + str(trade["id"])},
                    ]]}
                }, timeout=10)

            # Send P&L update every 10 checks (~10 min) if no warning sent
            elif trade["check_count"] % 10 == 0:
                pnl_emoji  = "📈" if pnl["positive"] else "📉"
                # Show peak profit if it was higher than current
                peak_prog  = trade.get("peak_progress", 0)
                tp_dist    = abs(trade["tp"] - trade["entry"])
                peak_line  = ""
                if peak_prog > 0:
                    if direction == "BUY":
                        peak_price = round(trade["entry"] + peak_prog * tp_dist, 5)
                    else:
                        peak_price = round(trade["entry"] - peak_prog * tp_dist, 5)
                    peak_pnl = calc_pnl(direction, trade["entry"], peak_price, symbol)
                    if not pnl["positive"] or peak_pnl["pnl_raw"] > pnl["pnl_raw"]:
                        peak_line = nl + "📊 Peak profit was: `" + peak_pnl["short"] + "`"

                send_message(
                    pnl_emoji + " *Trade Update* — " + display + nl +
                    direction + " | Entry: `" + str(trade["entry"]) + "`" + nl +
                    "Current: `" + str(round(current, 5)) + "`" + nl +
                    "P&L: `" + pnl["short"] + " (" + pnl["pct_str"] + ")`" +
                    peak_line + nl +
                    "🛡 Trail SL: `" + str(trade["trail_sl"]) + "`" + nl +
                    "🎯 TP: `" + str(trade["tp"]) + "`" + nl +
                    "🕐 " + to_user_time()
                )

    # Remove closed trades
    user_active_trades = [t for t in user_active_trades if t["id"] not in to_close]


async def check_signals(context, show_scanning: bool = False):
    """Rotate through symbols one per interval. show_scanning=True sends 'Scanning X...' message."""
    global symbol_queue, symbol_queue_idx

    in_blackout, blackout_window = is_news_blackout()
    if in_blackout:
        logger.info(f"⏸ Auto scan paused — news blackout: {blackout_window}")
        return

    news_imminent, news_event = check_imminent_news()
    if news_imminent:
        logger.info(f"⏸ Auto scan paused — news imminent: {news_event['name']}")
        return

    # Rebuild queue if empty or market changed
    if not symbol_queue:
        rebuild_symbol_queue()

    if not symbol_queue:
        logger.info("⏸ No symbols in queue")
        return

    # Wrap index around if we've gone through all symbols
    if symbol_queue_idx >= len(symbol_queue):
        rebuild_symbol_queue()   # Rebuild in case forex opened/closed
        symbol_queue_idx = 0
        # Silent — no Telegram spam. Just log it.
        mode = MARKET_MODES[active_market]
        logger.info(f"🔄 Queue complete — restarting {mode['label']} rotation")
        return

    # Binary mode — delegate entirely to binary scan engine
    if active_market == "binary":
        await scan_binary_signals(context, manual=False)
        return

    # Pick current symbol in rotation
    symbol = symbol_queue[symbol_queue_idx]
    info   = SYMBOLS.get(symbol)
    if not info:
        symbol_queue_idx += 1
        return

    display     = info["display"]
    symbol_type = info["type"]
    tf          = SCAN_MODES[active_scan["tf"]]
    mode        = MARKET_MODES[active_market]
    total       = len(symbol_queue)
    position    = symbol_queue_idx + 1

    logger.info(f"🔄 Rotating scan [{position}/{total}]: {display}")

    # Skip forex if market closed
    forex_open, _ = is_forex_open()
    if symbol_type == "forex" and not forex_open:
        logger.info(f"⏸ Skipping {display} — Forex closed")
        symbol_queue_idx += 1
        return

    try:
        logger.info(f"🔍 Scanning {display} [{position}/{total}]...")

        # Log only — no Telegram message while scanning (signal itself is the notification)
        logger.info(f"🔍 [{position}/{total}] Scanning {display} show_scanning={show_scanning}")

        mode_cfg = SCAN_MODES[active_scan["tf"]]
        df = fetch_data(symbol, interval=mode_cfg["interval"])
        if df is None or len(df) < 50:
            logger.warning(f"Not enough data for {display}")
            symbol_queue_idx += 1
            return

        df  = calculate_indicators(df)
        mtf = multi_timeframe_analysis(symbol)
        # generate_signal internally calls all detect_ functions
        # so we just pass df + mtf — no need to call them separately here
        sig = generate_signal(df, mtf)

        if sig["signal"] in ["BUY", "SELL"]:
            prob  = sig["prob"]
            price = sig["price"]
            next_sym = (SYMBOLS[symbol_queue[symbol_queue_idx + 1]]["display"]
                        if symbol_queue_idx + 1 < total
                        else SYMBOLS[symbol_queue[0]]["display"]) if symbol_queue else "—"

            # Build signal message
            msg      = format_signal_message(sig, symbol, display)
            sl_price = round(price - info["sl"] if sig["signal"] == "BUY" else price + info["sl"], 5)
            tp_price = round(price + info["sl"] * RISK_REWARD if sig["signal"] == "BUY" else price - info["sl"] * RISK_REWARD, 5)

            # Calculate actual clock time of next scan
            scan_secs   = active_scan["seconds"]
            next_dt     = datetime.now(user_tz_object) + timedelta(seconds=scan_secs)
            next_time   = next_dt.strftime("%H:%M")

            queue_indicator = (
                chr(10) + "━━━━━━━━━━━━━━━━━━━━" + chr(10) +
                "🔄 *Rotation:* `[" + str(position) + "/" + str(total) + "]`" + chr(10) +
                "⏱ *Next scan:* `" + next_sym + "` at `" + next_time + "`" + chr(10) +
                "🕐 *Signal time:* `" + to_user_time() + "`"
            )
            full_msg   = msg + queue_indicator
            send_signal_with_enter_button(
                sig["signal"], symbol, display,
                price, sl_price, tp_price,
                full_msg
            )

            save_to_history(sig["signal"], display, symbol, price,
                           prob["score"], sl_price, tp_price, sig["conf"])
        else:
            logger.info(f"📊 {display}: HOLD — {sig['conf']} confirmations")

    except Exception as e:
        import traceback
        err_detail = traceback.format_exc()
        logger.error("Error scanning %s: %s\n%s", display, e, err_detail)
        # Send error to Telegram so we can see it immediately
        send_message(
            "⚠️ *Scan Error — " + display + "*" + chr(10) + chr(10) +
            "`" + str(e)[:200] + "`" + chr(10) + chr(10) +
            "_Bot continues scanning next symbol..._"
        )

    finally:
        # Always advance to next symbol
        symbol_queue_idx += 1

async def check_trade_outcomes(context):
    """Check open trades for TP/SL hits and trailing stops."""
    # Skip entirely in binary mode — binary results handled by check_binary_results
    if active_market == "binary":
        return
    if open_trades:
        update_signal_outcomes()

# ============================================================
#   COMMANDS
# ============================================================

# old cmd_start removed — new one uses inline buttons

async def cmd_scan(update: Update, context):
    forex_open, _ = is_forex_open()
    sessions      = get_active_sessions()
    await update.message.reply_text(
        "🔍 *Deep scanning all symbols...*\n\n"
        f"📊 Forex: {'✅ Open' if forex_open else '❌ Closed'}\n"
        f"🌍 Session: {' + '.join(sessions) if sessions else 'Low activity'}\n\n"
        "📐 Checking MTF (30M + 1H + 4H)\n"
        "🏦 Running SMC analysis\n"
        "🕯 Checking Price Action\n\n"
        "⏳ _Results in 10-15 seconds..._",
        parse_mode="Markdown"
    )
    in_blackout, window = is_news_blackout()
    if in_blackout:
        await update.message.reply_text(
            f"⚠️ *News Blackout: {window}* — scanning anyway.",
            parse_mode="Markdown"
        )
    await scan_all_symbols(context, manual=True)

async def cmd_risk(update: Update, context):
    """Calculate lot size based on account balance."""
    args = context.args

    if not args:
        await update.message.reply_text(
            "💰 *Risk Calculator*\n\n"
            "Usage: `/risk [your balance]`\n\n"
            "Examples:\n"
            "`/risk 500` — $500 account\n"
            "`/risk 1000` — $1000 account\n"
            "`/risk 5000` — $5000 account",
            parse_mode="Markdown"
        )
        return

    try:
        balance = float(args[0].replace(",", ""))
    except ValueError:
        await update.message.reply_text("❌ Invalid amount. Example: `/risk 1000`", parse_mode="Markdown")
        return

    msg = f"💰 *Risk Calculator — ${balance:,.0f} Account*\n"
    msg += f"📊 Risk per trade: 2% = `${balance * 0.02:,.2f}`\n\n"
    msg += "━━━━━━━━━━━━━━━━━━━━\n"

    for symbol, info in SYMBOLS.items():
        r       = calculate_lot_size(balance, symbol)
        display = info["display"]
        msg    += (
            f"📌 *{display}*\n"
            f"   Lot size: `{r['lot_size']:.2f} lots`\n"
            f"   If WIN:  `+${r['potential_profit']:,.2f}`\n"
            f"   If LOSS: `-${r['potential_loss']:,.2f}`\n"
            f"   SL: ${r['sl_usd']} | TP: ${r['tp_usd']:.0f}\n\n"
        )

    msg += (
        "━━━━━━━━━━━━━━━━━━━━\n"
        "⚠️ _Always use Stop Loss_\n"
        "_Never risk more than 2% per trade_"
    )
    await update.message.reply_text(msg, parse_mode="Markdown")

async def cmd_performance(update: Update, context):
    """Show signal performance stats."""
    total   = performance["total"]
    wins    = performance["wins"]
    losses  = performance["losses"]
    pending = performance["pending"]

    if total == 0:
        await update.message.reply_text(
            "📊 *Performance Tracker*\n\nNo signals recorded yet.\nUse /scan to start!",
            parse_mode="Markdown"
        )
        return

    closed    = wins + losses
    win_rate  = round((wins / closed) * 100, 1) if closed > 0 else 0
    net_pips  = performance["total_pips"]

    bar_wins  = "🟢" * wins
    bar_loss  = "🔴" * losses

    msg = (
        f"📊 *@FaroSignal_bot Performance*\n\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎯 Win Rate:  `{win_rate}%`\n"
        f"✅ Wins:      `{wins}`\n"
        f"❌ Losses:    `{losses}`\n"
        f"⏳ Pending:   `{pending}`\n"
        f"📊 Total:     `{total}`\n"
        f"💰 Net P&L:   `${net_pips:+.0f}` per lot\n\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{bar_wins}{bar_loss}\n\n"
    )

    # Recent results
    if signal_history:
        msg += "*Recent Signals:*\n"
        for s in signal_history[:5]:
            if s["outcome"] == "WIN":
                out_emoji = "✅"
            elif s["outcome"] == "LOSS":
                out_emoji = "❌"
            else:
                out_emoji = "⏳"

            dir_emoji = "🟢" if s["signal"] == "BUY" else "🔴"
            msg += f"{out_emoji} {dir_emoji} {s['symbol']} {s['signal']} | `{s['prob']}%` | {s['time']}\n"

    await update.message.reply_text(msg, parse_mode="Markdown")

async def cmd_calendar(update: Update, context):
    """Show upcoming economic events."""
    events = get_upcoming_news()

    if not events:
        await update.message.reply_text(
            "📅 *Economic Calendar*\n\nNo major events in the next 24 hours.\nSafe to trade! ✅",
            parse_mode="Markdown"
        )
        return

    msg = "📅 *Upcoming High-Impact Events*\n\n"
    for event in events:
        hours   = event["minutes_away"] // 60
        minutes = event["minutes_away"] % 60
        time_str = f"{hours}h {minutes}m" if hours > 0 else f"{minutes}m"

        warning = " ⚠️ SOON!" if event["minutes_away"] <= 30 else ""
        msg    += (
            f"{event['impact']} *{event['name']}*{warning}\n"
            f"   🕐 {event['time']} (in {time_str})\n\n"
        )

    msg += "━━━━━━━━━━━━━━━━━━━━\n"
    msg += "⚠️ _Avoid trading 30min before/after red events_"
    await update.message.reply_text(msg, parse_mode="Markdown")

async def cmd_dashboard(update: Update, context):
    """Full market overview dashboard."""
    await update.message.reply_text("⏳ Building dashboard...")

    now           = get_utc_now()
    forex_open, _ = is_forex_open()
    sessions      = get_active_sessions()
    is_best, _    = is_best_trading_time()
    in_blackout, window = is_news_blackout()
    news_imminent, news_event = check_imminent_news()

    msg = (
        f"📊 *@FaroSignal_bot Dashboard*\n"
        f"🕐 `{now.strftime('%A %H:%M UTC')}`\n\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🌍 *Market Status*\n"
        f"Forex: {'🟢 Open' if forex_open else '🔴 Closed'}\n"
        f"Crypto: 🟢 Open 24/7\n"
        f"Sessions: {', '.join(sessions) if sessions else 'Low activity'}\n"
    )

    if is_best:
        msg += "🔥 PEAK HOURS — London + NY!\n"
    if in_blackout:
        msg += f"⚠️ News blackout: {window}\n"
    if news_imminent:
        msg += f"🚨 NEWS SOON: {news_event['name']} in {news_event['minutes_away']}min!\n"

    msg += "\n━━━━━━━━━━━━━━━━━━━━\n"
    msg += "📈 *Prices & Trends*\n"

    for symbol, info in SYMBOLS.items():
        display = info["display"]
        data    = get_current_price(symbol)
        if not data:
            continue

        df = fetch_data(symbol, interval="60m")
        trend   = "—"
        rsi_val = "—"
        mtf_bias = "—"

        if df is not None and len(df) > 21:
            df = calculate_indicators(df)
            rsi_val  = f"{df['rsi'].iloc[-1]:.0f}"
            ema_fast = df["ema_fast"].iloc[-1]
            ema_slow = df["ema_slow"].iloc[-1]
            trend    = "📈 Bull" if ema_fast > ema_slow else "📉 Bear"

        arrow = "📈" if data["change"] >= 0 else "📉"
        msg  += (
            f"\n{arrow} *{display}*: `${data['price']:,.2f}` ({data['change']:+.2f}%)\n"
            f"   Trend: {trend} | RSI: `{rsi_val}`\n"
        )

    msg += "\n━━━━━━━━━━━━━━━━━━━━\n"
    msg += "📊 *Bot Performance*\n"

    total  = performance["total"]
    wins   = performance["wins"]
    losses = performance["losses"]
    closed = wins + losses
    win_rate = round((wins / closed) * 100, 1) if closed > 0 else 0

    msg += (
        f"Win Rate: `{win_rate}%` | "
        f"W: `{wins}` L: `{losses}` P: `{performance['pending']}`\n"
        f"Net P&L: `${performance['total_pips']:+.0f}` per lot\n\n"
    )

    msg += "📅 *Next Events*\n"
    events = get_upcoming_news()
    if events:
        for e in events[:2]:
            msg += f"{e['impact']} {e['name']} — {e['time']}\n"
    else:
        msg += "No major events next 24h ✅\n"

    msg += "\n_Use /scan to check for signals_ 📱"
    await update.message.reply_text(msg, parse_mode="Markdown")

async def cmd_price(update: Update, context):
    await update.message.reply_text("⏳ Fetching prices...")
    forex_open, _ = is_forex_open()
    msg = "💰 *Current Prices* _(Yahoo Finance)_\n\n"
    for symbol, info in SYMBOLS.items():
        display  = info["display"]
        mkt_tag  = "" if info["type"] == "crypto" else (" ✅" if forex_open else " ❌")
        data     = get_current_price(symbol)
        if data:
            arrow = "📈" if data["change"] >= 0 else "📉"
            msg  += f"{arrow} *{display}:* `${data['price']:,.2f}` ({data['change']:+.2f}%){mkt_tag}\n   ⬆️ `{data['high']:,.2f}` ⬇️ `{data['low']:,.2f}`\n\n"
        else:
            msg += f"❌ *{display}:* Could not fetch\n\n"
    msg += f"🕐 `{datetime.now().strftime('%H:%M UTC')}`"
    await update.message.reply_text(msg, parse_mode="Markdown")

async def cmd_market(update: Update, context):
    now = get_utc_now()
    forex_open, forex_reason = is_forex_open()
    sessions   = get_active_sessions()
    is_best, _ = is_best_trading_time()
    in_blackout, window = is_news_blackout()
    sessions_text = "\n".join([f"   • {s} ✅" for s in sessions]) if sessions else "   • No major session"
    msg = (
        f"🌍 *Market Status*\n🕐 `{now.strftime('%A %H:%M UTC')}`\n\n"
        f"{'🟢' if forex_open else '🔴'} *Forex:* {'OPEN' if forex_open else 'CLOSED'}\n   {forex_reason}\n\n"
        f"🟢 *Crypto:* OPEN 24/7\n\n"
        f"🌐 *Active Sessions:*\n{sessions_text}\n\n"
    )
    if is_best:     msg += "🔥 *Peak Hours!* London + NY overlap!\n\n"
    if in_blackout: msg += f"⚠️ *News Blackout:* `{window}`\n\n"
    msg += "📅 Fri 22:00 close → Sun 22:00 open\n🔥 Best: Mon—Fri 13:00—17:00 UTC"
    await update.message.reply_text(msg, parse_mode="Markdown")

async def cmd_history(update: Update, context):
    if not signal_history:
        await update.message.reply_text("📋 *No signals yet.* Use /scan!", parse_mode="Markdown")
        return
    msg = "📋 *Last Signals*\n\n"
    for s in signal_history[:5]:
        dir_emoji = "🟢" if s["signal"] == "BUY" else "🔴"
        out_emoji = "✅" if s["outcome"] == "WIN" else "❌" if s["outcome"] == "LOSS" else "⏳"
        msg      += (
            f"{out_emoji} {dir_emoji} *{s['signal']} {s['symbol']}* | `{s['conf']} conf` | `{s['prob']}%`\n"
            f"   💰 `{s['price']:.2f}` → 🛑 `{s['sl']:.2f}` | 🎯 `{s['tp']:.2f}`\n"
            f"   🕐 `{s['time']}`\n\n"
        )
    await update.message.reply_text(msg, parse_mode="Markdown")

async def cmd_news(update: Update, context):
    in_blackout, window = is_news_blackout()
    now_utc = get_utc_now()
    if in_blackout:
        await update.message.reply_text(
            f"⚠️ *News Filter: ACTIVE*\nBlackout: `{window}`\nAuto signals paused. Use /scan to force.",
            parse_mode="Markdown"
        )
    else:
        await update.message.reply_text(
            f"✅ *News Filter: CLEAR*\nUTC: `{now_utc.strftime('%H:%M')}`\n\n"
            f"Blackout windows:\n• 07:45—08:30\n• 13:00—14:00\n• 18:45—19:30\n\n"
            f"_Use /calendar for upcoming events_",
            parse_mode="Markdown"
        )

async def cmd_status(update: Update, context):
    forex_open, _ = is_forex_open()
    symbols_list  = "\n".join([f"• {v['display']} ({v['type']})" for v in SYMBOLS.values()])
    await update.message.reply_text(
        f"✅ *@FaroSignal_bot: Running*\n\n"
        f"📌 *Symbols:*\n{symbols_list}\n\n"
        f"🧠 RSI+MA+MACD+MTF+SMC+PA\n"
        f"📡 Data: Yahoo Finance\n"
        f"📊 Forex: {'🟢 Open' if forex_open else '🔴 Closed'}\n"
        f"⏱ Timeframe: 30M + 1H + 4H\n"
        f"🔁 Scan: every 30 min\n"
        f"📋 Signals: {len(signal_history)} recorded\n"
        f"📊 Open trades: {len(open_trades)}",
        parse_mode="Markdown"
    )



# ============================================================
#   INLINE BUTTON HELPERS
# ============================================================

def make_timeframe_keyboard():
    """Build inline keyboard for timeframe selection."""
    rows = []
    row  = []
    for i, (key, val) in enumerate(SCAN_MODES.items()):
        marker = " ✅" if key == active_scan["tf"] else ""
        row.append(InlineKeyboardButton(
            val["emoji"] + " " + val["label"] + marker,
            callback_data="tf_" + key
        ))
        if len(row) == 3:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    # Add back button
    rows.append([InlineKeyboardButton("🔙 Back to Menu", callback_data="menu_main")])
    return InlineKeyboardMarkup(rows)


def make_market_keyboard():
    """Build inline keyboard for market mode selection."""
    rows = []
    for key, val in MARKET_MODES.items():
        marker = " ✅ ACTIVE" if key == active_market else ""
        rows.append([InlineKeyboardButton(
            val["emoji"] + " " + val["label"] + marker,
            callback_data="market_" + key
        )])
    rows.append([InlineKeyboardButton("🔙 Back to Menu", callback_data="menu_main")])
    return InlineKeyboardMarkup(rows)


def make_main_menu_keyboard():
    """Main control panel keyboard."""
    mode    = MARKET_MODES[active_market]
    tf      = SCAN_MODES[active_scan["tf"]]
    rows = [
        [
            InlineKeyboardButton("🔍 Scan Now",                                        callback_data="action_scan"),
            InlineKeyboardButton("💰 Prices",                                          callback_data="action_price"),
        ],
        [
            InlineKeyboardButton("⏱ " + tf["label"],                                  callback_data="menu_timeframe"),
            InlineKeyboardButton(mode["emoji"] + " " + mode["label"] + " ✏️",          callback_data="menu_market"),
        ],
        [
            InlineKeyboardButton("📊 Dashboard",      callback_data="action_dashboard"),
            InlineKeyboardButton("📋 History",        callback_data="action_history"),
        ],
        [
            InlineKeyboardButton("📅 Calendar",       callback_data="action_calendar"),
            InlineKeyboardButton("📈 Performance",    callback_data="action_performance"),
        ],
        [
            InlineKeyboardButton("🌍 Market Hours",   callback_data="action_market"),
            InlineKeyboardButton("ℹ️ Status",         callback_data="action_status"),
        ],
    ]
    return InlineKeyboardMarkup(rows)


# ============================================================
#   CALLBACK HANDLER
# ============================================================

# ============================================================
#   UPDATED /start with main menu
# ============================================================


async def cmd_dashboard_inline(chat_id, context):
    """Dashboard for inline button use."""
    now           = get_utc_now()
    forex_open, _ = is_forex_open()
    sessions      = get_active_sessions()
    is_best, _    = is_best_trading_time()
    in_blackout, window = is_news_blackout()
    nl = chr(10)

    msg = (
        "📊 *@FaroSignal_bot Dashboard*" + nl +
        "🕐 `" + now.strftime("%A %H:%M UTC") + "`" + nl + nl +
        "━━━━━━━━━━━━━━━━━━━━" + nl +
        ("🟢" if forex_open else "🔴") + " Forex " + ("OPEN" if forex_open else "CLOSED") +
        "  |  🟢 Crypto 24/7" + nl +
        "Sessions: " + (", ".join(sessions) if sessions else "Low activity") + nl
    )
    if is_best:     msg += "🔥 PEAK HOURS — London + NY!" + nl
    if in_blackout: msg += "⚠️ News Blackout: " + window + nl

    msg += nl + "━━━━━━━━━━━━━━━━━━━━" + nl + "📈 *Prices & Trends*" + nl
    mode_symbols = get_active_symbols()
    for symbol, info in SYMBOLS.items():
        if symbol not in mode_symbols: continue
        pdata = get_current_price(symbol)
        if not pdata: continue
        arrow = "📈" if pdata["change"] >= 0 else "📉"
        msg += nl + arrow + " *" + info["display"] + ":* `$" + "{:,.2f}".format(pdata["price"]) + "` (" + "{:+.2f}".format(pdata["change"]) + "%)" + nl

    total  = performance["total"]
    wins   = performance["wins"]
    losses = performance["losses"]
    closed = wins + losses
    wr     = round((wins / closed) * 100, 1) if closed > 0 else 0
    msg += (
        nl + "━━━━━━━━━━━━━━━━━━━━" + nl +
        "📊 Win Rate: `" + str(wr) + "%` | W:`" + str(wins) + "` L:`" + str(losses) + "` P:`" + str(performance["pending"]) + "`" + nl +
        "💰 Net: `$" + str(round(performance["total_pips"], 0)) + "` per lot"
    )
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton("🔄 Refresh", callback_data="action_dashboard"),
        InlineKeyboardButton("🏠 Menu",    callback_data="menu_main"),
    ]])
    await context.bot.send_message(chat_id=chat_id, text=msg, parse_mode="Markdown", reply_markup=kb)


async def handle_trade_callback(update: Update, context):
    """Handle ✅ I Entered This Trade button + trade management."""
    global user_active_trades
    query = update.callback_query
    await query.answer()
    data  = query.data
    nl    = chr(10)

    if data.startswith("trade_enter_"):
        # Look up full trade data from pending_signals using short numeric ID
        try:
            sid      = int(data.split("_")[2])
            pdata    = pending_signals.get(sid)
            if not pdata:
                await query.message.reply_text(
                    "⚠️ Signal data expired. Tap Scan Now for a fresh signal.",
                    parse_mode="Markdown"
                )
                return
            signal  = pdata["signal"]
            symbol  = pdata["symbol"]
            display = pdata["display"]
            entry   = pdata["entry"]
            sl      = pdata["sl"]
            tp      = pdata["tp"]
        except Exception as e:
            await query.message.reply_text("❌ Error loading trade: " + str(e))
            return

        # Check if already tracking this trade
        existing = [t for t in user_active_trades if t["symbol"] == symbol]
        if existing:
            await query.message.reply_text(
                "⚠️ *Already tracking " + display + "!*" + nl +
                "You have " + str(len(existing)) + " active trade(s) on this pair." + nl +
                "Use /mytrades to view or close them.",
                parse_mode="Markdown"
            )
            return

        # Add to active trades
        trade_id = len(user_active_trades) + 1
        trade    = {
            "id":          trade_id,
            "symbol":      symbol,
            "display":     display,
            "direction":   signal,
            "entry":       entry,
            "sl":          sl,
            "sl_initial":  sl,
            "trail_sl":    sl,    # Starts at initial SL, moves with price
            "tp":          tp,
            "extreme":     entry, # Tracks highest (BUY) or lowest (SELL) price seen
            "check_count": 0,
            "time_entered": to_user_time(),
        }
        user_active_trades.append(trade)

        pnl_dir  = "TP" if signal == "BUY" else "TP"
        rr_dist  = abs(tp - entry)
        sl_dist  = abs(sl - entry)
        rr_ratio = round(rr_dist / sl_dist, 1) if sl_dist > 0 else 0

        await query.message.reply_text(
            "✅ *Trade Entered — Now Monitoring!*" + nl + nl +
            "💱 *" + display + "* — " + signal + nl +
            "📥 Entry:  `" + str(entry) + "`" + nl +
            "🛑 SL:     `" + str(sl) + "` _(trailing)_" + nl +
            "🎯 TP:     `" + str(tp) + "`" + nl +
            "📊 R:R     `1:" + str(rr_ratio) + "`" + nl + nl +
            "🤖 *Bot will alert you when:*" + nl +
            "   • 🎯 TP is hit" + nl +
            "   • 🛑 SL is hit" + nl +
            "   • 📈 Trailing stop moves" + nl +
            "   • 📊 P&L update every ~10 min" + nl + nl +
            "Type /mytrades to view or exit" + nl +
            "🕐 " + to_user_time(),
            parse_mode="Markdown"
        )

    elif data.startswith("trade_hold_"):
        trade_id = int(data.split("_")[2])
        trade    = next((t for t in user_active_trades if t["id"] == trade_id), None)
        if trade:
            await query.answer("✋ Holding trade — bot continues monitoring.", show_alert=False)
            await query.message.reply_text(
                "✋ *Holding " + trade["display"] + "* — bot continues monitoring." + chr(10) +
                "You'll be alerted again if conditions worsen." + chr(10) +
                "🕐 " + to_user_time(),
                parse_mode="Markdown"
            )
        else:
            await query.answer("Trade already closed.", show_alert=False)

    elif data.startswith("trade_exit_"):
        trade_id = int(data.split("_")[2])
        trade    = next((t for t in user_active_trades if t["id"] == trade_id), None)
        if not trade:
            await query.message.reply_text("❌ Trade not found — may have already closed.")
            return

        symbol  = trade["symbol"]
        display = trade["display"]
        pdata   = get_current_price(symbol)
        current = pdata["price"] if pdata else trade["entry"]
        pnl     = calc_pnl(trade["direction"], trade["entry"], current, symbol)

        user_active_trades = [t for t in user_active_trades if t["id"] != trade_id]

        pnl_str  = ("+" if pnl["positive"] else "") + str(pnl["pips"]) + " pips"
        pct_str  = ("+" if pnl["positive"] else "") + str(pnl["pnl_pct"]) + "%"
        outcome  = "✅ Profitable" if pnl["positive"] else "❌ Loss"

        await query.message.reply_text(
            "🔒 *Trade Closed Manually*" + nl + nl +
            "💱 *" + display + "* — " + trade["direction"] + nl +
            "📥 Entry:   `" + str(trade["entry"]) + "`" + nl +
            "📤 Exit:    `" + str(round(current, 5)) + "`" + nl +
            "P&L: `" + pnl_str + "` (" + pct_str + ")" + nl +
            outcome + nl +
            "🕐 " + to_user_time(),
            parse_mode="Markdown"
        )


async def handle_timezone_callback(update: Update, context):
    """Handle timezone selection buttons."""
    global user_timezone, user_tz_object
    query = update.callback_query
    await query.answer()
    data  = query.data
    nl    = chr(10)

    if data.startswith("tz_region_"):
        region_key = data[10:]
        region     = TIMEZONE_REGIONS[region_key]
        await query.message.reply_text(
            "🌍 *" + region["label"] + "*" + nl + nl +
            "Select your city/zone:",
            parse_mode="Markdown",
            reply_markup=make_tz_zone_keyboard(region_key)
        )
        try:
            await query.message.delete()
        except Exception:
            pass

    elif data.startswith("tz_set_"):
        tz_key = data[7:]
        try:
            if tz_key == "UTC":
                user_timezone  = "UTC"
                user_tz_object = pytz.utc
                tz_label       = "UTC"
            else:
                user_timezone  = tz_key
                user_tz_object = pytz.timezone(tz_key)
                # Find label
                tz_label = tz_key.split("/")[-1].replace("_", " ")
                for region in TIMEZONE_REGIONS.values():
                    if tz_key in region["zones"]:
                        tz_label = region["zones"][tz_key]
                        break

            now_local = datetime.now(timezone.utc).astimezone(user_tz_object)
            welcome_kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("🚀 Open Control Panel", callback_data="menu_main")],
                [InlineKeyboardButton("⚡ Binary Signals",     callback_data="market_binary"),
                 InlineKeyboardButton("🌍 All Markets",        callback_data="market_all")],
                [InlineKeyboardButton("🔍 Scan Now",           callback_data="action_scan"),
                 InlineKeyboardButton("💰 Prices",             callback_data="action_price")],
            ])
            await query.message.reply_text(
                "✅ *Timezone Set!*" + nl + nl +
                "🌍 Zone: *" + tz_label + "*" + nl +
                "🕐 Your time: *" + now_local.strftime("%H:%M") + "*" + nl + nl +
                "All signal times will now show in your local time." + nl + nl +
                "👇 *Tap to get started:*",
                parse_mode="Markdown",
                reply_markup=welcome_kb
            )
            try:
                await query.message.delete()
            except Exception:
                pass
        except Exception as e:
            await query.message.reply_text(f"❌ Error setting timezone: {e}")

    elif data == "tz_back":
        await query.message.reply_text(
            "🌍 *Select your timezone region:*",
            parse_mode="Markdown",
            reply_markup=make_tz_region_keyboard()
        )
        try:
            await query.message.delete()
        except Exception:
            pass


async def handle_callback(update: Update, context):
    """Handle all inline button presses — sends NEW message, keeps chat history clean."""
    global active_scan, active_market
    query = update.callback_query
    await query.answer()
    data = query.data
    nl   = chr(10)

    # Send fresh — single message with keyboard attached (no duplicate)
    async def fresh(text, keyboard=None):
        try:
            await query.message.delete()
        except Exception:
            pass
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text=text,
            parse_mode="Markdown",
            reply_markup=keyboard or None
        )

    back_btn   = InlineKeyboardMarkup([[InlineKeyboardButton("🏠 Main Menu", callback_data="menu_main")]])
    change_tf  = InlineKeyboardMarkup([[
        InlineKeyboardButton("⬅️ Change Again", callback_data="menu_timeframe"),
        InlineKeyboardButton("🏠 Menu",         callback_data="menu_main"),
    ]])
    change_mkt = InlineKeyboardMarkup([[
        InlineKeyboardButton("⬅️ Change Again", callback_data="menu_market"),
        InlineKeyboardButton("🏠 Menu",         callback_data="menu_main"),
    ]])
    refresh_back = lambda cb: InlineKeyboardMarkup([[
        InlineKeyboardButton("🔄 Refresh", callback_data=cb),
        InlineKeyboardButton("🏠 Menu",    callback_data="menu_main"),
    ]])

    # ── Main menu ──────────────────────────────────────────────
    if data == "menu_main":
        mode       = MARKET_MODES[active_market]
        tf         = SCAN_MODES[active_scan["tf"]]
        forex_open, _ = is_forex_open()
        weekend    = is_weekend_otc() if active_market == "binary" else False
        mkt_status = "🟢 Open" if forex_open else "🔴 Closed"
        if active_market == "binary":
            bin_syms  = get_active_binary_symbols()
            bin_keys  = list(bin_syms.keys())
            total     = len(bin_keys) if bin_keys else 1
            position  = (symbol_queue_idx % total) + 1
            next_auto = bin_syms[bin_keys[symbol_queue_idx % len(bin_keys)]]["display"] if bin_keys else "—"
        else:
            total     = len(symbol_queue) if symbol_queue else 1
            position  = (symbol_queue_idx % total) + 1
            next_auto = SYMBOLS[symbol_queue[symbol_queue_idx % len(symbol_queue)]]["display"] if symbol_queue else "—"
        await fresh(
            "🤖 *@FaroSignal_bot Control Panel*" + nl + nl +
            "━━━━━━━━━━━━━━━━━━━━" + nl +
            mode["emoji"] + " Market: *" + mode["label"] + "*" + nl +
            "⏱ Timeframe: *" + tf["label"] + "*" + nl +
            "💱 Forex: " + mkt_status + nl +
            ("🌙 OTC Weekend Mode" + nl if weekend else "") +
            "🔄 Auto-scan: *" + next_auto + "* [" + str(position) + "/" + str(total) + "]" + nl +
            "━━━━━━━━━━━━━━━━━━━━" + nl + nl +
            "Choose an action:",
            make_main_menu_keyboard()
        )

    # ── Timeframe menu ─────────────────────────────────────────
    elif data == "menu_timeframe":
        current = SCAN_MODES[active_scan["tf"]]
        await fresh(
            "⏱ *Timeframe Switcher*" + nl + nl +
            "Current: " + current["emoji"] + " *" + current["label"] + "*" + nl + nl +
            "⚡ 5m  — Scalping (high noise)" + nl +
            "🔥 15m — Active day trading" + nl +
            "✅ 30m — Recommended default" + nl +
            "🕐 1h  — Swing trading" + nl +
            "📊 4h  — Position trading" + nl +
            "🌙 1d  — Long term only",
            make_timeframe_keyboard()
        )

    # ── Timeframe switch ───────────────────────────────────────
    elif data.startswith("tf_"):
        tf_key   = data[3:]
        old_tf   = active_scan["tf"]
        new_mode = SCAN_MODES[tf_key]
        old_mode = SCAN_MODES[old_tf]

        active_scan["tf"]      = tf_key
        active_scan["seconds"] = new_mode["seconds"]

        jobs = context.job_queue.get_jobs_by_name("signal_scan")
        for job in jobs:
            job.schedule_removal()
        context.job_queue.run_repeating(
            check_signals, interval=new_mode["seconds"], first=10, name="signal_scan"
        )

        if new_mode["seconds"] < 900:
            note = "⚠️ More signals — higher noise. Experienced traders only."
        elif new_mode["seconds"] == 1800:
            note = "✅ Balanced — recommended for most traders."
        else:
            note = "📊 Fewer signals — higher quality setups."

        await fresh(
            new_mode["emoji"] + " *Switched to " + new_mode["label"] + "!*" + nl + nl +
            "Old: " + old_mode["emoji"] + " " + old_mode["label"] + nl +
            "New: " + new_mode["emoji"] + " *" + new_mode["label"] + "* ✅" + nl + nl +
            note + nl + nl +
            "Next scan in ~10 seconds... 👇",
            make_main_menu_keyboard()   # ← refreshed with new TF label
        )
        send_message(new_mode["emoji"] + " *Scan mode: " + new_mode["label"] + "*" + nl + note)

    # ── Market mode menu ───────────────────────────────────────
    elif data == "menu_market":
        mode = MARKET_MODES[active_market]
        await fresh(
            "🌍 *Market Mode Switcher*" + nl + nl +
            "Current: " + mode["emoji"] + " *" + mode["label"] + "*" + nl + nl +
            "💱 *Forex*  — Gold (XAUUSD)" + nl +
            "🪙 *Crypto* — BTC, ETH, SOL, BNB, XRP..." + nl +
            "🌍 *All*    — Forex + All Crypto" + nl +
            "⚡ *Binary* — Coming soon!",
            make_market_keyboard()
        )

    # ── Market mode switch ─────────────────────────────────────
    elif data.startswith("market_"):
        new_market = data[7:]

        if new_market == "binary":
            active_market = "binary"
            broker_row_mkt = [
                InlineKeyboardButton(
                    BROKERS[bk]["emoji"] + " " + BROKERS[bk]["label"] + (" ✅" if bk == active_broker else ""),
                    callback_data="binary_broker_" + bk
                ) for bk in BROKERS
            ]
            kb = InlineKeyboardMarkup([
                broker_row_mkt,
                [InlineKeyboardButton("⚡ Scan Binary Now", callback_data="binary_scan"),
                 InlineKeyboardButton("📊 Stats",          callback_data="binary_stats")],
                [InlineKeyboardButton("📋 History",        callback_data="binary_history"),
                 InlineKeyboardButton("🏠 Main Menu",      callback_data="menu_main")],
            ])
            wins   = binary_performance["wins"]
            losses = binary_performance["losses"]
            closed = wins + losses
            wr     = round((wins / closed) * 100, 1) if closed > 0 else 0
            await fresh(
                "⚡ *Binary Options — Pocket Option*" + nl + nl +
                "Current expiry: " + expiry["emoji"] + " *" + expiry["label"] + "*" + nl + nl +
                "📊 Win Rate: `" + str(wr) + "%`  W:`" + str(wins) + "` L:`" + str(losses) + "` P:`" + str(binary_performance["pending"]) + "`" + nl + nl +
                "Select expiry then tap *Scan Binary Now*:",
                kb
            )
            return

        old_market    = active_market
        active_market = new_market
        new_m         = MARKET_MODES[new_market]
        old_m         = MARKET_MODES[old_market]
        sym_list      = nl.join(["   • " + SYMBOLS[s]["display"] for s in new_m["symbols"] if s in SYMBOLS])
        rebuild_symbol_queue()   # Reset rotation queue for new mode

        # Restart scan job immediately with fresh queue
        jobs = context.job_queue.get_jobs_by_name("signal_scan")
        for job in jobs:
            job.schedule_removal()
        context.job_queue.run_repeating(
            check_signals,
            interval=active_scan["seconds"],
            first=5,
            name="signal_scan"
        )

        tf = SCAN_MODES[active_scan["tf"]]
        # Send confirmation then immediately show updated main menu
        await fresh(
            new_m["emoji"] + " *Switched to " + new_m["label"] + " Mode!* ✅" + nl + nl +
            "Old: " + old_m["emoji"] + " " + old_m["label"] + nl +
            "New: " + new_m["emoji"] + " *" + new_m["label"] + "*" + nl +
            "Assets: `" + str(len(new_m["symbols"])) + "` | TF: " + tf["label"] + nl + nl +
            sym_list + nl + nl +
            "Main menu updated 👇",
            make_main_menu_keyboard()   # ← returns fresh keyboard with new mode label
        )

    # ── Quick actions ──────────────────────────────────────────
    elif data == "action_scan":
        await scan_all_symbols(context, manual=True)

    elif data == "action_price":
        forex_open, _ = is_forex_open()
        msg           = "💰 *Current Prices*" + nl + nl

        if active_market == "binary":
            bin_syms = get_active_binary_symbols()
            broker   = BROKERS[active_broker]
            msg     += broker["emoji"] + " *" + broker["label"] + "*" + nl + nl
            shown    = 0
            for sym_key, info in list(bin_syms.items())[:12]:
                base_key  = sym_key.replace("-OTC", "")
                base_info = BINARY_PAIRS.get(base_key, {})
                td_sym    = base_info.get("td")
                if not td_sym:
                    continue
                pdata = get_current_price_td(td_sym)
                if not pdata:
                    continue
                arrow  = "📈" if pdata["change"] >= 0 else "📉"
                payout = info.get("payout", 80)
                msg   += arrow + " *" + info["display"] + ":* `" + "{:,.5f}".format(pdata["price"]) + "` (" + "{:+.2f}".format(pdata["change"]) + "%) | " + str(payout) + "%" + nl
                shown += 1
            if shown == 0:
                msg += "_No prices available — check API_" + nl
        else:
            mode_symbols = get_active_symbols()
            for symbol, info in SYMBOLS.items():
                if symbol not in mode_symbols:
                    continue
                pdata = get_current_price(symbol)
                if pdata:
                    arrow = "📈" if pdata["change"] >= 0 else "📉"
                    mkt   = "" if info["type"] == "crypto" else (" ✅" if forex_open else " ❌")
                    msg  += arrow + " *" + info["display"] + ":* `" + "{:,.4f}".format(pdata["price"]) + "` (" + "{:+.2f}".format(pdata["change"]) + "%)" + mkt + nl
                else:
                    msg += "❌ *" + info["display"] + ":* Could not fetch" + nl

        msg += nl + "🕐 `" + to_user_time() + "`"
        await fresh(msg, refresh_back("action_price"))

    elif data == "action_history":
        if not signal_history:
            msg = "📋 *No signals yet.*" + nl + "Tap Scan Now to start!"
        else:
            msg = "📋 *Last Signals*" + nl + nl
            for s in signal_history[:5]:
                de = "🟢" if s["signal"] == "BUY" else "🔴"
                oe = "✅" if s["outcome"] == "WIN" else "❌" if s["outcome"] == "LOSS" else "⏰" if s["outcome"] == "MISSED" else "⏳"
                msg += oe + " " + de + " *" + s["signal"] + " " + s["symbol"] + "* `" + str(s["prob"]) + "%`" + nl
                msg += "   `" + str(round(s["price"],2)) + "` SL:`" + str(round(s["sl"],2)) + "` TP:`" + str(round(s["tp"],2)) + "` — " + s["time"] + nl + nl
        await fresh(msg, refresh_back("action_history"))

    elif data == "action_performance":
        total  = performance["total"]
        wins   = performance["wins"]
        losses = performance["losses"]
        closed = wins + losses
        wr     = round((wins / closed) * 100, 1) if closed > 0 else 0
        bar    = "🟢" * wins + "🔴" * losses
        msg    = (
            "📊 *Performance Tracker*" + nl + nl +
            "🎯 Win Rate: `" + str(wr) + "%`" + nl +
            "✅ Wins: `" + str(wins) + "`  ❌ Losses: `" + str(losses) + "`" + nl +
            "⏳ Pending: `" + str(performance["pending"]) + "`  📊 Total: `" + str(total) + "`" + nl +
            "💰 Net P&L: `$" + str(round(performance["total_pips"], 0)) + "` per lot" + nl + nl +
            (bar if bar else "_No closed trades yet_")
        )
        await fresh(msg, refresh_back("action_performance"))

    elif data == "action_calendar":
        events = get_upcoming_news()
        if not events:
            msg = "📅 *Economic Calendar*" + nl + nl + "No major events next 24h ✅" + nl + "Safe to trade!"
        else:
            msg = "📅 *Upcoming Events*" + nl + nl
            for e in events:
                h = e["minutes_away"] // 60
                m = e["minutes_away"] % 60
                t = (str(h) + "h " if h > 0 else "") + str(m) + "m"
                warn = " 🚨 SOON!" if e["minutes_away"] <= 30 else ""
                msg += e["impact"] + " *" + e["name"] + "*" + warn + nl
                msg += "   🕐 " + e["time"] + " (in " + t + ")" + nl + nl
            msg += "⚠️ _Avoid trading 30min before red events_"
        await fresh(msg, refresh_back("action_calendar"))

    elif data == "action_market":
        now = get_utc_now()
        forex_open, forex_reason = is_forex_open()
        sessions = get_active_sessions()
        is_best, _ = is_best_trading_time()
        in_blackout, window = is_news_blackout()
        msg = (
            "🌍 *Market Status*" + nl +
            "🕐 `" + now.strftime("%A %H:%M UTC") + "`" + nl + nl +
            ("🟢" if forex_open else "🔴") + " Forex: " + ("OPEN" if forex_open else "CLOSED") + nl +
            "   " + forex_reason + nl + nl +
            "🟢 Crypto: OPEN 24/7" + nl + nl +
            "Sessions: " + (", ".join(sessions) if sessions else "Low activity") + nl
        )
        if is_best:      msg += nl + "🔥 *Peak Hours! London + NY overlap!*" + nl
        if in_blackout:  msg += nl + "⚠️ *News Blackout:* `" + window + "`" + nl
        await fresh(msg, refresh_back("action_market"))

    elif data == "action_status":
        forex_open, _ = is_forex_open()
        mode = MARKET_MODES[active_market]
        tf   = SCAN_MODES[active_scan["tf"]]
        msg  = (
            "✅ *@FaroSignal_bot: Running*" + nl + nl +
            "🌍 Mode: " + mode["emoji"] + " " + mode["label"] + nl +
            "⏱ Timeframe: " + tf["emoji"] + " " + tf["label"] + nl +
            "📊 Forex: " + ("🟢 Open" if forex_open else "🔴 Closed") + nl +
            "📋 Signals: `" + str(len(signal_history)) + "` recorded" + nl +
            "📊 Open trades: `" + str(len(open_trades)) + "`"
        )
        await fresh(msg, back_btn)

    elif data == "action_dashboard":
        await fresh("⏳ Building dashboard...")
        await cmd_dashboard_inline(query.message.chat_id, context)



async def cmd_mytrades(update: Update, context):
    """Show all active monitored trades with exit buttons."""
    nl = chr(10)
    if not user_active_trades:
        await update.message.reply_text(
            "📊 *No Active Trades*" + nl + nl +
            "Tap *✅ I Entered This Trade* on any signal to start monitoring." + nl +
            "Bot will track P&L, trailing stop and alert you on TP/SL.",
            parse_mode="Markdown"
        )
        return

    for trade in user_active_trades:
        pdata   = get_current_price(trade["symbol"])
        current = pdata["price"] if pdata else trade["entry"]
        pnl     = calc_pnl(trade["direction"], trade["entry"], current, trade["symbol"])
        pnl_str = pnl["pnl_str"] + " (" + pnl["pct_str"] + ")"
        pnl_emoji = "📈" if pnl["positive"] else "📉"
        sl_moved  = trade["trail_sl"] != trade["sl_initial"]

        kb = InlineKeyboardMarkup([[
            InlineKeyboardButton("❌ Exit Trade", callback_data="trade_exit_" + str(trade["id"]))
        ]])
        await update.message.reply_text(
            pnl_emoji + " *" + trade["display"] + "* — " + trade["direction"] + nl + nl +
            "📥 Entry:     `" + str(trade["entry"]) + "`" + nl +
            "📊 Current:   `" + str(round(current, 5)) + "`" + nl +
            "🛑 Trail SL:  `" + str(trade["trail_sl"]) + "`" + (" _(moved)_" if sl_moved else "") + nl +
            "🎯 TP:        `" + str(trade["tp"]) + "`" + nl +
            "💰 P&L:       `" + pnl_str + "`" + nl +
            "⏱ Entered:   `" + trade["time_entered"] + "`" + nl + nl +
            "🕐 " + to_user_time(),
            parse_mode="Markdown",
            reply_markup=kb
        )


async def cmd_start(update: Update, context):
    nl = chr(10)
    await update.message.reply_text(
        "👋 *Welcome to @FaroSignal_bot!*" + nl + nl +
        "🤖 Professional trading signals for:" + nl +
        "   💱 Forex — Gold (XAUUSD)" + nl +
        "   🪙 Crypto — BTC, ETH, SOL, BNB..." + nl +
        "   ⚡ Binary — Pocket Option & Quotex" + nl + nl +
        "📊 *Analysis Engine:*" + nl +
        "   • RSI + MACD + Bollinger Bands" + nl +
        "   • SMC: Order Blocks, BOS, FVG" + nl +
        "   • Fibonacci + RSI Divergence" + nl +
        "   • Multi-Timeframe (30M + 1H + 4H)" + nl + nl +
        "🌍 *First — set your timezone so all signal" + nl +
        "times show in your local time:*",
        parse_mode="Markdown",
        reply_markup=make_tz_region_keyboard()
    )


async def cmd_timezone(update: Update, context):
    """Change timezone anytime."""
    await update.message.reply_text(
        "🌍 *Select your timezone region:*",
        parse_mode="Markdown",
        reply_markup=make_tz_region_keyboard()
    )


async def cmd_menu(update: Update, context):
    """Show the main control panel."""
    mode = MARKET_MODES[active_market]
    tf   = SCAN_MODES[active_scan["tf"]]
    await update.message.reply_text(
        "🤖 *@FaroSignal_bot Control Panel*" + chr(10) + chr(10) +
        "Mode: " + mode["emoji"] + " " + mode["label"] + " | " +
        "TF: " + tf["emoji"] + " " + tf["label"] + chr(10) + chr(10) +
        "Choose an action:",
        parse_mode="Markdown",
        reply_markup=make_main_menu_keyboard()
    )


async def cmd_binary(update: Update, context):
    """Binary options control panel."""
    expiry = BINARY_EXPIRIES[active_binary_expiry]
    nl     = chr(10)

    # Broker buttons only — expiry is auto-selected per signal
    broker_row = [
        InlineKeyboardButton(
            BROKERS[bk]["emoji"] + " " + BROKERS[bk]["label"] + (" ✅" if bk == active_broker else ""),
            callback_data="binary_broker_" + bk
        ) for bk in BROKERS
    ]

    weekend  = is_weekend_otc()
    keyboard = InlineKeyboardMarkup([
        broker_row,
        [InlineKeyboardButton("⚡ Scan Binary Now", callback_data="binary_scan"),
         InlineKeyboardButton("📊 Stats",           callback_data="binary_stats")],
        [InlineKeyboardButton("📋 History",         callback_data="binary_history"),
         InlineKeyboardButton("🏠 Main Menu",       callback_data="menu_main")],
    ])

    total   = binary_performance["total"]
    wins    = binary_performance["wins"]
    losses  = binary_performance["losses"]
    closed  = wins + losses
    wr      = round((wins / closed) * 100, 1) if closed > 0 else 0

    broker     = BROKERS[active_broker]
    weekend    = is_weekend_otc()
    mode_label = "🌙 OTC Mode — Weekend" if weekend else "📅 Regular Mode — Weekday"
    sym_count  = len(get_active_binary_symbols())

    await update.message.reply_text(
        "⚡ *Binary Options Panel*" + nl + nl +
        "Broker: " + broker["emoji"] + " *" + broker["label"] + "*" + nl +
        "Mode: " + mode_label + nl +
        "Assets: `" + str(sym_count) + "` available" + nl +
        "Expiry: " + expiry["emoji"] + " *" + expiry["label"] + "*" + nl + nl +
        "📊 Win Rate: `" + str(wr) + "%`  W:`" + str(wins) + "` L:`" + str(losses) + "` P:`" + str(binary_performance["pending"]) + "`" + nl + nl +
        "Switch broker, select expiry, then scan:",
        parse_mode="Markdown",
        reply_markup=keyboard
    )


async def handle_binary_callback(update: Update, context):
    """Handle binary-specific inline buttons."""
    global active_binary_expiry
    query = update.callback_query
    await query.answer()
    data  = query.data
    nl    = chr(10)

    async def fresh_binary(text, keyboard=None):
        try:
            await query.message.delete()
        except Exception:
            pass
        if keyboard:
            await context.bot.send_message(chat_id=query.message.chat_id, text=text,
                                           parse_mode="Markdown", reply_markup=keyboard)
        else:
            await context.bot.send_message(chat_id=query.message.chat_id, text=text,
                                           parse_mode="Markdown")

    # Build standard binary keyboard
    def binary_keyboard():
        expiry_btns = []
        for k, v in BINARY_EXPIRIES.items():
            marker = " ✅" if k == active_binary_expiry else ""
            expiry_btns.append(InlineKeyboardButton(v["emoji"] + " " + v["label"] + marker, callback_data="binary_expiry_" + k))
        return InlineKeyboardMarkup([
            expiry_btns[:2], expiry_btns[2:],
            [InlineKeyboardButton("⚡ Scan Now", callback_data="binary_scan"),
             InlineKeyboardButton("📊 Stats",   callback_data="binary_stats")],
            [InlineKeyboardButton("📋 History", callback_data="binary_history"),
             InlineKeyboardButton("🏠 Menu",    callback_data="menu_main")],
        ])

    if data.startswith("binary_broker_"):
        global active_broker
        new_broker   = data[14:]
        old_broker   = active_broker
        active_broker = new_broker
        bv           = BROKERS[new_broker]
        weekend      = is_weekend_otc()
        mode_label   = "🌙 OTC Mode" if weekend else "📅 Regular Mode"
        sym_count    = len(get_active_binary_symbols())
        nl2          = chr(10)

        # Rebuild binary keyboard
        expiry_btns2 = []
        for k, v in BINARY_EXPIRIES.items():
            marker = " ✅" if k == active_binary_expiry else ""
            expiry_btns2.append(InlineKeyboardButton(v["emoji"] + " " + v["label"] + marker, callback_data="binary_expiry_" + k))
        broker_btns2 = [
            InlineKeyboardButton(
                BROKERS[bk]["emoji"] + " " + BROKERS[bk]["label"] + (" ✅" if bk == active_broker else ""),
                callback_data="binary_broker_" + bk
            ) for bk in BROKERS
        ]
        kb2 = InlineKeyboardMarkup([
            broker_btns2,
            [InlineKeyboardButton("⚡ Scan Now", callback_data="binary_scan"),
             InlineKeyboardButton("📊 Stats",   callback_data="binary_stats")],
            [InlineKeyboardButton("📋 History", callback_data="binary_history"),
             InlineKeyboardButton("🏠 Menu",    callback_data="menu_main")],
        ])
        await fresh_binary(
            bv["emoji"] + " *Switched to " + bv["label"] + "!*" + nl2 + nl2 +
            "Mode: " + mode_label + nl2 +
            "Assets available: `" + str(sym_count) + "`" + nl2 + nl2 +
            ("📅 Showing regular pairs" if not weekend and new_broker != "quotex" else "🌙 Showing OTC pairs") + nl2 + nl2 +
            "Tap *Scan Binary Now* to start:",
            kb2
        )

    elif data.startswith("binary_expiry_"):
        new_expiry         = data[14:]
        old_expiry         = active_binary_expiry
        active_binary_expiry = new_expiry
        new_e = BINARY_EXPIRIES[new_expiry]
        old_e = BINARY_EXPIRIES[old_expiry]
        await fresh_binary(
            "⏱ *Expiry Switched!*" + nl + nl +
            "Old: " + old_e["emoji"] + " " + old_e["label"] + nl +
            "New: " + new_e["emoji"] + " *" + new_e["label"] + "* ✅" + nl + nl +
            "Tap *Scan Now* to find signals with this expiry:",
            binary_keyboard()
        )

    elif data == "binary_scan":
        await fresh_binary("⚡ *Scanning binary signals...*" + nl + "⏳ Checking all pairs...")
        await scan_binary_signals(context, manual=True)

    elif data == "binary_stats":
        total  = binary_performance["total"]
        wins   = binary_performance["wins"]
        losses = binary_performance["losses"]
        pend   = binary_performance["pending"]
        closed = wins + losses
        wr     = round((wins / closed) * 100, 1) if closed > 0 else 0
        filled = int(wr / 10)
        wr_bar = "█" * filled + "░" * (10 - filled)
        streak_type = binary_streak["type"] or "None"
        streak_icon = "🔥" if streak_type == "WIN" else ("💧" if streak_type == "LOSS" else "")
        asset_lines = ""
        if binary_asset_stats:
            sorted_assets = sorted(binary_asset_stats.items(),
                key=lambda x: x[1]["wins"] / max(x[1]["total"], 1), reverse=True)
            asset_lines = nl + "━━━━━━━━━━━━━━━━━━━━" + nl + "🏆 *Best Pairs:*" + nl
            medals = ["🥇", "🥈", "🥉"]
            for i, (asset, stats) in enumerate(sorted_assets[:8]):
                asset_wr = round(stats["wins"] / stats["total"] * 100) if stats["total"] > 0 else 0
                medal    = medals[i] if i < 3 else "  "
                bf       = int(asset_wr / 20)
                mini_bar = "█" * bf + "░" * (5 - bf)
                asset_lines += medal + " *" + asset + ":* `" + mini_bar + "` " + str(asset_wr) + "% (" + str(stats["wins"]) + "W/" + str(stats["losses"]) + "L)" + nl
        msg = (
            "📊 *Binary Performance Dashboard*" + nl + nl +
            "━━━━━━━━━━━━━━━━━━━━" + nl +
            "✅ Wins: `" + str(wins) + "` | ❌ Losses: `" + str(losses) + "` | ⏳ `" + str(pend) + "`" + nl + nl +
            "📈 *Win Rate:* `" + wr_bar + "` *" + str(wr) + "%*" + nl + nl +
            "━━━━━━━━━━━━━━━━━━━━" + nl +
            "⚡ *Streak:* " + streak_icon + " `" + str(binary_streak["current"]) + "x " + streak_type + "`" + nl +
            "🏆 Best win streak:   `" + str(binary_streak["best_win"]) + "`" + nl +
            "💧 Worst loss streak: `" + str(binary_streak["worst_loss"]) + "`" +
            asset_lines + nl + "🕐 `" + to_user_time() + "`"
        )
        await fresh_binary(msg, binary_keyboard())

    elif data == "binary_history":
        if not binary_results:
            msg = "📋 *No binary trades yet.*" + nl + "Tap Scan Now!"
        else:
            msg = "📋 *Binary History*" + nl + nl
            for r in binary_results[:8]:
                emoji = "✅" if r["result"] == "WIN" else "❌"
                de    = "⬆️" if r["direction"] == "CALL" else "⬇️"
                msg  += emoji + " " + de + " " + r["symbol"] + " " + r["direction"] + " — " + r["result"] + nl
                msg  += "   Entry:`" + str(round(r["entry"],4)) + "` Close:`" + str(round(r["close"],4)) + "` " + r["time"] + nl + nl
        await fresh_binary(msg, binary_keyboard())


async def cmd_help(update: Update, context):
    await update.message.reply_text(
        "📖 *How to Use @FaroSignal_bot*\n\n"
        "*Probability Score:*\n"
        "🔥 85-100% — Very strong, trade it\n"
        "💪 70-84%  — Strong, good to trade\n"
        "✅ 55-69%  — Moderate, smaller lot\n"
        "⚠️ Below 55% — Weak, skip it\n\n"
        "*MTF — Multi-Timeframe:*\n"
        "All 3 timeframes agree = strongest signal\n"
        "2/3 agree = good signal\n"
        "1/3 agree = wait for better setup\n\n"
        "*SMC Concepts:*\n"
        "🏦 OB — Order Block\n"
        "📈 BOS — Break of Structure\n"
        "🔄 CHoCH — Trend reversal warning\n"
        "⚡ FVG — Fair Value Gap\n"
        "💧 Liq.Sweep — Smart money move\n\n"
        "*Risk Rules:*\n"
        "• Always set Stop Loss\n"
        "• Use /risk to get correct lot size\n"
        "• Max 2% risk per trade\n"
        "• Check /calendar before trading",
        parse_mode="Markdown"
    )

# ============================================================
#   MAIN
# ============================================================

async def check_signal_expiry(context):
    """
    Every 60s — check if signals were entered within 15 minutes.
    If not entered in time → mark as MISSED and remove from open_trades.
    Also checks if price moved into entry zone (entry_triggered).
    """
    # Skip in binary mode — binary trades managed separately
    if active_market == "binary":
        return

    global performance
    now    = datetime.now(timezone.utc).timestamp()
    closed = []
    nl     = chr(10)

    for trade in open_trades:
        # Skip trades that already have entry confirmed
        if trade.get("entry_triggered"):
            continue

        current_data = get_current_price(trade["symbol"])
        if not current_data:
            continue

        current = current_data["price"]
        entry   = trade["price"]
        signal  = trade["signal"]
        sl      = trade["sl"]
        sl_usd  = trade["sl_usd"]

        # Check if price moved toward trade (within 0.3 x SL = entry triggered)
        if signal == "BUY":
            price_moved = current >= entry - (sl_usd * 0.3)
        else:
            price_moved = current <= entry + (sl_usd * 0.3)

        if price_moved:
            trade["entry_triggered"] = True
            logger.info(f"✅ {trade['display']} entry triggered — price moved into zone")
            continue

        # Check 15-minute expiry
        if now >= trade["entry_expiry_time"] and not trade.get("entry_missed_noted"):
            trade["entry_missed_noted"] = True

            # Update outcome to MISSED in history
            for h in signal_history:
                if h["id"] == trade["id"]:
                    h["outcome"] = "MISSED"
                    break

            performance["pending"] -= 1
            performance["total"]   -= 1   # Don't count missed in stats

            send_message(
                "⏰ *SIGNAL EXPIRED — NOT ENTERED*" + nl + nl +
                "❌ " + trade["display"] + " " + signal + " signal was not triggered." + nl + nl +
                "Entry price: `" + str(round(entry, 2)) + "`" + nl +
                "Current:     `" + str(round(current, 2)) + "`" + nl +
                "Expired:     15 minutes passed" + nl + nl +
                "_This trade has been removed from tracking._" + nl +
                "_Wait for the next signal!_ 🔄"
            )
            closed.append(trade)

    for t in closed:
        if t in open_trades:
            open_trades.remove(t)


async def post_init(application):
    """Called after bot starts — schedules all jobs reliably."""
    jq = application.job_queue

    # ── FIX: Build rotation queue immediately on startup ──────
    rebuild_symbol_queue()
    logger.info(f"🔄 Queue initialized: {[SYMBOLS[s]['display'] for s in symbol_queue]}")

    jq.run_repeating(check_signals,           interval=active_scan["seconds"], first=15,  name="signal_scan")
    jq.run_repeating(check_binary_results,    interval=30,  first=20)
    jq.run_repeating(check_trade_outcomes,    interval=60,  first=30)
    jq.run_repeating(check_user_trades,       interval=60,  first=15)
    jq.run_repeating(send_daily_summary,      interval=300, first=30)
    jq.run_repeating(check_signal_expiry,     interval=60,  first=45)
    jq.run_repeating(auto_binary_queue_scan,  interval=300, first=60, name="binary_auto_scan")  # Every 5 min

    logger.info("✅ All jobs scheduled via post_init")


def main():
    logger.info("🚀 @FaroSignal_bot starting...")
    forex_open, _ = is_forex_open()
    sessions      = get_active_sessions()

    send_message(
        "🤖 *@FaroSignal_bot — Ultimate Edition!*\n\n"
        "📌 XAUUSD | BTCUSD | ETHUSD\n\n"
        "🧠 *Full Engine:*\n"
        "✅ RSI + MA + MACD\n"
        "✅ Multi-Timeframe (30M + 1H + 4H)\n"
        "✅ SMC: OB, BOS, CHoCH, FVG, Liq.Sweep\n"
        "✅ Price Action patterns\n"
        "✅ Risk/Reward calculator\n"
        "✅ Performance tracker\n"
        "✅ Economic calendar alerts\n"
        "✅ Daily market summary\n"
        "✅ Trailing stop suggestions\n"
        "✅ Dashboard command\n\n"
        f"📊 Forex: {'🟢 Open' if forex_open else '🔴 Closed'}\n"
        f"🌍 Sessions: {', '.join(sessions) if sessions else 'None'}\n\n"
        "Type /help to get started! 🚀"
    )

    app = Application.builder().token(TELEGRAM_TOKEN).post_init(post_init).build()

    app.add_handler(CommandHandler("start",       cmd_start))
    app.add_handler(CommandHandler("menu",        cmd_menu))
    app.add_handler(CommandHandler("scan",        cmd_scan))
    app.add_handler(CallbackQueryHandler(handle_trade_callback,    pattern="^trade_"))
    app.add_handler(CallbackQueryHandler(handle_timezone_callback, pattern="^tz_"))
    app.add_handler(CallbackQueryHandler(handle_binary_callback,   pattern="^binary_"))
    app.add_handler(CallbackQueryHandler(handle_callback,          pattern="^(?!binary_|tz_|trade_)"))
    app.add_handler(CommandHandler("binary",   cmd_binary))
    app.add_handler(CommandHandler("timezone", cmd_timezone))
    app.add_handler(CommandHandler("mytrades", cmd_mytrades))
    # timeframe switching now handled via inline buttons (menu_timeframe callback)
    app.add_handler(CommandHandler("price",       cmd_price))
    app.add_handler(CommandHandler("risk",        cmd_risk))
    app.add_handler(CommandHandler("performance", cmd_performance))
    app.add_handler(CommandHandler("calendar",    cmd_calendar))
    app.add_handler(CommandHandler("dashboard",   cmd_dashboard))
    app.add_handler(CommandHandler("market",      cmd_market))
    app.add_handler(CommandHandler("history",     cmd_history))
    app.add_handler(CommandHandler("news",        cmd_news))
    app.add_handler(CommandHandler("status",      cmd_status))
    app.add_handler(CommandHandler("help",        cmd_help))

    logger.info("✅ Bot running! Jobs will start via post_init...")
    app.run_polling()

if __name__ == "__main__":
    main()
