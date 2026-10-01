"""Local intraday candlestick study app.

Fetches session bars and describes what the latest candles lean toward.
It does not place orders and it does not promise the next price.
"""

from __future__ import annotations

import math
import json
import threading
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from html import unescape
from datetime import datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote as urlquote, urlparse
from zoneinfo import ZoneInfo

HOST = "127.0.0.1"
PORT = 8765
ROOT = Path(__file__).resolve().parent
INDEX = ROOT / "static" / "index.html"
IST = ZoneInfo("Asia/Kolkata")
INTERVALS = {"1m": "1 minute", "5m": "5 minutes", "15m": "15 minutes"}
INTERVAL_MINUTES = {"1m": 1, "5m": 5, "15m": 15}
LIBRARY_RANGE = {"1m": "5d", "5m": "1mo", "15m": "1mo"}
RANGES = {"1d": "today", "5d": "last 5 sessions"}
WINDOW = 12
HORIZON = 8
SCAN_TTL = 300
LIQUID_NSE = (
    "RELIANCE", "TCS", "HDFCBANK", "BHARTIARTL", "ICICIBANK", "INFY", "SBIN",
    "HINDUNILVR", "ITC", "LT", "BAJFINANCE", "HCLTECH", "KOTAKBANK", "AXISBANK",
    "MARUTI", "SUNPHARMA", "TITAN", "NTPC", "ADANIENT", "WIPRO", "JSWSTEEL",
    "COALINDIA", "ONGC", "HINDALCO", "TECHM", "CIPLA", "TATASTEEL", "POWERGRID",
    "BAJAJFINSV", "ASIANPAINT", "ULTRACEMCO", "INDUSINDBK", "DRREDDY", "EICHERMOT",
    "HEROMOTOCO", "BPCL", "BEL", "HAL", "TRENT", "ADANIPORTS",
)
_scan_state = {"lock": threading.Lock(), "payload": None, "fetched_at": 0.0, "running": False, "retry_after": 0.0}
GROWW_CACHE = ROOT / "groww_names.json"
_groww_lock = threading.Lock()
_groww_names: dict[str, dict] = {}


def search_symbol(query: str) -> str | None:
    url = (
        "https://query1.finance.yahoo.com/v1/finance/search?q="
        + urlquote(query)
        + "&quotesCount=10&newsCount=0"
    )
    request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 CandleStudy/1.0"})
    try:
        with urllib.request.urlopen(request, timeout=20) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError):
        return None
    for item in payload.get("quotes") or []:
        symbol = str(item.get("symbol") or "")
        if symbol.endswith(".NS") and item.get("quoteType") in (None, "EQUITY", "ETF"):
            return symbol
    return None


def resolve_symbol(raw: str) -> str:
    text = (raw or "").strip()
    if not text:
        raise ValueError("Enter a stock symbol or company name.")
    upper = text.upper()
    if upper.startswith("^") or "." in text or upper.endswith("-USD"):
        return upper
    if " " in text:
        match = search_symbol(text)
        if not match:
            raise ValueError(f"No NSE stock found for {text}.")
        return match
    return upper + ".NS"


def _read_groww_cache() -> None:
    try:
        saved = json.loads(GROWW_CACHE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return
    if not isinstance(saved, dict):
        return
    with _groww_lock:
        for key, value in saved.items():
            if isinstance(value, dict) and value.get("name") and value.get("url"):
                _groww_names[str(key).upper()] = value


def _groww_query(query: str, key: str) -> dict | None:
    url = (
        "https://groww.in/v1/api/search/v3/query/global/st_p_query"
        f"?entity_type=stocks&page=0&query={urlquote(query)}&size=8&web=true"
    )
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "Mozilla/5.0 CandleStudy/1.0", "Accept": "application/json"},
    )
    try:
        with urllib.request.urlopen(request, timeout=12) as response:
            payload = json.loads(response.read().decode("utf-8"))
        content = ((payload.get("data") or {}).get("content")) or []
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError, OSError):
        return None
    for item in content:
        if str(item.get("entity_type") or "") != "Stocks":
            continue
        if str(item.get("nse_scrip_code") or "").upper() != key:
            continue
        search_id = str(item.get("search_id") or "").strip()
        title = str(item.get("title") or "").strip()
        if search_id and title:
            return {"name": title, "url": f"https://groww.in/stocks/{search_id}"}
    return None


def groww_stock(symbol: str, *hints: str) -> dict:
    """Groww's own company name and stock page for an NSE symbol."""
    key = symbol.upper().split(".")[0].strip()
    with _groww_lock:
        cached = _groww_names.get(key)
    if cached:
        return cached
    fallback = {"name": "", "url": f"https://groww.in/search?q={urlquote(key)}"}
    queries = [key]
    for hint in hints:
        text = " ".join(str(hint or "").split())
        if text and text.upper() not in {key, f"{key}.NS"} and text not in queries:
            queries.append(text)
    found = None
    for query in queries:
        found = _groww_query(query, key)
        if found:
            break
    if not found:
        return fallback
    with _groww_lock:
        _groww_names[key] = found
        try:
            GROWW_CACHE.write_text(json.dumps(_groww_names, ensure_ascii=False, indent=2), encoding="utf-8")
        except OSError:
            pass
    return found


_read_groww_cache()

_bar_cache: dict[tuple[str, str, str], tuple[float, list[dict], dict]] = {}
_bar_cache_lock = threading.Lock()
BAR_CACHE_TTL = 45


def load_bars(symbol: str, interval: str, range_name: str) -> tuple[list[dict], dict]:
    if interval not in {"1m", "5m", "15m", "1d"}:
        interval = "5m"
    if range_name not in {"1d", "5d", "1mo", "6mo"}:
        range_name = "1d"
    cache_key = (symbol, interval, range_name)
    cached_at = time.monotonic()
    with _bar_cache_lock:
        cached = _bar_cache.get(cache_key)
        if cached and cached_at - cached[0] < BAR_CACHE_TTL:
            bars, meta = cached[1], cached[2]
            return [dict(bar) for bar in bars], dict(meta)
    url = (
        "https://query1.finance.yahoo.com/v8/finance/chart/"
        f"{urlquote(symbol, safe='')}?interval={interval}&range={range_name}&includePrePost=false"
    )
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "Mozilla/5.0 CandleStudy/1.0"},
    )
    try:
        with urllib.request.urlopen(request, timeout=20) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        raise ValueError(f"Price source returned {exc.code} for {symbol}.") from exc
    except urllib.error.URLError as exc:
        raise ValueError("Could not reach the price source. Check the internet connection.") from exc

    result = (payload.get("chart") or {}).get("result") or []
    if not result:
        error = ((payload.get("chart") or {}).get("error") or {}).get("description")
        raise ValueError(error or f"No price data for {symbol}.")

    chart = result[0]
    timestamps = chart.get("timestamp") or []
    quote = ((chart.get("indicators") or {}).get("quote") or [{}])[0]
    meta = chart.get("meta") or {}
    candles = []
    for index, stamp in enumerate(timestamps):
        open_ = _num(quote.get("open"), index)
        high = _num(quote.get("high"), index)
        low = _num(quote.get("low"), index)
        close = _num(quote.get("close"), index)
        volume = _num(quote.get("volume"), index)
        if None in (open_, high, low, close):
            continue
        moment = datetime.fromtimestamp(stamp, IST)
        minute_of_day = moment.hour * 60 + moment.minute
        if interval != "1d" and (minute_of_day < 9 * 60 + 15 or minute_of_day > 15 * 60 + 30):
            continue
        candles.append(
            {
                "epoch": int(stamp),
                "date": moment.strftime("%Y-%m-%d"),
                "time": moment.strftime("%H:%M"),
                "open": round(open_, 2),
                "high": round(high, 2),
                "low": round(low, 2),
                "close": round(close, 2),
                "volume": int(volume or 0),
            }
        )
    if len(candles) < 3:
        raise ValueError(f"Need at least 3 intraday candles for {symbol}.")
    with _bar_cache_lock:
        _bar_cache[cache_key] = (time.monotonic(), candles, meta)
    return candles, meta


def _load_or_empty(symbol: str, interval: str, range_name: str) -> tuple[list[dict], dict]:
    try:
        return load_bars(symbol, interval, range_name)
    except ValueError:
        return [], {}


def fetch_candles(symbol: str, interval: str = "5m", range_name: str = "1d") -> dict:
    if interval not in INTERVALS:
        interval = "5m"
    if range_name not in RANGES:
        range_name = "1d"
    library = LIBRARY_RANGE[interval]
    with ThreadPoolExecutor(max_workers=6) as pool:
        stock_task = pool.submit(load_bars, symbol, interval, library)
        nifty_task = pool.submit(_load_or_empty, "^NSEI", interval, library)
        daily_task = pool.submit(_load_or_empty, symbol, "1d", "6mo")
        bank_task = pool.submit(_load_or_empty, "^NSEBANK", interval, "1d")
        context_task = pool.submit(load_market_context)
        history, meta = stock_task.result()
        news_task = pool.submit(load_news, meta.get("longName") or meta.get("shortName") or symbol)
        listing_task = pool.submit(
            groww_stock,
            meta.get("symbol") or symbol,
            meta.get("shortName") or "",
            meta.get("longName") or "",
        )
        market, _ = nifty_task.result()
        daily, daily_meta = daily_task.result()
        bank_bars, _ = bank_task.result()
        market_context = context_task.result()
        news = news_task.result()
        listing = listing_task.result()
    if not daily:
        daily, daily_meta = history, meta
    session_day = history[-1]["date"]
    session = [candle for candle in history if candle["date"] == session_day]
    if len(session) < 3:
        raise ValueError("Today's session does not have 3 candles yet.")
    days = list(dict.fromkeys(candle["date"] for candle in history))
    previous_day = [candle for candle in history if len(days) >= 2 and candle["date"] == days[-2]]
    company = company_situation(daily, daily_meta or meta, session, previous_day)
    direction = next_day_direction(daily, market_context, news, session)
    candle_call = next_candle_direction(history, session, previous_day, market, bank_bars, interval)
    projection = project(history, market, interval)
    chart_price, chart_until = path_reach(projection)
    watched = price_with_news(history[-1]["close"], chart_price, news)
    watched["until"] = chart_until
    watched["summary"] = news["summary"]
    genius = genius_note({
        "price": history[-1]["close"],
        "futurePrice": watched["futurePrice"],
        "pathUntil": chart_until,
        "newsSentiment": news["sentiment"],
        "grade": candle_call["desk"]["grade"],
        "lean": candle_call["lean"],
        "invalid": candle_call["desk"]["invalid"],
        "setup": candle_call["desk"]["setup"],
    })
    report = study(session, INTERVALS[interval])
    report["lean"] = direction["lean"]
    report["title"] = direction["title"]
    report["malayalam"] = direction["malayalam"]
    report["disclaimer"] = direction["disclaimer"]
    report["reasons"] = direction["reasons"]
    report["prediction"] = projection
    report["direction"] = direction
    report["candle"] = candle_call
    report["turn"] = candle_turn(session)
    market_open = _stamp_live(history, interval, meta)
    yahoo_name = meta.get("shortName") or meta.get("longName") or symbol
    return {
        "symbol": meta.get("symbol") or symbol,
        "name": listing["name"] or yahoo_name,
        "growwUrl": listing["url"],
        "currency": meta.get("currency") or "",
        "exchange": meta.get("exchangeName") or "",
        "interval": interval,
        "intervalLabel": INTERVALS[interval],
        "marketOpen": market_open,
        "range": range_name,
        "candles": session,
        "intraday": history,
        "previousDay": previous_day,
        "previousDate": previous_day[0]["date"] if previous_day else "",
        "dailyHistory": daily,
        "news": news,
        "future": watched,
        "genius": genius,
        "company": company,
        "study": report,
    }


def _shape(closes: list[float]) -> list[float]:
    base = closes[0] or 1.0
    return [(price / base) - 1 for price in closes]


def _mean_abs(left: list[float], right: list[float]) -> float:
    return sum(abs(a - b) for a, b in zip(left, right)) / len(left)


def _next_bar_epoch(epoch: int, step_seconds: int) -> int:
    moment = datetime.fromtimestamp(epoch + step_seconds, IST)
    for _ in range(8):
        if moment.weekday() >= 5:
            moment = (moment + timedelta(days=7 - moment.weekday())).replace(hour=9, minute=15, second=0, microsecond=0)
            continue
        minute_of_day = moment.hour * 60 + moment.minute
        if minute_of_day < 9 * 60 + 15:
            moment = moment.replace(hour=9, minute=15, second=0, microsecond=0)
            continue
        if minute_of_day > 15 * 60 + 30:
            moment = (moment + timedelta(days=1)).replace(hour=9, minute=15, second=0, microsecond=0)
            continue
        return int(moment.timestamp())
    return int(moment.timestamp())


def session_horizon(history: list[dict]) -> int:
    counts: dict[str, int] = {}
    for candle in history:
        counts[candle["date"]] = counts.get(candle["date"], 0) + 1
    last_day = history[-1]["date"]
    earlier = [count for day, count in counts.items() if day != last_day]
    typical = max(earlier) if earlier else max(counts.values())
    return max(HORIZON, min(typical, 400))


def _minute_of_day(candle: dict) -> int:
    hour, minute = candle["time"].split(":")
    return int(hour) * 60 + int(minute)


def _advance_bar(moment: datetime, minutes: int) -> datetime:
    moment = moment + timedelta(minutes=minutes)
    for _ in range(8):
        if moment.weekday() >= 5:
            moment = (moment + timedelta(days=(7 - moment.weekday()))).replace(hour=9, minute=15, second=0, microsecond=0)
            continue
        minute_of_day = moment.hour * 60 + moment.minute
        if minute_of_day < 9 * 60 + 15:
            moment = moment.replace(hour=9, minute=15, second=0, microsecond=0)
            continue
        if minute_of_day > 15 * 60 + 30:
            moment = (moment + timedelta(days=1)).replace(hour=9, minute=15, second=0, microsecond=0)
            continue
        return moment
    return moment


def _recent_drift(bars: list[dict]) -> float:
    recent = bars[-4:]
    changes = []
    for index in range(1, len(recent)):
        previous = recent[index - 1]["close"]
        if previous:
            changes.append(recent[index]["close"] / previous - 1)
    if not changes:
        return 0.0
    drift = sum(changes) / len(changes)
    return max(-0.01, min(0.01, drift))


def project(history: list[dict], market: list[dict], interval: str) -> dict:
    window = min(WINDOW, max(6, len(history) // 5))
    horizon = session_horizon(history)
    bars = list(history)
    while len(bars) > 8 and bars[-1]["high"] == bars[-1]["low"] and bars[-1]["volume"] == 0:
        bars.pop()
    last_close = bars[-1]["close"]
    drift = _recent_drift(bars)
    current = bars[-window:]
    current_shape = _shape([candle["close"] for candle in current])
    market_close = {candle["epoch"]: candle["close"] for candle in market}

    def market_shape(candles: list[dict]) -> list[float] | None:
        closes = []
        for candle in candles:
            price = market_close.get(candle["epoch"])
            if price is None:
                return None
            closes.append(price)
        return _shape(closes)

    current_market = market_shape(current)
    current_minute = _minute_of_day(current[-1])
    matches: list[tuple[float, list[float]]] = []
    last_index = len(bars) - horizon - 1
    for index in range(window - 1, last_index):
        if index >= len(bars) - window:
            continue
        chunk = bars[index - window + 1:index + 1]
        future = bars[index + 1:index + 1 + horizon]
        if chunk[-1]["close"] <= 0 or len(future) < horizon:
            continue
        distance = _mean_abs(current_shape, _shape([candle["close"] for candle in chunk]))
        if current_market is not None:
            past_market = market_shape(chunk)
            if past_market is not None:
                distance = distance * 0.7 + _mean_abs(current_market, past_market) * 0.3
        age = (len(bars) - 1 - index) / len(bars)
        distance += age * 0.004
        distance += abs(current_minute - _minute_of_day(chunk[-1])) / 390 * 0.03
        returns = [(bar["close"] / chunk[-1]["close"]) - 1 for bar in future]
        matches.append((distance, returns))

    matches.sort(key=lambda item: item[0])
    chosen = matches[:8]
    used_market = current_market is not None
    if len(chosen) >= 3:
        step_returns, step_lows, step_highs = _average_paths([item[1] for item in chosen])
        basis = f"Projected from {len(chosen)} similar past stretches"
        if used_market:
            nifty_move = current_market[-1] * 100
            basis += f", preferring times when Nifty moved like this stretch ({nifty_move:+.2f}%)."
        else:
            basis += "."
    else:
        step_returns, step_lows, step_highs = _slope_path(bars[-window:], horizon)
        basis = "Similar past stretches were scarce, so the line follows the recent slope."

    sign = 1 if drift > 0.0004 else (-1 if drift < -0.0004 else 0)
    running = 0.0
    recent_range = _atr(bars[-15:], 8) or abs(bars[-1]["high"] - bars[-1]["low"]) or last_close * 0.003
    for index, change in enumerate(step_returns):
        if index < 3:
            running += drift * (0.85 ** index)
            step_returns[index] = running
        elif sign and change * sign < 0:
            step_returns[index] = change * 0.35
        price = last_close * (1 + step_returns[index])
        pad = recent_range * (0.55 if index < 3 else 1)
        step_highs[index] = max(step_highs[index], (max(last_close, price) + pad * 0.35) / last_close - 1)
        step_lows[index] = min(step_lows[index], (min(last_close, price) - pad * 0.35) / last_close - 1)
        if index < 3:
            step_highs[index] = (max(last_close, price) + pad * (0.35 if drift >= 0 else 0.7)) / last_close - 1
            step_lows[index] = (min(last_close, price) - pad * (0.7 if drift >= 0 else 0.35)) / last_close - 1

    points = []
    moment = _advance_bar(datetime.fromtimestamp(bars[-1]["epoch"], IST), INTERVAL_MINUTES[interval])
    for step_index, change in enumerate(step_returns):
        if moment.hour * 60 + moment.minute > 15 * 60 + 30:
            break
        points.append(
            {
                "date": moment.strftime("%Y-%m-%d"),
                "time": moment.strftime("%H:%M"),
                "price": round(last_close * (1 + change), 2),
                "low": round(last_close * (1 + step_lows[step_index]), 2),
                "high": round(last_close * (1 + step_highs[step_index]), 2),
            }
        )
        moment = _advance_bar(moment, INTERVAL_MINUTES[interval])
    end_price = points[-1]["price"]
    change_pct = (end_price / last_close - 1) * 100
    when = f"{points[-1]['date']} {points[-1]['time']}"
    if change_pct >= 0.35:
        lean = "up"
        title = f"Projected path leans up to {end_price:.2f}"
        malayalam = "ചരിത്രവും മാർക്കറ്റും വച്ചുള്ള വഴി മുകളിലേക്ക് ചായുന്നു. അടുത്ത വില അങ്ങനെ ആകുമെന്ന ഉറപ്പ് ഇതല്ല."
    elif change_pct <= -0.35:
        lean = "down"
        title = f"Projected path leans down to {end_price:.2f}"
        malayalam = "ചരിത്രവും മാർക്കറ്റും വച്ചുള്ള വഴി താഴേക്ക് ചായുന്നു. അടുത്ത വില അങ്ങനെ ആകുമെന്ന ഉറപ്പ് ഇതല്ല."
    else:
        lean = "mixed"
        title = f"Projected path stays near {end_price:.2f}"
        malayalam = "ചരിത്രവും മാർക്കറ്റും വച്ചുള്ള വഴി വ്യക്തമായി ഒരു വശത്തേക്ക് ചായുന്നില്ല."
    return {
        "lean": lean,
        "title": title,
        "malayalam": malayalam,
        "basis": basis,
        "lastClose": round(last_close, 2),
        "endPrice": end_price,
        "changePct": round(change_pct, 2),
        "until": when,
        "points": points,
        "disclaimer": "The lower graph sketches the next session from past moves and Nifty. It is not a guaranteed price.",
    }


def _average_paths(paths: list[list[float]]) -> tuple[list[float], list[float], list[float]]:
    averages = []
    lows = []
    highs = []
    for step in range(len(paths[0])):
        values = sorted(path[step] for path in paths)
        averages.append(sum(values) / len(values))
        lows.append(values[len(values) // 4])
        highs.append(values[(len(values) * 3) // 4])
    return averages, lows, highs


def _slope_path(candles: list[dict], horizon: int) -> tuple[list[float], list[float], list[float]]:
    closes = [candle["close"] for candle in candles]
    count = len(closes)
    mean_x = (count - 1) / 2
    mean_y = sum(closes) / count
    variance = sum((index - mean_x) ** 2 for index in range(count)) or 1
    slope = sum((index - mean_x) * (price - mean_y) for index, price in enumerate(closes)) / variance
    last = closes[-1] or 1
    averages = []
    lows = []
    highs = []
    for step in range(1, horizon + 1):
        change = (last + slope * step) / last - 1
        averages.append(change)
        lows.append(change - 0.004 * step)
        highs.append(change + 0.004 * step)
    return averages, lows, highs


def _num(values, index):
    if not values or index >= len(values):
        return None
    value = values[index]
    if value is None:
        return None
    return float(value)


def candle_facts(candle: dict, previous: dict | None) -> dict:
    open_, high, low, close = candle["open"], candle["high"], candle["low"], candle["close"]
    span = max(high - low, 0.0001)
    body = abs(close - open_)
    upper = high - max(open_, close)
    lower = min(open_, close) - low
    direction = "green" if close > open_ else "red" if close < open_ else "doji"
    close_pos = (close - low) / span
    facts = {
        "date": candle["date"],
        "time": candle.get("time", ""),
        "open": open_,
        "high": high,
        "low": low,
        "close": close,
        "volume": candle["volume"],
        "direction": direction,
        "bodyPct": round(body / span * 100, 1),
        "upperWickPct": round(upper / span * 100, 1),
        "lowerWickPct": round(lower / span * 100, 1),
        "closePos": round(close_pos, 2),
    }
    notes = []
    if direction == "green":
        notes.append("Close finished above the open.")
    elif direction == "red":
        notes.append("Close finished below the open.")
    else:
        notes.append("Open and close are almost the same.")
    if facts["upperWickPct"] >= 40:
        notes.append("Long upper wick: the high was sold.")
    if facts["lowerWickPct"] >= 40:
        notes.append("Long lower wick: the low was bought.")
    if previous and close > previous["high"]:
        notes.append("Closed above the previous high.")
    if previous and close < previous["low"]:
        notes.append("Closed below the previous low.")
    facts["notes"] = notes
    return facts


def session_vwap(candles: list[dict]) -> float:
    traded = 0.0
    volume = 0.0
    for candle in candles:
        typical = (candle["high"] + candle["low"] + candle["close"]) / 3
        traded += typical * candle["volume"]
        volume += candle["volume"]
    if volume <= 0:
        return sum(candle["close"] for candle in candles) / len(candles)
    return traded / volume


def _pct_change(closes: list[float], days: int) -> float | None:
    if len(closes) <= days or closes[-1 - days] == 0:
        return None
    return (closes[-1] / closes[-1 - days] - 1) * 100


def _ema(values: list[float], length: int) -> float | None:
    if len(values) < length:
        return None
    weight = 2 / (length + 1)
    value = sum(values[:length]) / length
    for price in values[length:]:
        value = price * weight + value * (1 - weight)
    return value


def _rsi(closes: list[float], length: int = 14) -> float | None:
    if len(closes) < length + 1:
        return None
    gains = 0.0
    losses = 0.0
    for index in range(-length, 0):
        change = closes[index] - closes[index - 1]
        if change >= 0:
            gains += change
        else:
            losses -= change
    if losses == 0:
        return 100.0
    relative = (gains / length) / (losses / length)
    return 100 - (100 / (1 + relative))


def _macd_histogram(closes: list[float]) -> float | None:
    if len(closes) < 35:
        return None
    macd_line = []
    for end in range(26, len(closes) + 1):
        window = closes[:end]
        fast = _ema(window, 12)
        slow = _ema(window, 26)
        if fast is None or slow is None:
            continue
        macd_line.append(fast - slow)
    signal = _ema(macd_line, 9)
    if signal is None or not macd_line:
        return None
    return macd_line[-1] - signal


def _atr(candles: list[dict], length: int = 14) -> float | None:
    if len(candles) < length + 1:
        return None
    ranges = []
    for index in range(1, len(candles)):
        previous = candles[index - 1]["close"]
        ranges.append(max(
            candles[index]["high"] - candles[index]["low"],
            abs(candles[index]["high"] - previous),
            abs(candles[index]["low"] - previous),
        ))
    return sum(ranges[-length:]) / length


def _last_return(symbol: str, days: int = 1) -> float | None:
    try:
        bars, _ = load_bars(symbol, "1d", "1mo")
    except ValueError:
        return None
    closes = [bar["close"] for bar in bars]
    return _pct_change(closes, days)


def load_market_context() -> dict:
    names = {
        "nifty": "^NSEI",
        "bankNifty": "^NSEBANK",
        "vix": "^INDIAVIX",
        "usdInr": "INR=X",
        "crude": "BZ=F",
    }
    with ThreadPoolExecutor(max_workers=len(names)) as pool:
        loaded = {name: pool.submit(_load_or_empty, symbol, "1d", "1mo") for name, symbol in names.items()}
        bars = {name: future.result()[0] for name, future in loaded.items()}

    def change(series: list[dict], days: int) -> float | None:
        return _pct_change([bar["close"] for bar in series], days)

    nifty = bars["nifty"]
    return {
        "nifty": change(nifty, 1),
        "nifty5": change(nifty, 5),
        "bankNifty": change(bars["bankNifty"], 1),
        "vix": change(bars["vix"], 1),
        "usdInr": change(bars["usdInr"], 1),
        "crude": change(bars["crude"], 1),
    }


def _headline_tone(title: str) -> str:
    text = title.lower()
    positive = ("order", "profit", "growth", "upgrade", "surge", "rally", "beat", "approval", "contract", "dividend", "gain", "jumps", "record", "wins")
    negative = ("loss", "fraud", "selloff", "sell-off", "tanks", "probe", "penalty", "default", "downgrade", "plunge", "slump", "crash", "resign", "raid", "ban", "gst demand", "falls", "drops")
    score = sum(word in text for word in positive) - sum(word in text for word in negative)
    if score > 0:
        return "positive"
    if score < 0:
        return "negative"
    return "neutral"


def load_news(name: str) -> dict:
    query = f"{name} NSE"
    url = "https://news.google.com/rss/search?q=" + urlquote(query) + "&hl=en-IN&gl=IN&ceid=IN:en"
    request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 CandleStudy/1.0"})
    items = []
    try:
        with urllib.request.urlopen(request, timeout=8) as response:
            root = ET.fromstring(response.read())
    except (urllib.error.URLError, ET.ParseError, TimeoutError):
        root = None
    if root is not None:
        for node in root.findall("./channel/item")[:8]:
            raw = unescape(node.findtext("title") or "").strip()
            if not raw or raw == "Google News":
                continue
            headline, _, source = raw.rpartition(" - ")
            if not headline:
                headline, source = raw, ""
            items.append({"title": headline, "source": source, "tone": _headline_tone(headline)})
    positive = sum(item["tone"] == "positive" for item in items)
    negative = sum(item["tone"] == "negative" for item in items)
    count = len(items)
    if count:
        sentiment = (positive - negative) / count
    else:
        sentiment = 0.0
    important_words = ("result", "earning", "order", "contract", "gst", "penalty", "rating", "acquisition", "resign", "probe", "dividend", "court")
    important = sum(any(word in item["title"].lower() for word in important_words) for item in items)
    importance = 0 if count == 0 else min(1.0, (important + 1) / max(count, 1))
    if count == 0:
        summary = "No recent company headlines were found."
    else:
        summary = f"News: {positive} positive, {negative} negative, {count - positive - negative} neutral. Sentiment {sentiment:+.2f}, importance {importance:.2f}."
    return {
        "items": items,
        "positive": positive,
        "negative": negative,
        "count": count,
        "sentiment": round(sentiment, 2),
        "importance": round(importance, 2),
        "summary": summary,
    }


def path_reach(path: dict) -> tuple[float, str]:
    points = path.get("points") or []
    if not points:
        return float(path["endPrice"]), str(path.get("until") or "")
    near = points[min(2, len(points) - 1)]
    return float(near["price"]), f"{near['date']} {near['time']}"


def price_with_news(price: float, chart_price: float, news: dict) -> dict:
    """Move the chart target by the headline tone. The shift is capped at 1.5% of the last price."""
    sentiment = float(news.get("sentiment") or 0)
    importance = float(news.get("importance") or 0)
    cap = abs(price) * 0.015
    shift = price * sentiment * importance * 0.015
    shift = max(-cap, min(cap, shift))
    return {
        "chartPrice": round(chart_price, 2),
        "newsShift": round(shift, 2),
        "futurePrice": round(chart_price + shift, 2),
        "sentiment": round(sentiment, 2),
    }


def company_situation(daily: list[dict], meta: dict, session: list[dict], previous: list[dict]) -> dict:
    closes = [bar["close"] for bar in daily]
    price = closes[-1]
    month = _pct_change(closes, 21)
    quarter = _pct_change(closes, 63)
    previous_close = closes[-2] if len(closes) > 1 else price
    versus_previous = (price / previous_close - 1) * 100 if previous_close else 0
    high = meta.get("fiftyTwoWeekHigh")
    low = meta.get("fiftyTwoWeekLow")
    place = "inside its 52-week range"
    if high and low and high > low:
        spot = (price - low) / (high - low)
        if spot >= 0.8:
            place = "near the 52-week high"
        elif spot <= 0.2:
            place = "near the 52-week low"
    month_text = "n/a" if month is None else f"{month:+.1f}%"
    quarter_text = "n/a" if quarter is None else f"{quarter:+.1f}%"
    summary = (
        f"Last price {price:.2f} is {place}. About one month: {month_text}. "
        f"About three months: {quarter_text}. Versus the previous close {previous_close:.2f}: {versus_previous:+.1f}%."
    )
    return {"summary": summary, "price": round(price, 2), "versusPrevious": round(versus_previous, 2)}


def _vote(value: float | None, up_at: float, down_at: float) -> int:
    if value is None:
        return 0
    if value >= up_at:
        return 1
    if value <= down_at:
        return -1
    return 0


def next_day_direction(daily: list[dict], market: dict, news: dict, session: list[dict] | None = None) -> dict:
    completed = daily
    if session and daily and session[-1]["date"] == daily[-1]["date"] and _minute_of_day(session[-1]) < 15 * 60 + 20:
        completed = daily[:-1] or daily
    closes = [bar["close"] for bar in completed]
    volumes = [bar["volume"] for bar in completed]
    day = completed[-1]
    day_span = max(day["high"] - day["low"], 0.0001)
    day_close_pos = (day["close"] - day["low"]) / day_span
    upper_wick = (day["high"] - max(day["open"], day["close"])) / day_span
    lower_wick = (min(day["open"], day["close"]) - day["low"]) / day_span
    rejection = -2 if day_close_pos <= 0.35 and upper_wick >= 0.45 else (2 if day_close_pos >= 0.65 and lower_wick >= 0.45 else 0)
    previous_return = _pct_change(closes, 1)
    five_day = _pct_change(closes, 5)
    twenty_day = _pct_change(closes, 20)
    gap = None
    if len(daily) >= 2 and daily[-2]["close"]:
        gap = (daily[-1]["open"] / daily[-2]["close"] - 1) * 100
    rsi = _rsi(closes)
    macd = _macd_histogram(closes)
    ema9 = _ema(closes, 9)
    ema21 = _ema(closes, 21)
    trend = None if ema9 is None or ema21 is None or ema21 == 0 else (ema9 / ema21 - 1) * 100
    atr = _atr(daily)
    atr_pct = None if atr is None or closes[-1] == 0 else atr / closes[-1] * 100
    volume_change = None
    if len(volumes) >= 21 and sum(volumes[-21:-1]) > 0:
        average = sum(volumes[-21:-1]) / 20
        volume_change = (volumes[-1] / average - 1) * 100
    relative = None
    if five_day is not None and market.get("nifty5") is not None:
        relative = five_day - market["nifty5"]
    trend_vote = _majority([
        _vote(five_day, 1.5, -1.5),
        _vote(twenty_day, 3, -3),
        _vote(macd, 0, -0.0001),
        _vote(trend, 0.2, -0.2),
    ])
    if rejection < 0 and trend_vote > 0:
        trend_vote = 0
    volume_vote = 0
    if volume_change is not None and volume_change >= 20:
        volume_vote = 1 if (previous_return or 0) > 0 else -1
        if rejection < 0 and volume_vote > 0:
            volume_vote = -1
    relative_vote = _vote(relative, 1, -1)
    if rejection < 0 and relative_vote > 0:
        relative_vote = 0
    features = [
        ("Previous day return", previous_return, _vote(previous_return, 0.5, -0.5)),
        ("Trend, counted once", five_day, trend_vote),
        ("Gap", gap, _vote(gap, 0.4, -0.4)),
        ("RSI 14", rsi, 1 if rsi is not None and 50 <= rsi <= 68 else (-1 if rsi is not None and rsi >= 75 else (1 if rsi is not None and rsi <= 30 else 0))),
        ("Daily candle rejection", upper_wick * 100, rejection if rejection else 0),
        ("ATR % of price", atr_pct, 0),
        ("Volume vs 20-day", volume_change, volume_vote),
        ("Nifty return", market.get("nifty"), _vote(market.get("nifty"), 0.3, -0.3)),
        ("Bank Nifty return", market.get("bankNifty"), _vote(market.get("bankNifty"), 0.3, -0.3)),
        ("Stock vs Nifty, 5-day", relative, relative_vote),
        ("India VIX change", market.get("vix"), -_vote(market.get("vix"), 3, -3)),
        ("USD/INR change", market.get("usdInr"), -_vote(market.get("usdInr"), 0.15, -0.15)),
        ("Brent crude change", market.get("crude"), -_vote(market.get("crude"), 1, -1)),
        ("News sentiment", news["sentiment"], _vote(news["sentiment"], 0.2, -0.2)),
    ]
    score = sum(item[2] for item in features)
    if news["count"] >= 4 and abs(news["sentiment"]) >= 0.25:
        score += 1 if news["sentiment"] > 0 else -1
    up_logit = score * 0.22
    down_logit = -score * 0.22
    neutral_logit = 0.85
    peak = max(up_logit, down_logit, neutral_logit)
    weights = [math.exp(up_logit - peak), math.exp(neutral_logit - peak), math.exp(down_logit - peak)]
    total = sum(weights)
    up, neutral, down = [round(weight / total * 100, 1) for weight in weights]
    # Keep the three labels summing to 100 after rounding.
    drift = round(100 - (up + neutral + down), 1)
    neutral = round(neutral + drift, 1)
    if up >= neutral and up >= down:
        lean = "up"
        call = "UP"
        malayalam = "അടുത്ത ദിവസം മുകളിലേക്ക് പോകാനുള്ള സാധ്യത കൂടുതലാണ്. ഉറപ്പല്ല."
    elif down >= neutral and down >= up:
        lean = "down"
        call = "DOWN"
        malayalam = "അടുത്ത ദിവസം താഴേക്ക് പോകാനുള്ള സാധ്യത കൂടുതലാണ്. ഉറപ്പല്ല."
    else:
        lean = "mixed"
        call = "NEUTRAL"
        malayalam = "അടുത്ത ദിവസം വലിയ നീക്കമില്ലാതെ നിൽക്കാനുള്ള സാധ്യത കൂടുതലാണ്. ഉറപ്പല്ല."
    reasons = [
        f"Up means the next close is more than 0.5% higher. Down means more than 0.5% lower. Anything between is neutral.",
        f"Feature score {score:+d}. A long upper wick that closes near the low cancels a stacked uptrend. The 5-day, 20-day, MACD, and EMA votes count as one trend.",
        news["summary"],
    ]
    readable = []
    for name, value, vote in features:
        if value is None:
            text = "n/a"
        elif name in {"RSI 14", "MACD histogram", "News sentiment"}:
            text = f"{value:.2f}"
        else:
            text = f"{value:+.2f}%"
        mark = "up" if vote > 0 else "down" if vote < 0 else "flat"
        readable.append({"name": name, "value": text, "vote": mark})
    return {
        "lean": lean,
        "title": f"Next day {call} {max(up, neutral, down):.0f}%",
        "malayalam": malayalam,
        "up": up,
        "neutral": neutral,
        "down": down,
        "score": score,
        "features": readable,
        "reasons": reasons,
        "disclaimer": "These are probabilities from today's features, not a backtested model and not a guaranteed direction. FII/DII flows, option open interest, and earnings surprise are not in this score.",
    }


def _majority(votes: list[int]) -> int:
    total = sum(votes)
    if total > 0:
        return 1
    if total < 0:
        return -1
    return 0


def _matched_return(bars: list[dict], day: str, clock: str) -> float | None:
    if len(bars) < 2 or bars[-1]["date"] != day or bars[-1]["time"] != clock or bars[-2]["close"] == 0:
        return None
    return (bars[-1]["close"] / bars[-2]["close"] - 1) * 100


def next_candle_direction(history: list[dict], session: list[dict], previous_day: list[dict], nifty_bars: list[dict], bank_bars: list[dict], interval: str) -> dict:
    window = history[-40:]
    while len(window) > 8 and window[-1]["high"] == window[-1]["low"] and window[-1]["volume"] == 0:
        window = window[:-1]
    current = window[-1]
    closes = [bar["close"] for bar in window]
    price = current["close"] or 1
    span = max(current["high"] - current["low"], 0.0001)
    body = abs(current["close"] - current["open"])
    upper = current["high"] - max(current["open"], current["close"])
    lower = min(current["open"], current["close"]) - current["low"]
    close_pos = (current["close"] - current["low"]) / span
    atr = _atr(window, 14)
    threshold = 0.15
    if atr:
        threshold = max(0.05, min(0.35, (atr / price) * 100 * 0.3))
    def back(count: int) -> float | None:
        if len(closes) <= count or closes[-1 - count] == 0:
            return None
        return (closes[-1] / closes[-1 - count] - 1) * 100
    return1 = back(1)
    return3 = back(3)
    return5 = back(5)
    volumes = [bar["volume"] for bar in window]
    volume_ratio = None
    if len(volumes) >= 21 and sum(volumes[-21:-1]) > 0:
        volume_ratio = volumes[-1] / (sum(volumes[-21:-1]) / 20)
    vwap = session_vwap(session)
    vwap_distance = (price / vwap - 1) * 100 if vwap else None
    ema9 = _ema(closes, 9)
    ema21 = _ema(closes, 21)
    ema_gap = None if ema9 is None or ema21 is None or ema21 == 0 else (ema9 / ema21 - 1) * 100
    rsi = _rsi(closes)
    nifty_return = _matched_return(nifty_bars, current["date"], current["time"])
    bank_return = _matched_return(bank_bars, current["date"], current["time"])
    relative = None if return1 is None or nifty_return is None else return1 - nifty_return
    day_high = max(bar["high"] for bar in session)
    day_low = min(bar["low"] for bar in session)
    to_high = (day_high - price) / price * 100
    to_low = (price - day_low) / price * 100
    prev_high = max((bar["high"] for bar in previous_day), default=None)
    prev_low = min((bar["low"] for bar in previous_day), default=None)
    to_prev_high = None if not prev_high else (prev_high - price) / price * 100
    to_prev_low = None if not prev_low else (price - prev_low) / price * 100
    hour, minute = current["time"].split(":")
    minutes_open = int(hour) * 60 + int(minute) - (9 * 60 + 15)
    if minutes_open <= 45:
        day_part = "opening"
    elif int(hour) * 60 + int(minute) >= 14 * 60 + 45:
        day_part = "closing"
    else:
        day_part = "midday"
    last_three = window[-3:]
    rising = all(last_three[index]["close"] > last_three[index - 1]["close"] for index in range(1, 3))
    falling = all(last_three[index]["close"] < last_three[index - 1]["close"] for index in range(1, 3))
    features = [
        ("Close position", close_pos, 1 if close_pos >= 0.7 else (-1 if close_pos <= 0.3 else 0)),
        ("Upper wick %", upper / span * 100, -1 if upper / span >= 0.4 else 0),
        ("Lower wick %", lower / span * 100, 1 if lower / span >= 0.4 else 0),
        ("Return 1 candle", return1, _vote(return1, threshold, -threshold)),
        ("Return 3 candles", return3, _vote(return3, threshold * 1.5, -threshold * 1.5)),
        ("Return 5 candles", return5, _vote(return5, threshold * 2, -threshold * 2)),
        ("Last 3 closes", 1 if rising else (-1 if falling else 0), 1 if rising else (-1 if falling else 0)),
        ("Volume ratio", volume_ratio, 1 if volume_ratio is not None and volume_ratio >= 1.5 and (return1 or 0) > 0 else (-1 if volume_ratio is not None and volume_ratio >= 1.5 and (return1 or 0) < 0 else 0)),
        ("Distance from VWAP", vwap_distance, _vote(vwap_distance, 0.1, -0.1)),
        ("EMA 9 vs EMA 21", ema_gap, _vote(ema_gap, 0.05, -0.05)),
        ("RSI 14", rsi, 1 if rsi is not None and 55 <= rsi <= 70 else (-1 if rsi is not None and rsi >= 78 else 0)),
        ("Nifty candle", nifty_return, _vote(nifty_return, 0.05, -0.05)),
        ("Bank Nifty candle", bank_return, _vote(bank_return, 0.05, -0.05)),
        ("Vs Nifty", relative, _vote(relative, 0.08, -0.08)),
        ("Room to day high", to_high, -1 if to_high <= threshold else 0),
        ("Room above day low", to_low, 1 if to_low <= threshold else 0),
        ("Room to previous high", to_prev_high, -1 if to_prev_high is not None and 0 <= to_prev_high <= threshold else 0),
        ("Room above previous low", to_prev_low, 1 if to_prev_low is not None and 0 <= to_prev_low <= threshold else 0),
    ]
    opening_count = max(1, round(15 / INTERVAL_MINUTES[interval]))
    opening = session[:opening_count] or session[:1]
    opening_high = max(bar["high"] for bar in opening)
    opening_low = min(bar["low"] for bar in opening)
    structure_bits = []
    if close_pos >= 0.65:
        structure_bits.append(1)
    elif close_pos <= 0.35:
        structure_bits.append(-1)
    if upper / span >= 0.45:
        structure_bits.append(-1)
    if lower / span >= 0.45:
        structure_bits.append(1)
    if len(window) >= 2:
        prior = window[-2]
        if current["close"] > prior["high"]:
            structure_bits.append(1)
        elif current["close"] < prior["low"]:
            structure_bits.append(-1)
    structure = _majority(structure_bits)
    momentum_bits = [_vote(return3, threshold, -threshold)]
    if ema_gap is not None:
        momentum_bits.append(_vote(ema_gap, 0.05, -0.05))
    if rising:
        momentum_bits.append(1)
    elif falling:
        momentum_bits.append(-1)
    momentum = _majority(momentum_bits)
    if volume_ratio is not None and volume_ratio >= 1.25 and return1:
        participation = 1 if return1 > 0 else -1
    else:
        participation = 0
    if vwap and price >= opening_high and price > vwap:
        location = 1
    elif vwap and price <= opening_low and price < vwap:
        location = -1
    else:
        location = _vote(vwap_distance, 0.08, -0.08)
    market = _majority([
        _vote(nifty_return, 0.04, -0.04),
        _vote(relative, 0.06, -0.06),
    ])
    groups = {
        "structure": structure,
        "momentum": momentum,
        "volume": participation,
        "location": location,
        "nifty": market,
    }
    score = sum(groups.values())
    stretched_up = rsi is not None and rsi >= 75
    stretched_down = rsi is not None and rsi <= 25
    if score > 0 and stretched_up:
        score -= 1
    elif score < 0 and stretched_down:
        score += 1
    volume_boost = min(0.45, max(0.0, ((volume_ratio or 0) - 1.25) * 0.25))
    move_boost = 0.0 if return3 is None or threshold <= 0 else min(0.35, abs(return3) / threshold * 0.06)
    boost = volume_boost + move_boost if score else 0.0
    up_logit = max(score, 0) * 0.62 + (boost if score > 0 else 0)
    down_logit = max(-score, 0) * 0.62 + (boost if score < 0 else 0)
    neutral_logit = 1.45 if participation == 0 else 1.15
    peak = max(up_logit, down_logit, neutral_logit)
    weights = [math.exp(up_logit - peak), math.exp(neutral_logit - peak), math.exp(down_logit - peak)]
    total = sum(weights)
    up, neutral, down = [round(weight / total * 100, 1) for weight in weights]
    neutral = round(neutral + round(100 - (up + neutral + down), 1), 1)
    if up >= neutral and up >= down:
        lean, call = "up", "UP"
        malayalam = "അടുത്ത കാൻഡിൽ മുകളിലേക്ക് പോകാനുള്ള സാധ്യത കൂടുതലാണ്. ഉറപ്പല്ല."
    elif down >= neutral and down >= up:
        lean, call = "down", "DOWN"
        malayalam = "അടുത്ത കാൻഡിൽ താഴേക്ക് പോകാനുള്ള സാധ്യത കൂടുതലാണ്. ഉറപ്പല്ല."
    else:
        lean, call = "mixed", "NEUTRAL"
        malayalam = "അടുത്ത കാൻഡിൽ വലിയ നീക്കമില്ലാതെ നിൽക്കാനുള്ള സാധ്യത കൂടുതലാണ്. ഉറപ്പല്ല."
    readable = []
    for name, value, vote in features:
        if value is None:
            text = "n/a"
        elif name in {"Close position", "Volume ratio"}:
            text = f"{value:.2f}"
        elif name == "RSI 14":
            text = f"{value:.1f}"
        elif name == "Last 3 closes":
            text = "higher" if rising else "lower" if falling else "mixed"
        else:
            text = f"{value:+.2f}%"
        mark = "up" if vote > 0 else "down" if vote < 0 else "flat"
        readable.append({"name": name, "value": text, "vote": mark})
    if score > 0:
        agree = sum(value > 0 for value in groups.values())
        confirm = round(max(current["high"], opening_high), 2)
        invalid = round(min(current["low"], vwap or current["low"]), 2)
        side_name = "higher"
    elif score < 0:
        agree = sum(value < 0 for value in groups.values())
        confirm = round(min(current["low"], opening_low), 2)
        invalid = round(max(current["high"], vwap or current["high"]), 2)
        side_name = "lower"
    else:
        agree = 0
        confirm = round(current["high"], 2)
        invalid = round(current["low"], 2)
        side_name = "flat"
    fights_extension = (score > 0 and stretched_up) or (score < 0 and stretched_down)
    if lean == "mixed":
        grade = "Pass"
    elif agree >= 4 and participation != 0 and not fights_extension:
        grade = "A"
    elif agree >= 3 and participation != 0:
        grade = "B"
    elif agree >= 2:
        grade = "C"
    else:
        grade = "Pass"
    wick_fades = (upper / span >= 0.45 and momentum > 0) or (lower / span >= 0.45 and momentum < 0)
    if grade == "Pass":
        setup = "No clean setup"
    elif wick_fades:
        setup = "Rejection fade"
    elif (location > 0 and price >= opening_high) or (location < 0 and price <= opening_low):
        setup = "Opening-range break"
    elif participation:
        setup = "Confirmed continuation"
    else:
        setup = "Unconfirmed drift"
    cautions = []
    if participation == 0:
        cautions.append("Volume on the last bar is below 1.25 times the 20-bar average, so the move is not confirmed.")
    if stretched_up:
        cautions.append(f"RSI is {rsi:.0f}. An up idea here is extended, so chasing it has a poor reward.")
    if stretched_down:
        cautions.append(f"RSI is {rsi:.0f}. A down idea here is washed out, so chasing it has a poor reward.")
    winning = 1 if score > 0 else (-1 if score < 0 else 0)
    if market != 0 and winning != 0 and market != winning:
        cautions.append("Nifty is not moving with this stock. A stock-only lean fails more often.")
    if to_high <= threshold and score > 0:
        cautions.append("Price is already at the session high. A failed break often reverses.")
    if to_low <= threshold and score < 0:
        cautions.append("Price is already at the session low. A failed break often bounces.")
    if lean == "mixed":
        unfinished = "higher" if score > 0 else "lower" if score < 0 else "flat"
        suggestion = (
            f"Stand aside. The call is neutral. {agree} of 5 checks lean {unfinished}, and that is not enough to promote a side. "
            f"A higher idea needs a {INTERVALS[interval]} close above {current['high']:.2f}. "
            f"A lower idea needs a close below {current['low']:.2f}. "
            f"Either one still needs volume of at least 1.25 times the recent average. VWAP is {vwap:.2f}."
        )
    elif grade == "Pass":
        suggestion = (
            f"Stand aside. Structure, momentum, volume, VWAP, and Nifty do not agree. "
            f"A higher idea needs a close above {current['high']:.2f}. A lower idea needs a close below {current['low']:.2f}."
        )
    elif score > 0:
        suggestion = (
            f"Working bias is {side_name}, grade {grade}. It stays valid only while price holds above {invalid:.2f}. "
            f"It is confirmed by a {INTERVALS[interval]} close above {confirm:.2f}, not by the current price alone. "
            f"VWAP is {vwap:.2f}. Opening range is {opening_low:.2f}–{opening_high:.2f}."
        )
    else:
        suggestion = (
            f"Working bias is {side_name}, grade {grade}. It stays valid only while price holds below {invalid:.2f}. "
            f"It is confirmed by a {INTERVALS[interval]} close below {confirm:.2f}, not by the current price alone. "
            f"VWAP is {vwap:.2f}. Opening range is {opening_low:.2f}–{opening_high:.2f}."
        )
    desk = {
        "grade": grade,
        "setup": setup,
        "suggestion": suggestion,
        "confirm": confirm,
        "invalid": invalid,
        "agree": agree,
        "vwap": round(vwap, 2) if vwap else None,
        "openingHigh": round(opening_high, 2),
        "openingLow": round(opening_low, 2),
        "cautions": cautions,
    }
    return {
        "lean": lean,
        "title": f"Next {INTERVALS[interval]} candle {call} {max(up, neutral, down):.0f}%",
        "malayalam": malayalam,
        "up": up,
        "neutral": neutral,
        "down": down,
        "threshold": round(threshold, 2),
        "time": current["time"],
        "dayPart": day_part,
        "minutesOpen": minutes_open,
        "vwap": round(vwap, 2),
        "features": readable,
        "desk": desk,
        "reasons": [
            f"Up means the next {INTERVALS[interval]} close is more than {threshold:.2f}% above {price:.2f}. Down means more than {threshold:.2f}% below. The band is 30% of recent ATR.",
            "The percentage uses five separate checks: candle structure, momentum, volume, location versus VWAP and the opening range, and Nifty. Overlapping returns are shown in the feature list and counted once.",
            f"Last traded candle is {current['time']} ({day_part}, {minutes_open} minutes after 09:15). Body is {body / span * 100:.0f}% of the range. {agree} of 5 checks agree."
            + (" The cash session is closed, so this is the first candle of the next session." if current["time"] >= "15:20" else ""),
            "This is a read of closed candles, not an order. Bid/ask imbalance and option open interest are not in this feed.",
        ],
        "disclaimer": "This uses only candles that have already closed. It is a feature score, not a backtested model, and the next candle can go the other way.",
    }


def candle_turn(candles: list[dict]) -> dict:
    """Compare the last candle with the one before it, and with the session low."""
    bars = [bar for bar in candles if not (bar["high"] == bar["low"] and bar["volume"] == 0)]
    if len(bars) < 3:
        return {
            "ready": False,
            "lean": "mixed",
            "title": "Candle change needs more bars",
            "malayalam": "Candles താരതമ്യത്തിന് വേണ്ടത്ര ബാറുകൾ ഇല്ല.",
            "candles": [],
            "checks": [],
            "next": "",
            "invalid": None,
            "rows": [],
        }
    low_index = min(range(len(bars)), key=lambda index: (bars[index]["low"], index))
    swing = bars[low_index]
    previous = bars[-2]
    current = bars[-1]
    held = all(bar["low"] >= swing["low"] for bar in bars[low_index + 1 :])
    higher_low = current["low"] > previous["low"]
    higher_close = current["close"] > previous["close"]
    green = current["close"] > current["open"]
    lower_high = current["high"] < previous["high"]
    lower_close = current["close"] < previous["close"]
    red = current["close"] < current["open"]
    wick = swing["close"] - swing["low"] >= max((swing["high"] - swing["low"]) * 0.25, swing["close"] * 0.002)
    up_turn = higher_low and higher_close and green and held
    down_turn = lower_high and lower_close and red
    if up_turn:
        lean = "up"
        title = "Next candle leans up"
        malayalam = (
            f"{swing['time']}-ന്റെ താഴ്ച ₹{swing['low']:.2f} "
            f"{'ഒരു തിരിയാണ്' if wick else 'ആണ്'}. close ₹{swing['close']:.2f}. "
            f"മുമ്പത്തെ Candles {previous['time']} close ₹{previous['close']:.2f}, താഴ്ച ₹{previous['low']:.2f}. "
            f"ഈ Candles {current['time']} close ₹{current['close']:.2f}, താഴ്ച ₹{current['low']:.2f}. "
            f"താഴ്ച ഉയർന്നു, close ഉയർന്നു, ശരീരം പച്ച. അടുത്ത Candles മുകളിലേക്ക് ചായുന്നു. "
            f"close ₹{swing['low']:.2f}-ന് താഴെയായാൽ ഈ വായന തീരും. ഉറപ്പല്ല."
        )
        next_line = f"അടുത്ത Candles മുകളിലേക്ക്. റദ്ദ് close ₹{swing['low']:.2f}-ന് താഴെ."
    elif down_turn:
        lean = "down"
        title = "Next candle leans down"
        malayalam = (
            f"മുമ്പത്തെ Candles {previous['time']} ഉയരം ₹{previous['high']:.2f}, close ₹{previous['close']:.2f}. "
            f"ഈ Candles {current['time']} ഉയരം ₹{current['high']:.2f}, close ₹{current['close']:.2f}. "
            f"ഉയരം താഴ്ന്നു, close താഴ്ന്നു, ശരീരം ചുവന്നു. അടുത്ത Candles താഴേക്ക് ചായുന്നു. ഉറപ്പല്ല."
        )
        next_line = f"അടുത്ത Candles താഴേക്ക്. സെഷൻ താഴ്ച ₹{swing['low']:.2f}."
    else:
        lean = "mixed"
        title = "Candle change has not lined up"
        malayalam = (
            f"{swing['time']}-ന്റെ താഴ്ച ₹{swing['low']:.2f}. "
            f"{'close താഴ്ചയ്ക്ക് മുകളിലാണ്, അതുകൊണ്ട് അത് ഒരു തിരിയാണ്. ' if wick else ''}"
            f"മുമ്പത്തെ Candles {previous['time']} close ₹{previous['close']:.2f}. "
            f"ഈ Candles {current['time']} close ₹{current['close']:.2f}. "
            f"മൂന്ന് അടയാളവും ഒരുമിച്ച് വന്നിട്ടില്ല. അടുത്ത Candles-ന്റെ ദിശ ഇനി മാറിയിട്ടില്ല. ഉറപ്പല്ല."
        )
        next_line = "മാറ്റത്തിന് ഉയർന്ന താഴ്ചയും, ഉയർന്ന close-ഉം, പച്ച ശരീരവും ഒരേ Candles-ൽ വേണം."
    checks = [
        {"name": "താഴ്ച മുമ്പത്തേതിന് മുകളിൽ", "ok": higher_low, "detail": f"₹{current['low']:.2f} · മുമ്പ് ₹{previous['low']:.2f}"},
        {"name": "close മുമ്പത്തേതിന് മുകളിൽ", "ok": higher_close, "detail": f"₹{current['close']:.2f} · മുമ്പ് ₹{previous['close']:.2f}"},
        {"name": "പച്ച ശരീരം", "ok": green, "detail": f"open ₹{current['open']:.2f} · close ₹{current['close']:.2f}"},
        {"name": "സെഷൻ താഴ്ച പിടിച്ചു", "ok": held, "detail": f"{swing['time']} · ₹{swing['low']:.2f}"},
    ]
    labeled = []
    index_by_key: dict[tuple, int] = {}
    for bar, label in ((swing, "താഴ്ച"), (previous, "മുമ്പത്തെ Candles"), (current, "ഈ Candles")):
        key = (bar["epoch"], bar["open"], bar["close"])
        if key in index_by_key:
            labeled[index_by_key[key]]["label"] += " · " + label
            continue
        index_by_key[key] = len(labeled)
        labeled.append({
            "label": label,
            "time": bar["time"],
            "open": bar["open"],
            "high": bar["high"],
            "low": bar["low"],
            "close": bar["close"],
        })
    labeled.sort(key=lambda item: item["time"])
    return {
        "ready": True,
        "lean": lean,
        "title": title,
        "malayalam": malayalam,
        "candles": labeled,
        "checks": checks,
        "next": next_line,
        "invalid": swing["low"],
        "rows": _candle_chances(bars),
    }


def _split_chance(score: int) -> tuple[float, float, float, str, float]:
    up_logit = max(score, 0) * 0.9
    down_logit = max(-score, 0) * 0.9
    neutral_logit = 0.45
    peak = max(up_logit, down_logit, neutral_logit)
    weights = [math.exp(up_logit - peak), math.exp(neutral_logit - peak), math.exp(down_logit - peak)]
    total = sum(weights) or 1
    up, neutral, down = [round(weight / total * 100, 1) for weight in weights]
    neutral = round(neutral + round(100 - (up + neutral + down), 1), 1)
    if score > 0 and up >= down:
        return up, neutral, down, "മുകളിലേക്ക്", up
    if score < 0 and down >= up:
        return up, neutral, down, "താഴേക്ക്", down
    return up, neutral, down, "നിഷ്പക്ഷം", neutral


def _parts(bar: dict) -> dict:
    open_ = float(bar["open"])
    high = float(bar["high"])
    low = float(bar["low"])
    close = float(bar["close"])
    span = max(high - low, 1e-9)
    body = abs(close - open_)
    upper = max(high - max(open_, close), 0.0)
    lower = max(min(open_, close) - low, 0.0)
    return {
        "open": open_,
        "high": high,
        "low": low,
        "close": close,
        "span": span,
        "body": body,
        "upper": upper,
        "lower": lower,
        "green": close > open_ + span * 0.02,
        "red": close < open_ - span * 0.02,
        "doji": body <= span * 0.10,
        "small": body <= span * 0.35,
        "large": body >= span * 0.55,
        "close_pos": (close - low) / span,
        "body_top": max(open_, close),
        "body_bot": min(open_, close),
    }


def _trend_into(bars: list[dict], index: int) -> str:
    window = bars[max(0, index - 4):index]
    if len(window) < 2 or not window[0]["close"]:
        return "flat"
    change = window[-1]["close"] / window[0]["close"] - 1
    if change <= -0.004:
        return "down"
    if change >= 0.004:
        return "up"
    return "flat"


def _range_median(bars: list[dict], index: int) -> float:
    spans = [bar["high"] - bar["low"] for bar in bars[max(0, index - 8):index] if bar["high"] > bar["low"]]
    if not spans:
        return 0.0
    spans.sort()
    return spans[len(spans) // 2]


def _long_lower(part: dict) -> bool:
    return part["lower"] >= max(part["body"] * 2, part["span"] * 0.55) and part["upper"] <= part["span"] * 0.20 and part["close_pos"] >= 0.60


def _long_upper(part: dict) -> bool:
    return part["upper"] >= max(part["body"] * 2, part["span"] * 0.55) and part["lower"] <= part["span"] * 0.20 and part["close_pos"] <= 0.40


def _body_covers(curr: dict, prev: dict) -> bool:
    return curr["body_bot"] <= prev["body_bot"] and curr["body_top"] >= prev["body_top"] and curr["body"] > prev["body"]


def _near(left: float, right: float, price: float) -> bool:
    return abs(left - right) <= max(0.05, abs(price) * 0.0015)


def _rule(name: str, side: str, score: int, confirmed: bool, comment: str, invalid: float | None) -> dict:
    signed = score if side == "up" else -score if side == "down" else 0
    return {
        "name": name,
        "side": side,
        "score": signed,
        "confirmed": confirmed,
        "comment": comment,
        "invalid": invalid,
    }


def _famous_pattern(bars: list[dict], index: int) -> dict:
    """Classic candlestick rule at this close. Earlier bars only — no future bar."""
    curr = _parts(bars[index])
    prev = _parts(bars[index - 1]) if index else None
    trend = _trend_into(bars, index)
    median = _range_median(bars, index)
    huge = bool(median and curr["span"] >= median * 2.5)
    raw = bars[index]
    older = bars[index - 1] if index else raw

    if huge and curr["red"] and curr["close_pos"] <= 0.40:
        return _rule(
            "Selling climax", "up", 3, False,
            "വലിയ ചുവന്ന Candles. വിൽപ്പന ക്ലൈമാക്സ്. അടുത്തത് മുകളിലേക്ക് ചായുന്നു.",
            raw["low"],
        )
    if huge and curr["green"] and curr["close_pos"] >= 0.70 and curr["upper"] <= curr["span"] * 0.25 and trend == "up":
        return _rule(
            "Buying climax", "down", 3, False,
            "കയറ്റത്തിന് ശേഷം വലിയ പച്ച Candles, close മുകളിൽ ഒട്ടി. വാങ്ങൽ ക്ലൈമാക്സ്. അടുത്തത് താഴേക്ക് ചായുന്നു.",
            raw["high"],
        )

    if index >= 2:
        first, mid, last = _parts(bars[index - 2]), _parts(bars[index - 1]), curr
        first_mid = (first["body_top"] + first["body_bot"]) / 2
        if first["red"] and first["large"] and mid["small"] and last["green"] and last["close"] > first_mid and last["close"] > mid["close"] and mid["close"] <= first["close"]:
            return _rule(
                "Morning star", "up", 3, True,
                "Morning star: വലിയ ചുവപ്പ്, ചെറിയ നടുക്കം, പച്ച close മധ്യത്തിന് മുകളിൽ. അടുത്തത് മുകളിലേക്ക്.",
                min(bars[index - 2]["low"], bars[index - 1]["low"], raw["low"]),
            )
        if first["green"] and first["large"] and mid["small"] and last["red"] and last["close"] < first_mid and last["close"] < mid["close"] and mid["close"] >= first["close"]:
            return _rule(
                "Evening star", "down", 3, True,
                "Evening star: വലിയ പച്ച, ചെറിയ നടുക്കം, ചുവന്ന close മധ്യത്തിന് താഴെ. അടുത്തത് താഴേക്ക്.",
                max(bars[index - 2]["high"], bars[index - 1]["high"], raw["high"]),
            )
        if (
            first["green"] and mid["green"] and last["green"]
            and mid["close"] > first["close"] and last["close"] > mid["close"]
            and first["body_bot"] <= mid["open"] <= first["body_top"]
            and mid["body_bot"] <= last["open"] <= mid["body_top"]
            and first["upper"] <= first["body"] and mid["upper"] <= mid["body"] and last["upper"] <= last["body"]
        ):
            return _rule(
                "Three white soldiers", "up", 3, True,
                "Three white soldiers: മൂന്ന് പച്ച Candles തുടർച്ചയായി ഉയർന്നു. അടുത്തത് മുകളിലേക്ക്.",
                min(bars[index - 2]["low"], bars[index - 1]["low"], raw["low"]),
            )
        if (
            first["red"] and mid["red"] and last["red"]
            and mid["close"] < first["close"] and last["close"] < mid["close"]
            and first["body_bot"] <= mid["open"] <= first["body_top"]
            and mid["body_bot"] <= last["open"] <= mid["body_top"]
            and first["lower"] <= first["body"] and mid["lower"] <= mid["body"] and last["lower"] <= last["body"]
        ):
            return _rule(
                "Three black crows", "down", 3, True,
                "Three black crows: മൂന്ന് ചുവന്ന Candles തുടർച്ചയായി താഴ്ന്നു. അടുത്തത് താഴേക്ക്.",
                max(bars[index - 2]["high"], bars[index - 1]["high"], raw["high"]),
            )

    if prev and _body_covers(curr, prev) and prev["red"] and curr["green"] and trend != "up":
        return _rule(
            "Bullish engulfing", "up", 3, True,
            "Bullish engulfing: പച്ച Candles മുമ്പത്തെ ചുവന്ന ശരീരം മുഴുവൻ മൂടി. അടുത്തത് മുകളിലേക്ക്.",
            min(raw["low"], older["low"]),
        )
    if prev and _body_covers(curr, prev) and prev["green"] and curr["red"] and trend != "down":
        return _rule(
            "Bearish engulfing", "down", 3, True,
            "Bearish engulfing: ചുവന്ന Candles മുമ്പത്തെ പച്ച ശരീരം മുഴുവൻ മൂടി. അടുത്തത് താഴേക്ക്.",
            max(raw["high"], older["high"]),
        )
    if prev and prev["body"] >= prev["span"] * 0.40 and prev["red"] and curr["green"] and curr["open"] <= prev["close"] and curr["close"] > (prev["body_top"] + prev["body_bot"]) / 2 + prev["body"] * 0.15 and curr["close"] < prev["open"]:
        return _rule(
            "Piercing line", "up", 3, True,
            "Piercing line: പച്ച close മുമ്പത്തെ ചുവന്ന ശരീരത്തിന്റെ മധ്യത്തിന് മുകളിൽ. അടുത്തത് മുകളിലേക്ക്.",
            min(raw["low"], older["low"]),
        )
    if prev and prev["body"] >= prev["span"] * 0.40 and prev["green"] and curr["red"] and curr["open"] >= prev["close"] and curr["close"] < (prev["body_top"] + prev["body_bot"]) / 2 - prev["body"] * 0.15 and curr["close"] > prev["open"]:
        return _rule(
            "Dark cloud cover", "down", 3, True,
            "Dark cloud cover: ചുവന്ന close മുമ്പത്തെ പച്ച ശരീരത്തിന്റെ മധ്യത്തിന് താഴെ. അടുത്തത് താഴേക്ക്.",
            max(raw["high"], older["high"]),
        )

    if curr["doji"] and curr["lower"] >= curr["span"] * 0.60 and curr["upper"] <= curr["span"] * 0.15:
        return _rule(
            "Dragonfly doji", "up", 2 if trend == "down" else 1, False,
            "Dragonfly doji: open-ഉം close-ഉം താഴെ ഒത്തു, താഴത്തെ തിരി നീണ്ടു. അടുത്തത് മുകളിലേക്ക് ചായാം.",
            raw["low"],
        )
    if curr["doji"] and curr["upper"] >= curr["span"] * 0.60 and curr["lower"] <= curr["span"] * 0.15:
        return _rule(
            "Gravestone doji", "down", 2 if trend == "up" else 1, False,
            "Gravestone doji: open-ഉം close-ഉം മുകളിൽ ഒത്തു, മുകളിലെ തിരി നീണ്ടു. അടുത്തത് താഴേക്ക് ചായാം.",
            raw["high"],
        )
    if _long_lower(curr):
        if trend == "up":
            return _rule(
                "Hanging man", "down", 2, False,
                "Hanging man: കയറ്റത്തിന് ശേഷം താഴത്തെ തിരി നീണ്ടു. അടുത്തത് താഴേക്ക് ചായാം.",
                raw["low"],
            )
        return _rule(
            "Hammer", "up", 2, False,
            "Hammer: താഴത്തെ തിരി നീണ്ടു, close മുകളിൽ. വീഴ്ച തിരിയാൻ സാധ്യത.",
            raw["low"],
        )
    if _long_upper(curr):
        if trend == "down":
            return _rule(
                "Inverted hammer", "up", 1, False,
                "Inverted hammer: വീഴ്ചയിൽ മുകളിലെ തിരി നീണ്ടു. തിരിച്ചുവരാൻ സാധ്യത.",
                raw["low"],
            )
        return _rule(
            "Shooting star", "down", 2, False,
            "Shooting star: മുകളിലെ തിരി നീണ്ടു, close താഴെ. കയറ്റം നിരസിച്ചു. അടുത്തത് താഴേക്ക്.",
            raw["high"],
        )
    if prev and trend == "down" and _near(curr["low"], prev["low"], curr["close"]) and (curr["green"] or _long_lower(curr)):
        return _rule(
            "Tweezer bottom", "up", 2, False,
            "Tweezer bottom: രണ്ട് Candles-ന്റെ താഴ്ച ഒന്ന്. അടുത്തത് മുകളിലേക്ക് ചായാം.",
            min(raw["low"], older["low"]),
        )
    if prev and trend == "up" and _near(curr["high"], prev["high"], curr["close"]) and (curr["red"] or _long_upper(curr)):
        return _rule(
            "Tweezer top", "down", 2, False,
            "Tweezer top: രണ്ട് Candles-ന്റെ ഉയരം ഒന്ന്. അടുത്തത് താഴേക്ക് ചായാം.",
            max(raw["high"], older["high"]),
        )
    if prev and prev["large"] and curr["small"] and curr["body"] < prev["body"] * 0.6 and curr["body_bot"] >= prev["body_bot"] and curr["body_top"] <= prev["body_top"]:
        if prev["red"] and curr["green"]:
            return _rule(
                "Bullish harami", "up", 1, False,
                "Bullish harami: വലിയ ചുവപ്പിനുള്ളിൽ ചെറിയ പച്ച. ദുർബലമായ മുകളിലേക്കുള്ള സൂചന.",
                older["low"],
            )
        if prev["green"] and curr["red"]:
            return _rule(
                "Bearish harami", "down", 1, False,
                "Bearish harami: വലിയ പച്ചയ്ക്കുള്ളിൽ ചെറിയ ചുവപ്പ്. ദുർബലമായ താഴേക്കുള്ള സൂചന.",
                older["high"],
            )
    prior_low = min(bar["low"] for bar in bars[:index])
    prior_high = max(bar["high"] for bar in bars[:index])
    if _near(curr["low"], prior_low, curr["close"]) and curr["low"] >= prior_low - max(0.02, prior_low * 0.0008) and curr["close"] > curr["low"]:
        return _rule(
            "Low test", "up", 2, False,
            "Low test: മുമ്പത്തെ താഴ്ച പിടിച്ചു, താഴെ പൊട്ടിയില്ല. അടുത്തത് മുകളിലേക്ക് ചായാം.",
            raw["low"],
        )
    if _near(curr["high"], prior_high, curr["close"]) and curr["high"] <= prior_high + max(0.02, prior_high * 0.0008) and curr["close"] < curr["high"]:
        return _rule(
            "High test", "down", 2, False,
            "High test: മുമ്പത്തെ ഉയരം പിടിച്ചു, മുകളിൽ പൊട്ടിയില്ല. അടുത്തത് താഴേക്ക് ചായാം.",
            raw["high"],
        )
    if curr["large"] and curr["upper"] <= curr["span"] * 0.10 and curr["lower"] <= curr["span"] * 0.10 and curr["green"]:
        return _rule(
            "Bullish marubozu", "up", 2, True,
            "Bullish marubozu: തിരി കുറവുള്ള വലിയ പച്ച. close മുകളിൽ. അടുത്തത് മുകളിലേക്ക്.",
            raw["low"],
        )
    if curr["large"] and curr["upper"] <= curr["span"] * 0.10 and curr["lower"] <= curr["span"] * 0.10 and curr["red"]:
        return _rule(
            "Bearish marubozu", "down", 2, True,
            "Bearish marubozu: തിരി കുറവുള്ള വലിയ ചുവപ്പ്. close താഴെ. അടുത്തത് താഴേക്ക്.",
            raw["high"],
        )
    if curr["green"] and curr["body"] >= curr["span"] * 0.55 and curr["lower"] <= curr["span"] * 0.12 and curr["close_pos"] >= 0.75:
        return _rule(
            "Bullish belt hold", "up", 2, True,
            "Bullish belt hold: open താഴെ, close മുകളിൽ. അടുത്തത് മുകളിലേക്ക്.",
            raw["low"],
        )
    if curr["red"] and curr["body"] >= curr["span"] * 0.55 and curr["upper"] <= curr["span"] * 0.12 and curr["close_pos"] <= 0.25:
        return _rule(
            "Bearish belt hold", "down", 2, True,
            "Bearish belt hold: open മുകളിൽ, close താഴെ. അടുത്തത് താഴേക്ക്.",
            raw["high"],
        )
    if curr["doji"]:
        return _rule("Doji", "flat", 0, False, "Doji: open-ഉം close-ഉം ഏകദേശം ഒന്ന്. ദിശ വ്യക്തമല്ല.", None)
    if curr["small"] and curr["upper"] >= curr["span"] * 0.25 and curr["lower"] >= curr["span"] * 0.25:
        return _rule("Spinning top", "flat", 0, False, "Spinning top: ചെറിയ ശരീരം, രണ്ട് തിരിയും. ദിശ വ്യക്തമല്ല.", None)
    if prev and curr["high"] <= prev["high"] and curr["low"] >= prev["low"]:
        return _rule("Inside bar", "flat", 0, False, "Inside bar: ഈ Candles മുമ്പത്തേതിന്റെ ഉള്ളിലാണ്. ബ്രേക്ക് വരെ നിൽക്കുക.", None)
    if curr["lower"] >= curr["span"] * 0.45 and curr["close_pos"] >= 0.55:
        return _rule(
            "Bullish pin", "up", 1, False,
            "Bullish pin: close മുകൾ ഭാഗത്ത്, താഴത്തെ തിരി. അടുത്തത് മുകളിലേക്ക് ചായാം.",
            raw["low"],
        )
    if curr["upper"] >= curr["span"] * 0.45 and curr["close_pos"] <= 0.45:
        return _rule(
            "Bearish pin", "down", 1, False,
            "Bearish pin: close താഴ് ഭാഗത്ത്, മുകളിലെ തിരി. അടുത്തത് താഴേക്ക് ചായാം.",
            raw["high"],
        )
    return _rule("", "flat", 0, False, "പ്രശസ്ത Candles നിയമം ഒത്തില്ല. നിൽക്കുക.", None)


def _pattern_decision(found: dict, call: str, chance: float) -> str:
    if found["side"] == "flat" or not found["name"]:
        return "എന്റർ വേണ്ട. നിൽക്കുക. ഉറപ്പല്ല."
    if not found["confirmed"]:
        return f"എന്റർ വേണ്ട. അടുത്തത് {call} {chance:.0f}%. സ്ഥിരീകരണ Candles വേണം. ഉറപ്പല്ല."
    level = found["invalid"] if found["invalid"] is not None else 0
    if found["side"] == "up":
        return f"എന്റർ ചെയ്യാം, മുകളിലേക്ക്. അടുത്തത് {call} {chance:.0f}%. റദ്ദ് close ₹{level:.2f}-ന് താഴെ. ഉറപ്പല്ല."
    return f"എന്റർ ചെയ്യാം, താഴേക്ക്. അടുത്തത് {call} {chance:.0f}%. റദ്ദ് close ₹{level:.2f}-ന് മുകളിൽ. ഉറപ്പല്ല."


def _candle_chances(bars: list[dict]) -> list[dict]:
    """At the close of each candle, the next-candle read from classic rules. No future bars."""
    rows = []
    for index in range(1, len(bars)):
        previous = bars[index - 1]
        current = bars[index]
        found = _famous_pattern(bars, index)
        up, neutral, down, call, chance = _split_chance(found["score"])
        if found["side"] == "up":
            call, chance = "മുകളിലേക്ക്", up
        elif found["side"] == "down":
            call, chance = "താഴേക്ക്", down
        else:
            call, chance = "നിഷ്പക്ഷം", neutral
        action = _pattern_decision(found, call, chance)
        decision = f"{found['comment']} {action}"
        rule_line = f"{found['name']}: {found['comment']}" if found["name"] else found["comment"]
        previous_line = (
            f"മുമ്പത്തെ Candles {previous['time']}: open ₹{previous['open']:.2f}, "
            f"ഉയരം ₹{previous['high']:.2f}, താഴ്ച ₹{previous['low']:.2f}, close ₹{previous['close']:.2f}."
        )
        current_line = (
            f"ഈ Candles {current['time']}: open ₹{current['open']:.2f}, "
            f"ഉയരം ₹{current['high']:.2f}, താഴ്ച ₹{current['low']:.2f}, close ₹{current['close']:.2f}."
        )
        rows.append({
            "time": current["time"],
            "open": current["open"],
            "close": current["close"],
            "up": up,
            "neutral": neutral,
            "down": down,
            "call": call,
            "side": found["side"],
            "chance": chance,
            "date": current["date"],
            "pattern": found["name"],
            "comment": found["comment"],
            "decision": decision,
            "detail": "\n".join([rule_line, previous_line, current_line, action]),
        })
    return rows


def study(candles: list[dict], interval_label: str) -> dict:
    last = candles[-3:]
    described = []
    previous = candles[-4] if len(candles) >= 4 else None
    for candle in last:
        described.append(candle_facts(candle, previous))
        previous = candle

    score = 0
    reasons = []
    newest = described[-1]
    prior = described[-2]

    if newest["direction"] == "green":
        score += 1
        reasons.append("The latest candle is green.")
    elif newest["direction"] == "red":
        score -= 1
        reasons.append("The latest candle is red.")

    if newest["closePos"] >= 0.75:
        score += 1
        reasons.append("The latest close is near the high of its range.")
    elif newest["closePos"] <= 0.25:
        score -= 1
        reasons.append("The latest close is near the low of its range.")

    if newest["upperWickPct"] >= 40:
        score -= 1
        reasons.append("Sellers showed up at the latest high.")
    if newest["lowerWickPct"] >= 40 and newest["direction"] == "green":
        score += 1
        reasons.append("Buyers defended the latest low.")

    closes = [item["close"] for item in described]
    if closes[0] < closes[1] < closes[2]:
        score += 1
        reasons.append("The last three closes are each higher.")
    elif closes[0] > closes[1] > closes[2]:
        score -= 1
        reasons.append("The last three closes are each lower.")

    if newest["direction"] == "green" and prior["direction"] == "red" and newest["close"] > prior["open"] and newest["open"] <= prior["close"]:
        score += 2
        reasons.append("The latest green candle covers the previous red candle.")
    if newest["direction"] == "red" and prior["direction"] == "green" and newest["close"] < prior["open"] and newest["open"] >= prior["close"]:
        score -= 2
        reasons.append("The latest red candle covers the previous green candle.")

    session_open = candles[0]["open"]
    vwap = session_vwap(candles)
    if newest["close"] > session_open:
        score += 1
        reasons.append(f"Price is above today's open ({session_open:.2f}).")
    elif newest["close"] < session_open:
        score -= 1
        reasons.append(f"Price is below today's open ({session_open:.2f}).")
    if newest["close"] > vwap:
        score += 1
        reasons.append(f"Price is above today's VWAP ({vwap:.2f}).")
    elif newest["close"] < vwap:
        score -= 1
        reasons.append(f"Price is below today's VWAP ({vwap:.2f}).")

    if score >= 2:
        lean = "up"
        title = "Intraday candles lean up"
        malayalam = "ഇന്നത്തെ അവസാന കാൻഡിലുകൾ മുകളിലേക്ക് ചായുന്നു. അടുത്ത കാൻഡിൽ അങ്ങനെ പോകുമെന്ന ഉറപ്പ് ഇതല്ല."
    elif score <= -2:
        lean = "down"
        title = "Intraday candles lean down"
        malayalam = "ഇന്നത്തെ അവസാന കാൻഡിലുകൾ താഴേക്ക് ചായുന്നു. അടുത്ത കാൻഡിൽ അങ്ങനെ പോകുമെന്ന ഉറപ്പ് ഇതല്ല."
    else:
        lean = "mixed"
        title = "Intraday candles are mixed"
        malayalam = "ഇന്നത്തെ അവസാന കാൻഡിലുകൾ ഒരു വശത്തേക്ക് വ്യക്തമായി ചായുന്നില്ല."

    return {
        "lean": lean,
        "title": title,
        "malayalam": malayalam,
        "score": score,
        "interval": interval_label,
        "sessionDate": candles[-1]["date"],
        "sessionOpen": round(session_open, 2),
        "vwap": round(vwap, 2),
        "reasons": reasons,
        "last3": described,
        "disclaimer": "This is an intraday candle read, not a buy or sell instruction. The next candle can go the other way.",
    }


def _market_open(moment: datetime) -> bool:
    if moment.weekday() >= 5:
        return False
    minute_of_day = moment.hour * 60 + moment.minute
    return 9 * 60 + 15 <= minute_of_day <= 15 * 60 + 30


def _stamp_live(candles: list[dict], interval: str, meta: dict) -> bool:
    """Mark the last bar when it is still forming, and pull its close up to the latest price."""
    if not candles or interval not in INTERVAL_MINUTES:
        return False
    now = datetime.now(IST)
    last = candles[-1]
    last["live"] = False
    if not _market_open(now):
        return False
    start = datetime.fromtimestamp(last["epoch"], IST)
    end = start + timedelta(minutes=INTERVAL_MINUTES[interval])
    if not (start <= now < end):
        return False
    price = meta.get("regularMarketPrice")
    if price:
        price = round(float(price), 2)
        last["close"] = price
        last["high"] = round(max(last["high"], price), 2)
        last["low"] = round(min(last["low"], price), 2)
    last["live"] = True
    return True


def live_quote(symbol: str, interval: str = "5m") -> dict:
    if interval not in INTERVALS:
        interval = "5m"
    history, meta = load_bars(symbol, interval, "1d")
    forming = _stamp_live(history, interval, meta)
    now = datetime.now(IST)
    return {
        "marketOpen": _market_open(now),
        "live": forming,
        "asOf": now.strftime("%H:%M:%S"),
        "candle": history[-1],
    }


def _scan_symbol(symbol: str, nifty_bars: list[dict], bank_bars: list[dict]) -> dict | None:
    yahoo = f"{symbol}.NS"
    history = None
    meta = None
    for attempt in range(2):
        try:
            history, meta = load_bars(yahoo, "5m", "5d")
            break
        except ValueError:
            if attempt == 0:
                time.sleep(0.35)
    if not history:
        return None
    session_day = history[-1]["date"]
    session = [candle for candle in history if candle["date"] == session_day]
    if len(session) < 3:
        return None
    days = list(dict.fromkeys(candle["date"] for candle in history))
    previous_day = [candle for candle in history if len(days) >= 2 and candle["date"] == days[-2]]
    call = next_candle_direction(history, session, previous_day, nifty_bars, bank_bars, "5m")
    price = session[-1]["close"] or 1
    atr = _atr(history[-20:], 14)
    atr_pct = (atr / price) * 100 if atr else call["threshold"] / 0.3
    last = session[-1]
    last_range = (last["high"] - last["low"]) / price * 100
    recent = session[-3:]
    recent_move = (recent[-1]["close"] / recent[0]["open"] - 1) * 100 if recent[0]["open"] else 0
    yahoo_name = meta.get("shortName") or meta.get("longName") or symbol
    listing = groww_stock(meta.get("symbol") or yahoo, meta.get("shortName") or "", meta.get("longName") or "")
    reach = price
    reach_by = ""
    path_end = price
    path_until = ""
    try:
        path = project(history, nifty_bars, "5m")
        path_end, path_until = path_reach(path)
        near = path["points"][:3]
        if near:
            best = max(near, key=lambda point: point["high"])
            reach = best["high"]
            reach_by = f"{best['date']} {best['time']}"
        else:
            reach = path_end
            reach_by = path_until
    except (ValueError, ZeroDivisionError, IndexError):
        reach = price
        reach_by = ""
        path_end = price
        path_until = ""
    return {
        "symbol": meta.get("symbol") or yahoo,
        "name": listing["name"] or yahoo_name,
        "growwUrl": listing["url"],
        "price": round(price, 2),
        "time": call["time"],
        "up": call["up"],
        "down": call["down"],
        "neutral": call["neutral"],
        "lean": call["lean"],
        "band": call["threshold"],
        "atrPct": round(atr_pct, 2),
        "lastRange": round(last_range, 2),
        "recentMove": round(recent_move, 2),
        "upPace": round(call["up"] / 100 * atr_pct, 3),
        "downPace": round(call["down"] / 100 * atr_pct, 3),
        "grade": call["desk"]["grade"],
        "setup": call["desk"]["setup"],
        "suggestion": call["desk"]["suggestion"],
        "confirm": call["desk"]["confirm"],
        "invalid": call["desk"]["invalid"],
        "agree": call["desk"]["agree"],
        "reach": round(reach, 2),
        "reachBy": reach_by,
        "reachMove": round(reach - price, 2),
        "reachPct": round((reach / price - 1) * 100, 2) if price else 0,
        "pathEnd": round(path_end, 2),
        "pathUntil": path_until,
    }


def genius_note(row: dict) -> dict:
    """One read that puts the chart path, the grade, and the headlines in the same sentence."""
    price = float(row.get("price") or 0)
    future = float(row.get("futurePrice") or row.get("pathEnd") or price)
    sentiment = float(row.get("newsSentiment") or 0)
    grade = str(row.get("grade") or "")
    lean = str(row.get("lean") or "")
    invalid = float(row.get("invalid") or 0)
    setup = str(row.get("setup") or "no clean setup")
    when = str(row.get("pathUntil") or "the next session")
    clears = future > price
    news_up = sentiment >= 0.15
    news_down = sentiment <= -0.15
    if lean == "up" and clears and grade in {"A", "B"} and not news_down:
        verdict = "Buy lean"
        why = (
            "The chart path and the headlines point the same way."
            if news_up
            else "The chart path points up. The headlines are quiet, so they do not confirm it."
        )
    elif lean == "up" and clears and news_down:
        verdict = "Wait"
        why = "The chart path points up, but the headlines point down. That disagreement fails more often."
    elif lean == "up" and not clears:
        verdict = "Stand aside"
        why = "The score leans up, but the chart path does not get above the last price."
    elif lean == "down":
        verdict = "Stand aside"
        why = "The chart leans down, so this is not a buy."
    else:
        verdict = "Stand aside"
        why = "The chart and the checks do not line up for a buy."
    move = future - price
    text = (
        f"{verdict}. {why} Last price {price:.2f}. The price to watch is {future:.2f} ({move:+.2f}) by {when}. "
        f"Cancel it if price trades through {invalid:.2f}. Grade {grade}, {setup}. This is a read, not an order."
    )
    return {"verdict": verdict, "text": text}


def _attach_news(rows: list[dict]) -> None:
    def one(row: dict) -> None:
        news = load_news(row["name"])
        watched = price_with_news(row["price"], row.get("pathEnd") or row["price"], news)
        row["newsSentiment"] = watched["sentiment"]
        row["newsShift"] = watched["newsShift"]
        row["futurePrice"] = watched["futurePrice"]
        row["newsSummary"] = news["summary"]
        note = genius_note(row)
        row["genius"] = note["text"]
        row["verdict"] = note["verdict"]

    if not rows:
        return
    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(one, rows))


def _pick_buys(rows: list[dict]) -> list[dict]:
    grade_rank = {"A": 3, "B": 2, "C": 1}
    qualified = [
        row for row in rows
        if row["lean"] == "up" and grade_rank.get(row.get("grade"), 0) >= 2 and row.get("reach", 0) > row["price"]
    ]
    if len(qualified) < 3:
        qualified = [
            row for row in rows
            if row["lean"] == "up" and grade_rank.get(row.get("grade"), 0) >= 1 and row.get("reach", 0) > row["price"]
        ]
    qualified.sort(key=lambda row: (grade_rank.get(row["grade"], 0), row.get("agree", 0), row["reachPct"]), reverse=True)
    return qualified[:8]


def _pick_side(rows: list[dict], side: str) -> list[dict]:
    pace_key = "upPace" if side == "up" else "downPace"
    grade_rank = {"A": 3, "B": 2, "C": 1}
    qualified = [row for row in rows if row["lean"] == side and grade_rank.get(row.get("grade"), 0) >= 1]
    qualified.sort(key=lambda row: (grade_rank.get(row["grade"], 0), row.get("agree", 0), row[pace_key]), reverse=True)
    return qualified[:6]


def build_rapid_board() -> dict:
    try:
        nifty_bars, _ = load_bars("^NSEI", "5m", "5d")
    except ValueError:
        nifty_bars = []
    try:
        bank_bars, _ = load_bars("^NSEBANK", "5m", "5d")
    except ValueError:
        bank_bars = []
    rows = []
    with ThreadPoolExecutor(max_workers=6) as pool:
        futures = [pool.submit(_scan_symbol, symbol, nifty_bars, bank_bars) for symbol in LIQUID_NSE]
        for future in as_completed(futures):
            row = future.result()
            if row:
                rows.append(row)
    if not rows:
        raise ValueError("No liquid NSE names returned 5-minute candles.")
    now = datetime.now(IST)
    open_now = _market_open(now)
    buys = _pick_buys(rows)
    _attach_news(buys)
    return {
        "status": "ready",
        "asOf": now.strftime("%H:%M:%S"),
        "date": now.strftime("%Y-%m-%d"),
        "interval": "5 minutes",
        "refreshesEvery": SCAN_TTL,
        "marketOpen": open_now,
        "scanned": len(rows),
        "up": _pick_side(rows, "up"),
        "down": _pick_side(rows, "down"),
        "buys": buys,
        "note": (
            "A name is listed only when at least two independent checks agree: candle structure, momentum, volume, VWAP or the opening range, and Nifty. "
            "Grade A needs four checks plus volume. The confirm price is the close that validates the idea. The invalid price cancels it. This is not an order."
            if open_now
            else "The cash session is closed, so this is the read for the first 5-minute candle of the next session. "
            "A name is listed only when at least two independent checks agree. Grade A needs four checks plus volume. Confirm and invalid prices are levels, not an order."
        ),
    }


def _refresh_scan() -> None:
    try:
        payload = build_rapid_board()
        with _scan_state["lock"]:
            _scan_state["payload"] = payload
            _scan_state["fetched_at"] = time.time()
            _scan_state["retry_after"] = 0.0
    except Exception as exc:
        with _scan_state["lock"]:
            _scan_state["retry_after"] = time.time() + 20
            if not _scan_state["payload"]:
                _scan_state["payload"] = {
                    "status": "error",
                    "error": str(exc),
                    "up": [],
                    "down": [],
                    "refreshesEvery": SCAN_TTL,
                }
    finally:
        with _scan_state["lock"]:
            _scan_state["running"] = False


def _ensure_scan() -> None:
    now = time.time()
    with _scan_state["lock"]:
        payload = _scan_state["payload"]
        fresh = payload and payload.get("status") == "ready" and now - _scan_state["fetched_at"] < SCAN_TTL
        if fresh or _scan_state["running"] or now < _scan_state["retry_after"]:
            return
        _scan_state["running"] = True
    threading.Thread(target=_refresh_scan, daemon=True).start()


def _force_scan() -> None:
    with _scan_state["lock"]:
        if _scan_state["running"]:
            return
        _scan_state["retry_after"] = 0.0
        _scan_state["running"] = True
    threading.Thread(target=_refresh_scan, daemon=True).start()


def rapid_payload(force: bool = False) -> dict:
    if force:
        _force_scan()
    else:
        _ensure_scan()
    with _scan_state["lock"]:
        payload = _scan_state["payload"]
        age = time.time() - _scan_state["fetched_at"] if payload and _scan_state["fetched_at"] else None
        refreshing = _scan_state["running"]
    if not payload:
        return {"status": "scanning", "up": [], "down": [], "refreshing": True, "refreshesEvery": SCAN_TTL}
    body = dict(payload)
    body["refreshing"] = refreshing
    body["ageSeconds"] = int(age or 0)
    return body


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        parsed = urlparse(self.path)
        if parsed.path == "/":
            body = INDEX.read_bytes()
            self._send(200, "text/html; charset=utf-8", body)
            return
        if parsed.path == "/api/study":
            query = parse_qs(parsed.query)
            try:
                raw_symbol = (query.get("symbol") or ["DELTACORP"])[0]
                symbol = resolve_symbol(raw_symbol)
                interval = (query.get("interval") or ["5m"])[0]
                range_name = (query.get("range") or ["1d"])[0]
                try:
                    payload = fetch_candles(symbol, interval, range_name)
                except ValueError as exc:
                    if "404" not in str(exc):
                        raise
                    match = search_symbol(raw_symbol)
                    if not match or match == symbol:
                        raise ValueError(f"No NSE stock found for {raw_symbol.strip()}.") from exc
                    payload = fetch_candles(match, interval, range_name)
                self._send(200, "application/json", json.dumps(payload).encode("utf-8"))
            except ValueError as exc:
                self._send(400, "application/json", json.dumps({"error": str(exc)}).encode("utf-8"))
            return
        if parsed.path == "/api/live":
            query = parse_qs(parsed.query)
            try:
                raw_symbol = (query.get("symbol") or ["DELTACORP"])[0]
                symbol = resolve_symbol(raw_symbol)
                interval = (query.get("interval") or ["5m"])[0]
                self._send(200, "application/json", json.dumps(live_quote(symbol, interval)).encode("utf-8"))
            except ValueError as exc:
                self._send(400, "application/json", json.dumps({"error": str(exc)}).encode("utf-8"))
            return
        if parsed.path == "/api/rapid":
            query = parse_qs(parsed.query)
            force = (query.get("force") or ["0"])[0] in {"1", "true", "yes"}
            self._send(200, "application/json", json.dumps(rapid_payload(force)).encode("utf-8"))
            return
        self._send(404, "text/plain", b"Not found")

    def _send(self, status: int, content_type: str, body: bytes):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, fmt: str, *args):
        print(f"[{self.log_date_time_string()}] {self.address_string()} {fmt % args}")


def main():
    _ensure_scan()
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    print(f"Candle study is running at http://{HOST}:{PORT}")
    server.serve_forever()


if __name__ == "__main__":
    main()
