#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import re
import asyncio
import hashlib
import html
import json
import logging
import os
import random
import signal
import sys
import textwrap
import time
import unicodedata
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from functools import lru_cache
from io import BytesIO
from pathlib import Path
from typing import Dict, List, Optional, Any, Union, Set, Tuple
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

KALININGRAD_TZ = timezone(timedelta(hours=2), name='Europe/Kaliningrad')
TIMEZONE_REGIONS = {
    'калининград': (KALININGRAD_TZ, ('калининград', 'калининградская область')),
    'москва': (timezone(timedelta(hours=3)), ('москва', 'санкт-петербург', 'петербург', 'спб')),
    'самара': (timezone(timedelta(hours=4)), ('самара',)),
    'екатеринбург': (timezone(timedelta(hours=5)), ('екатеринбург',)),
    'омск': (timezone(timedelta(hours=6)), ('омск',)),
    'новосибирск': (timezone(timedelta(hours=7)), ('новосибирск',)),
    'красноярск': (timezone(timedelta(hours=7)), ('красноярск',)),
    'иркутск': (timezone(timedelta(hours=8)), ('иркутск',)),
    'якутск': (timezone(timedelta(hours=9)), ('якутск',)),
    'владивосток': (timezone(timedelta(hours=10)), ('владивосток',)),
    'магадан': (timezone(timedelta(hours=11)), ('магадан',)),
    'камчатка': (timezone(timedelta(hours=12)), ('камчатка', 'петропавловск-камчатский')),
}
TIMEZONE_REGION_ALIASES = {
    alias: region
    for region, (_, aliases) in TIMEZONE_REGIONS.items()
    for alias in aliases
}


def kaliningrad_now() -> datetime:
    return datetime.now(KALININGRAD_TZ)


def resolve_time_region(region: str):
    requested_region = region.strip()
    if not requested_region:
        return 'Калининград', KALININGRAD_TZ

    canonical_region = TIMEZONE_REGION_ALIASES.get(requested_region.casefold())
    if canonical_region:
        return canonical_region.title(), TIMEZONE_REGIONS[canonical_region][0]

    return requested_region, ZoneInfo(requested_region)


async def lookup_time_region(region: str) -> Optional[Tuple[str, datetime, timedelta]]:
    import aiohttp

    search_region = region.rsplit('/', 1)[-1].replace('_', ' ') if '/' in region else region
    timeout = aiohttp.ClientTimeout(total=12)
    try:
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.get(
                "https://geocoding-api.open-meteo.com/v1/search",
                params={
                    'name': search_region,
                    'count': 1,
                    'language': 'ru',
                    'format': 'json',
                },
            ) as response:
                if response.status != 200:
                    raise RuntimeError(f"Геопоиск вернул HTTP {response.status}")
                geocoding_data = await response.json()

            results = geocoding_data.get('results')
            if not results:
                return None

            location = results[0]
            location_name = str(location['name'])
            country = location.get('country')
            region_name = f"{location_name}, {country}" if country else location_name
            latitude = location['latitude']
            longitude = location['longitude']

            async with session.get(
                "https://api.open-meteo.com/v1/forecast",
                params={
                    'latitude': latitude,
                    'longitude': longitude,
                    'current': 'temperature_2m',
                    'timezone': 'auto',
                },
            ) as response:
                if response.status != 200:
                    raise RuntimeError(f"Сервис времени вернул HTTP {response.status}")
                time_data = await response.json()
    except (aiohttp.ClientError, asyncio.TimeoutError) as exc:
        raise RuntimeError("Не удалось связаться с сервисом времени") from exc

    current_time = datetime.fromisoformat(time_data['current']['time'])
    offset = timedelta(seconds=int(time_data['utc_offset_seconds']))
    return region_name, current_time, offset


try:
    from PIL import Image, ImageDraw, ImageFont, ImageFilter
except ImportError:
    Image = None
    ImageDraw = None
    ImageFont = None
    ImageFilter = None

from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton
from aiogram import Bot, Dispatcher, Router, F, BaseMiddleware
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandObject
from aiogram.types import (
    Message, CallbackQuery, ChatPermissions, InlineKeyboardButton,
    InlineKeyboardMarkup, BufferedInputFile, User, BotCommand
)
from aiogram.utils.keyboard import InlineKeyboardBuilder

# Force UTF-8 output for terminals with non-UTF locales (common on Linux servers)
try:
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    if hasattr(sys.stderr, 'reconfigure'):
        sys.stderr.reconfigure(encoding='utf-8')
except Exception:
    pass
os.environ.setdefault('PYTHONIOENCODING', 'utf-8')

# ==================== Кэширование ====================

class SimpleCache:
    def __init__(self, max_size: int = 1000, ttl: int = 300):
        self._cache: Dict[str, tuple] = {}
        self._max_size = max_size
        self._ttl = ttl

    def get(self, key: str) -> Any:
        if key in self._cache:
            value, expiry = self._cache[key]
            if time.time() < expiry:
                return value
            del self._cache[key]
        return None

    def set(self, key: str, value: Any, ttl: int = None):
        if len(self._cache) >= self._max_size:
            oldest = sorted(self._cache.items(), key=lambda x: x[1][1])[:len(self._cache) // 4]
            for k, _ in oldest:
                del self._cache[k]
        self._cache[key] = (value, time.time() + (ttl or self._ttl))

    def invalidate(self, key: str):
        self._cache.pop(key, None)

    def clear(self):
        self._cache.clear()


user_cache = SimpleCache(max_size=2000, ttl=300)
chat_settings_cache = SimpleCache(max_size=200, ttl=600)
mention_cache = SimpleCache(max_size=5000, ttl=3600)
anti_spam_admin_cache = SimpleCache(max_size=5000, ttl=10)

EXCHANGE_RATE_CACHE: Dict[str, Tuple[float, Dict[str, float]]] = {}
CURRENCY_DISPLAY = {
    'RUB': ('🇷🇺', 'российский рубль', '₽'),
    'EUR': ('🇪🇺', 'евро', '€'),
    'USD': ('🇺🇸', 'доллар США', '$'),
    'GBP': ('🇬🇧', 'британский фунт', '£'),
    'CNY': ('🇨🇳', 'китайский юань', '¥'),
    'KZT': ('🇰🇿', 'казахстанский тенге', '₸'),
    'UAH': ('🇺🇦', 'украинская гривна', '₴'),
    'BYN': ('🇧🇾', 'белорусский рубль', 'Br'),
    'TRY': ('🇹🇷', 'турецкая лира', '₺'),
    'JPY': ('🇯🇵', 'японская иена', '¥'),
    'CHF': ('🇨🇭', 'швейцарский франк', 'Fr'),
    'CAD': ('🇨🇦', 'канадский доллар', 'C$'),
    'AUD': ('🇦🇺', 'австралийский доллар', 'A$'),
    'INR': ('🇮🇳', 'индийская рупия', '₹'),
}
CURRENCY_ALIASES = {
    'USD': (r'USD', r'доллар\w*', r'dollar\w*', r'бакс\w*', r'\$'),
    'RUB': (r'RUB', r'руб\w*', r'₽'),
    'EUR': (r'EUR', r'евро', r'euro', r'€'),
    'GBP': (r'GBP', r'фунт\w*', r'£'),
    'CNY': (r'CNY', r'юан\w*', r'¥'),
    'KZT': (r'KZT', r'тенге', r'₸'),
    'UAH': (r'UAH', r'грив\w*', r'грн', r'₴'),
    'BYN': (r'BYN', r'белорус\w* руб\w*', r'бел\w* руб\w*'),
    'TRY': (r'TRY', r'лир\w*'),
    'JPY': (r'JPY', r'иен\w*', r'йен\w*'),
    'CHF': (r'CHF', r'франк\w*'),
    'CAD': (r'CAD', r'канад\w* доллар\w*'),
    'AUD': (r'AUD', r'австрал\w* доллар\w*'),
    'INR': (r'INR', r'рупи\w*'),
}
CURRENCY_AMOUNT_PATTERN = re.compile(
    r'(?<!\w)(?P<amount>\d+(?:[.,]\d+)?)\s*'
    r'(?P<currency>' + '|'.join(
        rf'(?:{alias})' for aliases in CURRENCY_ALIASES.values() for alias in aliases
    ) + r')(?!\w)',
    re.IGNORECASE,
)



# ==================== Загрузка .env ====================

try:
    from dotenv import load_dotenv

    env_path = Path(__file__).parent / '.env'
    if env_path.exists():
        load_dotenv(env_path, override=True)
        print(f"✅ .env загружен из: {env_path}")
    else:
        for path in [Path('.').absolute() / '.env', Path('/app/.env')]:
            if path.exists():
                load_dotenv(path, override=True)
                print(f"✅ .env загружен из: {path}")
                break
except ImportError:
    print("⚠️ python-dotenv не установлен")

BOT_TOKEN = os.getenv('BOT_TOKEN')
MAIN_GROUP_ID = os.getenv('MAIN_GROUP_ID')

if not BOT_TOKEN:
    print("❌ BOT_TOKEN не найден!")
    sys.exit(1)

if MAIN_GROUP_ID:
    try:
        MAIN_GROUP_ID = int(MAIN_GROUP_ID)
    except ValueError:
        MAIN_GROUP_ID = None

DATA_FILE = os.getenv('DATA_FILE', 'valera_data.json')
LOG_FILE = os.getenv('LOG_FILE', 'valera_bot.log')
BACKUP_DIR = os.getenv('BACKUP_DIR', 'backups')
UK_RF_ARTICLES_FILE = Path(__file__).parent / 'uk_rf_articles.json'
DEFAULT_MUTE_MINUTES = int(os.getenv('DEFAULT_MUTE_MINUTES', '30'))
DEFAULT_WARN_DAYS = int(os.getenv('DEFAULT_WARN_DAYS', '30'))
MAX_WARNINGS = int(os.getenv('MAX_WARNINGS', '7'))
REPUTATION_COOLDOWN = int(os.getenv('REPUTATION_COOLDOWN', '3600'))
REPUTATION_DAILY_LIMIT = int(os.getenv('REPUTATION_DAILY_LIMIT', '15'))
REPUTATION_REMOVE_COOLDOWN = int(os.getenv('REPUTATION_REMOVE_COOLDOWN', '3600'))
REPUTATION_REMOVE_DAILY_LIMIT = int(os.getenv('REPUTATION_REMOVE_DAILY_LIMIT', '15'))
MUTE_CHECK_INTERVAL = int(os.getenv('MUTE_CHECK_INTERVAL', '60'))
VIP_RP_RANK = int(os.getenv('VIP_RP_RANK', '2'))
AUTO_SAVE_INTERVAL = int(os.getenv('AUTO_SAVE_INTERVAL', '300'))
MAX_TAG_LENGTH = int(os.getenv('MAX_TAG_LENGTH', '32'))
ANTI_SPAM_ENABLED = os.getenv('ANTI_SPAM_ENABLED', 'true').lower() == 'true'
DEFAULT_WORDLE_LENGTH = 5
DEFAULT_WORDLE_ATTEMPTS = 6
WORDLE_WORDS_FILE = str(Path(__file__).resolve().parent / "russian_words.txt")
PIC_DISABLED_CHATS = {
    chat.strip().lstrip('@').casefold()
    for chat in os.getenv('PIC_DISABLED_CHATS', 'Weltobruhsuperchat').split(',')
    if chat.strip()
}

Path(BACKUP_DIR).mkdir(exist_ok=True)

try:
    import matplotlib

    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates

    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(LOG_FILE, encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)
# Очень компактный разделитель для мобильного вида.
UI_LINE = "─" * 12

print("=" * 60)
print("🐻 Обкуренный Валера v3.0 - Полная версия")
print("=" * 60)
print(f"🏠 Основная группа ID: {MAIN_GROUP_ID or 'не указана (статистика везде)'}")
print(f"📁 Данные: {DATA_FILE}")
print(f"💾 Бэкапы: {BACKUP_DIR}/")
print(f"🔄 Автосохранение: каждые {AUTO_SAVE_INTERVAL} сек")
print(f"🛡️ Анти-спам: {'Включен' if ANTI_SPAM_ENABLED else 'Отключен'}")
print(f"🚫 /pic отключена по умолчанию в: {', '.join(sorted(PIC_DISABLED_CHATS)) or 'нигде'}")
print(f"⭐ Лимит репутации: {REPUTATION_DAILY_LIMIT}/день")
print(f"📊 Графики: {'Да' if MATPLOTLIB_AVAILABLE else 'Нет'}")
print("=" * 60)


# ==================== Вспомогательная функция ====================

def is_main_chat(chat_id: int, message_thread_id: Optional[int] = None) -> bool:
    """
    Проверяет, является ли чат основной группой и главным топиком.
    Если MAIN_GROUP_ID не указан, разрешает все группы (обратная совместимость).
    """
    if MAIN_GROUP_ID is None:
        return True

    if chat_id != MAIN_GROUP_ID:
        return False

    if message_thread_id is None or message_thread_id == 1:
        return True

    return False


def max_consecutive_days(activity: dict) -> int:
    if not activity:
        return 0
    sorted_dates = sorted(activity.keys())
    if not sorted_dates:
        return 0

    max_streak = 1
    current_streak = 1

    for i in range(1, len(sorted_dates)):
        try:
            prev = datetime.strptime(sorted_dates[i - 1], '%Y-%m-%d')
            curr = datetime.strptime(sorted_dates[i], '%Y-%m-%d')
            if (curr - prev).days == 1:
                current_streak += 1
                max_streak = max(max_streak, current_streak)
            else:
                current_streak = 1
        except:
            continue

    return max_streak


# ==================== Анти-спам ====================

class AntiSpamSystem:
    def __init__(self):
        self.user_messages: Dict[Tuple[int, int], List[Tuple[float, int, str]]] = defaultdict(list)
        self.user_rate: Dict[Tuple[int, int], List[Tuple[float, int]]] = defaultdict(list)
        self.user_stickers: Dict[Tuple[int, int], List[Tuple[float, int]]] = defaultdict(list)
        self.user_animations: Dict[Tuple[int, int], List[Tuple[float, int]]] = defaultdict(list)
        self.user_caps: Dict[Tuple[int, int], List[Tuple[float, int]]] = defaultdict(list)
        self.user_fragments: Dict[Tuple[int, int], List[Tuple[float, int, str]]] = defaultdict(list)
        self.user_mentions: Dict[Tuple[int, int], List[Tuple[float, int, int]]] = defaultdict(list)
        self.user_links: Dict[Tuple[int, int], List[Tuple[float, int, Tuple[str, ...]]]] = defaultdict(list)
        self.message_dates: Dict[Tuple[int, int], Dict[int, Tuple[float, Optional[str]]]] = defaultdict(dict)
        self.last_cleanup = time.time()

    def _normalize_text(self, text: str) -> str:
        text = html.unescape(text or '')
        text = re.sub(r'https?://\S+|www\.\S+', ' ', text, flags=re.IGNORECASE)
        text = re.sub(r'@\w+', ' ', text)
        text = re.sub(r'[^\w\s]', ' ', text, flags=re.UNICODE)
        text = re.sub(r'\s+', ' ', text).strip().lower()
        return text

    def _words_set(self, text: str) -> Set[str]:
        normalized = self._normalize_text(text)
        if not normalized:
            return set()
        return {w for w in normalized.split() if len(w) > 2}

    def _similarity(self, a: str, b: str) -> float:
        if not a or not b:
            return 0.0
        left = self._words_set(a)
        right = self._words_set(b)
        if not left or not right:
            return 0.0
        inter = len(left & right)
        union = len(left | right)
        if union == 0:
            return 0.0
        return inter / union

    def _is_caps_flood(self, text: str) -> bool:
        if len(text) < 10:
            return False
        letters = [ch for ch in text if ch.isalpha()]
        if len(letters) < 6:
            return False
        upper_ratio = sum(1 for ch in letters if ch.isupper()) / len(letters)
        punct_ratio = text.count('!') + text.count('?')
        return upper_ratio >= 0.7 and punct_ratio <= 1

    def cleanup(self):
        now = time.time()
        if now - self.last_cleanup < 300:
            return
        self.last_cleanup = now

        for key, messages in list(self.user_rate.items()):
            recent = [(ts, mid) for ts, mid in messages if now - ts < 60]
            if recent:
                self.user_rate[key] = recent
            else:
                del self.user_rate[key]

        for key, messages in list(self.user_messages.items()):
            recent = [(ts, mid, body) for ts, mid, body in messages if now - ts < 60]
            if recent:
                self.user_messages[key] = recent
            else:
                del self.user_messages[key]

        for key, messages in list(self.user_stickers.items()):
            recent = [(ts, mid) for ts, mid in messages if now - ts < 10]
            if recent:
                self.user_stickers[key] = recent
            else:
                del self.user_stickers[key]

        for key, messages in list(self.user_animations.items()):
            recent = [(ts, mid) for ts, mid in messages if now - ts < 10]
            if recent:
                self.user_animations[key] = recent
            else:
                del self.user_animations[key]

        for key, messages in list(self.user_caps.items()):
            recent = [(ts, mid) for ts, mid in messages if now - ts < 10]
            if recent:
                self.user_caps[key] = recent
            else:
                del self.user_caps[key]

        for key, messages in list(self.user_fragments.items()):
            recent = [(ts, mid, body) for ts, mid, body in messages if now - ts < 10]
            if recent:
                self.user_fragments[key] = recent
            else:
                del self.user_fragments[key]

        for key, messages in list(self.user_mentions.items()):
            recent = [(ts, mid, count) for ts, mid, count in messages if now - ts < 15]
            if recent:
                self.user_mentions[key] = recent
            else:
                del self.user_mentions[key]

        for key, messages in list(self.user_links.items()):
            recent = [(ts, mid, urls) for ts, mid, urls in messages if now - ts < 60]
            if recent:
                self.user_links[key] = recent
            else:
                del self.user_links[key]

        for key, messages in list(self.message_dates.items()):
            recent = {
                message_id: (ts, activity_date)
                for message_id, (ts, activity_date) in messages.items()
                if now - ts < 60
            }
            if recent:
                self.message_dates[key] = recent
            else:
                del self.message_dates[key]

    def _remember_message(self, chat_user: Tuple[int, int], msg: Message, now: float):
        activity_date = None
        if is_main_chat(msg.chat.id, msg.message_thread_id):
            activity_date = datetime.fromtimestamp(now, KALININGRAD_TZ).strftime('%Y-%m-%d')
        self.message_dates[chat_user][msg.message_id] = (now, activity_date)

    def pop_message_date(self, chat_id: int, user_id: int, message_id: int) -> Optional[str]:
        message = self.message_dates.get((chat_id, user_id), {}).pop(message_id, None)
        return message[1] if message else None

    def check_message(self, msg: Message) -> Tuple[bool, Optional[str], List[int]]:
        if not msg.from_user or msg.from_user.is_bot:
            return False, None, []

        chat_user = (msg.chat.id, msg.from_user.id)
        now = time.time()
        self.cleanup()
        self._remember_message(chat_user, msg, now)

        recent_rate = [
            (ts, mid) for ts, mid in self.user_rate[chat_user] if now - ts < 60
        ]
        recent_rate.append((now, msg.message_id))
        self.user_rate[chat_user] = recent_rate
        burst_ids = [mid for ts, mid in recent_rate if now - ts < 10]
        if len(burst_ids) >= 12 or len(recent_rate) >= 31:
            self.user_rate[chat_user] = []
            return True, "Слишком частые сообщения", burst_ids[-12:] if len(burst_ids) >= 12 else [
                mid for _, mid in recent_rate[-31:]
            ]

        if msg.sticker:
            recent_stickers = [
                (ts, mid) for ts, mid in self.user_stickers[chat_user] if now - ts < 10
            ]
            recent_stickers.append((now, msg.message_id))
            if len(recent_stickers) > 5:
                self.user_stickers[chat_user] = []
                return True, "Слишком много стикеров", [mid for _, mid in recent_stickers]
            self.user_stickers[chat_user] = recent_stickers
            return False, None, []

        is_gif = bool(msg.animation) or bool(
            msg.document
            and (
                msg.document.mime_type == 'image/gif'
                or (msg.document.file_name and msg.document.file_name.lower().endswith('.gif'))
            )
        )
        if is_gif:
            recent_animations = [
                (ts, mid) for ts, mid in self.user_animations[chat_user] if now - ts < 10
            ]
            recent_animations.append((now, msg.message_id))
            if len(recent_animations) > 5:
                self.user_animations[chat_user] = []
                return True, "Слишком много GIF-анимаций", [mid for _, mid in recent_animations]
            self.user_animations[chat_user] = recent_animations
            return False, None, []

        if not msg.text:
            return False, None, []

        stripped_text = msg.text.lstrip()
        prefix = get_command_prefix(msg.chat.id)
        if (
            stripped_text.startswith(('!', '/'))
            or (prefix and stripped_text.startswith(prefix))
            or (not prefix and match_command(stripped_text)[0] is not None)
        ):
            return False, None, []

        links = tuple(
            match.group(0).rstrip('.,!?;:)')
            for match in re.finditer(r'https?://\S+|www\.\S+', msg.text, flags=re.IGNORECASE)
        )
        if links:
            normalized_links = tuple(link.lower() for link in links)
            recent_links = [
                (ts, mid, urls)
                for ts, mid, urls in self.user_links[chat_user]
                if now - ts < 60
            ]
            recent_links.append((now, msg.message_id, normalized_links))
            self.user_links[chat_user] = recent_links
            recent_link_burst = [entry for entry in recent_links if now - entry[0] < 15]
            url_message_counts: Dict[str, int] = defaultdict(int)
            for _, _, previous_urls in recent_links:
                for url in set(previous_urls):
                    url_message_counts[url] += 1
            repeated_urls = {
                url for url, count in url_message_counts.items() if count >= 3
            }
            if len(links) >= 2 or len(recent_link_burst) >= 4 or repeated_urls:
                if repeated_urls:
                    spam_ids = [
                        mid for _, mid, urls in recent_links
                        if repeated_urls.intersection(urls)
                    ]
                else:
                    spam_ids = [mid for _, mid, _ in recent_link_burst]
                return True, "Спам-ссылками", spam_ids

        mention_count = len(re.findall(r'@\w+', msg.text))
        if mention_count:
            recent_mentions = [
                (ts, mid, count)
                for ts, mid, count in self.user_mentions[chat_user]
                if now - ts < 15
            ]
            recent_mentions.append((now, msg.message_id, mention_count))
            self.user_mentions[chat_user] = recent_mentions
            if mention_count >= 5 or sum(count for _, _, count in recent_mentions) >= 8:
                return True, "Массовые упоминания", [mid for _, mid, _ in recent_mentions]

        normalized_text = self._normalize_text(msg.text)
        if not normalized_text:
            return False, None, []

        recent_messages = [
            (ts, mid, body) for ts, mid, body in self.user_messages[chat_user] if now - ts < 60
        ]
        recent_messages.append((now, msg.message_id, normalized_text))
        self.user_messages[chat_user] = recent_messages

        if len(normalized_text) <= 3:
            fragments = [
                (ts, mid, body) for ts, mid, body in self.user_fragments[chat_user]
                if now - ts < 10
            ]
            fragments.append((now, msg.message_id, normalized_text))
            self.user_fragments[chat_user] = fragments
            distinct_fragments = {body for _, _, body in fragments}
            if len(fragments) >= 8 and len(distinct_fragments) >= 6:
                fragment_ids = [mid for _, mid, _ in fragments]
                self.user_fragments[chat_user] = []
                return True, "Флуд короткими сообщениями", fragment_ids

        exact_count = sum(1 for _, _, body in recent_messages if body == normalized_text)
        if exact_count >= 4:
            self.user_messages[chat_user] = []
            return True, "Повторяющиеся сообщения", [mid for _, mid, _ in recent_messages]

        if self._is_caps_flood(msg.text):
            caps_messages = [
                (ts, mid) for ts, mid in self.user_caps[chat_user] if now - ts < 10
            ]
            caps_messages.append((now, msg.message_id))
            self.user_caps[chat_user] = caps_messages
            if len(caps_messages) >= 3:
                return True, "Капс-флуд", [mid for _, mid in caps_messages]

        if len(recent_messages) >= 6:
            recent_bodies = [body for _, _, body in recent_messages]
            similarity_hits = 0
            for i in range(1, len(recent_bodies)):
                if self._similarity(recent_bodies[i - 1], recent_bodies[i]) >= 0.7:
                    similarity_hits += 1
            if similarity_hits >= 3:
                self.user_messages[chat_user] = []
                return True, "Повторяющиеся сообщения", [mid for _, mid, _ in recent_messages]

        return False, None, []


anti_spam = AntiSpamSystem()


async def handle_anti_spam(msg: Message) -> bool:
    if not msg.from_user or msg.from_user.is_bot:
        return False

    if msg.chat.type not in ('group', 'supergroup'):
        return False

    if await is_anti_spam_admin(msg.chat.id, msg.from_user.id):
        return False

    settings = storage.get_chat_settings(msg.chat.id)
    if not settings.get('anti_spam', {}).get('enabled', True):
        return False

    is_spam, reason, message_ids = anti_spam.check_message(msg)
    if not is_spam:
        return False

    deleted_ids = set()
    deduped_ids = list(dict.fromkeys(message_ids))
    for message_id in deduped_ids:
        try:
            await bot.delete_message(msg.chat.id, message_id)
            deleted_ids.add(message_id)
        except Exception as e:
            logger.warning(
                "Антиспам: не удалось удалить сообщение %s в чате %s: %s",
                message_id, msg.chat.id, e
            )

    for message_id in deleted_ids:
        activity_date = anti_spam.pop_message_date(msg.chat.id, msg.from_user.id, message_id)
        if activity_date:
            remove_message_activity(msg.chat.id, msg.from_user.id, activity_date)

    now = time.time()
    mutes = storage.get_chat(msg.chat.id, 'mutes')
    if not isinstance(mutes, list):
        mutes = []
        storage.data['mutes'][str(msg.chat.id)] = mutes

    active_mutes = [
        mute for mute in mutes
        if mute.get('user_id') == msg.from_user.id
        and (
            mute.get('permanent') is True
            or isinstance(mute.get('expire_time'), (int, float)) and mute['expire_time'] > now
        )
    ]
    if any(mute.get('permanent') is True for mute in active_mutes):
        return True
    base_wait = 60
    if reason == 'Капс-флуд':
        base_wait = 120
    elif reason in {'Спам-ссылками', 'Массовые упоминания', 'Флуд короткими сообщениями'}:
        base_wait = 180
    mute_until = max([now + base_wait] + [mute['expire_time'] for mute in active_mutes])
    try:
        await bot.restrict_chat_member(
            msg.chat.id,
            msg.from_user.id,
            ChatPermissions(can_send_messages=False),
            until_date=int(mute_until)
        )
    except Exception as e:
        logger.warning(
            "Антиспам: не удалось ограничить пользователя %s в чате %s: %s",
            msg.from_user.id, msg.chat.id, e
        )
        return True

    if active_mutes:
        active_mutes[0]['expire_time'] = mute_until
        issued_at = active_mutes[0].get('issued_at')
        if not isinstance(issued_at, (int, float)):
            issued_at = now
            active_mutes[0]['issued_at'] = issued_at
        active_mutes[0]['duration_minutes'] = max(1, round((mute_until - issued_at) / 60))
        active_mutes[0]['auto_mute'] = True
        for duplicate_mute in active_mutes[1:]:
            mutes.remove(duplicate_mute)
    else:
        mutes.append({
            'user_id': msg.from_user.id,
            'expire_time': mute_until,
            'issued_at': now,
            'duration_minutes': max(1, round((mute_until - now) / 60)),
            'muted_by': 'auto',
            'auto_mute': True,
            'reason': f'Антиспам: {reason}'
        })

    storage.mark_dirty()
    await storage.save()
    return True


# ==================== Хранилище данных ====================

class DataStorage:
    def __init__(self):
        self.data: Dict[str, Any] = self._get_default_data()
        self._lock = asyncio.Lock()
        self._dirty = False
        self._last_backup_ts = 0
        self._last_save_time = 0.0
        self._save_cooldown = 1.0
        self._save_task: Optional[asyncio.Task] = None
        self._chat_user_index: Dict[str, Dict[str, Dict[str, int]]] = {}
        import atexit
        atexit.register(self.save_sync)
        self.load()

    @staticmethod
    def _get_default_data() -> dict:
        return {
            'users': {}, 'command_access': {}, 'personal_access': {}, 'chat_owners': {},
            'mutes': {}, 'phrases': {},
            'welcome_settings': {}, 'marriages': {},
            'games': {}, 'backups': [], 'chat_settings': {}, 'rules': {}, 'polls': {},
            'rank_names': {}, 'rank_emoji': {}
        }

    @staticmethod
    def _create_default_user(uid: int) -> dict:
        """Создаёт пользователя с правильными полями."""
        return {
            'id': uid, 'username': '', 'first_name': '', 'rank': 0,
            'reputation': 0, 'last_rep_time_by_target': {}, 'last_rep_removed_time_by_target': {},
            'rep_given_today': {},
            'rep_given_total': 0, 'warnings': [], 'awards': [], 'marriage_partner': None,
            'marriage_date': None, 'pending_marriage': None, 'messages_count': 0,
            'activity': {}, 'ttt_games': 0, 'ttt_wins': 0, 'rps_games': 0,
            'rps_wins': 0, 'rps_current_streak': 0, 'rps_best_streak': 0,
            'custom_name': '', 'custom_tag': '', 'total_mutes_survived': 0, 'first_seen': time.time(),
            'last_seen': time.time(), 'night_messages': 0,
            'early_messages': 0, 'reports_sent': 0, 'phrases_added': 0,
            'marriage_count': 0, 'divorced_count': 0, 'proposals_sent': 0,
            'proposals_rejected': 0, 'chats_activity': {},
            'rp_victims_sex': [], 'rp_victims_kill': []
        }

    def load(self):
        """Стартовая загрузка без долгой нормализации всех пользователей."""
        try:
            if not os.path.exists(DATA_FILE):
                return

            with open(DATA_FILE, 'r', encoding='utf-8') as f:
                loaded = json.load(f)

            if isinstance(loaded, dict):
                self.data = loaded
            else:
                self.data = self._get_default_data()

            for key, default_value in self._get_default_data().items():
                if isinstance(default_value, dict):
                    self.data.setdefault(key, {})
                elif isinstance(default_value, list):
                    self.data.setdefault(key, [])
                else:
                    self.data.setdefault(key, default_value)

            users = self.data.get('users', {})
            legacy_chat_key = str(MAIN_GROUP_ID) if MAIN_GROUP_ID else 'legacy'
            is_old_format = False
            for k, v in users.items():
                if isinstance(v, dict) and 'id' in v and 'rank' in v:
                    is_old_format = True
                    break
            if is_old_format and users:
                logger.info("Обнаружен старый формат данных пользователей — переношу в per-chat формат")
                self.data['users'] = {legacy_chat_key: users}

            self._chat_user_index.clear()
            logger.info(f"Загружены данные: {len(self.data.get('users', {}))} чат(ов)")

        except Exception as e:
            logger.error(f"Ошибка загрузки: {e}")
            self.data = self._get_default_data()

    async def save(self):
        """Сохраняет текущее состояние и не теряет изменения при частых вызовах."""
        self._dirty = True
        if self._save_task and not self._save_task.done():
            return

        self._save_task = asyncio.create_task(self._background_save())
        await self._save_task

    async def _background_save(self):
        try:
            async with self._lock:
                if os.path.exists(DATA_FILE):
                    now_ts = time.time()
                    if now_ts - self._last_backup_ts >= 300:
                        backup_name = f"{BACKUP_DIR}/backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
                        import shutil
                        shutil.copy(DATA_FILE, backup_name)
                        self._last_backup_ts = now_ts
                        backups = sorted(Path(BACKUP_DIR).glob("backup_*.json"))
                        for old_backup in backups[:-5]:
                            old_backup.unlink()

                temp_file = f'{DATA_FILE}.tmp'
                with open(temp_file, 'w', encoding='utf-8') as f:
                    json.dump(self.data, f, ensure_ascii=False, indent=2, default=str)
                    f.flush()
                    os.fsync(f.fileno())
                os.replace(temp_file, DATA_FILE)

                self._last_save_time = time.monotonic()
                self._dirty = False
                logger.debug("Данные сохранены")

        except Exception as e:
            logger.error(f"Ошибка сохранения: {e}")
        finally:
            self._save_task = None

    def save_sync(self):
        try:
            save_data = json.loads(json.dumps(self.data, default=str))
            temp_file = f'{DATA_FILE}.tmp'
            with open(temp_file, 'w', encoding='utf-8') as f:
                json.dump(save_data, f, ensure_ascii=False, indent=2, default=str)
                f.flush()
                os.fsync(f.fileno())
            os.replace(temp_file, DATA_FILE)
            self._dirty = False
            logger.debug("Данные синхронно сохранены")
        except Exception as e:
            logger.error(f"Ошибка синхронного сохранения: {e}")

    def mark_dirty(self):
        self._dirty = True

    def _cleanup_old_games(self):
        now = time.time()
        if 'games' in self.data:
            expired = [gid for gid, game in self.data['games'].items() if now - game.get('started_at', now) > 86400]
            for gid in expired:
                del self.data['games'][gid]

    def invalidate_chat_user_index(self, chat_id: int):
        self._chat_user_index.pop(str(chat_id), None)

    def _rebuild_chat_user_index(self, chat_id: int) -> Dict[str, Dict[str, int]]:
        chat_key = str(chat_id)
        users = self.data.get('users', {}).get(chat_key, {})
        index = {'username': {}, 'names': {}}

        for uid_str, user_data in users.items():
            if not isinstance(user_data, dict):
                continue
            uid = int(uid_str)
            username = (user_data.get('username') or '').strip().lower()
            if username:
                index['username'][username] = uid

            for field_name in ('custom_name', 'first_name'):
                name = (user_data.get(field_name) or '').strip().lower()
                if name:
                    index['names'].setdefault(name, uid)

        self._chat_user_index[chat_key] = index
        return index

    def get_user_by_username(self, chat_id: int, username: str) -> Optional[int]:
        if not username:
            return None
        chat_key = str(chat_id)
        index = self._chat_user_index.get(chat_key)
        if index is None:
            index = self._rebuild_chat_user_index(chat_id)
        return index['username'].get(username.strip().lower())

    def get_user_by_name(self, chat_id: int, name: str) -> Optional[int]:
        if not name:
            return None
        chat_key = str(chat_id)
        index = self._chat_user_index.get(chat_key)
        if index is None:
            index = self._rebuild_chat_user_index(chat_id)
        return index['names'].get(name.strip().lower())

    def get_user(self, chat_id: int, uid: int, use_cache: bool = True) -> dict:
        chat_str, uid_str = str(chat_id), str(uid)
        cache_key = f"{chat_str}:{uid_str}"
        if use_cache:
            cached = user_cache.get(cache_key)
            if cached:
                return cached

        if 'users' not in self.data:
            self.data['users'] = {}
        if chat_str not in self.data['users']:
            self.data['users'][chat_str] = {}
        if uid_str not in self.data['users'][chat_str]:
            self.data['users'][chat_str][uid_str] = self._create_default_user(uid)

        user = self.data['users'][chat_str][uid_str]
        if not isinstance(user, dict):
            user = self._create_default_user(uid)
            self.data['users'][chat_str][uid_str] = user

        default_fields = {
            'chats_activity': {},
            'night_messages': 0,
            'early_messages': 0,
            'reports_sent': 0,
            'phrases_added': 0,
            'marriage_count': 0,
            'divorced_count': 0,
            'proposals_sent': 0,
            'proposals_rejected': 0,
            'total_mutes_survived': 0,
            'custom_tag': '',
            'custom_name': '',
            'first_name': '',
            'username': '',
            'rank': 0,
            'reputation': 0,
            'last_rep_time_by_target': {},
            'last_rep_removed_time_by_target': {},
            'warnings': [],
            'awards': [],
            'activity': {},
            'marriage_partner': None
        }
        for field, default_value in default_fields.items():
            if field not in user:
                user[field] = default_value

        if use_cache:
            user_cache.set(cache_key, user)
        return user

    def invalidate_user_cache(self, chat_id: int, uid: int):
        user_cache.invalidate(f"{chat_id}:{uid}")
        mention_cache.invalidate(f"mention_{chat_id}_{uid}")
        self.invalidate_chat_user_index(chat_id)

    def update_user_from_message(self, msg: Message):
        if msg.from_user.is_bot:
            return False

        u = self.get_user(msg.chat.id, msg.from_user.id)
        changed = False

        if is_main_chat(msg.chat.id, msg.message_thread_id):
            hour = datetime.now().hour
            if hour >= 23 or hour <= 4:
                u['night_messages'] = u.get('night_messages', 0) + 1
            elif hour >= 5 and hour <= 7:
                u['early_messages'] = u.get('early_messages', 0) + 1

        if msg.from_user.username and u.get('username') != msg.from_user.username:
            u['username'] = msg.from_user.username
            changed = True
        if msg.from_user.first_name and u.get('first_name') != msg.from_user.first_name:
            u['first_name'] = msg.from_user.first_name
            changed = True
        u['last_seen'] = time.time()
        changed = True

        if changed:
            self.invalidate_user_cache(msg.chat.id, msg.from_user.id)
        return changed

    def get_chat(self, chat_id: int, key: str):
        chat_id = str(chat_id)
        if key not in self.data:
            self.data[key] = {}
        if chat_id not in self.data[key]:
            if key in ['mutes', 'phrases', 'rules', 'polls']:
                self.data[key][chat_id] = []
            else:
                self.data[key][chat_id] = {}
        return self.data[key][chat_id]

    def get_chat_settings(self, chat_id: int, use_cache: bool = True) -> dict:
        chat_id = str(chat_id)
        if use_cache:
            cached = chat_settings_cache.get(chat_id)
            if cached:
                return cached
        if 'chat_settings' not in self.data:
            self.data['chat_settings'] = {}
        if chat_id not in self.data['chat_settings']:
            self.data['chat_settings'][chat_id] = {
                'command_prefix': '!',
                'anti_moderation': True,
                'anti_spam': {'enabled': ANTI_SPAM_ENABLED},
                'warn_actions': [{'count': 3, 'action': 'mute', 'duration': 60},
                                 {'count': 5, 'action': 'mute', 'duration': 1440},
                                 {'count': MAX_WARNINGS, 'action': 'ban', 'duration': 0}]
            }
        result = self.data['chat_settings'][chat_id]
        if use_cache:
            chat_settings_cache.set(chat_id, result)
        return result

    def invalidate_chat_settings_cache(self, chat_id: int):
        chat_settings_cache.invalidate(str(chat_id))


storage = DataStorage()


# ==================== Wordle (русский) ====================

class WordleGame:
    """
    Класс для управления игрой Wordle (русская версия).
    Использует файл russian_words.txt (если есть) или встроенный словарь.
    """
    def __init__(self, words_file: str = WORDLE_WORDS_FILE):
        self.words_file = words_file
        self._words_cache = None
        self.games = {}  # активные игры: key = f"wordle_{user_id}"

    DIFFICULTY_NAMES = {
        'easy': 'лёгкий',
        'medium': 'средний',
        'hard': 'сложный',
        'expert': 'экспертный',
    }
    DIFFICULTY_ALIASES = {
        'лёгкий': 'easy', 'легкий': 'easy', 'легкая': 'easy', 'лёгкая': 'easy', 'easy': 'easy', 'легко': 'easy',
        'средний': 'medium', 'средняя': 'medium', 'medium': 'medium', 'среднее': 'medium',
        'сложный': 'hard', 'сложная': 'hard', 'hard': 'hard',
        'эксперт': 'expert', 'экспертный': 'expert', 'экспертная': 'expert', 'expert': 'expert', 'экстрим': 'expert',
    }
    COMMON_WORDS = {
        'вода', 'ветер', 'город', 'дверь', 'земля', 'игрок', 'книга', 'кошка', 'луна',
        'море', 'ночь', 'огонь', 'песня', 'птица', 'река', 'собака', 'слово', 'солнце',
        'стена', 'стол', 'текст', 'цветок', 'школа', 'шутка', 'яблоко', 'молоко',
    }

    def _load_words(self):
        if self._words_cache is not None:
            return self._words_cache

        words = []
        try:
            with open(self.words_file, 'r', encoding='utf-8') as f:
                for line in f:
                    w = line.strip().lower()
                    if 4 <= len(w) <= 6 and w.isalpha():
                        words.append(w)
            if words:
                self._words_cache = words
                return words
        except FileNotFoundError:
            pass

        # Fallback-словарь (500+ слов)
        fallback = [
            "дом", "год", "день", "ночь", "мир", "вода", "огонь", "земля", "ветер", "лес",
            "река", "гора", "море", "солнце", "луна", "звезда", "небо", "облако", "дождь", "снег",
            "город", "дело", "слово", "друг", "враг", "мать", "отец", "брат", "сестра", "сын",
            "дочь", "муж", "жена", "человек", "народ", "власть", "сила", "мысль", "душа", "сердце",
            "кровь", "кость", "рука", "нога", "глаз", "ухо", "нос", "рот", "зуб", "язык",
            "лицо", "лоб", "бровь", "ресница", "щека", "губа", "шея", "плечо", "грудь", "спина",
            "живот", "пояс", "бедро", "колено", "голень", "стопа", "палец", "ноготь", "волос", "борода",
            "усы", "бакен", "шевелюра", "челка", "затылок", "висок", "скула", "челюсть", "подбородок", "горло",
            "трава", "цветок", "дерево", "куст", "лист", "корень", "ствол", "ветка", "плод", "семя",
            "животное", "птица", "рыба", "зверь", "волк", "лиса", "медведь", "заяц", "лось", "олень",
            "кошка", "собака", "корова", "лошадь", "свинья", "коза", "овца", "курица", "утка", "гусь",
            "лебедь", "ворона", "сорока", "воробей", "голубь", "орёл", "сокол", "ястреб", "филин", "сова",
            "мышь", "крыса", "хомяк", "морж", "тюлень", "дельфин", "кит", "акула", "осьминог", "медуза",
            "растение", "гриб", "ягода", "яблоко", "груша", "слива", "вишня", "черешня", "абрикос", "персик",
            "виноград", "арбуз", "дыня", "тыква", "огурец", "помидор", "картофель", "морковь", "свекла", "лук",
            "чеснок", "капуста", "салат", "укроп", "петрушка", "перец", "баклажан", "кабачок", "горох", "фасоль",
            "хлеб", "молоко", "масло", "сыр", "творог", "сметана", "яйцо", "мясо", "рыба", "соль",
            "сахар", "мед", "варенье", "компот", "кисель", "суп", "борщ", "щи", "каша", "макароны",
            "печенье", "пирог", "блин", "оладья", "вафля", "конфета", "шоколад", "вареник", "пельмень", "чебурек",
            "квартира", "комната", "кухня", "ванна", "туалет", "коридор", "лестница", "лифт", "балкон", "крыша",
            "стена", "пол", "потолок", "окно", "дверь", "замок", "ключ", "стол", "стул", "кровать",
            "диван", "кресло", "шкаф", "полка", "зеркало", "ковер", "лампа", "свет", "тень", "цвет",
            "рисунок", "картина", "фотография", "книга", "журнал", "газета", "письмо", "конверт", "марка", "почта",
            "школа", "учитель", "ученик", "парта", "доска", "мел", "ручка", "карандаш", "ластик", "тетрадь",
            "дневник", "урок", "звонок", "перемена", "экзамен", "оценка", "знание", "ум", "талант", "гений",
            "врач", "больница", "аптека", "лекарство", "таблетка", "укол", "перевязка", "здоровье", "болезнь", "грипп",
            "магазин", "продавец", "покупатель", "товар", "цена", "деньги", "монета", "кусок", "мелочь", "сдача",
            "дорога", "путь", "тропа", "шоссе", "перекресток", "светофор", "машина", "автобус", "троллейбус", "трамвай",
            "метро", "поезд", "самолет", "вертолет", "корабль", "лодка", "пароход", "яхта", "весло", "парус",
            "спорт", "футбол", "хоккей", "теннис", "волейбол", "баскетбол", "лыжи", "коньки", "санки", "шахматы",
            "музыка", "песня", "танец", "театр", "кино", "актер", "роль", "сцена", "зритель", "аплодисменты"
        ]
        fallback = sorted(set(fallback))
        self._words_cache = fallback
        return fallback

    @classmethod
    def normalize_difficulty(cls, difficulty: str = 'medium') -> str:
        return cls.DIFFICULTY_ALIASES.get((difficulty or '').lower().strip(), 'medium')

    @staticmethod
    def _word_difficulty_score(word: str) -> int:
        rare_letters = set('жцчщъэюяфх')
        score = sum(letter in rare_letters for letter in word)
        score += max(0, len(set(word)) - 3) // 2
        score += sum(word[index] == word[index - 1] for index in range(1, len(word)))
        return score

    def get_random_word(self, length: int, difficulty: str = 'medium') -> str:
        words = self._load_words()
        filtered = [w for w in words if len(w) == length]
        if not filtered:
            fallback = {4: "река", 5: "слово", 6: "сестра"}
            return fallback.get(length, "слово")

        difficulty = self.normalize_difficulty(difficulty)
        if difficulty == 'easy':
            common = [word for word in filtered if word in self.COMMON_WORDS]
            candidates = common or sorted(filtered, key=self._word_difficulty_score)[:max(1, len(filtered) // 4)]
        else:
            scores = {word: self._word_difficulty_score(word) for word in filtered}
            ordered = sorted(filtered, key=lambda word: scores[word])
            start = {'medium': 0, 'hard': 1, 'expert': 2}[difficulty] * len(ordered) // 4
            end = (('medium', 'hard', 'expert').index(difficulty) + 2) * len(ordered) // 4
            candidates = ordered[start:max(start + 1, end)]
        return random.choice(candidates)

    @staticmethod
    def check_guess(word: str, guess: str) -> str:
        result = [''] * len(word)
        word_list = list(word)
        guess_list = list(guess)

        for i in range(len(word_list)):
            if guess_list[i] == word_list[i]:
                result[i] = '🟩'
                word_list[i] = None
                guess_list[i] = None

        for i in range(len(guess_list)):
            if guess_list[i] is None:
                continue
            if guess_list[i] in word_list:
                result[i] = '🟨'
                word_list[word_list.index(guess_list[i])] = None
            else:
                result[i] = '⬛'

        return ''.join(result)

    def start_game(self, user_id: int, length: int = DEFAULT_WORDLE_LENGTH,
                   attempts: int = DEFAULT_WORDLE_ATTEMPTS, difficulty: str = 'medium'):
        key = f"wordle_{user_id}"
        if key in self.games:
            return False, "❌ Вы уже играете. Завершите: !wordle exit"

        difficulty = self.normalize_difficulty(difficulty)
        word = self.get_random_word(length, difficulty)
        if not word:
            return False, "❌ Не удалось получить слово."

        self.games[key] = {
            'word': word,
            'length': length,
            'attempts': attempts,
            'attempts_left': attempts,
            'guesses': [],
            'status': 'active',
            'user_id': user_id,
            'chat_id': None,
            'message_id': None,
            'difficulty': difficulty
        }
        return True, (f"🎮 <b>Wordle (русский)</b>\n\n"
                      f"Загадано слово из <b>{length}</b> букв.\n"
                      f"У вас <b>{attempts}</b> попыток.\n\n"
                      f"Введите слово в следующем сообщении.\n"
                      f"🟩 — на месте\n🟨 — есть, но не на месте\n⬛ — нет\n\n"
                      f"Для выхода: <code>!wordle exit</code>")

    def start_chat_game(self, chat_id: int, user_id: int, length: int = DEFAULT_WORDLE_LENGTH,
                        attempts: int = DEFAULT_WORDLE_ATTEMPTS, difficulty: str = 'medium'):
        key = f"wordle_chat_{chat_id}"
        if key in self.games and self.games[key]['status'] == 'active':
            return False, "❌ В этом чате уже идёт игра Wordle."

        difficulty = self.normalize_difficulty(difficulty)
        word = self.get_random_word(length, difficulty)
        if not word:
            return False, "❌ Не удалось получить слово."

        self.games[key] = {
            'word': word,
            'length': length,
            'attempts': attempts,
            'attempts_left': attempts,
            'guesses': [],
            'status': 'active',
            'user_id': user_id,
            'chat_id': chat_id,
            'message_id': None
            , 'difficulty': difficulty
        }
        return True, (f"🎮 <b>Wordle на русском</b>\n\n"
                  f"🔤 Загадано слово из <b>{length}</b> букв.\n"
                f"🎚️ Сложность: <b>{self.DIFFICULTY_NAMES[difficulty]}</b>\n"
                  f"🎯 Всего на всех игроков — до <b>{attempts}</b> попыток.\n\n"
                  f"<b>Как играть:</b>\n"
                  f"1️⃣ Ответьте на это сообщение словом из {length} букв.\n"
                  f"2️⃣ Бот покажет результат после каждой попытки.\n"
                  f"🟩 буква угадана и стоит на месте\n"
                  f"🟨 буква есть, но место другое\n"
                  f"⬛ такой буквы нет в слове\n\n"
                  f"💡 Это одна общая игра для всего чата: отвечайте на это сообщение.\n"
                  f"⏹️ Отменить игру: <code>!wordle exit</code>\n"
                  f"🛑 Админу остановить игру: <code>!wordle stop</code>")

    def make_guess(self, chat_id: int, user_id: int, guess: str, player_name: str):
        game = self.get_chat_game(chat_id)
        if not game or game['status'] != 'active':
            return False, "❌ В этом чате нет активной игры.", None

        if len(guess) != game['length']:
            return False, f"❌ Слово должно быть из {game['length']} букв.", None
        if not re.fullmatch(r'[а-яё]+', guess):
            return False, "❌ Только русские буквы.", None

        used_words = {entry[1] for entry in game['guesses']}
        if guess in used_words:
            return False, "❌ Это слово уже вводили. Попробуйте другое.", None

        result_emoji = self.check_guess(game['word'], guess)
        game['guesses'].append((player_name, guess, result_emoji))
        game['attempts_left'] -= 1

        display = '\n'.join([f"👤 <b>{name}</b>: <code>{g}</code> — {r}"
                     for name, g, r in game['guesses']])

        if guess == game['word']:
            game['status'] = 'finished'
            return True, (f"🎉 <b>Поздравляем!</b>\n\n{display}\n\n"
                          f"Попыток: {game['attempts'] - game['attempts_left']}"), game

        if game['attempts_left'] == 0:
            game['status'] = 'finished'
            return True, (f"😞 <b>Игра окончена!</b>\n\n{display}\n\n"
                          f"Загаданное слово: <b>{game['word']}</b>"), game

        return True, (f"📝 <b>Попытка {game['attempts'] - game['attempts_left']}</b>\n\n{display}\n\n"
                      f"Осталось: {game['attempts_left']}"), None

    def exit_chat_game(self, chat_id: int) -> bool:
        key = f"wordle_chat_{chat_id}"
        if key in self.games:
            del self.games[key]
            return True
        return False

    def set_game_message(self, user_id: int, chat_id: int, message_id: int):
        game = self.get_chat_game(chat_id)
        if game is not None:
            game['message_id'] = message_id

    def get_game_state(self, user_id: int):
        return self.games.get(f"wordle_{user_id}")

    def get_chat_game(self, chat_id: int):
        return self.games.get(f"wordle_chat_{chat_id}")

wordle = WordleGame()
# ==================== Бот ====================

bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
dp = Dispatcher()
router = Router()
dp.include_router(router)

RANK_EMOJI = {
    0: "👤",  # Обычный
    1: "🪪",  # Стажёр
    2: "👨‍👦",  # Папаша
    3: "👑",  # Батя
    4: "⭐",  # Главный Отец
    5: "🔥"  # Отец Нации
}

RANK_NAMES = {
    0: "Обычный",
    1: "Стажёр",
    2: "Папаша",
    3: "Батя",
    4: "Главный Отец",
    5: "Отец Нации"
}

MAX_RANK = 5


def get_rank_name(chat_id: int, level: int) -> str:
    """Возвращает название ранга с учётом кастомных настроек чата"""
    custom = storage.data.get('rank_names', {}).get(str(chat_id), {})
    return custom.get(str(level)) or RANK_NAMES.get(level, "Обычный")


def get_rank_emoji(chat_id: int, level: int) -> str:
    """Возвращает эмодзи ранга с учётом кастомных настроек чата"""
    custom = storage.data.get('rank_emoji', {}).get(str(chat_id), {})
    return custom.get(str(level)) or RANK_EMOJI.get(level, "👤")


# ==================== Вспомогательные функции ====================

MUTE_TIME_UNIT_PATTERN = (
    r'(?:тысячелети(?:е|я|й|и)?|тыс\.?|век(?:а|у|и|ов)?|'
    r'год(?:а|у|ы|ов)?|лет|г(?![а-яёa-z])|'
    r'месяц(?:а|у|е|ы|ев)?|мес\.?|'
    r'недел(?:я|и|ю|ей|е)|нед\.?|'
    r'день|дня|дней|дни|дн\.?|д(?![а-яёa-z])|'
    r'час(?:а|у|ы|ов)?|ч\.?|'
    r'мин(?:ут(?:а|ы|у|е|ой|ами|ах)?|\.?)|м(?![а-яёa-z])|'
    r'years?|yrs?|months?|mos?|weeks?|wks?|days?|hrs?|hours?|mins?|minutes?|'
    r'y|d|h)'
)
MUTE_TIME_UNIT_REGEX = re.compile(
    rf'(?P<value>\d+)\s*(?P<unit>{MUTE_TIME_UNIT_PATTERN})(?=$|\s|[.,])',
    re.IGNORECASE,
)
MUTE_TIME_MULTIPLIERS = {
    'тысячелетие': 525600000, 'тысячелетия': 525600000, 'тысячелетий': 525600000,
    'тысячилетие': 525600000, 'тыс': 525600000,
    'век': 52560000, 'века': 52560000, 'веку': 52560000, 'веки': 52560000, 'веков': 52560000,
    'год': 525600, 'года': 525600, 'году': 525600, 'годы': 525600, 'годов': 525600, 'лет': 525600, 'г': 525600,
    'месяц': 43800, 'месяца': 43800, 'месяцу': 43800, 'месяце': 43800, 'месяцы': 43800, 'месяцев': 43800, 'мес': 43800,
    'неделя': 10080, 'недели': 10080, 'неделю': 10080, 'недель': 10080, 'неделе': 10080, 'нед': 10080,
    'день': 1440, 'дня': 1440, 'дней': 1440, 'дни': 1440, 'дн': 1440, 'д': 1440,
    'час': 60, 'часа': 60, 'часу': 60, 'часы': 60, 'часов': 60, 'ч': 60,
    'минута': 1, 'минуты': 1, 'минуту': 1, 'минуте': 1, 'минутой': 1,
    'минутами': 1, 'минутах': 1, 'мин': 1, 'м': 1,
    'year': 525600, 'years': 525600, 'yr': 525600, 'yrs': 525600, 'y': 525600,
    'month': 43800, 'months': 43800, 'mo': 43800, 'mos': 43800,
    'week': 10080, 'weeks': 10080, 'wk': 10080, 'wks': 10080, 'w': 10080,
    'day': 1440, 'days': 1440, 'd': 1440,
    'hour': 60, 'hours': 60, 'hr': 60, 'hrs': 60, 'h': 60,
    'minute': 1, 'minutes': 1, 'min': 1, 'mins': 1,
}


def _normalize_mute_time_unit(unit: str) -> Optional[int]:
    normalized = unit.lower().rstrip('.')
    multiplier = MUTE_TIME_MULTIPLIERS.get(normalized)
    if multiplier is not None:
        return multiplier
    if normalized.startswith('тысячелети'):
        return 525600000
    return None


def _parse_mute_duration_prefix(text: str) -> Tuple[str, str]:
    """Splits a leading sequence of duration units from the remaining reason."""
    position = 0
    total_components = 0
    length = len(text)

    while position < length:
        whitespace_start = position
        while position < length and text[position].isspace():
            position += 1
        match = MUTE_TIME_UNIT_REGEX.match(text, position)
        if match:
            multiplier = _normalize_mute_time_unit(match.group('unit'))
            if multiplier is None:
                position = whitespace_start
                break
            try:
                int(match.group('value'))
            except ValueError:
                position = whitespace_start
                break
            position = match.end()
            total_components += 1
            continue

        number_match = re.match(r'\d+', text[position:])
        if number_match and total_components == 0:
            number_end = position + number_match.end()
            if number_end == length or text[number_end].isspace():
                position = number_end
                total_components = 1
        break

    if not total_components:
        return '', text.strip()
    duration = text[:position].strip()
    reason = text[position:].strip()
    return duration, reason or 'Без причины'


def format_mute_duration(duration_minutes: int) -> str:
    if duration_minutes >= 525600:
        years, remainder = divmod(duration_minutes, 525600)
        months = remainder // 43800
        parts = [f"{years} г."]
        if months:
            parts.append(f"{months} мес.")
        return ' '.join(parts)
    if duration_minutes >= 43800:
        months, remainder = divmod(duration_minutes, 43800)
        days = remainder // 1440
        parts = [f"{months} мес."]
        if days:
            parts.append(f"{days} д.")
        return ' '.join(parts)
    if duration_minutes >= 1440:
        days, remainder = divmod(duration_minutes, 1440)
        hours, minutes = divmod(remainder, 60)
        parts = [f"{days} д."]
        if hours:
            parts.append(f"{hours} ч.")
        if minutes:
            parts.append(f"{minutes} мин.")
        return ' '.join(parts)
    if duration_minutes >= 60:
        hours, minutes = divmod(duration_minutes, 60)
        return f"{hours} ч." + (f" {minutes} мин." if minutes else '')
    return f"{duration_minutes} мин."


def parse_time(s: str) -> int:
    if not s:
        return DEFAULT_MUTE_MINUTES
    s = s.strip()
    if re.fullmatch(r'\d+', s):
        try:
            return int(s)
        except ValueError:
            return 0

    total_minutes = 0
    position = 0
    components = 0
    while position < len(s):
        while position < len(s) and s[position].isspace():
            position += 1
        if position == len(s):
            break
        match = MUTE_TIME_UNIT_REGEX.match(s, position)
        if not match:
            return 0
        multiplier = _normalize_mute_time_unit(match.group('unit'))
        if multiplier is None:
            return 0
        try:
            total_minutes += int(match.group('value')) * multiplier
        except ValueError:
            return 0
        position = match.end()
        components += 1
    return total_minutes if components else 0


PERMANENT_MUTE_ALIASES = {
    'навсегда', 'навечно', 'бессрочно', 'бессрочный', 'бессрочная',
    'перманент', 'перманентно', 'forever', 'permanent', 'perm',
}
MAX_MUTE_MINUTES = 365 * 24 * 60


def parse_mute_duration_and_reason(text: str) -> Tuple[bool, str, str]:
    text = text.strip()
    permanent_aliases = '|'.join(
        re.escape(alias) for alias in sorted(PERMANENT_MUTE_ALIASES, key=len, reverse=True)
    )
    permanent_match = re.match(
        rf'^({permanent_aliases})\b(?:\s+(.*))?$',
        text,
        re.IGNORECASE,
    )
    if permanent_match:
        return True, '', (permanent_match.group(2) or 'Без причины').strip()

    duration, reason = _parse_mute_duration_prefix(text)
    if not duration and re.match(r'^\d', text):
        return False, text, 'Без причины'
    return False, duration, reason


def warning_is_active(warning: dict, now: Optional[float] = None) -> bool:
    if warning.get('permanent') is True:
        return True
    expire_date = warning.get('expire_date')
    current_time = time.time() if now is None else now
    return isinstance(expire_date, (int, float)) and expire_date > current_time


def mention(chat_id: int, user: Union[User, int, str]) -> str:
    """Возвращает кликабельную ссылку на пользователя"""
    try:
        if isinstance(user, User):
            safe_name = html.escape(str(user.first_name or user.username or "Пользователь"), quote=False)
            if user.username:
                safe_username = html.escape(str(user.username), quote=True)
                return f'<a href="https://t.me/{safe_username}">{safe_name}</a>'
            else:
                return f'<a href="tg://user?id={user.id}">{safe_name}</a>'
        if isinstance(user, int):
            cache_key = f"mention_{chat_id}_{user}"
            cached = mention_cache.get(cache_key)
            if cached:
                return cached
            u = storage.get_user(chat_id, user)
            username = u.get('username', '')
            base_display = u.get('custom_name') or u.get('first_name') or username or f"ID:{user}"
            display = html.escape(str(base_display), quote=False)
            safe_username = html.escape(str(username), quote=True)
            if username:
                result = f'<a href="https://t.me/{safe_username}">{display}</a>'
            else:
                result = f'<a href="tg://user?id={user}">{display}</a>'
            mention_cache.set(cache_key, result)
            return result
        return html.escape(str(user), quote=False)
    except:
        return str(user)


def get_display_name(chat_id: int, uid: int) -> str:
    """Возвращает кастомное или реальное имя пользователя."""
    u = storage.get_user(chat_id, uid)
    base = u.get('custom_name') or u.get('first_name') or u.get('username') or f"ID:{uid}"
    return html.escape(str(base), quote=False)


def get_target_mention_span(msg: Message, arg: Optional[str]) -> Optional[Tuple[int, int, int]]:
    """Возвращает ID и границы кликабельного упоминания без username в тексте команды."""
    if not arg or not msg.text:
        return None

    argument = arg.strip().lstrip('@').casefold()
    if not argument:
        return None

    encoded_text = msg.text.encode('utf-16-le')
    for entity in msg.entities or []:
        entity_type = getattr(entity.type, 'value', entity.type)
        target_id = None
        if entity_type == 'text_mention' and entity.user:
            target_id = entity.user.id
        elif entity_type == 'text_link':
            match = re.fullmatch(r'tg://user\?id=(\d+)', entity.url or '')
            if match:
                target_id = int(match.group(1))
        if target_id is None:
            continue

        byte_start = entity.offset * 2
        byte_end = (entity.offset + entity.length) * 2
        if byte_end > len(encoded_text):
            continue
        try:
            start = len(encoded_text[:byte_start].decode('utf-16-le'))
            end = len(encoded_text[:byte_end].decode('utf-16-le'))
            entity_text = encoded_text[byte_start:byte_end].decode('utf-16-le')
        except UnicodeDecodeError:
            logger.warning("Некорректные границы Telegram entity в сообщении %s", msg.message_id)
            continue

        normalized_entity = entity_text.strip().casefold()
        if (
            normalized_entity == argument
            or normalized_entity.startswith(argument)
            and len(normalized_entity) > len(argument)
            and normalized_entity[len(argument)].isspace()
        ):
            return target_id, start, end
    return None


async def get_target(msg: Message, arg: str = None) -> Optional[int]:
    """
    Получить ID цели. Приоритет: ответ на сообщение > аргумент (username, ID, имя).
    Поддерживает @username, Telegram ID и кликабельные упоминания без username.
    """
    if msg.reply_to_message and msg.reply_to_message.from_user:
        return msg.reply_to_message.from_user.id

    if not arg:
        return None

    arg = arg.strip()

    mention_span = get_target_mention_span(msg, arg)
    if mention_span:
        return mention_span[0]

    # Если это @username
    if arg.startswith('@'):
        username = arg[1:].lower()
        uid = storage.get_user_by_username(msg.chat.id, username)
        if uid is not None:
            return uid

        # Если не нашли в базе - пробуем найти через API Telegram
        try:
            # Пытаемся получить пользователя по username через API
            # Используем get_chat, который работает с @username
            chat_info = await bot.get_chat(arg)
            if chat_info and chat_info.type == 'private':
                return chat_info.id
        except Exception as e:
            logger.debug(f"Не удалось найти пользователя @{username} через API: {e}")

        # Всё ещё не нашли
        return None

    # Если это числовой ID
    if arg.isdigit():
        return int(arg)

    # Поиск по имени (только в сохранённых)
    search = arg.lower()
    uid = storage.get_user_by_name(msg.chat.id, search)
    if uid is not None:
        return uid

    return None


CHAT_OWNER_CACHE_TTL = 60
chat_owner_sync_cache: Dict[int, Tuple[float, Optional[int]]] = {}
chat_owner_sync_locks: Dict[int, asyncio.Lock] = {}


async def sync_chat_owner(chat_id: int):
    """Keeps rank 5 assigned to the current Telegram chat owner."""
    now = time.monotonic()
    cached = chat_owner_sync_cache.get(chat_id)
    if cached and cached[0] > now:
        return

    lock = chat_owner_sync_locks.setdefault(chat_id, asyncio.Lock())
    async with lock:
        now = time.monotonic()
        cached = chat_owner_sync_cache.get(chat_id)
        if cached and cached[0] > now:
            return

        try:
            administrators = await bot.get_chat_administrators(chat_id)
        except Exception as e:
            logger.warning("Не удалось определить владельца чата %s: %s", chat_id, e)
            return

        owner = next((member.user for member in administrators if member.status == 'creator'), None)
        if owner is None:
            logger.warning("Telegram не вернул владельца чата %s среди администраторов", chat_id)
            chat_owner_sync_cache[chat_id] = (now + CHAT_OWNER_CACHE_TTL, None)
            return

        owners = storage.data.setdefault('chat_owners', {})
        chat_key = str(chat_id)
        previous = owners.get(chat_key)
        if previous is not None and not isinstance(previous, dict):
            logger.warning("Некорректная запись владельца чата %s в хранилище", chat_id)
            previous = None

        if previous and previous.get('user_id') != owner.id:
            previous_user_id = previous.get('user_id')
            previous_rank = previous.get('rank_before', 0)
            if isinstance(previous_user_id, int):
                if isinstance(previous_rank, int) and 0 <= previous_rank <= MAX_RANK:
                    storage.get_user(chat_id, previous_user_id, use_cache=False)['rank'] = previous_rank
                    storage.invalidate_user_cache(chat_id, previous_user_id)
                else:
                    logger.warning("Некорректный прежний ранг владельца чата %s", chat_id)

        if not previous or previous.get('user_id') != owner.id:
            owner_user = storage.get_user(chat_id, owner.id, use_cache=False)
            owners[chat_key] = {'user_id': owner.id, 'rank_before': owner_user.get('rank', 0)}
            owner_user['rank'] = MAX_RANK
            storage.invalidate_user_cache(chat_id, owner.id)
            storage.mark_dirty()
        else:
            owner_user = storage.get_user(chat_id, owner.id, use_cache=False)
            if owner_user.get('rank') != MAX_RANK:
                owner_user['rank'] = MAX_RANK
                storage.invalidate_user_cache(chat_id, owner.id)
                storage.mark_dirty()

        chat_owner_sync_cache[chat_id] = (now + CHAT_OWNER_CACHE_TTL, owner.id)


def check_access(uid: int, chat_id: int, cmd: str, min_rank: int = 0) -> bool:
    chat_id_str = str(chat_id)
    command_func = COMMANDS.get(cmd)
    aliases = (
        [alias for alias, func in COMMANDS.items() if func == command_func]
        if command_func else [cmd]
    )
    command_access = storage.data['command_access'].get(chat_id_str, {})
    if any(command_access.get(alias) == 9 for alias in aliases):
        return False

    personal_access = storage.data['personal_access'].get(chat_id_str, {})
    if any(uid in personal_access.get(alias, []) for alias in aliases):
        return True

    configured_ranks = [
        command_access[alias]
        for alias in aliases
        if alias in command_access and isinstance(command_access[alias], int)
    ]
    required_rank = max(configured_ranks) if configured_ranks else min_rank
    return storage.get_user(chat_id, uid).get('rank', 0) >= required_rank if required_rank else True


def get_command_aliases(command: str) -> List[str]:
    command_func = COMMANDS.get(command)
    if command_func is None:
        return [command]
    return [alias for alias, func in COMMANDS.items() if func == command_func]


async def is_telegram_admin(chat_id: int, uid: int) -> bool:
    """Проверяет реальные права пользователя в Telegram перед модерацией."""
    try:
        member = await bot.get_chat_member(chat_id, uid)
        return member.status in ('administrator', 'creator')
    except Exception as e:
        logger.warning("Не удалось проверить права %s в чате %s: %s", uid, chat_id, e)
        return False


async def is_anti_spam_admin(chat_id: int, uid: int) -> bool:
    cache_key = f"{chat_id}:{uid}"
    cached_status = anti_spam_admin_cache.get(cache_key)
    if cached_status is not None:
        return cached_status

    try:
        member = await bot.get_chat_member(chat_id, uid)
    except Exception as e:
        logger.warning(
            "Антиспам: не удалось проверить права %s в чате %s: %s",
            uid, chat_id, e
        )
        anti_spam_admin_cache.set(cache_key, False, ttl=3)
        return False

    is_admin = member.status in ('administrator', 'creator')
    anti_spam_admin_cache.set(cache_key, is_admin)
    return is_admin


async def require_telegram_admin(msg: Message) -> bool:
    if await is_telegram_admin(msg.chat.id, msg.from_user.id):
        return True
    await msg.answer("❌ Нужны права администратора Telegram для этой команды.")
    return False


def check_anti_moderation(initiator_id: int, target_id: int, chat_id: int) -> bool:
    if initiator_id == target_id:
        return False
    if not storage.get_chat_settings(chat_id).get('anti_moderation', True):
        return True
    initiator_rank = storage.get_user(chat_id, initiator_id).get('rank', 0)
    target_rank = storage.get_user(chat_id, target_id).get('rank', 0)
    if initiator_rank == 0 and target_rank == 0:
        return True
    if target_rank == 0:
        return True
    if initiator_rank > target_rank:
        return True
    return False


def save_activity(chat_id: int, uid: int, atype: str = 'messages', amount: int = 1):
    """Сохраняет активность только если пользователь в основной группе"""
    atype_map = {'command': 'commands', 'commands': 'commands', 'rep': 'reputation', 'reputation': 'reputation',
                 'game': 'games', 'games': 'games', 'message': 'messages', 'messages': 'messages'}
    atype = atype_map.get(atype, 'messages')
    u = storage.get_user(chat_id, uid)
    today = kaliningrad_now().strftime('%Y-%m-%d')
    if 'activity' not in u:
        u['activity'] = {}
    if today not in u['activity']:
        u['activity'][today] = {'messages': 0, 'reputation': 0, 'commands': 0, 'games': 0}
    if atype not in u['activity'][today]:
        u['activity'][today][atype] = 0
    u['activity'][today][atype] += amount
    dates = sorted(u['activity'].keys())
    if len(dates) > 60:
        for old in dates[:-60]:
            del u['activity'][old]
    storage.mark_dirty()


def get_activity_message_count(activity: dict, period: str, now: datetime) -> int:
    """Возвращает число сообщений за календарный период."""
    today = now.astimezone(KALININGRAD_TZ).date()
    if period == 'day':
        start = today
    elif period == 'week':
        start = today - timedelta(days=today.weekday())
    elif period == 'month':
        start = today.replace(day=1)
    elif period == 'year':
        start = today.replace(month=1, day=1)
    else:
        return 0

    return sum(
        activity.get((start + timedelta(days=offset)).strftime('%Y-%m-%d'), {}).get('messages', 0)
        for offset in range((today - start).days + 1)
    )


@lru_cache(maxsize=1)
def get_graph_emoji_fonts() -> Tuple[Tuple[str, Any], ...]:
    if not MATPLOTLIB_AVAILABLE:
        return ()
    try:
        from matplotlib import font_manager
        from matplotlib.ft2font import FT2Font
    except ImportError:
        return ()

    preferred_names = (
        'Noto Color Emoji', 'Segoe UI Emoji', 'Apple Color Emoji',
        'Twitter Color Emoji', 'Noto Emoji', 'Symbola',
    )
    fonts = []
    seen_paths = set()
    for preferred in preferred_names:
        for entry in font_manager.fontManager.ttflist:
            if preferred.casefold() not in entry.name.casefold() or entry.fname in seen_paths:
                continue
            try:
                glyphs = FT2Font(entry.fname).get_charmap()
            except (OSError, RuntimeError):
                continue
            fonts.append((entry.fname, glyphs))
            seen_paths.add(entry.fname)
    return tuple(fonts)


def split_graph_text(text: str) -> List[Tuple[str, bool]]:
    """Split text into grapheme-like clusters and mark emoji clusters for font fallback."""
    clusters = []
    current = ''
    join_next = False
    regional_count = 0
    for char in text:
        codepoint = ord(char)
        is_regional = 0x1F1E6 <= codepoint <= 0x1F1FF
        is_modifier = 0x1F3FB <= codepoint <= 0x1F3FF
        is_variation = 0xFE00 <= codepoint <= 0xFE0F or 0xE0100 <= codepoint <= 0xE01EF
        is_combining = unicodedata.category(char).startswith('M')
        if not current or join_next or is_modifier or is_variation or is_combining:
            current += char
        elif char == '\u200d':
            current += char
        elif is_regional and regional_count % 2 == 1:
            current += char
        else:
            clusters.append(current)
            current = char
        join_next = char == '\u200d'
        if is_regional:
            regional_count += 1
        else:
            regional_count = 0
    if current:
        clusters.append(current)

    result = []
    for cluster in clusters:
        is_emoji = any(
            (ord(char) >= 0x1F000 or ord(char) >= 0x2600 and unicodedata.category(char) == 'So')
            and char not in {'\ufe0f', '\ufe0e', '\u200d'}
            for char in cluster
        )
        result.append((cluster, is_emoji))
    return result


def strip_graph_emojis(text: str) -> str:
    """Remove emoji clusters from user-provided graph labels."""
    return ''.join(
        cluster for cluster, is_emoji in split_graph_text(text)
        if not is_emoji and '\u20e3' not in cluster
    )


def add_graph_text(
    fig,
    text: str,
    x: float,
    y: float,
    *,
    fontsize: float,
    color: str,
    fontweight: str = 'normal',
) -> None:
    """Draw text with installed emoji fonts and readable fallback for unsupported emoji."""
    try:
        from matplotlib.font_manager import FontProperties
    except ImportError:
        fig.text(x, y, text, color=color, fontsize=fontsize, fontweight=fontweight)
        return

    default_font = FontProperties(family='DejaVu Sans', weight=fontweight, size=fontsize)
    emoji_fonts = get_graph_emoji_fonts()
    runs = []
    for cluster, is_emoji in split_graph_text(text):
        properties = default_font
        font_key = None
        display = cluster
        if is_emoji:
            codepoints = {
                ord(char) for char in cluster
                if char not in {'\ufe0f', '\ufe0e', '\u200d'}
                and not 0x1F3FB <= ord(char) <= 0x1F3FF
            }
            selected_font = next(
                (
                    path for path, glyphs in emoji_fonts
                    if codepoints and codepoints.issubset(glyphs)
                ),
                None,
            )
            if selected_font:
                properties = FontProperties(fname=selected_font, size=fontsize)
                font_key = selected_font
            else:
                names = [
                    unicodedata.name(char, '').lower().replace(' ', '_')
                    for char in cluster
                    if ord(char) >= 0x1F000 or ord(char) >= 0x2600
                ]
                display = f":{names[0]}:" if names and names[0] else ''
        if not display:
            continue
        if runs and runs[-1][0] == font_key:
            runs[-1] = (font_key, runs[-1][1] + display, properties)
        else:
            runs.append((font_key, display, properties))

    for font_key, display, properties in runs:
        artist = fig.text(
            x, y, display, color=color, fontproperties=properties,
            ha='left', va='center',
        )
        try:
            fig.canvas.draw()
            x += artist.get_window_extent(renderer=fig.canvas.get_renderer()).width / fig.bbox.width
        except (OSError, RuntimeError, ValueError):
            artist.remove()
            if font_key is None:
                raise
            name = next(
                (
                    unicodedata.name(char, '').lower().replace(' ', '_')
                    for char in display
                    if ord(char) >= 0x1F000 or ord(char) >= 0x2600
                ),
                'emoji',
            )
            display = f":{name}:"
            artist = fig.text(
                x, y, display, color=color, fontproperties=default_font,
                ha='left', va='center',
            )
            fig.canvas.draw()
            x += artist.get_window_extent(renderer=fig.canvas.get_renderer()).width / fig.bbox.width


def remove_message_activity(chat_id: int, uid: int, activity_date: str):
    """Убирает удалённое антиспамом сообщение из статистики пользователя."""
    user = storage.get_user(chat_id, uid, use_cache=False)
    day_activity = user.get('activity', {}).get(activity_date)
    if not isinstance(day_activity, dict):
        return

    day_messages = day_activity.get('messages', 0)
    total_messages = user.get('messages_count', 0)
    if day_messages <= 0 and total_messages <= 0:
        return

    if day_messages > 0:
        day_activity['messages'] = day_messages - 1
    if total_messages > 0:
        user['messages_count'] = total_messages - 1

    storage.invalidate_user_cache(chat_id, uid)
    storage.mark_dirty()
    
class MessageStatsMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        if isinstance(event, Message) and event.from_user and not event.from_user.is_bot:
            if event.chat.type in ('group', 'supergroup'):
                await sync_chat_owner(event.chat.id)
            if is_main_chat(event.chat.id, event.message_thread_id):
                updated = storage.update_user_from_message(event)
                if updated:
                    save_activity(event.chat.id, event.from_user.id, 'messages')
                    user = storage.get_user(event.chat.id, event.from_user.id)
                    user['messages_count'] = user.get('messages_count', 0) + 1
                    storage.mark_dirty()

            if await handle_anti_spam(event):
                return None

        return await handler(event, data)


router.message.middleware(MessageStatsMiddleware())


class CallbackFloodMiddleware(BaseMiddleware):
    def __init__(self):
        self.user_callbacks: Dict[Tuple[int, int], List[float]] = defaultdict(list)
        self.last_cleanup = time.time()

    async def __call__(self, handler, event, data):
        if not isinstance(event, CallbackQuery) or not event.from_user:
            return await handler(event, data)

        if event.message and event.message.chat.type in ('group', 'supergroup'):
            chat_id = event.message.chat.id
            if not storage.get_chat_settings(chat_id).get('anti_spam', {}).get('enabled', True):
                return await handler(event, data)
            if await is_anti_spam_admin(chat_id, event.from_user.id):
                return await handler(event, data)

        now = time.time()
        if now - self.last_cleanup >= 300:
            self.user_callbacks = defaultdict(
                list,
                {
                    key: [timestamp for timestamp in timestamps if now - timestamp < 10]
                    for key, timestamps in self.user_callbacks.items()
                    if any(now - timestamp < 10 for timestamp in timestamps)
                }
            )
            self.last_cleanup = now

        chat_id = event.message.chat.id if event.message else 0
        key = (chat_id, event.from_user.id)
        recent = [timestamp for timestamp in self.user_callbacks[key] if now - timestamp < 5]
        if len(recent) >= 10:
            self.user_callbacks[key] = recent
            await event.answer("Слишком частые нажатия. Подождите немного.")
            return None

        recent.append(now)
        self.user_callbacks[key] = recent
        return await handler(event, data)


router.callback_query.middleware(CallbackFloodMiddleware())


ACTIVITY_GRAPH_THEMES = {
    'light_default': ('Стандартная', 'light', '#ffffff', '#f5f6f8', '#5865f2', '#d9defa', '#747f8d', '#23272a'),
    'light_sand': ('Песочная', 'light', '#fbf7f0', '#f3ecdf', '#b77936', '#ead7bd', '#8c7963', '#392f25'),
    'light_sky': ('Небесная', 'light', '#f4f9ff', '#e8f2ff', '#3787e5', '#c8e0fb', '#7188a3', '#20344d'),
    'light_mint': ('Мятная', 'light', '#f2fbf6', '#e5f5ec', '#31a875', '#c4ead6', '#708d7d', '#234536'),
    'light_lavender': ('Лавандовая', 'light', '#f8f5ff', '#eee8fb', '#8d63d8', '#dacdf5', '#827699', '#382c4e'),
    'light_rose': ('Розовая', 'light', '#fff5f7', '#fbe9ed', '#db6685', '#f4ccd7', '#98747f', '#4a2934'),
    'light_red': ('Алый', 'light', '#fff5f5', '#fbe8e8', '#d64545', '#f2c5c5', '#986e6e', '#492525'),
    'dark_default': ('Стандартная', 'dark', '#1a170d', '#211d13', '#ebaa47', '#604e29', '#c5a66f', '#f8fafc'),
    'dark_midnight': ('Полночь', 'dark', '#161821', '#202331', '#8b9cff', '#414a75', '#aeb5d0', '#f4f5ff'),
    'dark_ocean': ('Океан', 'dark', '#101c24', '#172832', '#45c7d5', '#275967', '#91bac2', '#ecfbff'),
    'dark_forest': ('Лесная', 'dark', '#121d18', '#1b2b22', '#62c98b', '#315d43', '#9bb8a5', '#effcf3'),
    'dark_amethyst': ('Аметистовая', 'dark', '#1c1623', '#291f33', '#bd83ed', '#594071', '#b9a7ca', '#fbf4ff'),
    'dark_sunset': ('Закатная', 'dark', '#241817', '#33211f', '#ff9274', '#704039', '#c9a39a', '#fff5f1'),
    'dark_red': ('Багровый', 'dark', '#160606', '#260909', '#ff1a1a', '#801010', '#e08b8b', '#fff0f0'),
}
ACTIVITY_GRAPH_THEME_NAMES = {
    theme_id: theme[0] for theme_id, theme in ACTIVITY_GRAPH_THEMES.items()
}


def create_graph(chat_id: int, uid: int, days: int = 7) -> Optional[BytesIO]:
    if not MATPLOTLIB_AVAILABLE:
        return None
    u = storage.get_user(chat_id, uid)
    act = u.get('activity', {})
    if not act:
        return None
    today = kaliningrad_now().date()
    dates, messages = [], []
    for i in range(days):
        d = today - timedelta(days=days - 1 - i)
        ds = d.strftime('%Y-%m-%d')
        dates.append(d)
        messages.append(max(0, act.get(ds, {}).get('messages', 0)))

    try:
        theme_id = u.get('activity_graph_theme', 'dark_default')
        if not isinstance(theme_id, str):
            theme_id = 'dark_default'
        theme = ACTIVITY_GRAPH_THEMES.get(theme_id, ACTIVITY_GRAPH_THEMES['dark_default'])
        _, _, background, panel, accent, fill, muted, text_color = theme

        fig, ax = plt.subplots(figsize=(10, 4.8), facecolor=background)
        fig.subplots_adjust(left=0.09, right=0.97, top=0.77, bottom=0.19)
        ax.set_facecolor(panel)
        graph_name = strip_graph_emojis(
            html.unescape(get_display_name(chat_id, uid))
        ).strip() or f'ID:{uid}'
        add_graph_text(
            fig,
            f'Активность · {graph_name}',
            0.09, 0.91, color=text_color, fontsize=17, fontweight='bold',
        )
        total_messages = sum(messages)
        active_days = sum(1 for count in messages if count > 0)
        average = total_messages / days if days else 0
        add_graph_text(
            fig,
            f'{total_messages:,} сообщений     ·     '
            f'{active_days}/{days} активных дней     ·     '
            f'{average:.1f} в день',
            0.09, 0.83, color=muted, fontsize=10,
        )

        maximum = max(messages, default=0)
        positions = list(range(len(dates)))
        ax.fill_between(positions, messages, color=fill, alpha=0.55, zorder=2)
        ax.plot(
            positions, messages, color=accent, linewidth=2.7,
            marker='o', markersize=5.5, markerfacecolor=accent,
            markeredgecolor=background, markeredgewidth=1.5, zorder=4,
        )
        ax.scatter(
            [positions[-1]], [messages[-1]], s=58,
            color=accent, edgecolors=background, linewidths=1.5, zorder=5,
        )
        ax.set_xlim(-0.25, max(len(dates) - 0.75, 0.25))
        ax.set_ylim(0, max(maximum * 1.22, 1))
        ax.set_ylabel('Сообщения', color=muted, fontsize=9, labelpad=12)
        ax.yaxis.grid(True, color=fill, alpha=0.65, linewidth=0.8)
        ax.set_axisbelow(True)
        ax.tick_params(axis='y', colors=muted, labelsize=8, length=0, pad=8)
        ax.tick_params(axis='x', colors=muted, labelsize=8, length=0, pad=10)
        ax.set_yticks(plt.MaxNLocator(nbins=4, integer=True).tick_values(0, max(maximum, 1)))
        ax.set_xticks(positions)
        label_step = max(1, (len(dates) + 5) // 6)
        ax.set_xticklabels([
            date.strftime('%d.%m') if index % label_step == 0 or index == len(dates) - 1 else ''
            for index, date in enumerate(dates)
        ])
        for spine in ax.spines.values():
            spine.set_visible(False)
        for index, count in enumerate(messages):
            if count > 0 and (count == maximum or index == len(messages) - 1):
                ax.annotate(
                    f'{count:,}',
                    (positions[index], count),
                    xytext=(0, 6), textcoords='offset points',
                    ha='center', va='bottom', color=text_color,
                    fontsize=8, fontweight='bold',
                )
        buf = BytesIO()
        fig.savefig(buf, format='png', dpi=150, facecolor=background)
        buf.seek(0)
        plt.close(fig)
        return buf
    except Exception:
        logger.exception("Не удалось создать график активности пользователя %s", uid)
        plt.close('all')
        return None


async def get_user_status(uid: int, user_data: dict) -> str:
    """
    Определяет статус пользователя:
    🟢 - онлайн (был активен менее 15 минут назад)
    ⚪ - не в сети (был активен от 15 минут до 1 дня)
    🔴 - давно не в сети (более 1 дня)
    """
    last_seen = user_data.get('last_seen', 0)
    now = time.time()
    diff_seconds = now - last_seen

    if diff_seconds < 900:  # Менее 15 минут
        return '🟢'
    elif diff_seconds < 86400:  # Менее 1 дня
        return '⚪'
    else:  # Более 1 дня
        return '🔴'


# ==================== РП-команды ====================

# Категоризированные обычные команды
RP_FRIENDLY = {
    'обнять': (['обнял(а)', 'крепко обнял(а) в объятия'], '🤗'),
    'поцеловать': (['поцеловал(а)', 'нежно поцеловал(а)'], '💋'),
    'ударить': (['ударил(а)', 'отвесил(а) удар'], '👊'),
    'убить': (['убил(а)', 'отправил(а) на тот свет'], '💀'),
    'пнуть': (['пнул(а)', 'дал(а) пинка'], '🦶'),
    'укусить': (['укусил(а)', 'цапнул(а) зубами'], '🦷'),
    'лизнуть': (['лизнул(а)', 'провёл(а) языком по'], '👅'),
    'погладить': (['погладил(а)', 'ласково погладил(а)'], '🖐️'),
    'ущипнуть': (['ущипнул(а)', 'больно ущипнул(а)'], '👌'),
    'шлёпнуть': (['шлёпнул(а)', 'отвесил(а) шлепок'], '✋'),
    'дать пять': (['дал(а) пять', 'хлопнул(а) по ладони'], '✋'),
    'извиниться': (['извинился(ась) перед', 'повинился(ась) перед'], '🙏'),
    'похвалить': (['похвалил(а)', 'искренне похвалил(а)'], '👏'),
    'поздравить': (['поздравил(а)', 'тепло поздравил(а)'], '🎉'),
    'испугать': (['испугал(а)', 'внезапно напугал(а)'], '😱'),
    'прижать': (['прижал(а)', 'крепко прижал(а) к себе'], '🤜'),
    'потрогать': (['потрогал(а)', 'аккуратно потрогал(а)'], '👆'),
    'пожать руку': (['пожал(а) руку', 'крепко пожал(а) руку'], '🤝'),
    'понюхать': (['понюхал(а)', 'принюхался(лась) к'], '👃'),
    'покормить': (['покормил(а)', 'с ложечки покормил(а)'], '🍽️'),
    'сжечь': (['сжёг(жгла)', 'спалил(а) дотла'], '🔥'),
    'расстрелять': (['расстрелял(а)', 'открыл(а) огонь по'], '🔫'),
    'отравить': (['отравил(а)', 'подсыпал(а) яд', 'коварно отравил(а)'], '☠️'),
    'послать нахуй': (['послал(а) нахуй', 'отправил(а) по известному адресу'], '🖕'),
    'пригласить на чаёк': (['пригласил(а) на чаёк', 'позвал(а) на чашечку чая'], '☕'),
    'выебать': (['выебал(а)', 'оттрахал(а)'], '🔞'),
    'трахнуть': (['трахнул(а)', 'оттрахал(а)'], '🔞'),
    'кастрировать': (['кастрировал(а)', 'лишил(а) достоинства'], '🔪'),
    'отдаться': (['отдался(лась)', 'полностью отдался(лась)'], '💫'),

    # ===== НОВЫЕ КОМАНДЫ =====

    # Дружеские
    'обнять крепко': (['крепко обнял(а)', 'сжал(а) в медвежьих объятиях'], '🫂'),
    'поцеловать в щёку': (['поцеловал(а) в щёку', 'чмокнул(а) в щёчку'], '😊'),
    'поцеловать в лоб': (['поцеловал(а) в лоб', 'нежно поцеловал(а) в лоб'], '😇'),
    'подмигнуть': (['подмигнул(а)', 'хитро подмигнул(а)'], '😉'),
    'помахать': (['помахал(а)', 'радостно помахал(а) рукой'], '👋'),
    'улыбнуться': (['улыбнулся(ась)', 'тепло улыбнулся(ась)'], '😊'),
    'поддержать': (['поддержал(а)', 'оказал(а) поддержку'], '💪'),
    'поблагодарить': (['поблагодарил(а)', 'сказал(а) спасибо'], '🙏'),
    'похлопать': (['похлопал(а)', 'зааплодировал(а)'], '👏'),
    'ободрить': (['ободрил(а)', 'подбодрил(а)'], '🌟'),

    # Агрессивные
    'дать леща': (['дал(а) леща', 'отвесил(а) знатного леща'], '👋'),
    'дать подзатыльник': (['дал(а) подзатыльник', 'отвесил(а) подзатыльник'], '🤕'),
    'задушить': (['задушил(а)', 'сжал(а) горло'], '😤'),
    'придушить': (['придушил(а)', 'чуть придушил(а)'], '🤯'),
    'избить': (['избил(а)', 'жестоко избил(а)'], '👊'),
    'покалечить': (['покалечил(а)', 'нанёс(ла) увечья'], '🤕'),
    'обезглавить': (['обезглавил(а)', 'снёс(ла) голову'], '🗡️'),
    'закопать': (['закопал(а)', 'зарыл(а) в землю'], '⚰️'),
    'утопить': (['утопил(а)', 'утащил(а) на дно'], '🌊'),
    'повесить': (['повесил(а)', 'вздёрнул(а) на виселице'], '🪢'),
    'запытать': (['запытал(а)', 'замучил(а) пытками'], '😈'),
    'растоптать': (['растоптал(а)', 'втоптал(а) в грязь'], '👣'),
    'раздавить': (['раздавил(а)', 'расплющил(а)'], '🔨'),
    'прибить': (['прибил(а)', 'приколотил(а)'], '🔨'),
    'зарезать': (['зарезал(а)', 'пустил(а) под нож'], '🔪'),

    # Шуточные
    'потроллить': (['потроллил(а)', 'знатно потроллил(а)'], '😏'),
    'затроллить': (['затроллил(а)', 'жёстко затроллил(а)'], '🤪'),
    'подколоть': (['подколол(а)', 'вставил(а) шпильку'], '😜'),
    'разыграть': (['разыграл(а)', 'устроил(а) розыгрыш над'], '🎭'),
    'напугать': (['напугал(а)', 'до смерти напугал(а)'], '👻'),
    'рассмешить': (['рассмешил(а)', 'довёл(а) до слёз со смеху'], '😂'),
    'удивить': (['удивил(а)', 'поразил(а)'], '😲'),
    'заинтриговать': (['заинтриговал(а)', 'заинтересовал(а)'], '🤔'),
    'смутить': (['смутил(а)', 'вогнал(а) в краску'], '😳'),
    'покраснеть': (['покраснел(а) от', 'залился(лась) краской от'], '😊'),

    # Забота
    'угостить': (['угостил(а)', 'поделился(лась) угощением с'], '🍕'),
    'накормить': (['накормил(а)', 'сытно накормил(а)'], '🍜'),
    'напоить': (['напоил(а)', 'налил(а) напиток'], '🥤'),
    'согреть': (['согрел(а)', 'укутал(а) в тепло'], '🔥'),
    'укрыть': (['укрыл(а)', 'заботливо укрыл(а) одеялом'], '🛌'),
    'полечить': (['полечил(а)', 'оказал(а) первую помощь'], '💊'),
    'защитить': (['защитил(а)', 'встал(а) на защиту'], '🛡️'),
    'спасти': (['спас(ла)', 'вытащил(а) из беды'], '🦸'),
    'помочь': (['помог(ла)', 'протянул(а) руку помощи'], '🤝'),
    'успокоить': (['успокоил(а)', 'унял(а) тревогу'], '😌'),

    # Странные
    'загипнотизировать': (['загипнотизировал(а)', 'ввёл(а) в транс'], '🌀'),
    'заколдовать': (['заколдовал(а)', 'наложил(а) чары на'], '🪄'),
    'проклясть': (['проклял(а)', 'наложил(а) проклятие на'], '🧙'),
    'благословить': (['благословил(а)', 'даровал(а) благословение'], '✝️'),
    'крестить': (['крестил(а)', 'провёл(а) обряд крещения над'], '⛪'),
    'похитить': (['похитил(а)', 'выкрал(а)'], '🕵️'),
    'украсть': (['украл(а)', 'стащил(а)'], '🥷'),
    'обокрасть': (['обокрал(а)', 'очистил(а) карманы'], '💰'),
    'завербовать': (['завербовал(а)', 'переманил(а) на свою сторону'], '🕴️'),
    'заблокировать': (['заблокировал(а)', 'внёс(ла) в чёрный список'], '🚫'),
}

# Дополнительные VIP команды (ранг 2+)
VIP_RP = {
    # Существующие
    'связать': (['связал(а)', 'скрутил(а)'], '🪢'),
    'заставить': (['заставил(а)', 'принудил(а)'], '⚠️'),
    'повесить': (['повесил(а)', 'вздёрнул(а) на виселице'], '🪢'),
    'уничтожить': (['уничтожил(а)', 'стёр(ла) с лица земли'], '💥'),
    'продать': (['продал(а)', 'сбыл(а) с рук'], '💰'),
    'взорвать': (['взорвал(а)', 'подорвал(а)'], '💣'),
    'засосать': (['засосал(а)', 'впился(лась) поцелуем в'], '💋'),
    'унизить': (['унизил(а)', 'растоптал(а) достоинство'], '😤'),
    'арестовать': (['арестовал(а)', 'заковал(а) в наручники'], '🚔'),
    'наорать': (['наорал(а) на', 'раскричался(лась) на'], '🗣️'),

    # ===== НОВЫЕ VIP КОМАНДЫ =====
    'депортировать': (['депортировал(а)', 'выслал(а) из страны'], '✈️'),
    'казнить': (['казнил(а)', 'привёл(а) приговор в исполнение над'], '⚰️'),
    'пытать': (['пытал(а)', 'устроил(а) допрос с пристрастием'], '🪚'),
    'забанить': (['забанил(а)', 'выписал(а) бан'], '⛔'),
    'разжаловать': (['разжаловал(а)', 'лишил(а) звания'], '📉'),
    'кикнуть': (['кикнул(а)', 'вышвырнул(а) из чата'], '👢'),
    'замутить': (['замутил(а)', 'заткнул(а) на время'], '🔇'),
    'обнулить': (['обнулил(а)', 'стёр(ла) всю статистику'], '0️⃣'),
    'сжечь дотла': (['сжёг(жгла) дотла', 'спалил(а) дотла без остатка'], '🔥'),
    'расстрелять в упор': (['расстрелял(а) в упор', 'влепил(а) пулю в упор'], '🔫'),
    'посадить в тюрьму': (['посадил(а) в тюрьму', 'упрятал(а) за решётку'], '⛓️'),
    'отправить в бан': (['отправил(а) в бан', 'вышвырнул(а) в бан'], '🚫'),
}

# Дополнительные команды для влюблённых (только в браке)
LOVE_RP = {
    # Существующие
    'сделать большой подарок': (['сделал(а) большой подарок для', 'преподнёс(ла) роскошный подарок'], '🎁'),
    'устроить сюрприз': (['устроил(а) сюрприз для', 'приготовил(а) сюрприз для'], '🎊'),
    'пригласить в клуб': (['пригласил(а) в клуб', 'позвал(а) потанцевать в клуб'], '🪩'),
    'поговорить по душам': (['поговорил(а) по душам с', 'открыл(а) душу'], '💬'),
    'сходить в кино': (['сходил(а) в кино с', 'позвал(а) на сеанс в кино'], '🎬'),
    'подарить конфеты': (['подарил(а) конфеты', 'угостил(а) сладостями'], '🍬'),
    'сделать завтрак': (['сделал(а) завтрак для', 'приготовил(а) романтичный завтрак для'], '🍳'),
    'пригласить погулять': (['пригласил(а) погулять', 'позвал(а) на прогулку'], '🚶'),

    # ===== НОВЫЕ LOVE КОМАНДЫ =====
    'признаться в любви': (['признался(ась) в любви', 'открыл(а) сердце и признался(ась) в любви'], '💌'),
    'подарить цветы': (['подарил(а) цветы', 'вручил(а) букет цветов'], '💐'),
    'подарить кольцо': (['подарил(а) кольцо', 'надел(а) кольцо на палец'], '💍'),
    'приготовить ужин': (['приготовил(а) ужин для', 'накрыл(а) романтичный стол для'], '🍝'),
    'устроить свидание': (['устроил(а) свидание с', 'организовал(а) романтичное свидание с'], '🌹'),
    'станцевать с': (['станцевал(а) с', 'закружил(а) в танце'], '💃'),
    'спеть для': (['спел(а) для', 'исполнил(а) серенаду для'], '🎵'),
    'обнять нежно': (['нежно обнял(а)', 'бережно заключил(а) в объятия'], '💕'),
    'поцеловать страстно': (['страстно поцеловал(а)', 'впился(лась) в страстном поцелуе'], '💋'),
    'приласкать': (['приласкал(а)', 'нежно приласкал(а)'], '🥰'),
    'заботиться о': (['заботится о', 'трепетно заботится о'], '🤱'),
    'боготворить': (['боготворит', 'не может надышаться на'], '🙇'),
    'носить на руках': (['носит на руках', 'бережно носит на руках'], '👰'),
    'сделать массаж': (['сделал(а) массаж', 'расслабляюще помассировал(а)'], '💆'),
    'подарить сердце': (['подарил(а) сердце', 'отдал(а) своё сердце'], '❤️'),
    'украсть сердечко': (['украл(а) сердечко у', 'похитил(а) сердце у'], '💘'),
    'написать стих': (['написал(а) стих для', 'сочинил(а) стихотворение для'], '📝'),
    'посвятить песню': (['посвятил(а) песню', 'написал(а) песню в честь'], '🎶'),
}

# Объединяем все команды
def ensure_rp_phrase_variants(commands: dict, modifiers: tuple) -> dict:
    expanded = {}
    for action, (phrases, emoji) in commands.items():
        variants = list(dict.fromkeys(phrases))
        for modifier in modifiers:
            for phrase in phrases:
                variant = f"{modifier} {phrase}"
                if variant not in variants:
                    variants.append(variant)
                if len(variants) >= 10:
                    break
            if len(variants) >= 10:
                break
        expanded[action] = (variants, emoji)
    return expanded


RP_FRIENDLY = ensure_rp_phrase_variants(RP_FRIENDLY, (
    'крепко', 'нежно', 'радостно', 'бережно', 'искренне',
    'с улыбкой', 'от души', 'неожиданно', 'энергично', 'с азартом',
    'решительно', 'без лишних слов',
))
VIP_RP = ensure_rp_phrase_variants(VIP_RP, (
    'решительно', 'с размахом', 'без промедления', 'эффектно',
    'грозно', 'внезапно', 'с важным видом', 'уверенно',
    'демонстративно', 'стремительно', 'хладнокровно', 'во всю силу',
))
LOVE_RP = ensure_rp_phrase_variants(LOVE_RP, (
    'нежно', 'бережно', 'с любовью', 'с улыбкой', 'трепетно',
    'романтично', 'от всего сердца', 'с особой заботой',
    'ласково', 'искренне', 'по-особенному', 'с нежностью',
))

RP = RP_FRIENDLY
ALL_RP = {**RP, **VIP_RP, **LOVE_RP}

REPUTATION_WORDS = frozenset({
    '+', 'плюс', 'спасибо', 'спс', 'пасиб', 'благодарю',
    'жиза', 'красава', 'красавчик', 'красавица', 'респект', 'респектую',
    'уважение', 'лайк', 'like', 'топ', 'молодец', 'молодчина',
    'умница', 'умничка', 'based', 'base', 'огонь', 'круто', 'класс',
    'зачёт', 'зачет', 'имба', 'легенда', 'лучший', 'лучшая',
    'так держать', 'поддерживаю', 'nice', 'great', 'awesome',
    'заебись', 'охуенно', 'пиздато', 'ебать круто',
    'well done', 'good job', 'respect', 'thanks', 'thank you', 'thx',
    '👍', '👍🏻', '👍🏼', '👍🏽', '👍🏾', '👍🏿', '🔥', '💯', '✅',
    '🫡', '👏', '🙌', '🤝', '💪', '❤️', '❤', '💙', '💚', '✨', '🌟',
})

REPUTATION_REMOVE_WORDS = frozenset({
    '-', 'минус', 'минусую', 'минус реп', 'минус репутация',
    'дизлайк', 'диз', 'не лайк', 'не респект', 'не одобряю',
    'осуждаю', 'не согласен', 'не согласна', 'не понравилось',
    'не зашло', 'так себе', 'слабовато', 'мимо', 'не круто',
    'плохо', 'плохой', 'плохая', 'ужас', 'отстой', 'фу', 'кринж',
    'стыдно', 'позор', 'провал', 'фейл', 'разочаровал', 'разочаровала',
    'хуйня', 'говно', 'дерьмо', 'говнище', 'пиздец',
    'dislike', 'downvote', 'down vote', 'bad', 'nope', 'boo',
    'worst', 'terrible', 'awful', 'hate', 'not cool', 'not good',
    'not impressed', 'disappointed', 'disappointing', 'cringe',
    'lame', 'fail', 'failed', 'failure', 'trash', 'garbage', 'sucks',
    'bad job', 'weak', 'meh', 'yikes', 'shame',
    '👎', '👎🏻', '👎🏼', '👎🏽', '👎🏾', '👎🏿',
    '❌', '🚫', '⛔', '💩', '🤮', '😡', '🤬', '🙄', '😒',
    '😠', '🖕', '🤡', '😐', '😕', '😟', '😞', '😔', '😣',
    '😖', '😫', '😩', '🤢', '🤨', '😬', '🫤', '🗑️', '🚮', '💔',
})


def is_reputation_message(text: str) -> bool:
    normalized = ' '.join(text.casefold().replace('\ufe0f', '').split())
    return normalized in REPUTATION_WORDS or (text.startswith('+') and len(text) <= 3)


def is_reputation_removal_message(text: str) -> bool:
    normalized = ' '.join(text.casefold().replace('\ufe0f', '').split())
    return normalized in REPUTATION_REMOVE_WORDS


async def rp_handler(msg: Message) -> bool:
    if not msg.text:
        return False
    raw_text = strip_command_prefix(msg.text, msg.chat.id)
    text = raw_text.lower()

    for act in sorted(ALL_RP.keys(), key=len, reverse=True):
        if text == act or text.startswith(act + ' '):
            target_arg = raw_text[len(act):].strip()
            tid = None

            # ПРИОРИТЕТ: ответ на сообщение
            if msg.reply_to_message and msg.reply_to_message.from_user:
                tid = msg.reply_to_message.from_user.id
            elif target_arg:
                # Если есть аргументы, пробуем найти пользователя
                tid = await get_target(msg, target_arg.split(maxsplit=1)[0])

            if not tid:
                return False

            if act in VIP_RP and storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) < VIP_RP_RANK:
                await msg.answer(f"❌ Нужен ранг {VIP_RP_RANK}+")
                return True
            if act in LOVE_RP and not storage.get_user(msg.chat.id, msg.from_user.id).get('marriage_partner'):
                await msg.answer("❌ Только в браке")
                return True
            if tid == msg.from_user.id and act not in ['извиниться', 'поздравить']:
                await msg.answer("❌ Нельзя с собой")
                return True

            action_text = random.choice(ALL_RP[act][0])
            emoji = ALL_RP[act][1]
            save_activity(msg.chat.id, msg.from_user.id, 'commands')

            await msg.answer(
                f"{emoji} {mention(msg.chat.id, msg.from_user)} {action_text} {mention(msg.chat.id, tid)}",
                disable_web_page_preview=True
            )
            return True

    return False


# ==================== Команды ====================

COMMANDS = {
    'кто я': 'who_am_i',
    'профиль': 'who_am_i',
    'кто ты': 'who_are_you',
    'кто админ': 'who_admin',
    'ранг': 'cmd_rank',
    'ранги': 'cmd_ranks_list',
    'название ранга': 'cmd_rank_rename',
    'переранг': 'cmd_rank_rename',
    'ид': 'cmd_id',
    'топ': 'cmd_top',
    'статистика чата': 'cmd_chat_stats',
    'статистика': 'cmd_stats',
    'мут': 'cmd_mute',
    'размут': 'cmd_unmute',
    'бан': 'cmd_ban',
    'разбан': 'cmd_unban',
    '-мут': 'cmd_unmute',
    '-бан': 'cmd_unban',
    'пред': 'cmd_warn',
    'варн': 'cmd_warn',
    'warn': 'cmd_warn',
    'преды': 'show_warnings',
    'варны': 'show_warnings',
    'warns': 'show_warnings',
    'мутлист': 'cmd_mute_list',
    'муты': 'cmd_mute_list',
    'мутылист': 'cmd_mute_list',
    'список мутов': 'cmd_mute_list',
    'mutelist': 'cmd_mute_list',
    'mutes': 'cmd_mute_list',
    'банлист': 'cmd_ban_list',
    'баны': 'cmd_ban_list',
    'список банов': 'cmd_ban_list',
    'banlist': 'cmd_ban_list',
    'bans': 'cmd_ban_list',
    'варнлист': 'cmd_warn_list',
    'предлист': 'cmd_warn_list',
    'варнылист': 'cmd_warn_list',
    'предупреждения': 'cmd_warn_list',
    'список предупреждений': 'cmd_warn_list',
    'warnlist': 'cmd_warn_list',
    'warninglist': 'cmd_warn_list',
    'warningslist': 'cmd_warn_list',
    'снятьпред': 'cmd_unwarn',
    'снятьварн': 'cmd_unwarn',
    '-пред': 'cmd_unwarn',
    '-варн': 'cmd_unwarn',
    'unwarn': 'cmd_unwarn',
    '-смс': 'cmd_del',
    'пин': 'cmd_pin',
    'очистить': 'cmd_purge',
    'повысить': 'cmd_promote',
    'понизить': 'cmd_demote',
    'наградить': 'cmd_give_award',
    'снять награду': 'cmd_rem_award',
    'мои награды': 'cmd_my_awards',
    'топ наград': 'cmd_top_awards',
    'брак': 'cmd_marry',
    'принять брак': 'cmd_accept_marry',
    'отклонить брак': 'cmd_reject_marry',
    'развод': 'cmd_divorce',
    'браки': 'cmd_marriages_list',
    'добавить фразу': 'cmd_add_phrase',
    'удалить фразу': 'cmd_del_phrase',
    'фразы': 'cmd_list_phrases',
    'статистика фраз': 'cmd_phrase_stats',
    'показать фразу': 'cmd_phrase_show',
    'приветствие': 'cmd_welcome',
    'прощание': 'cmd_farewell',
    'прощание текст': 'cmd_farewell',
    'правила': 'cmd_rules',
    'добавитьправило': 'cmd_add_rule',
    'очиститьправила': 'cmd_clear_rules',
    'игры': 'cmd_games_menu',
    'игра': 'cmd_games_menu',
    'game': 'cmd_games_menu',
    'играть': 'cmd_games_menu',
    'кнб': 'cmd_rps_menu',
    'кнб бот': 'cmd_rps_with_bot',
    'камень': 'cmd_rps_choice',
    'ножницы': 'cmd_rps_choice',
    'бумага': 'cmd_rps_choice',
    'крестики нолики': 'cmd_ttt_menu',
    'ttt': 'cmd_ttt_menu',
    'погода': 'cmd_weather',
    'п': 'cmd_weather_short',
    'время': 'cmd_time',
    'который час': 'cmd_time',
    'сколько времени': 'cmd_time',
    'тема графика': 'cmd_activity_graph_theme',
    'график тема': 'cmd_activity_graph_theme',
    'шутка': 'cmd_random_joke',
    'шиперим': 'cmd_ship',
    'шипперим': 'cmd_ship',
    'моя статья': 'cmd_my_article',
    'опрос': 'cmd_poll',
    'валера': 'cmd_iris',
    'валера вопрос': 'cmd_iris',
    'валерка': 'cmd_iris',
    'валерианыч': 'cmd_iris',
    'репорт': 'cmd_report',
    'ник': 'cmd_nick',
    'погоняло': 'cmd_pogonialo',
    'антимодерация': 'cmd_anti_moderation',
    'антиспам': 'cmd_anti_spam',
    'пинг': 'cmd_ping_check',
    'ping': 'cmd_ping_check',
    'пик выкл': 'cmd_pic_toggle',
    'пик вкл': 'cmd_pic_toggle',
    'pic off': 'cmd_pic_toggle',
    'pic on': 'cmd_pic_toggle',
    'общий сбор': 'cmd_ping',
    'бэкап': 'cmd_backup',
    'восстановить': 'cmd_restore',
    'дк': 'cmd_dk_set',
    '+дк': 'cmd_dk_enable',
    '-дк': 'cmd_dk_disable',
    '+лдк': 'cmd_ldk_add',
    '-лдк': 'cmd_ldk_rem',
    'дкм': 'cmd_dk_menu',
    'перед': 'cmd_forward',
    'помощь': 'cmd_help',
    'help': 'cmd_help',
    'инфо': 'cmd_help',
    'info': 'cmd_help',
    'префикс': 'cmd_prefix',
    'wordle': 'cmd_wordle',
    'вордле': 'cmd_wordle',
    'вордл': 'cmd_wordle',
    'слово': 'cmd_wordle',
    'угадай слово': 'cmd_wordle',
}

COMMAND_ERROR_HINTS = {
    'кто я': '!кто я',
    'кто ты': '!кто ты @user',
    'кто админ': '!кто админ',
    'мут': '!мут @user 30м флуд',
    'размут': '!размут @user',
    'бан': '!бан @user реклама',
    'разбан': '!разбан @user',
    'пред': '!пред @user 7 флуд',
    'варн': '!пред @user 7 флуд',
    'снятьпред': '!снятьпред @user',
    'погоняло': '!погоняло @user Крутой',
    'топ': '!топ день',
    'статистика': '!статистика',
    'помощь': '!помощь',
    'погода': '!погода',
    'опрос': '!опрос Вопрос? | Да | Нет',
    'брак': '!брак @user',
    'награда': '!наградить @user Награда',
    'пинг': '!пинг',
    'моя статья': '!моя статья',
    'мутлист': '!мутлист',
    'банлист': '!банлист',
    'варнлист': '!варнлист',
}


def get_command_example(cmd_name: str) -> str:
    return COMMAND_ERROR_HINTS.get(cmd_name, COMMAND_ERROR_HINTS.get(cmd_name.lower(), '!помощь'))


async def report_command_error(msg: Message, cmd_name: str, title: str, message: str, example: str = ""):
    error_msg = await msg.answer(
        ui_error(title, message, example or get_command_example(cmd_name), message_is_html=True),
        disable_web_page_preview=True,
    )
    asyncio.create_task(delete_message_after(error_msg, 4))


async def delete_message_after(msg: Message, delay: int):
    await asyncio.sleep(delay)
    try:
        await msg.delete()
    except Exception:
        logger.debug("Не удалось удалить временное сообщение", exc_info=True)


def get_command_prefix(chat_id: int) -> str:
    """Возвращает префикс команд для чата; пустая строка означает команды без префикса."""
    prefix = storage.get_chat_settings(chat_id).get('command_prefix', '!')
    return prefix if isinstance(prefix, str) else '!'


def strip_command_prefix(text: str, chat_id: Optional[int] = None) -> str:
    """Удаляет настроенный префикс или совместимый префикс известной команды."""
    text = text.strip()
    prefix = get_command_prefix(chat_id) if chat_id is not None else '!'
    if prefix and text.startswith(prefix):
        return text[len(prefix):].lstrip()

    if not prefix:
        if match_command(text)[0] is not None:
            return text
        prefix_length = 0
        for char in text:
            if not unicodedata.category(char).startswith(('P', 'S')):
                break
            prefix_length += 1
            candidate = text[prefix_length:].lstrip()
            command_name = match_command(candidate)[0]
            if command_name is not None or any(
                candidate.casefold() == action
                or candidate.casefold().startswith(action + ' ')
                for action in ALL_RP
            ):
                return candidate
    return text


def match_command(text: str) -> tuple:
    """Проверяет, начинается ли текст с одной из команд"""
    text_lower = text.lower().strip()

    for cmd in sorted(COMMANDS.keys(), key=len, reverse=True):
        if text_lower == cmd or text_lower.startswith(cmd + ' '):
            return cmd, text[len(cmd):].strip()

    return None, None


def _quote_find_font(bold: bool, size: int):
    """На Linux отдаёт приоритет шрифтам с кириллицей и безопасным fallback."""
    candidates = [
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSansCondensed-Bold.ttf" if bold else "/usr/share/fonts/truetype/dejavu/DejaVuSansCondensed.ttf",
        "/usr/share/fonts/truetype/liberation2/LiberationSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf",
        "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf" if bold else "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
        "DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf",
        "LiberationSans-Bold.ttf" if bold else "LiberationSans-Regular.ttf",
        "C:/Windows/Fonts/segoeuib.ttf" if bold else "C:/Windows/Fonts/segoeui.ttf",
        "C:/Windows/Fonts/arialbd.ttf" if bold else "C:/Windows/Fonts/arial.ttf",
    ]

    for path in candidates:
        try:
            font = ImageFont.truetype(path, size)
            for sample in ("Привет", "Тест", "Hello", "Привет мир"):
                try:
                    bbox = font.getbbox(sample)
                    if bbox is not None and bbox[2] > bbox[0]:
                        return font
                except Exception:
                    continue
        except Exception:
            continue

    return ImageFont.load_default()


def _quote_wrap_px(draw, text: str, font, max_width: float) -> List[str]:
    """Переносит текст по словам, укладываясь в max_width пикселей (с разбивкой очень длинных слов)."""
    words = text.split()
    if not words:
        return ['']

    def hard_break(word):
        parts, cur = [], ''
        for ch in word:
            trial = cur + ch
            if draw.textlength(trial, font=font) <= max_width or not cur:
                cur = trial
            else:
                parts.append(cur)
                cur = ch
        if cur:
            parts.append(cur)
        return parts

    lines = []
    current = words[0]
    if draw.textlength(current, font=font) > max_width:
        broken = hard_break(current)
        lines.extend(broken[:-1])
        current = broken[-1]

    for w in words[1:]:
        trial = current + ' ' + w
        if draw.textlength(trial, font=font) <= max_width:
            current = trial
        else:
            lines.append(current)
            if draw.textlength(w, font=font) > max_width:
                broken = hard_break(w)
                lines.extend(broken[:-1])
                current = broken[-1]
            else:
                current = w
    lines.append(current)
    return lines


def _quote_bezier(p0, p1, p2, steps: int):
    pts = []
    for i in range(steps + 1):
        t = i / steps
        x = (1 - t) ** 2 * p0[0] + 2 * (1 - t) * t * p1[0] + t ** 2 * p2[0]
        y = (1 - t) ** 2 * p0[1] + 2 * (1 - t) * t * p1[1] + t ** 2 * p2[1]
        pts.append((x, y))
    return pts


@router.message(Command('start'))
async def cmd_start(msg: Message):
    storage.update_user_from_message(msg)
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    await msg.answer(
        "🐻 <b>Добро пожаловать в Обкуренный Валера!</b>\n\n"
        "Я помогаю с модерацией, статистикой, играми и шутками.\n\n"
        "📌 Основные команды:\n"
        "<code>!помощь</code> — все команды\n"
        "<code>!кто я</code> — профиль\n"
        "<code>!опрос</code> — быстрый опрос\n"
        "<code>!погода</code> — погода\n"
        "<code>!время [регион]</code> — дата и время в регионе\n\n"
        "Напишите <code>!помощь</code>, чтобы посмотреть всё меню.")


PIC_TARGET_GROUP_USERNAME = 'Weltobruhsuperchat'
PIC_TARGET_GROUP_URL = 'https://t.me/Weltobruhsuperchat'

PIC_SHUFFLE_PHRASES = [
    "🎲 Перемешиваем колоду...",
    "🌀 Проверяем шансы...",
    "🃏 Смотрим, что выпадет сегодня...",
    "✨ Подготавливаем разворот...",
    "🔮 Снова врубаем магию...",
]

PIC_DRAW_PHRASES = [
    "📦 Вытягиваем карту...",
    "🎯 Крепко держим и тянем...",
    "🫧 Проводим последнюю проверку...",
    "💫 Открываем результат...",
    "🎭 Момент истины уже близко...",
]

PIC_APOLOGY_MESSAGES = [
    "😔 Извините, в этом чате пока нет этого бота. Но он есть в другой группе: <a href='{url}'>{name}</a>.",
    "💬 Простите, здесь бот не подключён. Его можно найти в другой группе: <a href='{url}'>{name}</a>.",
    "🙇‍♂️ В этом чате бота нет, но он работает в другой группе: <a href='{url}'>{name}</a>.",
    "🫡 Извините за неудобство — в этом чате бот отсутствует. Он доступен здесь: <a href='{url}'>{name}</a>.",
]


def get_pic_shuffle_phrase() -> str:
    return random.choice(PIC_SHUFFLE_PHRASES)


def get_pic_draw_phrase() -> str:
    return random.choice(PIC_DRAW_PHRASES)


def get_pic_apology_message() -> str:
    return random.choice(PIC_APOLOGY_MESSAGES).format(
        url=PIC_TARGET_GROUP_URL,
        name=PIC_TARGET_GROUP_USERNAME,
    )


def is_pic_disabled_by_default(chat_id: int, chat_username: Optional[str]) -> bool:
    username = (chat_username or '').lstrip('@').casefold()
    return str(chat_id) in PIC_DISABLED_CHATS or username in PIC_DISABLED_CHATS


@router.message(Command('pic'))
async def cmd_pic(msg: Message):
    settings = storage.get_chat_settings(msg.chat.id)
    pic_enabled = settings.get(
        'pic_enabled',
        not is_pic_disabled_by_default(msg.chat.id, msg.chat.username)
    )
    if not pic_enabled:
        return

    shuffle_phrase = get_pic_shuffle_phrase()
    draw_phrase = get_pic_draw_phrase()

    thinking_msg = await msg.answer(shuffle_phrase, parse_mode='HTML')
    await asyncio.sleep(0.8)
    await thinking_msg.edit_text(draw_phrase, parse_mode='HTML')
    await asyncio.sleep(0.8)

    await thinking_msg.delete()
    await asyncio.sleep(0.3)

    await msg.answer(get_pic_apology_message(), parse_mode='HTML', disable_web_page_preview=False)


async def cmd_pic_toggle(msg: Message, cmd_name: str):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return await msg.answer("❌ Недостаточно прав! Требуется ранг 5+")

    enabled = cmd_name in ('пик вкл', 'pic on')
    settings = storage.get_chat_settings(msg.chat.id)
    settings['pic_enabled'] = enabled
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"✅ Ответы на /pic в этом чате {'включены' if enabled else 'отключены'}.")


async def cmd_prefix(msg: Message, args: str = ''):
    if not check_access(msg.from_user.id, msg.chat.id, 'префикс', 5):
        return await msg.answer("❌ Настроить префикс может только участник с рангом 5+")

    value = args.strip()
    settings = storage.get_chat_settings(msg.chat.id)
    if not value or value.casefold() in {'инфо', 'info'}:
        prefix = get_command_prefix(msg.chat.id)
        current = html.escape(prefix, quote=False) if prefix else 'отключён'
        return await msg.answer(
            f"⚙️ <b>Префикс команд</b>\nТекущий: <code>{current}</code>\n\n"
            "Изменить: <code>!префикс !</code> или <code>!префикс .</code>\n"
            "Отключить: <code>!префикс откл</code> — команды будут работать без префикса."
        )

    if value.casefold() in {'откл', 'отключить', 'выкл', 'off', 'none'}:
        new_prefix = ''
    else:
        if len(value) > 16 or any(
            char.isspace() or unicodedata.category(char).startswith('C')
            for char in value
        ):
            return await msg.answer(
                "❌ Префикс должен состоять из 1–16 знаков без пробелов и управляющих символов. "
                "Для команд без префикса укажите <code>откл</code>."
            )
        new_prefix = value

    settings['command_prefix'] = new_prefix
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    shown_prefix = html.escape(new_prefix, quote=False) if new_prefix else 'отключён'
    await msg.answer(
        f"✅ Префикс команд в этом чате: <code>{shown_prefix}</code>."
        + ("" if new_prefix else " Теперь известные команды можно отправлять без префикса.")
    )


# ==================== Справка (блоки + кнопки) ====================

HELP_SECTIONS = {
    'info': ("📊 Инфо и статистика",
             "📊 <b>Инфо и статистика</b>\n"
             f"{UI_LINE}\n\n"
             "👤 <b>Профиль</b>\n"
             "  <code>!кто я</code> / <code>!профиль</code> — ваш профиль (<code>/profile</code>)\n"
             "  <code>!кто ты @user</code> — информация о пользователе\n"
             "  <code>!кто админ</code> — администрация и ранги чата\n"
             "  <code>!ид</code> — ваш ID и ID чата; ответом — ID автора сообщения\n\n"
             "🏅 <b>Ранги и статистика</b>\n"
             "  <code>!ранг</code> — ваш ранг; <code>!ранги</code> — список рангов\n"
             "  <code>!топ [день/неделя/месяц/год/всё]</code> — рейтинг активности (<code>/top</code>)\n"
             "  <code>!статистика</code> — ваша статистика\n"
             "  <code>!статистика чата</code> — статистика чата\n"
             "  <code>!топ наград</code> — рейтинг наград\n\n"
             "🎨 <b>Оформление</b>\n"
             "  <code>!тема графика</code> — выбрать светлую или тёмную тему графика активности профиля\n\n"
             "🎲 <b>Разное</b>\n"
             "  <code>!опрос Вопрос? | Да | Нет</code> — создать опрос\n"
             "  <code>!погода</code> / <code>!п</code> — погода (<code>/weather</code>)\n"
             "  <code>!время [город или регион]</code> / <code>!который час [город или регион]</code> — дата и время (по умолчанию Калининград; поддерживаются города по всему миру, например <code>!время Токио</code>)\n"
             "  <code>!шутка</code> — случайная шутка\n"
             "  <code>!шиперим</code> — случайно выбрать пару из знакомых боту участников чата\n"
             "  <code>!моя статья</code> — случайная статья УК РФ в шуточном приговоре\n"
             "  <code>!валера</code> / <code>!валерка</code> / <code>!валерианыч</code> — интерактивное меню и функции Валеры\n"
             "  <code>1 доллар</code> — показать эквивалент суммы в рублях, евро и других валютах\n"
             "  <code>!пинг</code> / <code>!ping</code> — задержка бота (<code>/ping</code>)\n\n"
             "⚙️ <b>Префикс команд</b>\n"
             "  <code>!префикс</code> — показать текущий префикс\n"
             "  <code>!префикс .</code> — установить свой префикс (1–16 знаков)\n"
             "  <code>!префикс откл</code> — вызывать известные команды без префикса; настройка доступна рангу 5+\n\n"
             "🏷️ <b>Ник и тег</b>\n"
             "  <code>!ник Имя</code> — изменить своё отображаемое имя; ответом или <code>!ник @user Имя</code> — изменить ник участника (администратору)\n"
             "  <code>!погоняло Текст</code> — установить себе тег; <code>!погоняло сбросить</code> — убрать\n"
             "  Для справки: <code>!помощь</code> / <code>!help</code> / <code>!инфо</code> / <code>!info</code>"),
    'moderation': ("🛡️ Модерация",
             "🛡️ <b>Модерация</b>\n"
             f"{UI_LINE}\n\n"
             "🔇 <b>Мут и бан</b>\n"
             "  <code>!мут @user 30м причина</code> — ограничить участника; можно ответом или кликабельным упоминанием имени без @username\n"
             "  <code>!мут @user навсегда причина</code> — бессрочный мут; временный срок — не более 1 года\n"
             "  <code>!размут @user</code> / <code>!-мут @user</code> — снять мут\n"
             "  <code>!бан @user причина</code> — заблокировать; чтобы забанить канал, ответьте на его сообщение командой <code>!бан причина</code>\n"
             "  <code>!разбан @user</code> / <code>!-бан @user</code> — снять бан; канал разбанивается ответом на его сообщение командой <code>!разбан</code>\n\n"
             "⚠️ <b>Предупреждения</b>\n"
             "  <code>!пред @user причина</code> / <code>!варн</code> / <code>!warn</code> — выдать предупреждение\n"
             "  <code>!преды @user</code> / <code>!варны</code> / <code>!warns</code> — посмотреть предупреждения\n"
             "  <code>!варнлист</code> / <code>!предлист</code> / <code>!варнылист</code> / <code>!предупреждения</code> / <code>!список предупреждений</code> / <code>!warnlist</code> / <code>!warninglist</code> / <code>!warningslist</code> — все активные предупреждения\n"
             "  <code>!снятьпред @user [номер]</code> / <code>!снятьварн</code> / <code>!-пред</code> / <code>!-варн</code> / <code>!unwarn</code> — снять предупреждение\n\n"
             "🔎 <b>Списки наказаний</b>\n"
             "  <code>!мутлист</code> / <code>!муты</code> / <code>!мутылист</code> / <code>!список мутов</code> / <code>!mutelist</code> / <code>!mutes</code> — активные муты\n"
             "  <code>!банлист</code> / <code>!баны</code> / <code>!список банов</code> / <code>!banlist</code> / <code>!bans</code> — действующие баны из списка бота\n\n"
             "🧹 <b>Сообщения</b>\n"
             "  <code>!-смс</code> — удалить сообщение (ответом)\n"
             "  <code>!очистить</code> — очистить сообщения\n"
             "  <code>!пин</code> — закрепить сообщение (ответом)\n\n"
             "🪜 <b>Ранги</b>\n"
             "  <code>!повысить @user [ранг]</code> / <code>!понизить @user [ранг]</code> — изменить ранг\n"
             "  Владелец Telegram-чата автоматически получает ранг 5; его ранг нельзя изменить этими командами.\n\n"
             "📝 <b>Ещё</b>\n"
             "  <code>!репорт текст</code> — отправить жалобу\n"
             "  <code>!погоняло @user Текст</code> — изменить тег другого участника\n\n"
             "Для мута и бана нужны права администратора Telegram и соответствующий ранг бота. Остальные команды требуют указанный для них ранг; ответ на сообщение часто заменяет <code>@user</code>."),
    'awards': ("🏆 Награды и браки",
             "🏆 <b>Награды и браки</b>\n"
             f"{UI_LINE}\n\n"
             "🎖️ <b>Награды</b>\n"
             "  <code>!наградить @user Название</code> — выдать награду\n"
             "  <code>!снять награду @user</code> — снять награду\n"
             "  <code>!мои награды</code> — ваши награды\n"
             "  <code>!топ наград</code> — рейтинг наград\n\n"
             "💍 <b>Браки</b>\n"
             "  <code>!брак @user</code> — предложение\n"
             "  <code>!принять брак</code> / <code>!отклонить брак</code> — ответить на предложение\n"
             "  <code>!развод</code> — расторгнуть\n"
             "  <code>!браки</code> — список пар"),
    'phrases': ("💬 Фразы и правила",
             "💬 <b>Фразы, приветствия и правила</b>\n"
             f"{UI_LINE}\n\n"
             "🗨️ <b>Фразы</b>\n"
             "  <code>!добавить фразу [-any] слово ответ</code> — добавить автоответ\n"
             "  <code>!удалить фразу слово [ответ]</code> — удалить фразу\n"
             "  <code>!фразы</code> — список фраз\n"
             "  <code>!показать фразу слово</code> — ответы на триггер\n"
             "  <code>!статистика фраз</code> — частота использования\n\n"
             "👋 <b>Приветствие и прощание</b>\n"
             "  <code>!приветствие вкл/выкл</code>, <code>!приветствие текст ...</code> или <code>!приветствие картинка URL</code>\n"
             "  <code>!прощание вкл/выкл</code> / <code>!прощание текст ...</code> / <code>!прощание картинка URL</code> — настроить прощание\n\n"
             "📜 <b>Правила</b>\n"
             "  <code>!правила</code> — посмотреть правила\n"
             "  <code>!добавитьправило текст</code> — добавить правило\n"
             "  <code>!очиститьправила</code> — удалить правила"),
    'games': ("🎮 Игры, РП и репутация",
             "🎮 <b>Игры, РП и репутация</b>\n"
             f"{UI_LINE}\n\n"
             "🕹️ <b>Игры</b>\n"
             "  <code>!игры</code> / <code>!игра</code> / <code>!играть</code> / <code>!game</code> — меню игр (<code>/game</code>)\n"
             "  <code>!кнб</code> — камень-ножницы-бумага; <code>!кнб бот</code> — против бота\n"
             "  <code>!камень</code> / <code>!ножницы</code> / <code>!бумага</code> — ход в КНБ\n"
             "  <code>!крестики нолики</code> / <code>!ttt</code> — крестики-нолики\n"
             "  <code>!wordle</code> / <code>!вордле</code> / <code>!вордл</code> / <code>!слово</code> / <code>!угадай слово</code> — Wordle\n"
             "  В Wordle отвечайте словом на сообщение игры; <code>!wordle exit</code> — выйти, <code>!wordle stop</code> — остановить.\n\n"
             "🎭 <b>РП</b>\n"
             "  <code>!рп</code> — меню РП-команд\n"
             "  Используйте команду РП с <code>@user</code> или ответом на его сообщение.\n\n"
             "⭐ <b>Репутация</b>\n"
             "  Ответьте на сообщение символом <code>+</code> или словом/эмодзи одобрения; для снятия — <code>-</code> или дизлайк.\n"
             "  Действуют лимиты на выдачу репутации; некоторые действия доступны с рангом или в браке."),
    'settings': ("⚙️ Настройки и ДК",
             "⚙️ <b>Настройки и ДК</b>\n"
             f"{UI_LINE}\n\n"
             "🛠️ <b>Общие настройки</b>\n"
             "  <code>!антимодерация</code> — включить/выключить анти-модерацию\n"
             "  <code>!антиспам</code> — включить/выключить анти-спам\n\n"
             "🔐 <b>Доступ к командам (ДК)</b>\n"
             "  <code>!дк команда 0-5/откл</code> — задать уровень команды\n"
             "  <code>!дк инфо</code> — показать текущие настройки\n"
             "  <code>!+дк команда</code> / <code>!-дк команда</code> — разрешить/отключить команду\n"
             "  <code>!+лдк команда @user</code> / <code>!-лдк команда @user</code> — выдать/отозвать личный доступ\n"
             "  <code>!дкм</code> — открыть меню настроек ДК\n\n"
             "Менять настройки ДК могут пользователи с рангом 5."),
    'admin': ("🛠️ Админ",
             "🛠️ <b>Админ</b>\n"
             f"{UI_LINE}\n\n"
             "📢 <b>Вызов и проверка</b>\n"
             "  <code>!общий сбор</code> — упомянуть администраторов (ранг 5)\n"
             "  <code>!пинг</code> / <code>!ping</code> — проверить задержку; также <code>/ping</code>\n\n"
             "💾 <b>Данные</b>\n"
             "  <code>!бэкап</code> — создать резервную копию\n"
             "  <code>!восстановить</code> — восстановить последнюю копию\n\n"
             "👑 <b>Управление</b>\n"
             "  <code>!перед @user</code> — переслать сообщение в ответ на него\n"
             "  <code>!название ранга 0-5 Название</code> / <code>!переранг 0-5 Название</code> — переименовать ранг\n\n"
             "🔎 <b>Служебные команды</b>\n"
             "  <code>/start</code> — приветствие и краткая справка\n"
             "  <code>/pic</code> — сообщение о карточном боте\n"
             "  <code>!пик выкл</code> / <code>!pic off</code> — отключить ответы на /pic в этом чате\n"
             "  <code>!пик вкл</code> / <code>!pic on</code> — снова включить ответы (нужен ранг 5+)\n"
             "  <code>/help</code> — открыть эту справку\n\n"
             "Команды с повышенными правами требуют соответствующий ранг; действия модерации также требуют прав администратора Telegram."),
}


def help_main_text() -> str:
    total_cmds = len(COMMANDS)
    counter_line = f"📦 <b>{total_cmds} вариантов команд</b> (включая алиасы)\n\n" if total_cmds else ""
    return (
        "🐻 <b>ОБКУРЕННЫЙ ВАЛЕРА</b>\n"
        f"{UI_LINE}\n"
        "🧭 <b>Главное меню</b>\n\n"
        "Выбери раздел ниже 👇\n"
        f"{counter_line}"
        "📊 <b>Инфо и статистика</b> — профиль, ранг, топ\n"
        "🛡 <b>Модерация</b> — мут, бан, предупреждения\n"
        "🏆 <b>Награды и браки</b> — любовь, награды\n"
        "🎮 <b>Игры и РП</b> — игры, репутация, РП-команды\n"
        "⚙️ <b>Настройки</b> — ДК, права, анти-спам\n"
        f"{UI_LINE}\n"
        "💡 Префикс команд можно настроить через <code>!префикс</code>\n"
        "📌 Примеры: <code>!кто я</code>, <code>!пред @user</code>, <code>!мут @user</code>"
    )


def help_main_kb() -> InlineKeyboardMarkup:
    keys = list(HELP_SECTIONS.keys())
    rows = []
    for i in range(0, len(keys), 2):
        row = []
        for k in keys[i:i + 2]:
            row.append(InlineKeyboardButton(text=HELP_SECTIONS[k][0], callback_data=f"help_{k}"))
        rows.append(row)
    rows.append([InlineKeyboardButton(text="❌ Закрыть", callback_data="help_close")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def help_section_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="◀️ Назад", callback_data="help_back")]
    ])


@router.callback_query(F.data.startswith('help_'))
async def help_callback(call: CallbackQuery):
    try:
        action = call.data.replace('help_', '', 1)
        
        if action == 'close':
            try:
                await call.message.delete()
            except:
                pass
        elif action == 'back':
            await call.message.edit_text(help_main_text(), reply_markup=help_main_kb())
        elif action in HELP_SECTIONS:
            await call.message.edit_text(HELP_SECTIONS[action][1], reply_markup=help_section_kb())
        
        await call.answer()
    except Exception as e:
        logger.error(f"help_callback ошибка: {e}", exc_info=True)
        try:
            await call.answer("❌ Ошибка", show_alert=True)
        except:
            pass


async def cmd_help(msg: Message):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    await msg.answer(help_main_text(), reply_markup=help_main_kb())


@router.message(Command('help'))
async def slash_help(msg: Message):
    await cmd_help(msg)


@router.message(Command('prefix'))
async def slash_prefix(msg: Message, command: CommandObject):
    await cmd_prefix(msg, command.args or '')


@router.message(Command('profile'))
async def slash_profile(msg: Message):
    await who_am_i(msg, 'кто я')


@router.message(Command('top'))
async def slash_top(msg: Message):
    await cmd_top(msg, '', 'топ')


@router.message(Command('game'))
async def slash_game(msg: Message):
    await cmd_games_menu(msg, 'игры')


@router.message(Command('weather'))
async def slash_weather(msg: Message):
    await cmd_weather(msg, 'погода')


@router.message(Command('time'))
async def slash_time(msg: Message, command: CommandObject):
    await cmd_time(msg, command.args or '', 'время')


@router.message(Command('graphtheme'))
async def slash_activity_graph_theme(msg: Message):
    await cmd_activity_graph_theme(msg, 'тема графика')


@router.message(Command('ping'))
async def slash_ping(msg: Message):
    await cmd_ping_check(msg)


async def cmd_rp_list(msg: Message):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    
    # Показываем главное меню РП с кнопками
    txt = f"🎭 <b>РП-команды</b>\n{UI_LINE}\n"
    txt += f"Всего команд: <b>{len(ALL_RP)}</b>\n\n"
    txt += "Выбери раздел ниже 👇"
    
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"📌 Обычные ({len(RP)})", callback_data="rp_section:normal")],
        [InlineKeyboardButton(text=f"⭐ ВИП ({len(VIP_RP)})", callback_data="rp_section:vip")],
        [InlineKeyboardButton(text=f"💝 Влюблённые ({len(LOVE_RP)})", callback_data="rp_section:love")],
    ])
    
    await msg.answer(txt, reply_markup=kb)


@router.callback_query(F.data.startswith("rp_section:"))
async def handle_rp_section(query: CallbackQuery):
    section = query.data.split(":")[1]
    rank = storage.get_user(query.message.chat.id, query.from_user.id).get('rank', 0)
    married = bool(storage.get_user(query.message.chat.id, query.from_user.id).get('marriage_partner'))
    
    if section == "normal":
        cmds = sorted(RP.keys())
        title = "📌 <b>Обычные РП-команды</b>"
        desc = "Доступны всем:"
    elif section == "vip":
        if rank < VIP_RP_RANK:
            return await query.answer(f"❌ Нужен ранг {VIP_RP_RANK}+", show_alert=True)
        cmds = sorted(VIP_RP.keys())
        title = "⭐ <b>ВИП РП-команды</b>"
        desc = f"Доступны с рангом {VIP_RP_RANK}+:"
    elif section == "love":
        if not married:
            return await query.answer("❌ Доступны только в браке", show_alert=True)
        cmds = sorted(LOVE_RP.keys())
        title = "💝 <b>РП-команды для влюблённых</b>"
        desc = "Доступны в браке:"
    else:
        return
    
    # Форматируем список команд построчно по 3-4 команды
    txt = f"{title}\n{UI_LINE}\n{desc}\n\n"
    for i in range(0, len(cmds), 4):
        line = ", ".join(f"<code>{c}</code>" for c in cmds[i:i+4])
        txt += line + "\n"
    
    txt += "\n💡 Используй: <code>команда @user</code> или ответь на сообщение"
    
    # Клавиатура с кнопкой возврата
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="◀️ В меню", callback_data="rp_menu")]
    ])
    
    # Обновляем сообщение
    await query.message.edit_text(txt, reply_markup=kb)
    await query.answer()


@router.callback_query(F.data == "rp_menu")
async def handle_rp_menu(query: CallbackQuery):
    """Возврат в главное меню РП"""
    txt = f"🎭 <b>РП-команды</b>\n{UI_LINE}\n"
    txt += f"Всего команд: <b>{len(ALL_RP)}</b>\n\n"
    txt += "Выбери раздел ниже 👇"
    
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"📌 Обычные ({len(RP)})", callback_data="rp_section:normal")],
        [InlineKeyboardButton(text=f"⭐ ВИП ({len(VIP_RP)})", callback_data="rp_section:vip")],
        [InlineKeyboardButton(text=f"💝 Влюблённые ({len(LOVE_RP)})", callback_data="rp_section:love")],
    ])
    
    await query.message.edit_text(txt, reply_markup=kb)
    await query.answer()


def parse_currency_amount(text: str) -> Optional[Tuple[float, str]]:
    match = CURRENCY_AMOUNT_PATTERN.search(text)
    if not match:
        return None

    currency_text = match.group('currency')
    currency_code = next(
        (
            code for code, aliases in CURRENCY_ALIASES.items()
            if any(re.fullmatch(alias, currency_text, re.IGNORECASE) for alias in aliases)
        ),
        None,
    )
    if not currency_code:
        return None
    return float(match.group('amount').replace(',', '.')), currency_code


async def get_exchange_rates(base_currency: str) -> Optional[Dict[str, float]]:
    cached = EXCHANGE_RATE_CACHE.get(base_currency)
    now = time.monotonic()
    if cached and now < cached[0]:
        return cached[1]

    import aiohttp

    url = f"https://open.er-api.com/v6/latest/{base_currency}"
    try:
        timeout = aiohttp.ClientTimeout(total=8)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            async with session.get(url) as response:
                response.raise_for_status()
                data = await response.json()
    except (aiohttp.ClientError, asyncio.TimeoutError, OSError, ValueError) as exc:
        logger.warning("Не удалось получить курсы валют для %s: %s", base_currency, exc)
        return None

    rates = (
        data.get('rates')
        if isinstance(data, dict) and data.get('result') == 'success'
        else None
    )
    if not isinstance(rates, dict):
        logger.warning("API вернул некорректные курсы валют для %s", base_currency)
        return None

    EXCHANGE_RATE_CACHE[base_currency] = (now + 3600, rates)
    return rates


async def answer_currency_amount(msg: Message, amount: float, base_currency: str):
    rates = await get_exchange_rates(base_currency)
    if rates is None:
        return await msg.answer("❌ Не удалось получить актуальные курсы валют. Попробуйте позже.")

    def format_money(value: float, code: str) -> str:
        if code == 'JPY':
            formatted = f"{value:,.0f}"
        elif 0 < abs(value) < 0.01:
            formatted = f"{value:,.6f}"
        else:
            formatted = f"{value:,.2f}"
        formatted = formatted.replace(",", " ")
        if '.' in formatted:
            formatted = formatted.rstrip('0').rstrip('.')
        return formatted

    base_flag, base_name, base_symbol = CURRENCY_DISPLAY[base_currency]
    amount_text = format_money(amount, base_currency)
    lines = []
    for code, (flag, name, symbol) in CURRENCY_DISPLAY.items():
        if code == base_currency:
            continue
        rate = rates.get(code)
        if not isinstance(rate, (int, float)):
            continue
        converted = amount * rate
        converted_text = format_money(converted, code)
        lines.append(f"{flag} <b>{converted_text} {symbol}</b> — {name}")

    if not lines:
        logger.warning("В ответе API нет поддерживаемых курсов для %s", base_currency)
        return await msg.answer("❌ Для этой валюты сейчас нет доступных курсов.")

    await msg.answer(
        f"💱 {base_flag} <b>{amount_text} {base_symbol} — {base_name}</b>\n\n"
        "<i>Примерная стоимость по актуальному курсу:</i>\n"
        f"<blockquote expandable>{chr(10).join(lines)}</blockquote>\n\n"
        "<i>Курсы могут отличаться от курса вашего банка.</i>",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="❌ Закрыть", callback_data="currency_close")]
        ])
    )


@router.callback_query(F.data == "currency_close")
async def close_currency_message(call: CallbackQuery):
    if call.message:
        await call.message.delete()
    await call.answer()


async def handle_wordle_guess(msg: Message, game: dict) -> bool:
    game_message = msg.reply_to_message
    is_game_reply = (
        game_message is not None
        and game_message.from_user is not None
        and game_message.from_user.id == bot.id
        and game_message.message_id == game.get('message_id')
        and msg.chat.id == game.get('chat_id')
    )
    if not is_game_reply:
        return False

    guess = msg.text.strip().lower()
    player_name = f"@{msg.from_user.username}" if msg.from_user.username else msg.from_user.full_name
    player_name = html.escape(player_name)
    success, response, updated_game = wordle.make_guess(
        msg.chat.id, msg.from_user.id, guess, player_name
    )

    try:
        await msg.delete()
    except Exception:
        pass

    if not success:
        await msg.answer(response)
        return True

    if updated_game:
        user = storage.get_user(msg.chat.id, msg.from_user.id)
        user['wordle_games'] = user.get('wordle_games', 0) + 1
        if guess == updated_game['word']:
            user['wordle_wins'] = user.get('wordle_wins', 0) + 1
        storage.mark_dirty()
        await storage.save()
        wordle.exit_chat_game(msg.chat.id)

    try:
        await bot.edit_message_text(
            chat_id=game['chat_id'],
            message_id=game['message_id'],
            text=response
        )
    except Exception as e:
        logger.error(f"Ошибка редактирования сообщения Wordle: {e}")
    return True


@router.message(F.text)
async def main_text_handler(msg: Message):
    if not msg.text or not msg.from_user or msg.from_user.is_bot:
        return

    # *** ПРОВЕРКА РЕПУТАЦИИ В ПЕРВУЮ ОЧЕРЕДЬ ***
    if msg.reply_to_message and msg.reply_to_message.from_user:
        if not msg.reply_to_message.from_user.is_bot and msg.from_user.id != msg.reply_to_message.from_user.id:
            text = msg.text.strip()
            if is_reputation_removal_message(text):
                await give_reputation(msg, remove=True)
                return
            if is_reputation_message(text):
                await give_reputation(msg)
                return

    chat_id = msg.chat.id
    user_id = msg.from_user.id
    main_chat = is_main_chat(chat_id, msg.message_thread_id)

    user = storage.get_user(chat_id, user_id)

    text = msg.text.strip()
    prefix = get_command_prefix(chat_id)
    prefixed_command = bool(prefix and text.startswith(prefix))
    prefix_command = text == '!префикс' or text.startswith('!префикс ')
    cleaned = strip_command_prefix(text, chat_id)
    compatible_prefixed_command = not prefix and cleaned != text
    bare_command = not prefix and match_command(cleaned)[0] is not None

    # ===== Wordle (обработка ходов) =====
    if not prefixed_command and not prefix_command and not compatible_prefixed_command and not bare_command:
        game = wordle.get_chat_game(msg.chat.id)
        if game is not None and game['status'] == 'active':
            if await handle_wordle_guess(msg, game):
                return

    if text == '-смс' or text.startswith('-смс '):
        await execute_command('-смс', text[len('-смс'):].strip(), msg, main_chat)
        return

    if prefix_command:
        await cmd_prefix(msg, text[len('!префикс'):].strip())
        return

    if prefix and not prefixed_command:
        cleaned = ''
    if cleaned and not (cleaned == '-смс' or cleaned.startswith('-смс ')):
        cmd_name, args = match_command(cleaned)
        if cmd_name:
            await execute_command(cmd_name, args, msg, main_chat)
            return
        if prefixed_command or compatible_prefixed_command:
            if await rp_handler(msg):
                return
            await report_command_error(
                msg,
                cleaned.split()[0],
                'Неизвестная команда',
                f"Команда <code>{html.escape(cleaned.split()[0], quote=False)}</code> не найдена или недоступна в этом чате.",
                '!помощь',
            )
            return

    currency_query = parse_currency_amount(text)
    if currency_query:
        await answer_currency_amount(msg, *currency_query)
        return

    await rp_handler(msg)


async def execute_command(cmd_name: str, args: str, msg: Message, main_chat: bool):
    """Выполняет команду по её имени"""

    handlers = {
        'cmd_help': lambda: cmd_help(msg),
        'cmd_prefix': lambda: cmd_prefix(msg, args),
        'cmd_rp_list': lambda: cmd_rp_list(msg),
        'who_am_i': lambda: who_am_i(msg, cmd_name),
        'who_are_you': lambda: who_are_you(msg, args, cmd_name),
        'who_admin': lambda: who_admin(msg),
        'cmd_rank': lambda: cmd_rank(msg),
        'cmd_ranks_list': lambda: cmd_ranks_list(msg),
        'cmd_rank_rename': lambda: cmd_rank_rename(msg, cmd_name, args),
        'cmd_id': lambda: cmd_id(msg, cmd_name),
        'cmd_top': lambda: cmd_top(msg, args, cmd_name),
        'cmd_chat_stats': lambda: cmd_chat_stats(msg, cmd_name),
        'cmd_stats': lambda: cmd_stats(msg, args, cmd_name),
        'cmd_mute': lambda: cmd_mute(msg, cmd_name),
        'cmd_unmute': lambda: cmd_unmute(msg, cmd_name),
        'cmd_ban': lambda: cmd_ban(msg, cmd_name),
        'cmd_unban': lambda: cmd_unban(msg, cmd_name),
        'cmd_warn': lambda: cmd_warn(msg, cmd_name),
        'show_warnings': lambda: show_warnings(msg, cmd_name),
        'cmd_mute_list': lambda: cmd_mute_list(msg, cmd_name),
        'cmd_ban_list': lambda: cmd_ban_list(msg, cmd_name),
        'cmd_warn_list': lambda: cmd_warn_list(msg, cmd_name),
        'cmd_unwarn': lambda: cmd_unwarn(msg, cmd_name),
        'cmd_del': lambda: cmd_del(msg, cmd_name),
        'cmd_pin': lambda: cmd_pin(msg, cmd_name),
        'cmd_purge': lambda: cmd_purge(msg, cmd_name),
        'cmd_promote': lambda: cmd_promote(msg, cmd_name),
        'cmd_demote': lambda: cmd_demote(msg, cmd_name),
        'cmd_give_award': lambda: cmd_give_award(msg, cmd_name),
        'cmd_rem_award': lambda: cmd_rem_award(msg, cmd_name),
        'cmd_my_awards': lambda: cmd_my_awards(msg, cmd_name),
        'cmd_top_awards': lambda: cmd_top_awards(msg, cmd_name),
        'cmd_marry': lambda: cmd_marry(msg, cmd_name),
        'cmd_accept_marry': lambda: cmd_accept_marry(msg, cmd_name),
        'cmd_reject_marry': lambda: cmd_reject_marry(msg, cmd_name),
        'cmd_divorce': lambda: cmd_divorce(msg, cmd_name),
        'cmd_marriages_list': lambda: cmd_marriages_list(msg),
        'cmd_add_phrase': lambda: cmd_add_phrase(msg, cmd_name),
        'cmd_del_phrase': lambda: cmd_del_phrase(msg, cmd_name),
        'cmd_list_phrases': lambda: cmd_list_phrases(msg, cmd_name),
        'cmd_phrase_stats': lambda: cmd_phrase_stats(msg),
        'cmd_phrase_show': lambda: cmd_phrase_show(msg, cmd_name),
        'cmd_welcome': lambda: cmd_welcome(msg, cmd_name),
        'cmd_farewell': lambda: cmd_farewell(msg, cmd_name),
        'cmd_rules': lambda: cmd_rules(msg),
        'cmd_add_rule': lambda: cmd_add_rule(msg, cmd_name),
        'cmd_clear_rules': lambda: cmd_clear_rules(msg, cmd_name),
        'cmd_games_menu': lambda: cmd_games_menu(msg, cmd_name),
        'cmd_rps_menu': lambda: cmd_rps(msg, cmd_name),
        'cmd_rps_with_bot': lambda: cmd_rps(msg, cmd_name),
        'cmd_rps_choice': lambda: cmd_rps(msg, cmd_name),
        'cmd_ttt_menu': lambda: cmd_games_menu(msg, cmd_name),
        'cmd_wordle': lambda: cmd_wordle(msg),
        'cmd_weather': lambda: cmd_weather(msg, cmd_name),
        'cmd_time': lambda: cmd_time(msg, args, cmd_name),
        'cmd_activity_graph_theme': lambda: cmd_activity_graph_theme(msg, cmd_name),
        'cmd_random_joke': lambda: cmd_random_joke(msg, cmd_name),
        'cmd_ship': lambda: cmd_ship(msg, cmd_name),
        'cmd_my_article': lambda: cmd_my_article(msg, cmd_name),
        'cmd_poll': lambda: cmd_poll(msg, cmd_name),
        'cmd_iris': lambda: cmd_iris(msg, cmd_name),
        'cmd_report': lambda: cmd_report(msg, cmd_name),
        'cmd_nick': lambda: cmd_nick(msg, cmd_name),
        'cmd_pogonialo': lambda: cmd_pogonialo(msg, cmd_name),
        'cmd_anti_spam': lambda: cmd_anti_spam(msg, cmd_name),
        'cmd_ping_check': lambda: cmd_ping_check(msg),
        'cmd_pic_toggle': lambda: cmd_pic_toggle(msg, cmd_name),
        'cmd_ping': lambda: cmd_ping(msg, cmd_name),
        'cmd_backup': lambda: cmd_backup(msg, cmd_name),
        'cmd_restore': lambda: cmd_restore(msg, cmd_name),
        'cmd_dk_set': lambda: cmd_dk_set(msg, cmd_name),
        'cmd_dk_enable': lambda: cmd_dk_enable(msg, cmd_name),
        'cmd_dk_disable': lambda: cmd_dk_disable(msg, cmd_name),
        'cmd_ldk_add': lambda: cmd_ldk_add(msg, cmd_name),
        'cmd_ldk_rem': lambda: cmd_ldk_rem(msg, cmd_name),
        'cmd_dk_menu': lambda: cmd_dk_menu(msg, cmd_name),
        'cmd_forward': lambda: cmd_forward(msg, cmd_name),
    }

    func_name = COMMANDS.get(cmd_name)
    if not func_name:
        await report_command_error(
            msg,
            cmd_name,
            'Неизвестная команда',
            f"Команда <code>{html.escape(str(cmd_name), quote=False)}</code> не распознана.",
            '!помощь',
        )
        return

    if func_name not in handlers:
        await report_command_error(
            msg,
            cmd_name,
            'Команда не подключена',
            f"Команда <code>{html.escape(str(cmd_name), quote=False)}</code> есть в списке, но пока не подключена к обработчику.",
            '!помощь',
        )
        return

    try:
        await handlers[func_name]()
    except Exception as exc:
        logger.exception('Ошибка выполнения команды %s', cmd_name)
        detail = str(exc).strip() or 'Проверьте формат вызова и попробуйте ещё раз.'
        await report_command_error(
            msg,
            cmd_name,
            'Ошибка команды',
            f"Команда <code>{html.escape(str(cmd_name), quote=False)}</code> завершилась с ошибкой: {html.escape(detail[:250], quote=False)}",
            get_command_example(cmd_name),
        )


# ==================== Профиль и информация ====================

def build_profile_text(chat_id: int, uid: int, u: dict, show_last_active: bool = False) -> str:
    """Собирает красиво оформленный текст профиля пользователя."""
    username = u.get('username', '')
    custom_name = u.get('custom_name', '')
    original_name = u.get('first_name') or (f"@{username}" if username else f"ID:{uid}")
    display_name = custom_name or original_name

    safe_display_name = html.escape(str(display_name), quote=False)
    if username:
        safe_username = html.escape(str(username), quote=True)
        profile_link = f'<a href="https://t.me/{safe_username}">{safe_display_name}</a>'
    else:
        profile_link = f'<a href="tg://user?id={uid}">{safe_display_name}</a>'

    rank = u.get('rank', 0)
    reputation = u.get('reputation', 0)
    rank_emoji = get_rank_emoji(chat_id, rank)
    rank_name = get_rank_name(chat_id, rank)

    activity = u.get('activity', {})
    now = kaliningrad_now()
    today_msgs = get_activity_message_count(activity, 'day', now)
    week_msgs = get_activity_message_count(activity, 'week', now)
    month_msgs = get_activity_message_count(activity, 'month', now)
    total_msgs = u.get('messages_count', 0)

    first_seen = u.get('first_seen', time.time())
    first_seen_date = datetime.fromtimestamp(first_seen)
    days_since = (datetime.now() - first_seen_date).days

    wrn = [w for w in u.get('warnings', []) if isinstance(w, dict) and warning_is_active(w)]
    tag = custom_name or original_name

    lines = [
        "👤 <b>Профиль</b>",
        f"{UI_LINE}",
        f"{profile_link}",
    ]
    if custom_name:
        lines.append(f"🏷️ <i>Оригинальное имя: {html.escape(str(original_name), quote=False)}</i>")
    lines.append(f"{rank_emoji} <b>{html.escape(str(rank_name), quote=False)}</b> <i>(уровень {rank})</i>")
    lines.append(f"⭐ Репутация: <b>{reputation}</b>")
    lines.append(f"⚠️ Варны: <b>{len(wrn)}/{MAX_WARNINGS}</b>")

    if u.get('marriage_partner'):
        partner = u['marriage_partner']
        marriage_date = u.get('marriage_date')
        if marriage_date:
            days_married = int((time.time() - marriage_date) / 86400)
            lines.append(f"💍 Брак: {mention(chat_id, partner)} <i>({days_married} дн)</i>")
        else:
            lines.append(f"💍 Брак: {mention(chat_id, partner)}")

    lines.append(f"{UI_LINE}")
    lines.append("📊 <b>Активность</b>")
    lines.append(f"• Сегодня: {today_msgs}")
    lines.append(f"• Неделя: {week_msgs}")
    lines.append(f"• Месяц: {month_msgs}")
    lines.append(f"• Всего: <b>{total_msgs}</b>")
    lines.append(f"{UI_LINE}")
    lines.append(f"📅 В чате с {first_seen_date.strftime('%d.%m.%Y')} <i>({days_since} дн)</i>")

    if show_last_active:
        last_seen = u.get('last_seen', time.time())
        diff = int(time.time() - last_seen)
        if diff < 60:
            last_active = "только что"
        elif diff < 3600:
            last_active = f"{diff // 60} мин назад"
        elif diff < 86400:
            last_active = f"{diff // 3600} ч назад"
        else:
            last_active = f"{diff // 86400} дн назад"
        lines.append(f"🕐 Последний актив: {last_active}")

    awards = u.get('awards', [])
    recent_awards = sorted(awards, key=lambda x: x.get('given_at', 0), reverse=True)[:5]
    if recent_awards:
        lines.append(f"{UI_LINE}")
        lines.append("🏆 <b>Последние награды</b>")
        for award in recent_awards:
            lines.append(f"• {html.escape(str(award['name']), quote=False)} <i>(ст. {award.get('degree', 1)})</i>")

    return "\n".join(lines)


async def who_am_i(msg: Message, cmd_name: str = 'кто я'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!кто я'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    uid = msg.from_user.id
    u = storage.get_user(msg.chat.id, uid)

    text = build_profile_text(msg.chat.id, uid, u, show_last_active=True)

    graph = create_graph(msg.chat.id, uid, 30)
    if graph:
        await msg.answer_photo(BufferedInputFile(graph.read(), 'profile_graph.png'), caption=text)
    else:
        await msg.answer(text, disable_web_page_preview=True)


def activity_graph_theme_keyboard(uid: int, mode: Optional[str] = None, selected_theme: str = '') -> InlineKeyboardMarkup:
    keyboard = InlineKeyboardBuilder()
    if mode is None:
        keyboard.button(text='☀️ Светлая', callback_data=f'activity_theme:mode:{uid}:light')
        keyboard.button(text='🌙 Тёмная', callback_data=f'activity_theme:mode:{uid}:dark')
        keyboard.adjust(2)
        return keyboard.as_markup()

    for theme_id, theme in ACTIVITY_GRAPH_THEMES.items():
        if theme[1] != mode:
            continue
        label = f"✅ {theme[0]}" if theme_id == selected_theme else theme[0]
        keyboard.button(text=label, callback_data=f'activity_theme:set:{uid}:{theme_id}')
    keyboard.adjust(2)
    keyboard.row(InlineKeyboardButton(text='◀️ Назад', callback_data=f'activity_theme:back:{uid}'))
    return keyboard.as_markup()


async def cmd_activity_graph_theme(msg: Message, cmd_name: str = 'тема графика'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    current_theme = storage.get_user(msg.chat.id, msg.from_user.id).get('activity_graph_theme', 'dark_default')
    current_name = ACTIVITY_GRAPH_THEME_NAMES.get(current_theme, 'Стандартная')
    await msg.answer(
        f"🎨 <b>Тема графика активности</b>\nТекущая тема: <b>{current_name}</b>\n\nВыберите светлую или тёмную палитру:",
        reply_markup=activity_graph_theme_keyboard(msg.from_user.id),
    )


@router.callback_query(F.data.startswith('activity_theme:'))
async def activity_graph_theme_callback(call: CallbackQuery):
    parts = call.data.split(':')
    if len(parts) < 3:
        return await call.answer('Некорректная настройка темы.', show_alert=True)

    action, owner_id = parts[1], parts[2]
    if not owner_id.isdigit() or int(owner_id) != call.from_user.id:
        return await call.answer('Эти настройки открыты другим пользователем.', show_alert=True)

    chat_id = call.message.chat.id
    user = storage.get_user(chat_id, call.from_user.id, use_cache=False)
    if action == 'mode' and len(parts) == 4 and parts[3] in ('light', 'dark'):
        mode = parts[3]
        current_theme = user.get('activity_graph_theme', 'dark_default')
        await call.message.edit_text(
            f"🎨 Выберите тему для {'светлого' if mode == 'light' else 'тёмного'} оформления:",
            reply_markup=activity_graph_theme_keyboard(call.from_user.id, mode, current_theme),
        )
    elif action == 'back' and len(parts) == 3:
        current_theme = user.get('activity_graph_theme', 'dark_default')
        current_name = ACTIVITY_GRAPH_THEME_NAMES.get(current_theme, 'Стандартная')
        await call.message.edit_text(
            f"🎨 <b>Тема графика активности</b>\nТекущая тема: <b>{current_name}</b>\n\nВыберите светлую или тёмную палитру:",
            reply_markup=activity_graph_theme_keyboard(call.from_user.id),
        )
    elif action == 'set' and len(parts) == 4 and parts[3] in ACTIVITY_GRAPH_THEMES:
        theme_id = parts[3]
        user['activity_graph_theme'] = theme_id
        storage.invalidate_user_cache(chat_id, call.from_user.id)
        storage.mark_dirty()
        await storage.save()
        mode = ACTIVITY_GRAPH_THEMES[theme_id][1]
        await call.message.edit_text(
            f"✅ Тема графика сохранена: <b>{ACTIVITY_GRAPH_THEME_NAMES[theme_id]}</b>.",
            reply_markup=activity_graph_theme_keyboard(call.from_user.id, mode, theme_id),
        )
        return await call.answer('Тема сохранена')
    else:
        return await call.answer('Неизвестная тема графика.', show_alert=True)

    await call.answer()


async def who_are_you(msg: Message, args: str = None, cmd_name: str = 'кто ты'):
    if not await require_access(msg, cmd_name, 0, example='!кто ты @user'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    tid = None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif args:
        tid = await get_target(msg, args)

    if not tid:
        return await msg.answer(ui_error("Не указан пользователь", "Укажи пользователя через @user или ответь на сообщение пользователя.", "!кто ты @user"), disable_web_page_preview=True)

    u = storage.get_user(msg.chat.id, tid)
    text = build_profile_text(msg.chat.id, tid, u, show_last_active=False)

    graph = create_graph(msg.chat.id, tid, 30)
    if graph:
        await msg.answer_photo(BufferedInputFile(graph.read(), 'profile_graph.png'), caption=text)
    else:
        await msg.answer(text, disable_web_page_preview=True)


async def who_admin(msg: Message):
    if not await require_access(msg, 'кто админ', 0, example='!кто админ'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    admins = []
    for uid, d in storage.data['users'].get(str(msg.chat.id), {}).items():
        rank = d.get('rank', 0)
        if rank >= 1:
            admins.append((int(uid), d, rank))

    admins.sort(key=lambda x: x[2], reverse=True)

    if not admins:
        return await msg.answer("👤 Нет администраторов")

    ranks_grouped = defaultdict(list)
    for uid, user_data, rank in admins:
        ranks_grouped[rank].append((uid, user_data))

    txt = "👑 <b>Администрация чата:</b>\n\n"

    for rank in sorted(ranks_grouped.keys(), reverse=True):
        group = ranks_grouped[rank]
        role_name = get_rank_name(msg.chat.id, rank)
        mango_count = max(1, min(rank, MAX_RANK))
        mango_line = '🥭' * mango_count
        txt += f"{mango_line} <b>{role_name}</b>\n"

        for uid, user_data in group:
            status = await get_user_status(uid, user_data)
            username = user_data.get('username', '')
            custom_name = user_data.get('custom_name', '')
            display_name = custom_name or user_data.get('first_name') or username or f"ID:{uid}"
            safe_display_name = html.escape(str(display_name), quote=False)

            if username:
                safe_username = html.escape(str(username), quote=True)
                profile_link = f'<a href="https://t.me/{safe_username}">{safe_display_name}</a>'
            else:
                profile_link = f'<a href="tg://user?id={uid}">{safe_display_name}</a>'

            txt += f"{status} {profile_link}\n"

        txt += "\n"

    txt += f"{UI_LINE}\n"
    txt += "🟢 В сети | ⚪ Не в сети | 🔴 Давно не в сети (1+ день)"

    await msg.answer(txt, disable_web_page_preview=True)


async def cmd_rank(msg: Message):
    r = storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0)
    await msg.answer(f"{get_rank_emoji(msg.chat.id, r)} {get_rank_name(msg.chat.id, r)} ({r}/{MAX_RANK})")


async def cmd_ranks_list(msg: Message):
    """Показывает названия всех уровней иерархии в этом чате"""
    lines = ["🏆 <b>Иерархия рангов</b>\n"]
    for level in range(MAX_RANK + 1):
        lines.append(f"{get_rank_emoji(msg.chat.id, level)} <b>{level}</b> — {get_rank_name(msg.chat.id, level)}")
    lines.append("\n<code>!переранг 0-5 Новое название</code> — переименовать")
    await msg.answer("\n".join(lines))


async def cmd_rank_rename(msg: Message, cmd_name: str = 'название ранга', args: str = ""):
    if not await require_access(msg, cmd_name, 5, title='Недостаточно прав', message='Эта команда доступна только старшему администратору.', example='!переранг 3 Батя'):
        return
    parts = args.split(maxsplit=1)
    if len(parts) < 2 or not parts[0].isdigit():
        return await msg.answer(
            "❌ <b>Неверный формат</b>\n"
            "Укажи уровень и новое название\n"
            f"<code>!переранг 0-{MAX_RANK} Новое название</code>"
        )
    level = int(parts[0])
    if not (0 <= level <= MAX_RANK):
        return await msg.answer(
            "❌ <b>Неверный уровень</b>\n"
            f"Уровень должен быть от 0 до {MAX_RANK}\n"
            "<code>!переранг 3 Батя</code>"
        )
    new_name = parts[1].strip()
    if not new_name:
        return await msg.answer(
            "❌ <b>Не указано название</b>\n"
            "Добавь название для ранга\n"
            "<code>!переранг 3 Батя</code>"
        )
    storage.data['rank_names'].setdefault(str(msg.chat.id), {})[str(level)] = new_name
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"✅ <b>Ранг {level}</b>: теперь называется «{html.escape(new_name, quote=False)}»")


async def cmd_id(msg: Message, cmd_name: str = 'ид'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!ид'):
        return
    await msg.answer(
        f"🆔 <code>{msg.reply_to_message.from_user.id}</code>" if msg.reply_to_message else f"🆔 Ваш: <code>{msg.from_user.id}</code>\n💬 Чат: <code>{msg.chat.id}</code>")


# ==================== Топы ====================

async def cmd_top(msg: Message, args: str = "", cmd_name: str = 'топ'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!топ день'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    if not args:
        await show_msg_top(msg, 'day')
        return

    arg = args.lower()
    periods = {
        'день': 'day', 'дня': 'day', 'day': 'day', 'today': 'day', 'сегодня': 'day',
        'неделя': 'week', 'неделю': 'week', 'week': 'week', 'нед': 'week',
        'месяц': 'month', 'month': 'month', 'мес': 'month',
        'год': 'year', 'year': 'year', 'года': 'year',
        'всё': 'all', 'все': 'all', 'вся': 'all', 'все время': 'all', 'all': 'all', 'общий': 'all', 'сообщения': 'all',
        'сообщ': 'all', 'msg': 'all', 'messages': 'all'
    }

    period = periods.get(arg, 'day')
    await show_msg_top(msg, period)


async def show_msg_top(msg: Message, period: str = 'all'):
    now = kaliningrad_now()

    users_data = []

    for uid, d in storage.data['users'].get(str(msg.chat.id), {}).items():
        activity = d.get('activity', {})
        msg_count = 0

        if period in ('day', 'week', 'month', 'year'):
            msg_count = get_activity_message_count(activity, period, now)
        else:
            msg_count = d.get('messages_count', 0)

        if msg_count > 0:
            users_data.append((int(uid), msg_count, d.get('rank', 0)))

    users_data.sort(key=lambda x: x[1], reverse=True)

    if not users_data:
        return await msg.answer("📊 Нет данных за этот период")

    period_names = {'day': 'за сегодня', 'week': 'за неделю', 'month': 'за месяц', 'year': 'за год',
                    'all': 'за всё время'}
    period_name = period_names.get(period, 'за всё время')

    txt = f"🏆 <b>Топ активности {period_name}</b>\n{UI_LINE}\n"

    for i, (uid, count, rank) in enumerate(users_data[:20], 1):
        medal = "🥇" if i == 1 else "🥈" if i == 2 else "🥉" if i == 3 else f"{i}."
        txt += f"{medal} {mention(msg.chat.id, uid)} — <b>{count}</b> сообщ.\n"

    my_position = None
    for idx, (uid, count, rank) in enumerate(users_data, 1):
        if uid == msg.from_user.id:
            my_position = idx
            break

    if my_position is not None and my_position > 20:
        txt += f"\n📍 Ты: <b>{my_position}</b> место — <b>{users_data[my_position - 1][1]}</b> сообщ."
    elif my_position is not None:
        txt += f"\n📍 Ты: <b>{my_position}</b> место — <b>{users_data[my_position - 1][1]}</b> сообщ."

    total_messages = sum(count for _, count, _ in users_data)
    txt += f"\n\n💬 Всего сообщений {period_name}: <b>{total_messages}</b>"

    await msg.answer(txt, disable_web_page_preview=True)


async def cmd_chat_stats(msg: Message, cmd_name: str = 'статистика чата'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!статистика чата'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    total_msgs = sum(d.get('messages_count', 0) for d in storage.data['users'].get(str(msg.chat.id), {}).values())
    total_rep = sum(d.get('reputation', 0) for d in storage.data['users'].get(str(msg.chat.id), {}).values())
    moders = sum(1 for d in storage.data['users'].get(str(msg.chat.id), {}).values() if d.get('rank', 0) >= 1)
    marriages = len(storage.get_chat(msg.chat.id, 'marriages'))
    await msg.answer(
        f"📊 <b>Статистика чата</b>\n\n👥 Пользователей: {len(storage.data['users'].get(str(msg.chat.id), {}))}\n👑 Модераторов: {moders}\n💬 Сообщений: {total_msgs}\n⭐ Репутации: {total_rep}\n💍 Браков: {marriages}")


async def cmd_stats(msg: Message, args: str = "", cmd_name: str = 'статистика'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!статистика'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    parts = args.split()

    days = 7
    if parts and parts[0].isdigit():
        days = int(parts[0])

    tid = msg.from_user.id
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif len(parts) > 1:
        target = await get_target(msg, parts[1])
        if target:
            tid = target

    u = storage.get_user(msg.chat.id, tid)
    act = u.get('activity', {})
    total_msgs = sum(d.get('messages', 0) for d in act.values())
    total_rep = sum(d.get('reputation', 0) for d in act.values())

    info = (
        f"📊 <b>{mention(msg.chat.id, tid)}</b>\n\n"
        f"📝 Сообщений: {total_msgs}\n"
        f"⭐ Репутации: +{total_rep}\n"
        f" TTT: {u.get('ttt_wins', 0)}/{u.get('ttt_games', 0)}\n"
        f"🎯 КНБ: {u.get('rps_wins', 0)}/{u.get('rps_games', 0)}"
    )

    graph = create_graph(msg.chat.id, tid, days)
    if graph:
        await msg.answer_photo(BufferedInputFile(graph.read(), 'graph.png'), caption=info)
    else:
        await msg.answer(info, disable_web_page_preview=True)


# ==================== Модерация ====================

def ui_error(title: str, message: str, example: str = "", *, message_is_html: bool = False) -> str:
    """Возвращает стандартное сообщение об ошибке для доступа/формата команды."""
    block = (
        f"❌ <b>{html.escape(str(title), quote=False)}</b>\n\n"
        f"{str(message) if message_is_html else html.escape(str(message), quote=False)}"
    )
    if example:
        block += f"\n\n💡 Пример: <code>{html.escape(str(example), quote=False)}</code>"
    return block


async def require_access(msg: Message, cmd_name: str, min_rank: int = 0, *, title: str = "Недостаточно прав",
                        message: Optional[str] = None, example: str = "") -> bool:
    """Проверяет доступ и возвращает False, если нет прав, с понятной подсказкой."""
    if check_access(msg.from_user.id, msg.chat.id, cmd_name, min_rank):
        return True

    rank_text = "всем участникам" if min_rank <= 0 else f"с ранга {min_rank}+"
    detail = message or f"Эта команда доступна {rank_text}."
    await msg.answer(ui_error(title, detail, example or get_command_example(cmd_name)), disable_web_page_preview=True)
    return False


async def require_target(msg: Message, target: Optional[int], *, not_found_message: str = "Пользователь не найден") -> bool:
    """Проверяет, что целевой пользователь найден, и выводит понятную ошибку."""
    if target:
        return True
    await msg.answer(ui_error("Пользователь не найден", not_found_message, "!кто ты @user"), disable_web_page_preview=True)
    return False


async def cmd_mute(msg: Message, cmd_name: str = 'мут'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 1, title='Недостаточно прав', message='Эта команда доступна только модераторам и выше.', example='!мут @user 30м флуд'):
        return

    text = msg.text.strip()
    parts = text.split(maxsplit=2)

    tid = None
    dur_text = ""
    reason = "Без причины"
    permanent = False

    # ПРИОРИТЕТ 1: Ответ на сообщение
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            rest = text[len(parts[0]):].strip()
            permanent, dur_text, reason = parse_mute_duration_and_reason(rest)

    # ПРИОРИТЕТ 2: Аргументы в команде
    elif len(parts) >= 2:
        target_arg = parts[1]
        target_mention = get_target_mention_span(msg, target_arg)
        tid = await get_target(msg, target_arg)

        if not tid:
            return await msg.answer(
                ui_error(
                    "Пользователь не найден",
                    f"Не могу определить пользователя <code>{html.escape(str(target_arg), quote=False)}</code>. "
                    "Используйте @username, числовой ID, кликабельное упоминание Telegram или ответ на его сообщение.",
                    "!мут @user 30м флуд"
                ),
                disable_web_page_preview=True,
            )

        if target_mention:
            rest = msg.text[target_mention[2]:].strip()
            if rest:
                permanent, dur_text, reason = parse_mute_duration_and_reason(rest)
        elif len(parts) >= 3:
            permanent, dur_text, reason = parse_mute_duration_and_reason(parts[2])

    else:
        return await msg.answer(
            ui_error(
                "Не указаны аргументы",
                "Нужно указать пользователя, время и причину",
                "!мут @user 2ч флуд"
            )
        )

    if not tid:
        return await msg.answer(ui_error("Не удалось определить пользователя", "Не удалось понять, кого именно вы хотите замутить. Ответьте на сообщение пользователя или укажите @user.", "!мут @user 30м флуд"), disable_web_page_preview=True)

    if tid == msg.from_user.id:
        return await msg.answer(ui_error("Нельзя замутить себя", "Вы не можете ограничить доступ сами себе.", "!мут @user 30м флуд"), disable_web_page_preview=True)

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer(ui_error("Анти-модерация", "Нельзя применять эту команду к пользователю с равным или более высоким уровнем доступа.", "!мут @user 30м флуд"), disable_web_page_preview=True)

    dur = parse_time(dur_text) if dur_text else DEFAULT_MUTE_MINUTES
    if not permanent and not 1 <= dur <= MAX_MUTE_MINUTES:
        return await msg.answer("❌ Срок мута должен быть от 1 минуты до 1 года. Для бессрочного мута укажите «навсегда».")

    try:
        until = None if permanent else datetime.now() + timedelta(minutes=dur)
        permissions = ChatPermissions(can_send_messages=False)
        if permanent:
            await bot.restrict_chat_member(msg.chat.id, tid, permissions)
            time_str = "навсегда"
            expire_time = None
        else:
            await bot.restrict_chat_member(
                msg.chat.id, tid, permissions, until_date=int(until.timestamp())
            )
            expire_time = until.timestamp()

        # Форматируем время
        if permanent:
            pass
        elif dur >= 525600000:  # тысячелетие (1000 * 365 * 1440)
            count = dur // 525600000
            time_str = f"{count} тысячелетие" if count == 1 else f"{count} тысячелетий"
        elif dur >= 52560000:  # век (100 * 365 * 1440)
            count = dur // 52560000
            if count % 10 == 1 and count != 11:
                time_str = f"{count} век"
            elif count % 10 in [2, 3, 4] and count not in [12, 13, 14]:
                time_str = f"{count} века"
            else:
                time_str = f"{count} веков"
        elif dur >= 525600:  # год (365 * 1440)
            count = dur // 525600
            if count % 10 == 1 and count != 11:
                time_str = f"{count} год"
            elif count % 10 in [2, 3, 4] and count not in [12, 13, 14]:
                time_str = f"{count} года"
            else:
                time_str = f"{count} лет"
        elif dur >= 43800:  # месяц (30 * 1440)
            count = dur // 43800
            if count % 10 == 1 and count != 11:
                time_str = f"{count} месяц"
            elif count % 10 in [2, 3, 4] and count not in [12, 13, 14]:
                time_str = f"{count} месяца"
            else:
                time_str = f"{count} месяцев"
        elif dur >= 1440:  # дни
            days = dur // 1440
            hours = (dur % 1440) // 60
            minutes = dur % 60
            if hours > 0 and minutes > 0:
                time_str = f"{days}д {hours}ч {minutes}м"
            elif hours > 0:
                time_str = f"{days}д {hours}ч"
            elif minutes > 0:
                time_str = f"{days}д {minutes}м"
            else:
                time_str = f"{days}д"
        elif dur >= 60:  # часы
            hours = dur // 60
            minutes = dur % 60
            if minutes > 0:
                time_str = f"{hours}ч {minutes}м"
            else:
                time_str = f"{hours}ч"
        else:  # минуты
            time_str = f"{dur}м"

        # Сохраняем мут
        mutes = storage.get_chat(msg.chat.id, 'mutes')
        if not isinstance(mutes, list):
            mutes = []
            storage.data['mutes'][str(msg.chat.id)] = mutes
        mutes.append({
            'user_id': tid,
            'expire_time': expire_time,
            'permanent': permanent,
            'issued_at': time.time(),
            'duration_minutes': dur if not permanent else None,
            'muted_by': msg.from_user.id,
            'reason': reason
        })

        # Увеличиваем счётчик мутов
        target_user = storage.get_user(msg.chat.id, tid, use_cache=False)
        target_user['total_mutes_survived'] = target_user.get('total_mutes_survived', 0) + 1
        storage.invalidate_user_cache(msg.chat.id, tid)

        storage.mark_dirty()
        await storage.save()

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"🔇 <b>Вы получили мут!</b>\n\n"
                f"⏱️ Длительность: {html.escape(time_str, quote=False)}\n"
                f"📝 Причина: {html.escape(reason, quote=False)}\n"
                f"👮 Выдал: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except:
            pass

        # Сообщение в чат
        await msg.answer(
            "🔇 <b>Мут выдан</b>\n"
            f"{UI_LINE}\n"
            f"👤 Пользователь: {mention(msg.chat.id, tid)}\n"
            f"⏱ Срок: {html.escape(str(time_str), quote=False)}\n"
            f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
            f"👮 Выдал: {mention(msg.chat.id, msg.from_user.id)}",
            disable_web_page_preview=True
        )


    except Exception as e:
        logger.exception("Не удалось выдать мут пользователю %s", tid)
        await msg.answer(f"❌ Не удалось выдать мут: {html.escape(str(e)[:250], quote=False)}")


async def cmd_unmute(msg: Message, cmd_name: str = 'размут'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 1, title='Недостаточно прав', message='Эта команда доступна только модераторам и выше.', example='!размут @user'):
        return

    text = msg.text.strip()
    parts = text.split(maxsplit=1)

    tid = None

    # ПРИОРИТЕТ 1: Ответ на сообщение
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

    # ПРИОРИТЕТ 2: Аргумент @user
    elif len(parts) > 1:
        target_arg = parts[1]
        tid = await get_target(msg, target_arg)

        if not tid:
            return await msg.answer(
                ui_error(
                    "Пользователь не найден",
                    f"Не могу найти <code>{html.escape(str(target_arg), quote=False)}</code> в этом чате. Ответьте на сообщение пользователя или укажите @username.",
                    "!размут @user"
                ),
                disable_web_page_preview=True,
            )

    else:
        return await msg.answer(
            ui_error(
                "Неверный формат",
                "Используйте <code>!размут @user</code> или ответьте на сообщение пользователя и напишите <code>размут</code>",
                "!размут @user"
            ),
            disable_web_page_preview=True,
        )

    if not tid:
        return await msg.answer(ui_error("Не удалось определить пользователя", "Не удалось понять, кого именно вы хотите размутить.", "!размут @user"), disable_web_page_preview=True)

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Нельзя снимать мут с пользователя с равным или более высоким рангом.")

    try:
        # Получаем информацию о муте для лога
        mutes = storage.get_chat(msg.chat.id, 'mutes')
        mute_info = None
        if isinstance(mutes, list):
            for m in mutes:
                if m.get('user_id') == tid:
                    mute_info = m
                    break

        await bot.restrict_chat_member(
            msg.chat.id, tid,
            ChatPermissions(
                can_send_messages=True,
                can_send_media_messages=True,
                can_send_other_messages=True,
                can_add_web_page_previews=True
            )
        )

        # Удаляем из списка мутов
        if isinstance(mutes, list):
            storage.data['mutes'][str(msg.chat.id)] = [m for m in mutes if m.get('user_id') != tid]
            await storage.save()

        reason_text = (
            f"\n📝 Причина мута была: {html.escape(str(mute_info['reason']), quote=False)}"
            if mute_info and mute_info.get('reason') else ""
        )

        # Сообщение в чат
        await msg.answer(f"🔊 {mention(msg.chat.id, tid)} размучен{reason_text}",
                        disable_web_page_preview=True)

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"🔊 <b>Мут снят!</b>\n\n👮 Снял: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except:
            pass


    except Exception as e:
        logger.exception("Не удалось снять мут с пользователя %s", tid)
        await msg.answer(f"❌ Не удалось снять мут: {html.escape(str(e)[:250], quote=False)}")


async def cmd_ban(msg: Message, cmd_name: str = 'бан'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 3, title='Недостаточно прав', message='Для этой команды нужен ранг 3+.', example='!бан @user реклама'):
        return

    text = msg.text.strip()
    parts = text.split(maxsplit=2)

    sender_chat = (
        msg.reply_to_message.sender_chat
        if msg.reply_to_message else None
    )
    if sender_chat:
        if sender_chat.id == msg.chat.id:
            return await msg.answer("❌ Нельзя забанить сам этот чат.")
        reason = text.split(maxsplit=1)[1] if len(parts) > 1 else "Без причины"
        try:
            await bot.ban_chat_sender_chat(msg.chat.id, sender_chat.id)

            chat_id_str = str(msg.chat.id)
            banned_users = storage.data.setdefault('banned_users', {}).setdefault(chat_id_str, [])
            banned_users[:] = [
                ban for ban in banned_users
                if not isinstance(ban, dict) or ban.get('sender_chat_id') != sender_chat.id
            ]
            banned_users.append({
                'sender_chat_id': sender_chat.id,
                'sender_chat_title': sender_chat.title,
                'sender_chat_username': sender_chat.username,
                'banned_by': msg.from_user.id,
                'reason': reason,
                'date': time.time(),
            })
            storage.mark_dirty()
            await storage.save()

            channel_name = html.escape(sender_chat.title or sender_chat.username or str(sender_chat.id), quote=False)
            await msg.answer(
                "🚫 <b>Бан канала выдан</b>\n"
                f"{UI_LINE}\n"
                f"📢 Канал: <b>{channel_name}</b>\n"
                f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
                f"👮 Забанил: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True,
            )
        except Exception as e:
            logger.exception("Не удалось забанить канал-отправитель %s", sender_chat.id)
            await msg.answer(f"❌ Не удалось забанить канал: {html.escape(str(e)[:250], quote=False)}")
        return

    tid = None
    reason = "Без причины"

    # ПРИОРИТЕТ 1: Ответ на сообщение
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            reason = parts[1] if len(parts) > 1 else "Без причины"

    # ПРИОРИТЕТ 2: Аргументы в команде
    elif len(parts) >= 2:
        target_arg = parts[1]
        target_mention = get_target_mention_span(msg, target_arg)
        tid = await get_target(msg, target_arg)

        if not tid:
            return await msg.answer(
                f"❌ Пользователь <code>{html.escape(str(target_arg), quote=False)}</code> не найден!\n\n"
                "💡 Ответьте на сообщение пользователя"
            )

        if target_mention:
            reason = msg.text[target_mention[2]:].strip() or "Без причины"
        elif len(parts) >= 3:
            reason = parts[2]

    else:
        return await msg.answer(
            ui_error(
                "Не указаны аргументы",
                "Нужно указать пользователя и причину",
                "!бан @user реклама"
            )
        )

    if not tid:
        return await msg.answer(ui_error("Не удалось определить пользователя", "Не удалось понять, кого именно вы хотите забанить. Ответьте на сообщение пользователя или укажите @user.", "!бан @user реклама"), disable_web_page_preview=True)

    if tid == msg.from_user.id:
        return await msg.answer(ui_error("Нельзя забанить себя", "Вы не можете забанить самого себя.", "!бан @user реклама"), disable_web_page_preview=True)

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer(ui_error("Анти-модерация", "Нельзя банить пользователя с равным или более высоким уровнем доступа.", "!бан @user реклама"), disable_web_page_preview=True)

    try:
        await bot.ban_chat_member(msg.chat.id, tid)

        # Сохраняем в банлист
        chat_id_str = str(msg.chat.id)
        if 'banned_users' not in storage.data:
            storage.data['banned_users'] = {}
        if chat_id_str not in storage.data['banned_users']:
            storage.data['banned_users'][chat_id_str] = []
        storage.data['banned_users'][chat_id_str].append({
            'user_id': tid,
            'banned_by': msg.from_user.id,
            'reason': reason,
            'date': time.time()
        })

        storage.mark_dirty()
        await storage.save()

        # Сообщение в чат
        await msg.answer(
            "🚫 <b>Бан выдан</b>\n"
            f"{UI_LINE}\n"
            f"👤 Пользователь: {mention(msg.chat.id, tid)}\n"
            f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
            f"👮 Забанил: {mention(msg.chat.id, msg.from_user.id)}",
            disable_web_page_preview=True
        )

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"🚫 <b>Вы были забанены!</b>\n\n"
                f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
                f"👮 Забанил: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except:
            pass

    except Exception as e:
        logger.exception("Не удалось забанить пользователя %s", tid)
        await msg.answer(f"❌ Не удалось забанить: {html.escape(str(e)[:250], quote=False)}")


async def cmd_unban(msg: Message, cmd_name: str = 'разбан'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 3, title='Недостаточно прав', message='Для этой команды нужен ранг 3+.', example='!разбан @user'):
        return

    text = msg.text.strip()
    parts = text.split(maxsplit=1)

    sender_chat = (
        msg.reply_to_message.sender_chat
        if msg.reply_to_message else None
    )
    if sender_chat:
        if sender_chat.id == msg.chat.id:
            return await msg.answer("❌ Нельзя снять бан с самого этого чата.")
        try:
            await bot.unban_chat_sender_chat(msg.chat.id, sender_chat.id)

            chat_id_str = str(msg.chat.id)
            banned_users = storage.data.get('banned_users', {}).get(chat_id_str, [])
            ban_info = next(
                (
                    ban for ban in banned_users
                    if isinstance(ban, dict) and ban.get('sender_chat_id') == sender_chat.id
                ),
                None,
            )
            if ban_info:
                storage.data['banned_users'][chat_id_str] = [
                    ban for ban in banned_users
                    if not isinstance(ban, dict) or ban.get('sender_chat_id') != sender_chat.id
                ]
                storage.mark_dirty()
                await storage.save()

            channel_name = html.escape(
                sender_chat.title or sender_chat.username or str(sender_chat.id),
                quote=False,
            )
            reason_text = (
                f"\n📝 Причина бана: {html.escape(str(ban_info['reason']), quote=False)}"
                if ban_info and ban_info.get('reason') else ""
            )
            await msg.answer(
                f"✅ Бан канала <b>{channel_name}</b> снят{reason_text}",
                disable_web_page_preview=True,
            )
        except Exception as e:
            logger.exception("Не удалось снять бан с канала-отправителя %s", sender_chat.id)
            await msg.answer(f"❌ Не удалось разбанить канал: {html.escape(str(e)[:250], quote=False)}")
        return

    tid = None

    # ПРИОРИТЕТ 1: Ответ на сообщение
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

    # ПРИОРИТЕТ 2: Аргумент @user
    elif len(parts) > 1:
        target_arg = parts[1]
        tid = await get_target(msg, target_arg)

        if not tid:
            return await msg.answer(
                ui_error(
                    "Пользователь не найден",
                    f"Не могу найти <code>{html.escape(str(target_arg), quote=False)}</code> в этом чате. Ответьте на сообщение пользователя или укажите @username.",
                    "!разбан @user"
                ),
                disable_web_page_preview=True,
            )

    else:
        return await msg.answer(
            ui_error(
                "Неверный формат",
                "Используйте <code>!разбан @user</code> или ответьте на сообщение пользователя и напишите <code>разбан</code>",
                "!разбан @user"
            ),
            disable_web_page_preview=True,
        )

    if not tid:
        return await msg.answer(ui_error("Не удалось определить пользователя", "Не удалось понять, кого именно вы хотите разбанить.", "!разбан @user"), disable_web_page_preview=True)

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Нельзя разбанивать пользователя с равным или более высоким рангом.")

    try:
        # Получаем информацию о бане для лога
        chat_id_str = str(msg.chat.id)
        ban_info = None
        if 'banned_users' in storage.data and chat_id_str in storage.data['banned_users']:
            for b in storage.data['banned_users'][chat_id_str]:
                if b.get('user_id') == tid:
                    ban_info = b
                    break

        await bot.unban_chat_member(msg.chat.id, tid)

        # Удаляем из банлиста
        if 'banned_users' in storage.data and chat_id_str in storage.data['banned_users']:
            storage.data['banned_users'][chat_id_str] = [
                b for b in storage.data['banned_users'][chat_id_str]
                if b.get('user_id') != tid
            ]
            storage.mark_dirty()
            await storage.save()

        reason_text = (
            f"\n📝 Причина бана: {html.escape(str(ban_info['reason']), quote=False)}"
            if ban_info and ban_info.get('reason') else ""
        )

        # Сообщение в чат
        await msg.answer(f"✅ {mention(msg.chat.id, tid)} разбанен{reason_text}",
                        disable_web_page_preview=True)

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"✅ <b>Бан снят!</b>\n\n{reason_text}\n👮 Снял: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except:
            pass


    except Exception as e:
        logger.exception("Не удалось выдать предупреждение пользователю %s", tid)
        await msg.answer(f"❌ Не удалось выдать предупреждение: {html.escape(str(e)[:250], quote=False)}")


async def cmd_warn(msg: Message, cmd_name: str = 'пред'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 1, title='Недостаточно прав', message='Эта команда доступна только модераторам и выше.', example='!пред @user 7 флуд'):
        return

    # Определяем какая команда была использована
    text = msg.text.strip()
    command_used = text.split()[0].lower() if text.split() else ''

    parts = msg.text.split(maxsplit=4)
    tid = None
    reason = 'Без причины'
    days = DEFAULT_WARN_DAYS

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            try:
                days = int(parts[1])
                reason = ' '.join(parts[2:]) or 'Без причины'
            except:
                reason = ' '.join(parts[1:]) or 'Без причины'
    else:
        if len(parts) < 2:
            return await msg.answer(
                ui_error(
                    "Не указаны аргументы",
                    "Укажи пользователя, срок и причину",
                    "!пред @user 7 флуд"
                )
            )
        tid = await get_target(msg, parts[1])
        if not tid:
            return await msg.answer("❌ Пользователь не найден")
        target_mention = get_target_mention_span(msg, parts[1])
        if target_mention:
            trailing_args = msg.text[target_mention[2]:].strip().split(maxsplit=1)
            if trailing_args:
                try:
                    days = int(trailing_args[0])
                    reason = trailing_args[1] if len(trailing_args) > 1 else 'Без причины'
                except ValueError:
                    reason = ' '.join(trailing_args) or 'Без причины'
        elif len(parts) > 2:
            try:
                days = int(parts[2])
                reason = ' '.join(parts[3:]) or 'Без причины'
            except ValueError:
                reason = ' '.join(parts[2:]) or 'Без причины'

    if not tid:
        return await msg.answer("❌ Пользователь не найден")

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Анти-модерация!")

    u = storage.get_user(msg.chat.id, tid)
    
    # Добавляем предупреждение
    new_warning = {
        'reason': reason,
        'date': time.time(),
        'expire_date': (datetime.now() + timedelta(days=days)).timestamp() if days > 0 else None,
        'permanent': days <= 0,
        'warned_by': msg.from_user.id
    }
    
    if 'warnings' not in u:
        u['warnings'] = []
    
    u['warnings'].append(new_warning)
    
    # Получаем активные предупреждения
    active = [w for w in u['warnings'] if isinstance(w, dict) and warning_is_active(w)]
    
    storage.mark_dirty()
    await storage.save()
    
    logger.info(f"Предупреждение: {msg.from_user.id} дал {tid}, активных: {len(active)}/{MAX_WARNINGS}")

    # Формируем информативное сообщение
    time_str = f"{days} дн" if days > 0 else "навсегда"

    if len(active) >= MAX_WARNINGS:
        try:
            await bot.ban_chat_member(msg.chat.id, tid)

            chat_id_str = str(msg.chat.id)
            if 'banned_users' not in storage.data:
                storage.data['banned_users'] = {}
            if chat_id_str not in storage.data['banned_users']:
                storage.data['banned_users'][chat_id_str] = []

            storage.data['banned_users'][chat_id_str].append({
                'user_id': tid,
                'banned_by': msg.from_user.id,
                'reason': f"Достигнут лимит предупреждений ({MAX_WARNINGS})",
                'date': time.time()
            })

            storage.mark_dirty()
            await storage.save()

            await msg.answer(
                f"🚫 {mention(msg.chat.id, tid)} забанен по лимиту предупреждений\n"
                f"📊 {len(active)}/{MAX_WARNINGS}\n"
                f"📝 Причина: {html.escape(str(reason), quote=False)}",
                disable_web_page_preview=True
            )

            try:
                await bot.send_message(
                    tid,
                    f"🚫 <b>Вы были забанены!</b>\n\n"
                    f"📊 Достигнут лимит предупреждений: {len(active)}/{MAX_WARNINGS}\n"
                    f"📝 Последняя причина: {html.escape(str(reason), quote=False)}",
                    disable_web_page_preview=True
                )
            except:
                pass
            return

        except Exception as e:
            logger.warning(f"Не удалось забанить пользователя {tid} после предупреждений: {e}")

    # Уведомление в чат
    await msg.answer(
        "⚠️ <b>Предупреждение выдано</b>\n"
        f"{UI_LINE}\n"
        f"👤 Пользователь: {mention(msg.chat.id, tid)}\n"
        f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
        f"⏱ Срок: {html.escape(str(time_str), quote=False)}\n"
        f"📊 Активных: {len(active)}/{MAX_WARNINGS}\n"
        f"👮 Выдал: {mention(msg.chat.id, msg.from_user.id)}",
        disable_web_page_preview=True
    )

    # Уведомление в личку пользователю
    try:
        user_msg = (
            f"⚠️ <b>Вы получили предупреждение!</b>\n\n"
            f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
            f"⏱️ Срок: {html.escape(str(time_str), quote=False)}\n"
            f"📊 Всего активных: {len(active)}/{MAX_WARNINGS}\n\n"
            f"📌 При {MAX_WARNINGS} предупреждениях вы получите бан."
        )
        await bot.send_message(tid, user_msg, disable_web_page_preview=True)
    except Exception as e:
        logger.debug(f"Не удалось отправить ДМ о варне: {e}")


async def show_warnings(msg: Message, cmd_name: str = 'преды'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!преды'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    parts = strip_command_prefix(msg.text, msg.chat.id).split()

    tid = msg.from_user.id
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif len(parts) > 1:
        target = await get_target(msg, parts[1])
        if target:
            tid = target

    wrn = [
        w for w in storage.get_user(msg.chat.id, tid).get('warnings', [])
        if isinstance(w, dict) and warning_is_active(w)
    ]

    if not wrn:
        msg_to_send = await msg.answer(
            ui_error("Нет активных предупреждений", f"У {mention(msg.chat.id, tid)} сейчас нет действующих предупреждений.", "!преды"),
            disable_web_page_preview=True,
        )
        await asyncio.sleep(3)
        try:
            await msg_to_send.delete()
        except:
            pass
        return

    txt = f"⚠️ <b>Предупреждения {mention(msg.chat.id, tid)}:</b> {len(wrn)}/{MAX_WARNINGS}\n\n"
    for i, w in enumerate(wrn, 1):
        expire_date = (
            'навсегда'
            if w.get('permanent') is True
            else datetime.fromtimestamp(w['expire_date']).strftime('%d.%m.%Y')
        )
        txt += (
            f"{i}. {html.escape(str(w.get('reason') or 'Без причины'), quote=False)}\n"
            f"   └ до {expire_date} | выдал: {mention(msg.chat.id, w['warned_by'])}\n"
        )

    await msg.answer(txt, disable_web_page_preview=True)


async def send_moderation_list(msg: Message, title: str, entries: List[str]):
    if not entries:
        return await msg.answer(f"{title}\n\nСписок пуст.")

    lines = [f"{title} ({len(entries)}):\n"]
    shown = 0
    for entry in entries:
        if len("\n".join(lines + [entry])) > 3800:
            break
        lines.append(entry)
        shown += 1

    if shown < len(entries):
        lines.append(f"\nПоказаны первые {shown} из {len(entries)} записей.")
    await msg.answer("\n".join(lines), disable_web_page_preview=True)


async def cmd_mute_list(msg: Message, cmd_name: str = 'мутлист'):
    if not await require_access(
        msg, cmd_name, 1, title='Недостаточно прав',
        message='Список мутов доступен модераторам и выше.',
        example='!мутлист'
    ):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    mutes = storage.get_chat(msg.chat.id, 'mutes')
    if not isinstance(mutes, list):
        logger.error("Некорректный список мутов в чате %s", msg.chat.id)
        return await msg.answer("❌ Не удалось прочитать список мутов.")

    now = time.time()
    active_mutes = [
        mute for mute in mutes
        if isinstance(mute, dict)
        and (
            mute.get('permanent') is True
            or isinstance(mute.get('expire_time'), (int, float)) and mute['expire_time'] > now
        )
    ]
    active_mutes.sort(
        key=lambda mute: float('inf') if mute.get('permanent') else mute['expire_time']
    )

    entries = []
    for mute in active_mutes:
        expires = (
            'навсегда'
            if mute.get('permanent')
            else datetime.fromtimestamp(mute['expire_time']).strftime('%d.%m.%Y %H:%M')
        )
        reason = html.escape(str(mute.get('reason') or 'Без причины')[:120], quote=False)
        entries.append(
            f"• {mention(msg.chat.id, mute['user_id'])} — до {expires}; "
            f"{reason}; выдал: {mention(msg.chat.id, mute.get('muted_by', 'неизвестно'))}"
            if isinstance(mute.get('user_id'), int)
            else f"• Некорректная запись мута (ID: {html.escape(str(mute.get('user_id')), quote=False)})"
        )

    await send_moderation_list(msg, "🔇 Активные муты", entries)


async def cmd_ban_list(msg: Message, cmd_name: str = 'банлист'):
    if not await require_access(
        msg, cmd_name, 3, title='Недостаточно прав',
        message='Список банов доступен с ранга 3+.',
        example='!банлист'
    ):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    bans_by_chat = storage.data.get('banned_users', {})
    if not isinstance(bans_by_chat, dict):
        logger.error("Некорректное хранилище банов")
        return await msg.answer("❌ Не удалось прочитать список банов.")
    banned_users = bans_by_chat.get(str(msg.chat.id), [])
    if not isinstance(banned_users, list):
        logger.error("Некорректный список банов в чате %s", msg.chat.id)
        return await msg.answer("❌ Не удалось прочитать список банов.")

    stale_bans = []
    bans_by_user = {}
    bans_by_sender_chat = {}
    for ban in banned_users:
        if isinstance(ban, dict) and isinstance(ban.get('sender_chat_id'), int):
            sender_chat_id = ban['sender_chat_id']
            previous = bans_by_sender_chat.get(sender_chat_id)
            ban_date = ban.get('date') if isinstance(ban.get('date'), (int, float)) else 0
            previous_date = (
                previous.get('date') if previous and isinstance(previous.get('date'), (int, float))
                else 0
            )
            if previous is None or ban_date > previous_date:
                if previous is not None:
                    stale_bans.append(previous)
                bans_by_sender_chat[sender_chat_id] = ban
            else:
                stale_bans.append(ban)
            continue

        if not isinstance(ban, dict) or not isinstance(ban.get('user_id'), int):
            stale_bans.append(ban)
            continue

        user_id = ban['user_id']
        try:
            member = await bot.get_chat_member(msg.chat.id, user_id)
        except Exception as e:
            logger.error(
                "Не удалось проверить статус бана пользователя %s в чате %s: %s",
                user_id, msg.chat.id, e
            )
            return await msg.answer(
                "❌ Не удалось проверить актуальность банов в Telegram. "
                "Список не изменён; попробуйте позже."
            )

        if member.status != 'kicked':
            stale_bans.append(ban)
            continue

        previous = bans_by_user.get(user_id)
        ban_date = ban.get('date') if isinstance(ban.get('date'), (int, float)) else 0
        previous_date = (
            previous.get('date') if previous and isinstance(previous.get('date'), (int, float))
            else 0
        )
        if previous is None or ban_date > previous_date:
            if previous is not None:
                stale_bans.append(previous)
            bans_by_user[user_id] = ban
        else:
            stale_bans.append(ban)

    active_bans = list(bans_by_user.values()) + list(bans_by_sender_chat.values())
    if stale_bans:
        stale_ids = {id(ban) for ban in stale_bans}
        storage.data['banned_users'][str(msg.chat.id)] = [
            ban for ban in banned_users if id(ban) not in stale_ids
        ]
        storage.mark_dirty()
        await storage.save()

    active_bans.sort(
        key=lambda ban: ban.get('date') if isinstance(ban.get('date'), (int, float)) else 0,
        reverse=True
    )
    entries = []
    for ban in active_bans:
        banned_at = ban.get('date')
        date_text = (
            datetime.fromtimestamp(banned_at).strftime('%d.%m.%Y %H:%M')
            if isinstance(banned_at, (int, float)) else 'дата неизвестна'
        )
        reason = html.escape(str(ban.get('reason') or 'Без причины')[:120], quote=False)
        if isinstance(ban.get('user_id'), int):
            entries.append(
                f"• {mention(msg.chat.id, ban['user_id'])} — с {date_text}; {reason}; "
                f"выдал: {mention(msg.chat.id, ban.get('banned_by', 'неизвестно'))}"
            )
        elif isinstance(ban.get('sender_chat_id'), int):
            sender_title = html.escape(
                str(ban.get('sender_chat_title') or ban.get('sender_chat_username') or ban['sender_chat_id']),
                quote=False,
            )
            sender_username = ban.get('sender_chat_username')
            sender_label = (
                f'<a href="https://t.me/{html.escape(str(sender_username), quote=True)}">{sender_title}</a>'
                if sender_username else f"<b>{sender_title}</b>"
            )
            entries.append(
                f"• 📢 {sender_label} — с {date_text}; {reason}; "
                f"выдал: {mention(msg.chat.id, ban.get('banned_by', 'неизвестно'))}"
            )
        else:
            entries.append(
                f"• Некорректная запись бана (ID: "
                f"{html.escape(str(ban.get('user_id')), quote=False)})"
            )

    await send_moderation_list(msg, "🚫 Активные баны", entries)


async def cmd_warn_list(msg: Message, cmd_name: str = 'варнлист'):
    if not await require_access(
        msg, cmd_name, 1, title='Недостаточно прав',
        message='Общий список предупреждений доступен модераторам и выше.',
        example='!варнлист'
    ):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    users_by_chat = storage.data.get('users', {})
    if not isinstance(users_by_chat, dict):
        logger.error("Некорректное хранилище пользователей")
        return await msg.answer("❌ Не удалось прочитать список предупреждений.")
    users = users_by_chat.get(str(msg.chat.id), {})
    if not isinstance(users, dict):
        logger.error("Некорректные данные пользователей в чате %s", msg.chat.id)
        return await msg.answer("❌ Не удалось прочитать список предупреждений.")

    now = time.time()
    warnings = []
    for user_id, user_data in users.items():
        if not isinstance(user_data, dict):
            continue
        try:
            uid = int(user_id)
        except (TypeError, ValueError):
            logger.warning("Некорректный ID пользователя в списке чата %s: %s", msg.chat.id, user_id)
            continue
        user_warnings = user_data.get('warnings', [])
        if not isinstance(user_warnings, list):
            logger.warning("Некорректный список предупреждений пользователя %s в чате %s", uid, msg.chat.id)
            continue
        for warning in user_warnings:
            if (
                isinstance(warning, dict)
                and warning_is_active(warning, now)
            ):
                warnings.append((uid, warning))

    warnings.sort(key=lambda item: item[1].get('date', 0), reverse=True)
    entries = []
    for uid, warning in warnings:
        expire_date = (
            'навсегда'
            if warning.get('permanent') is True
            else datetime.fromtimestamp(warning['expire_date']).strftime('%d.%m.%Y')
        )
        reason = html.escape(str(warning.get('reason') or 'Без причины')[:120], quote=False)
        issuer = warning.get('warned_by', 'неизвестно')
        entries.append(
            f"• {mention(msg.chat.id, uid)} — до {expire_date}; {reason}; "
            f"выдал: {mention(msg.chat.id, issuer) if isinstance(issuer, int) else html.escape(str(issuer), quote=False)}"
        )

    await send_moderation_list(msg, "⚠️ Активные предупреждения", entries)


async def cmd_unwarn(msg: Message, cmd_name: str = 'снятьпред'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 2, title='Недостаточно прав', message='Эта команда доступна только модераторам 2+ и выше.', example='!снятьпред @user 1'):
        return

    parts = msg.text.split()

    tid = None
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif len(parts) > 1:
        tid = await get_target(msg, parts[1])

    if not tid:
        return await msg.answer(
            ui_error(
                "Неверный формат",
                "Используйте <code>!снятьпред @user [номер]</code>, <code>!снятьпред @user</code> или ответьте на сообщение пользователя.",
                "!снятьпред @user 1"
            ),
            disable_web_page_preview=True,
        )

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Нельзя снимать предупреждения с пользователя с равным или более высоким рангом.")

    u = storage.get_user(msg.chat.id, tid)
    active = [
        (i, w) for i, w in enumerate(u.get('warnings', []))
        if isinstance(w, dict) and warning_is_active(w)
    ]

    if not active:
        chat_msg = await msg.answer(
            ui_error("Нет активных предупреждений", f"У {mention(msg.chat.id, tid)} сейчас нет действующих предупреждений.", "!преды"),
            disable_web_page_preview=True,
        )
        await asyncio.sleep(3)
        try:
            await chat_msg.delete()
        except:
            pass
        return

    num_idx = 2 if not msg.reply_to_message else 1
    if len(parts) > num_idx and parts[num_idx].isdigit():
        idx = int(parts[num_idx]) - 1
        if 0 <= idx < len(active):
            removed_warning = u['warnings'][active[idx][0]]
            del u['warnings'][active[idx][0]]

            storage.mark_dirty()
            await storage.save()

            logger.info(f"Снято предупреждение #{idx + 1} у {tid}")

            chat_msg = await msg.answer(
                f"✅ Снято предупреждение #{idx + 1} у {mention(msg.chat.id, tid)}\n"
                f"📝 Причина была: {html.escape(str(removed_warning.get('reason') or 'Без причины'), quote=False)}",
                disable_web_page_preview=True,
            )
            await asyncio.sleep(3)
            try:
                await chat_msg.delete()
            except:
                pass
            return
        else:
            return await msg.answer(ui_error("Предупреждение не найдено", f"У пользователя {mention(msg.chat.id, tid)} нет предупреждения под номером {idx + 1}.", "!снятьпред @user 1"), disable_web_page_preview=True)

    before_count = len(active)
    for idx, _ in sorted(active, key=lambda x: x[0], reverse=True):
        del u['warnings'][idx]

    storage.mark_dirty()
    await storage.save()

    logger.info(f"Снято {before_count} предупреждений у {tid}")

    await msg.answer(
        f"✅ Снято <b>{before_count}</b> предупреждений у {mention(msg.chat.id, tid)}",
        disable_web_page_preview=True,
    )


async def cmd_del(msg: Message, cmd_name: str = '-смс'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 1, title='Недостаточно прав', message='Эта команда доступна только модераторам и выше.', example='! -смс'):
        return
    if msg.reply_to_message:
        try:
            await msg.reply_to_message.delete()
            await msg.delete()
        except Exception:
            await msg.answer(ui_error("Не удалось удалить сообщение", "Бот не может удалить это сообщение. Возможно, оно слишком старое или у бота нет прав.", "-смс"), disable_web_page_preview=True)
    else:
        await msg.answer(ui_error("Неверный формат", "Ответьте на сообщение, которое нужно удалить, и затем используйте <code>-смс</code>.", "-смс"), disable_web_page_preview=True)


async def cmd_pin(msg: Message, cmd_name: str = 'пин'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 2, title='Недостаточно прав', message='Эта команда доступна только модераторам 2+ и выше.', example='!пин'):
        return
    if msg.reply_to_message:
        try:
            await msg.reply_to_message.pin()
        except Exception:
            await msg.answer(ui_error("Не удалось закрепить сообщение", "Бот не может закрепить это сообщение. Возможно, у бота нет прав или сообщение уже закреплено.", "!пин"), disable_web_page_preview=True)
    else:
        await msg.answer(ui_error("Не выбрано сообщение", "Ответьте на сообщение, которое нужно закрепить, и затем используйте <code>!пин</code>.", "!пин"), disable_web_page_preview=True)


async def cmd_purge(msg: Message, cmd_name: str = 'очистить'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 2, title='Недостаточно прав', message='Эта команда доступна только модераторам 2+ и выше.', example='!очистить'):
        return

    if not msg.reply_to_message:
        return await msg.answer(
            ui_error(
                "Как использовать очистку",
                "1. Ответьте на сообщение, с которого хотите начать очистку\n2. Напишите <code>очистить</code>\n\n📌 Будут удалены все сообщения от отвеченного и выше.",
                "!очистить"
            ),
            disable_web_page_preview=True,
        )

    try:
        # Удаляем сообщение с командой
        await msg.delete()

        deleted = 0
        current_id = msg.message_id
        target_id = msg.reply_to_message.message_id

        # Удаляем сообщения от текущего ID до целевого
        for message_id in range(current_id - 1, target_id - 1, -1):
            try:
                await bot.delete_message(chat_id=msg.chat.id, message_id=message_id)
                deleted += 1
                await asyncio.sleep(0.1)  # Пауза чтобы не превысить лимиты API
            except Exception as e:
                # Пропускаем сообщения, которые нельзя удалить
                # (слишком старые, уже удалённые, или нет прав)
                continue

        # Отправляем результат и удаляем его через 3 секунды
        result_msg = await msg.answer(f"✅ Удалено {deleted} сообщений")
        await asyncio.sleep(3)
        await result_msg.delete()

    except Exception as e:
        error_msg = str(e)
        if "message can't be deleted" in error_msg.lower():
            await msg.answer(ui_error("Нельзя удалить часть сообщений", "Сообщения слишком старые: Telegram запрещает удалять сообщения старше 48 часов.", "!очистить"), disable_web_page_preview=True)
        elif "not enough rights" in error_msg.lower():
            await msg.answer(ui_error("Нет прав на удаление", "У бота нет прав на удаление сообщений в этом чате.", "!очистить"), disable_web_page_preview=True)
        else:
            await msg.answer(ui_error("Ошибка очистки", f"Не удалось завершить очистку: {html.escape(error_msg[:120], quote=False)}", "!очистить"), disable_web_page_preview=True)


# ==================== Награды ====================

async def cmd_give_award(msg: Message, cmd_name: str = 'наградить'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 4):
        return await msg.answer("❌ Недостаточно прав! Требуется ранг 4+")

    text = msg.text.strip()

    text = strip_command_prefix(text, msg.chat.id)

    if text.lower().startswith('наградить'):
        remaining = text[9:].strip()
        if remaining.lower().startswith('степень'):
            remaining = remaining[7:].strip()
        text = remaining
    else:
        return await msg.answer("❌ Используйте: <code>наградить [степень] @user Название</code>")

    if not text:
        return await msg.answer(
            "❌ Не указаны параметры\n\n📝 <b>Примеры:</b>\n• <code>наградить 1 @user Название</code>\n• <code>наградить @user Название</code> (степень 1)\n• <code>наградить Название</code> — ответом")

    parts = text.split(None, 1)

    degree = 1

    if parts[0].isdigit():
        degree = int(parts[0])
        if degree < 1 or degree > 8:
            return await msg.answer("❌ Степень от 1 до 8")
        if len(parts) > 1:
            text = parts[1]
        else:
            text = ""
    elif len(parts) > 0:
        text = ' '.join(parts)

    if not text:
        return await msg.answer("❌ Укажите получателя и название награды")

    tid = None
    award_name = None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        award_name = text
    else:
        parts = text.split(None, 1)
        target_mention = get_target_mention_span(msg, parts[0])
        potential_tid = await get_target(msg, parts[0])

        if potential_tid:
            tid = potential_tid
            award_name = (
                msg.text[target_mention[2]:].strip()
                if target_mention
                else parts[1] if len(parts) > 1 else None
            )
        else:
            return await msg.answer("❌ Пользователь не найден. Используйте @username или ответьте на сообщение")

    if not tid:
        return await msg.answer("❌ Не удалось определить получателя")

    if not award_name or not award_name.strip():
        return await msg.answer("❌ Укажите название награды")

    award_name = award_name.strip()

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Анти-модерация запрещает")

    award = {
        'name': award_name,
        'degree': degree,
        'given_by': msg.from_user.id,
        'given_at': time.time()
    }

    target_user = storage.get_user(msg.chat.id, tid)
    if 'awards' not in target_user:
        target_user['awards'] = []
    target_user['awards'].append(award)

    storage.invalidate_user_cache(msg.chat.id, tid)
    storage.mark_dirty()
    await storage.save()

    medals = {1: '🥉', 2: '🥈', 3: '🏆', 4: '💎', 5: '👑', 6: '🌟', 7: '💫', 8: '⭐'}
    medal = medals.get(degree, '🏅')

    total = len(target_user['awards'])
    safe_award_name = html.escape(award_name, quote=False)

    await msg.answer(
        f"{medal} <b>Награда вручена!</b>\n\n"
        f"👤 Получатель: {mention(msg.chat.id, tid)}\n"
        f"🏅 Награда: {safe_award_name}\n"
        f"⭐ Степень: {degree}\n"
        f"📊 Всего наград: {total}\n"
        f"👮 Выдал: {mention(msg.chat.id, msg.from_user.id)}",
        disable_web_page_preview=True
    )


async def cmd_rem_award(msg: Message, cmd_name: str = 'снять награду'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 4):
        return await msg.answer("❌ Недостаточно прав! Требуется ранг 4+")

    text = msg.text.strip()

    text = strip_command_prefix(text, msg.chat.id)

    for cmd_word in ['снять награду', 'снятьнаграду']:
        if text.lower().startswith(cmd_word):
            text = text[len(cmd_word):].strip()
            break
    else:
        return await msg.answer("❌ Используйте: <code>снять награду @user Название</code>")

    if not text:
        return await msg.answer(
            "❌ Укажите название награды\n\n📝 <b>Использование:</b>\n• <code>снять награду Название</code> — ответом\n• <code>снять награду @user Название</code>")

    tid = None
    award_name = None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        award_name = text
    else:
        parts = text.split(None, 1)
        target_mention = get_target_mention_span(msg, parts[0])
        potential_tid = await get_target(msg, parts[0])

        if potential_tid:
            tid = potential_tid
            award_name = (
                msg.text[target_mention[2]:].strip()
                if target_mention
                else parts[1] if len(parts) > 1 else None
            )
        else:
            return await msg.answer("❌ Пользователь не найден")

    if not tid:
        return await msg.answer("❌ Не удалось определить пользователя")

    if not award_name or len(award_name.strip()) == 0:
        return await msg.answer("❌ Укажите название награды для снятия")

    award_name = award_name.strip()

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Нельзя снимать награды у пользователя с равным или более высоким рангом.")

    target_user = storage.get_user(msg.chat.id, tid)
    awards = target_user.get('awards', [])

    if not awards:
        return await msg.answer(f"❌ У {mention(msg.chat.id, tid)} нет наград", disable_web_page_preview=True)

    found_award = None
    for award in awards:
        if award['name'].lower() == award_name.lower():
            found_award = award
            break

    if found_award:
        awards.remove(found_award)
        storage.invalidate_user_cache(msg.chat.id, tid)
        storage.mark_dirty()
        await storage.save()

        safe_award_name = html.escape(str(found_award.get('name') or ''), quote=False)
        await msg.answer(
            f"✅ <b>Награда снята</b>\n\n"
            f"👤 Пользователь: {mention(msg.chat.id, tid)}\n"
            f"🏅 Награда: {safe_award_name}\n"
            f"⭐ Степень: {found_award.get('degree', '?')}\n"
            f"📊 Осталось наград: {len(awards)}",
            disable_web_page_preview=True
        )
        return

    similar = [a for a in awards if award_name.lower() in a['name'].lower()]
    if similar:
        similar_list = "\n".join([
            f"• {html.escape(str(a.get('name') or ''), quote=False)} (ст. {a.get('degree', '?')})"
            for a in similar[:10]
        ])
        safe_award_name = html.escape(award_name, quote=False)
        return await msg.answer(f"❌ Награда '{safe_award_name}' не найдена\n\n🔍 <b>Похожие:</b>\n{similar_list}",
                                disable_web_page_preview=True)

    await msg.answer(
                     f"❌ Награда '{html.escape(award_name, quote=False)}' не найдена у {mention(msg.chat.id, tid)}",
                     disable_web_page_preview=True)


async def cmd_my_awards(msg: Message, cmd_name: str = 'мои награды'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    tid = msg.from_user.id

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    else:
        text = msg.text.strip()
        text = strip_command_prefix(text, msg.chat.id)
        if text.lower().startswith('мои награды'):
            text = text[10:].strip()
        if text:
            target = await get_target(msg, text)
            if target:
                tid = target

    awards = storage.get_user(msg.chat.id, tid).get('awards', [])

    if not awards:
        if tid == msg.from_user.id:
            return await msg.answer("🏆 У вас пока нет наград")
        else:
            return await msg.answer(f"🏆 У {mention(msg.chat.id, tid)} пока нет наград", disable_web_page_preview=True)

    sorted_awards = sorted(awards, key=lambda x: (-x.get('degree', 0), -x.get('given_at', 0)))

    txt = f"🏆 <b>Награды {mention(msg.chat.id, tid)} ({len(awards)}):</b>\n\n"

    for award in sorted_awards:
        degree = award.get('degree', 1)
        name = award.get('name', 'Без названия')

        if degree >= 8:
            medal = "👑"
        elif degree >= 5:
            medal = "💎"
        elif degree >= 3:
            medal = "🏆"
        elif degree >= 2:
            medal = "🥈"
        else:
            medal = "🥉"

        txt += f"{medal} <b>{html.escape(str(name), quote=False)}</b> (ст. {degree})\n"

    await msg.answer(txt, disable_web_page_preview=True)


async def cmd_top_awards(msg: Message, cmd_name: str = 'топ наград'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    awards_stats = []
    for uid, data in storage.data['users'].get(str(msg.chat.id), {}).items():
        awards = data.get('awards', [])
        if awards:
            total_degree = sum(a.get('degree', 0) for a in awards)
            awards_stats.append({
                'uid': int(uid),
                'count': len(awards),
                'total_degree': total_degree
            })

    if not awards_stats:
        return await msg.answer("🏆 Пока никто не получил наград")

    awards_stats.sort(key=lambda x: (-x['count'], -x['total_degree']))

    txt = f"🏆 <b>Топ по наградам ({len(awards_stats)}):</b>\n\n"

    for i, stat in enumerate(awards_stats[:20], 1):
        medal = "🥇" if i == 1 else "🥈" if i == 2 else "🥉" if i == 3 else f"{i}."
        txt += f"{medal} {mention(msg.chat.id, stat['uid'])}: {stat['count']} нагр.\n"

    await msg.answer(txt, disable_web_page_preview=True)


# ==================== Браки ====================

async def cmd_marry(msg: Message, cmd_name: str = 'брак'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    parts = msg.text.split()

    tid = None
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif len(parts) > 1:
        tid = await get_target(msg, parts[1])

    if not tid:
        return await msg.answer("❌ Использование:\n<code>брак @user</code> или ответьте на сообщение")

    if tid == msg.from_user.id:
        return await msg.answer("❌ Нельзя жениться на себе!")

    if tid == bot.id:
        return await msg.answer("❌ Я бот, мне нельзя предлагать брак!")

    user = storage.get_user(msg.chat.id, msg.from_user.id)
    target = storage.get_user(msg.chat.id, tid)

    if user.get('marriage_partner'):
        partner_name = mention(msg.chat.id, user['marriage_partner'])
        return await msg.answer(f"❌ Вы уже в браке с {partner_name}!", disable_web_page_preview=True)

    if target.get('marriage_partner'):
        return await msg.answer(f"❌ {mention(msg.chat.id, tid)} уже в браке!", disable_web_page_preview=True)

    if target.get('pending_marriage') == msg.from_user.id:
        return await msg.answer("❌ Вы уже отправили предложение этому пользователю!")

    target['pending_marriage'] = msg.from_user.id
    user['pending_marriage'] = tid
    user['proposals_sent'] = user.get('proposals_sent', 0) + 1
    storage.mark_dirty()
    await storage.save()

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="💍 Принять", callback_data=f"marry_accept_{msg.from_user.id}"),
            InlineKeyboardButton(text="❌ Отклонить", callback_data=f"marry_reject_{msg.from_user.id}")
        ]
    ])

    await msg.answer(
        f"💍 <b>Предложение брака!</b>\n\n"
        f"{mention(msg.chat.id, msg.from_user.id)} предлагает брак {mention(msg.chat.id, tid)}!\n\n"
        f"Ожидание ответа...",
        reply_markup=kb,
        disable_web_page_preview=True
    )


@router.callback_query(F.data.startswith('marry_'))
async def marry_callback(call: CallbackQuery):
    parts = call.data.split('_')
    action = parts[1]
    proposer_id = int(parts[2])

    target_user = storage.get_user(call.message.chat.id, call.from_user.id)
    proposer_user = storage.get_user(call.message.chat.id, proposer_id)

    if target_user.get('pending_marriage') != proposer_id:
        await call.answer("❌ Это предложение не для вас!", show_alert=True)
        return

    if action == 'accept':
        if target_user.get('marriage_partner'):
            await call.answer("❌ Вы уже в браке!", show_alert=True)
            return
        if proposer_user.get('marriage_partner'):
            await call.answer("❌ Предложивший уже в браке!", show_alert=True)
            return

        current_time = time.time()
        target_user['marriage_partner'] = proposer_id
        proposer_user['marriage_partner'] = call.from_user.id
        target_user['marriage_date'] = current_time
        proposer_user['marriage_date'] = current_time
        target_user['pending_marriage'] = None
        proposer_user['pending_marriage'] = None

        target_user['marriage_count'] = target_user.get('marriage_count', 0) + 1
        proposer_user['marriage_count'] = proposer_user.get('marriage_count', 0) + 1

        marriage_id = f"{min(call.from_user.id, proposer_id)}_{max(call.from_user.id, proposer_id)}"
        storage.get_chat(call.message.chat.id, 'marriages')[marriage_id] = {
            'user1': min(call.from_user.id, proposer_id),
            'user2': max(call.from_user.id, proposer_id),
            'date': current_time
        }

        storage.mark_dirty()
        await storage.save()

        await call.message.edit_text(
            f"💒 <b>Поздравляем!</b>\n\n"
            f"💍 {mention(call.message.chat.id, proposer_id)} и {mention(call.message.chat.id, call.from_user.id)} "
            f"теперь в браке!\n\n"
            f"🎉 Совет да любовь!",
            reply_markup=None,
            disable_web_page_preview=True
        )

    elif action == 'reject':
        target_user['pending_marriage'] = None
        proposer_user['pending_marriage'] = None
        target_user['proposals_rejected'] = target_user.get('proposals_rejected', 0) + 1
        storage.mark_dirty()
        await storage.save()

        await call.message.edit_text(
            f"💔 <b>Предложение отклонено</b>\n\n"
            f"{mention(call.message.chat.id, call.from_user.id)} отклонил(а) предложение "
            f"{mention(call.message.chat.id, proposer_id)}",
            reply_markup=None,
            disable_web_page_preview=True
        )

    await call.answer()


async def cmd_accept_marry(msg: Message, cmd_name: str = 'принять брак'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    u = storage.get_user(msg.chat.id, msg.from_user.id)
    proposer_id = u.get('pending_marriage')

    if not proposer_id:
        return await msg.answer("❌ У вас нет активных предложений брака!")

    proposer = storage.get_user(msg.chat.id, proposer_id)

    if u.get('marriage_partner'):
        return await msg.answer("❌ Вы уже в браке!")
    if proposer.get('marriage_partner'):
        return await msg.answer("❌ Предложивший уже в браке!")

    current_time = time.time()
    u['marriage_partner'] = proposer_id
    proposer['marriage_partner'] = msg.from_user.id
    u['marriage_date'] = current_time
    proposer['marriage_date'] = current_time
    u['pending_marriage'] = None
    proposer['pending_marriage'] = None

    u['marriage_count'] = u.get('marriage_count', 0) + 1
    proposer['marriage_count'] = proposer.get('marriage_count', 0) + 1

    marriage_id = f"{min(msg.from_user.id, proposer_id)}_{max(msg.from_user.id, proposer_id)}"
    storage.get_chat(msg.chat.id, 'marriages')[marriage_id] = {
        'user1': min(msg.from_user.id, proposer_id),
        'user2': max(msg.from_user.id, proposer_id),
        'date': current_time
    }

    storage.mark_dirty()
    await storage.save()

    await msg.answer(
        f"💒 <b>Поздравляем!</b>\n\n"
        f"💍 {mention(msg.chat.id, proposer_id)} и {mention(msg.chat.id, msg.from_user.id)} "
        f"теперь в браке!\n\n"
        f"🎉 Совет да любовь!",
        disable_web_page_preview=True
    )


async def cmd_reject_marry(msg: Message, cmd_name: str = 'отклонить брак'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    u = storage.get_user(msg.chat.id, msg.from_user.id)
    proposer_id = u.get('pending_marriage')

    if not proposer_id:
        return await msg.answer("❌ У вас нет активных предложений брака!")

    proposer = storage.get_user(msg.chat.id, proposer_id)
    u['pending_marriage'] = None
    proposer['pending_marriage'] = None
    u['proposals_rejected'] = u.get('proposals_rejected', 0) + 1
    storage.mark_dirty()
    await storage.save()

    await msg.answer(f"💔 Предложение от {mention(msg.chat.id, proposer_id)} отклонено.", disable_web_page_preview=True)


async def cmd_divorce(msg: Message, cmd_name: str = 'развод'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    u = storage.get_user(msg.chat.id, msg.from_user.id)
    partner_id = u.get('marriage_partner')

    if not partner_id:
        return await msg.answer("❌ Вы не состоите в браке!")

    partner_name = mention(msg.chat.id, partner_id)

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="✅ Да, развестись", callback_data=f"divorce_confirm_{msg.from_user.id}"),
            InlineKeyboardButton(text="❌ Нет, оставить", callback_data=f"divorce_cancel_{msg.from_user.id}")
        ]
    ])

    await msg.answer(
        f"💔 <b>Вы уверены?</b>\n\n"
        f"Вы хотите развестись с {partner_name}?\n"
        f"Это действие нельзя отменить!",
        reply_markup=kb,
        disable_web_page_preview=True
    )


@router.callback_query(F.data.startswith('divorce_'))
async def divorce_callback(call: CallbackQuery):
    parts = call.data.split('_')
    action = parts[1]
    user_id = int(parts[2])

    if call.from_user.id != user_id:
        await call.answer("❌ Это не ваша кнопка!", show_alert=True)
        return

    if action == 'confirm':
        u = storage.get_user(call.message.chat.id, user_id)
        partner_id = u.get('marriage_partner')

        if not partner_id:
            await call.answer("❌ Вы уже не в браке!", show_alert=True)
            return

        partner = storage.get_user(call.message.chat.id, partner_id)
        partner_name = mention(call.message.chat.id, partner_id)

        u['marriage_partner'] = None
        u['marriage_date'] = None
        partner['marriage_partner'] = None
        partner['marriage_date'] = None

        u['divorced_count'] = u.get('divorced_count', 0) + 1
        partner['divorced_count'] = partner.get('divorced_count', 0) + 1

        marriage_id = f"{min(user_id, partner_id)}_{max(user_id, partner_id)}"
        storage.get_chat(call.message.chat.id, 'marriages').pop(marriage_id, None)

        storage.mark_dirty()
        await storage.save()

        await call.message.edit_text(
            f"💔 <b>Брак расторгнут</b>\n\n"
            f"{mention(call.message.chat.id, user_id)} и {partner_name} больше не в браке.",
            reply_markup=None,
            disable_web_page_preview=True
        )

    elif action == 'cancel':
        await call.message.edit_text("✅ Развод отменён. Вы остаётесь в браке!", reply_markup=None)

    await call.answer()


async def cmd_marriages_list(msg: Message):
    marriages = storage.get_chat(msg.chat.id, 'marriages')
    if not marriages:
        return await msg.answer("💔 В чате пока нет браков")

    txt = "💍 <b>Браки в чате:</b>\n\n"
    for i, (mid, data) in enumerate(marriages.items(), 1):
        user1 = mention(msg.chat.id, data['user1'])
        user2 = mention(msg.chat.id, data['user2'])
        date = datetime.fromtimestamp(data['date']).strftime('%d.%m.%Y')
        days = int((time.time() - data['date']) / 86400)
        txt += f"{i}. 💑 {user1} ❤️ {user2}\n   📅 {date} ({days} дн)\n\n"

    await msg.answer(txt, disable_web_page_preview=True)


# ==================== Фразы ====================

async def cmd_add_phrase(msg: Message, cmd_name: str = 'добавить фразу'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 1):
        return

    parts = msg.text.split(maxsplit=4)
    anywhere = len(parts) > 2 and parts[2] == '-any'
    idx = 3 if anywhere else 2

    if len(parts) < idx + 2:
        return await msg.answer(
            "❌ <code>добавить фразу [-any] слово ответ</code>\n\nМожно добавлять несколько ответов на одно слово!")

    trigger = parts[idx].lower()
    response = ' '.join(parts[idx + 1:])

    phrases = storage.get_chat(msg.chat.id, 'phrases')
    if not isinstance(phrases, list):
        phrases = []
        storage.data['phrases'][str(msg.chat.id)] = phrases

    # Просто добавляем новую фразу, даже если триггер уже существует
    phrases.append({
        'trigger': trigger,
        'response': response,
        'anywhere': anywhere,
        'added_by': msg.from_user.id,
        'uses': 0,
        'created_at': time.time()
    })

    # Подсчитываем сколько всего фраз с таким триггером
    count = sum(1 for p in phrases if p['trigger'] == trigger and p.get('anywhere', False) == anywhere)

    storage.get_user(msg.chat.id, msg.from_user.id)['phrases_added'] = storage.get_user(msg.chat.id,
                                                                                        msg.from_user.id).get(
        'phrases_added', 0) + 1
    storage.mark_dirty()
    await storage.save()

    await msg.answer(
        f"✅ Фраза добавлена: {html.escape(trigger, quote=False)} → "
        f"{html.escape(response, quote=False)}\n"
        f"📊 Теперь у этого слова {count} вариант(ов) ответа"
    )


async def cmd_list_phrases(msg: Message, cmd_name: str = 'фразы'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    phrases = storage.get_chat(msg.chat.id, 'phrases')
    if not isinstance(phrases, list) or not phrases:
        return await msg.answer("📝 Нет фраз")

    # Группируем по триггерам
    grouped = {}
    for p in phrases:
        trigger = p['trigger']
        if trigger not in grouped:
            grouped[trigger] = []
        grouped[trigger].append(p)

    txt = f"📝 <b>Фразы ({len(phrases)}):</b>\n\n"

    for trigger, items in list(grouped.items())[:20]:
        anywhere_icon = '🌐' if items[0].get('anywhere') else '📌'
        responses_count = len(items)
        # Показываем первый ответ как пример
        preview = items[0]['response'][:30] + "..." if len(items[0]['response']) > 30 else items[0]['response']
        txt += (
            f"{anywhere_icon} <b>{html.escape(str(trigger), quote=False)}</b>: "
            f"{responses_count} отв. (напр. {html.escape(str(preview), quote=False)})\n"
        )

        # Опционально: показать все ответы
        if len(items) <= 3:
            for p in items:
                txt += f"   └ {html.escape(str(p.get('response') or '')[:40], quote=False)}\n"

    await msg.answer(txt)


async def cmd_phrase_stats(msg: Message):
    phrases = storage.get_chat(msg.chat.id, 'phrases')
    if not isinstance(phrases, list) or not phrases:
        return await msg.answer("📝 Нет фраз")
    sorted_p = sorted(phrases, key=lambda x: x.get('uses', 0), reverse=True)
    txt = "📊 <b>Статистика фраз:</b>\n\n"
    for p in sorted_p[:20]:
        txt += f"• {html.escape(str(p.get('trigger') or ''), quote=False)}: {p.get('uses', 0)} раз\n"
    await msg.answer(txt)


async def cmd_del_phrase(msg: Message, cmd_name: str = 'удалить фразу'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 1):
        return

    parts = msg.text.split(maxsplit=2)
    if len(parts) < 2:
        return await msg.answer("❌ <code>удалить фразу слово [текст]</code>\n\n"
                                "• <code>удалить фразу бот</code> - удалить ВСЕ фразы с триггером 'бот'\n"
                                "• <code>удалить фразу бот пошел</code> - удалить конкретную фразу")

    trigger = parts[1].lower()
    response_text = parts[2] if len(parts) > 2 else None

    phrases = storage.get_chat(msg.chat.id, 'phrases')
    if not isinstance(phrases, list) or not phrases:
        return await msg.answer("❌ Фраз не найдено")

    before_count = len(phrases)

    if response_text:
        # Удаляем конкретную фразу
        phrases[:] = [p for p in phrases if
                      not (p['trigger'] == trigger and p['response'].lower() == response_text.lower())]
        removed = before_count - len(phrases)
        await msg.answer(
            f"✅ Удалено {removed} фраз с ответом '{html.escape(response_text, quote=False)}'"
        )
    else:
        # Удаляем все фразы с таким триггером
        phrases[:] = [p for p in phrases if p['trigger'] != trigger]
        removed = before_count - len(phrases)
        await msg.answer(
            f"✅ Удалено {removed} фраз с триггером '{html.escape(trigger, quote=False)}'"
        )

    storage.mark_dirty()
    await storage.save()


async def cmd_phrase_show(msg: Message, cmd_name: str = 'показать фразу'):
    """Показать все ответы на определённую фразу"""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    parts = msg.text.split(maxsplit=1)
    if len(parts) < 2:
        return await msg.answer("❌ <code>показать фразу слово</code>")

    trigger = parts[1].lower()
    phrases = storage.get_chat(msg.chat.id, 'phrases')

    if not isinstance(phrases, list):
        return await msg.answer("❌ Фраз не найдено")

    matching = [p for p in phrases if p['trigger'] == trigger]

    if not matching:
        return await msg.answer(f"❌ Нет фраз с триггером '{html.escape(trigger, quote=False)}'")

    txt = f"📝 <b>Все ответы на '{html.escape(trigger, quote=False)}':</b>\n\n"
    for i, p in enumerate(matching, 1):
        anywhere = "🌐 (везде)" if p.get('anywhere') else "📌 (точно)"
        uses = p.get('uses', 0)
        txt += (
            f"{i}. {html.escape(str(p.get('response') or ''), quote=False)}\n"
            f"   └ {anywhere} | использовано: {uses} раз\n\n"
        )

    await msg.answer(txt)


# ==================== Приветствия ====================

async def cmd_welcome(msg: Message, cmd_name: str = 'приветствие'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return
    txt = msg.text.lower()
    cid = str(msg.chat.id)
    settings = storage.data['welcome_settings'].setdefault(cid, {})

    if 'вкл' in txt or 'выкл' in txt:
        settings['enabled'] = 'вкл' in txt
        storage.mark_dirty();
        await storage.save()
        await msg.answer(f"✅ Приветствия {'включены' if settings['enabled'] else 'выключены'}")
        return

    parts = msg.text.split()
    if len(parts) >= 3 and parts[1].lower() == 'картинка':
        url = ' '.join(parts[2:]).strip()
        if not url:
            return await msg.answer("❌ Укажите ссылку после <code>!приветствие картинка</code>")
        settings['image_url'] = url
        storage.mark_dirty();
        await storage.save()
        await msg.answer("✅ Картинка приветствия установлена")
        return

    if 'текст' in txt:
        text = ' '.join(msg.text.split()[2:])
        settings['text'] = text
        storage.mark_dirty();
        await storage.save()
        await msg.answer("✅ Текст приветствия установлен")
        return

    await msg.answer("❌ Использование: <code>!приветствие вкл/выкл</code> | <code>!приветствие текст ...</code> | <code>!приветствие картинка URL</code>")


async def cmd_farewell(msg: Message, cmd_name: str = 'прощание'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return

    txt = msg.text.lower()
    cid = str(msg.chat.id)
    settings = storage.data['welcome_settings'].setdefault(cid, {})

    if 'вкл' in txt or 'выкл' in txt:
        settings['farewell_enabled'] = 'вкл' in txt
        storage.mark_dirty()
        await storage.save()
        await msg.answer(f"✅ Прощание {'включено' if settings['farewell_enabled'] else 'выключено'}")
        return

    parts = msg.text.split()
    if len(parts) >= 3 and parts[1].lower() == 'картинка':
        url = ' '.join(parts[2:]).strip()
        if not url:
            return await msg.answer("❌ Укажите ссылку после <code>!прощание картинка</code>")
        settings['farewell_image_url'] = url
        storage.mark_dirty();
        await storage.save()
        await msg.answer("✅ Картинка прощания установлена")
        return

    if 'текст' in txt:
        text = ' '.join(msg.text.split()[2:])
        settings['farewell_text'] = text
        storage.mark_dirty()
        await storage.save()
        await msg.answer("✅ Текст прощания установлен")
        return

    text = ' '.join(msg.text.split()[1:])
    if text:
        settings['farewell_text'] = text
        storage.mark_dirty()
        await storage.save()
        await msg.answer("✅ Текст прощания установлен")
    else:
        await msg.answer("❌ Использование: <code>!прощание вкл/выкл</code> | <code>!прощание текст ...</code> | <code>!прощание картинка URL</code>")


# ==================== Правила ====================

async def cmd_rules(msg: Message):
    rules_list = storage.get_chat(msg.chat.id, 'rules')
    if not rules_list:
        return await msg.answer("📜 Правила чата пока не установлены.")
    txt = "📜 <b>Правила чата:</b>\n\n"
    for i, rule in enumerate(rules_list, 1):
        txt += f"{i}. {html.escape(str(rule), quote=False)}\n"
    await msg.answer(txt)


async def cmd_add_rule(msg: Message, cmd_name: str = 'добавитьправило'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 4):
        return
    parts = msg.text.split(maxsplit=1)
    if len(parts) < 2:
        return await msg.answer("❌ <code>добавитьправило Текст</code>")
    rules = storage.get_chat(msg.chat.id, 'rules')
    rules.append(parts[1])
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"✅ Правило #{len(rules)} добавлено")


async def cmd_clear_rules(msg: Message, cmd_name: str = 'очиститьправила'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 4):
        return
    storage.data.setdefault('rules', {})[str(msg.chat.id)] = []
    storage.mark_dirty();
    await storage.save()
    await msg.answer("🧹 Все правила удалены")


# ==================== ИГРЫ (ПОЛНОСТЬЮ НА КНОПКАХ) ====================

active_games = {}  # game_id -> game_data
pending_challenges = {}  # challenge_id -> challenge_data


# ==================== ГЛАВНОЕ МЕНЮ ====================

async def cmd_games_menu(msg: Message, cmd_name: str = 'игры'):
    """Главное меню игр"""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🎮 КНБ (с ботом)", callback_data="game_rps_bot"),
            InlineKeyboardButton(text="🤝 КНБ (с игроком)", callback_data="game_rps_player")
        ],
        [
            InlineKeyboardButton(text="❌ Крестики-Нолики", callback_data="game_ttt_menu"),
            InlineKeyboardButton(text="🎲 Wordle", callback_data="game_wordle")
        ],
        [
            InlineKeyboardButton(text="❌ Закрыть", callback_data="game_cancel")
        ]
    ])

    await msg.answer(
        "🎮 <b>Игровое меню</b>\n\n"
        "Выберите игру:",
        reply_markup=kb
    )

def get_wordle_menu_text() -> str:
    return (
        "🎲 <b>Wordle (русский)</b>\n\n"
        "Выберите сложность — игра сразу начнётся в этом чате:\n\n"
        "🟢 <b>Лёгкий</b> — распространённые слова\n"
        "🟡 <b>Средний</b> — обычные слова\n"
        "🔴 <b>Сложный</b> — редкие сочетания букв\n"
        "⚫ <b>Экспертный</b> — самые необычные слова\n\n"
        "После запуска отвечайте на сообщение игры словом из 5 букв.\n\n"
        "Длина: 4-6 букв · Попытки: 4-6\n"
        "Если сложность не указана, используется средняя."
    )


def get_wordle_menu_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🟢 Лёгкий", callback_data="wordle_difficulty_easy"),
            InlineKeyboardButton(text="🟡 Средний", callback_data="wordle_difficulty_medium")
        ],
        [
            InlineKeyboardButton(text="🔴 Сложный", callback_data="wordle_difficulty_hard"),
            InlineKeyboardButton(text="⚫ Экспертный", callback_data="wordle_difficulty_expert")
        ],
        [InlineKeyboardButton(text="◀️ Назад", callback_data="game_back_to_menu")]
    ])


async def cmd_wordle(msg: Message):
    if not check_access(msg.from_user.id, msg.chat.id, 'wordle', 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    parts = msg.text.split()
    if len(parts) == 1:
        await msg.answer(get_wordle_menu_text(), reply_markup=get_wordle_menu_keyboard())
        return

    if len(parts) > 1 and parts[1].lower() == 'exit':
        if wordle.exit_chat_game(msg.chat.id):
            await msg.answer("❌ Вы вышли из игры Wordle.")
        else:
            await msg.answer("❌ В этом чате нет активной игры.")
        return

    # Админ-команда: !wordle stop
    if len(parts) > 1 and parts[1].lower() == 'stop':
        is_admin = storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) >= 1
        if not is_admin:
            await msg.answer("❌ Только администраторы могут остановить игру.")
            return
        if wordle.exit_chat_game(msg.chat.id):
            await msg.answer("⏹️ Администратор остановил игру Wordle.")
        else:
            await msg.answer("❌ В этом чате нет активной игры.")
        return

    length = 5
    attempts = 6
    difficulty = 'medium'
    arguments = parts[1:]
    difficulty_tokens = {'лёгкий', 'легкий', 'легкая', 'лёгкая', 'easy', "легко",
                         'средний', 'средняя', 'medium', 'сложный', 'сложная', 'hard',
                         'эксперт', 'экспертный', 'экспертная', 'expert'}
    difficulty_argument = next((item for item in arguments if item.lower() in difficulty_tokens), None)
    if difficulty_argument:
        difficulty = wordle.normalize_difficulty(difficulty_argument.lower())
        arguments.remove(difficulty_argument)

    numeric_arguments = [item for item in arguments if item.isdigit()]
    if numeric_arguments:
        length = int(numeric_arguments[0])
        if length < 4 or length > 6:
            return await msg.answer("❌ Длина слова должна быть от 4 до 6.")
    if len(numeric_arguments) > 1:
        attempts = int(numeric_arguments[1])
        if attempts < 4 or attempts > 6:
            return await msg.answer("❌ Количество попыток должно быть от 4 до 6.")

    success, response = wordle.start_chat_game(
        msg.chat.id, msg.from_user.id, length, attempts, difficulty
    )
    game_msg = await msg.answer(response)
    if success:
        wordle.set_game_message(msg.from_user.id, msg.chat.id, game_msg.message_id)

# ==================== ОБРАБОТЧИК ВСЕХ ИГРОВЫХ CALLBACK'ОВ ====================

@router.callback_query(lambda c: c.data and c.data.startswith('game_'))
async def game_menu_handler(call: CallbackQuery):
    action = call.data

    if action == "game_rps_bot":
        await start_rps_bot(call)
    elif action == "game_rps_player":
        await create_rps_challenge(call)
    elif action == "game_ttt_menu":
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(text="🤖 С ботом", callback_data="ttt_mode_bot"),
                InlineKeyboardButton(text="👤 С игроком", callback_data="ttt_mode_player")
            ],
            [InlineKeyboardButton(text="◀️ Назад", callback_data="game_back_to_menu")]
        ])
        await call.message.edit_text(
            "🎮 <b>Крестики-Нолики</b>\n\nВыберите режим:",
            reply_markup=kb
        )
    elif action == "game_wordle":
        await call.message.edit_text(
            get_wordle_menu_text(),
            reply_markup=get_wordle_menu_keyboard()
        )
    elif action == "game_back_to_menu":
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(text="🎮 КНБ (с ботом)", callback_data="game_rps_bot"),
                InlineKeyboardButton(text="🤝 КНБ (с игроком)", callback_data="game_rps_player")
            ],
            [
                InlineKeyboardButton(text="❌ Крестики-Нолики", callback_data="game_ttt_menu"),
                InlineKeyboardButton(text="🎲 Wordle", callback_data="game_wordle")
            ],
            [
                InlineKeyboardButton(text="❌ Закрыть", callback_data="game_cancel")
            ]
        ])
        await call.message.edit_text(
            "🎮 <b>Игровое меню</b>\n\nВыберите игру:",
            reply_markup=kb
        )
    elif action == "game_cancel":
        await call.message.delete()
    elif action.startswith("game_accept_"):
        challenge_id = action.replace("game_accept_", "")
        await accept_challenge(call, challenge_id)
    elif action == "game_cancel_challenge":
        to_remove = [cid for cid, ch in pending_challenges.items()
                     if ch.get('challenger') == call.from_user.id]
        for cid in to_remove:
            pending_challenges.pop(cid, None)
        await call.message.edit_text("❌ Вызов отменён", reply_markup=None)

    await call.answer()


@router.callback_query(lambda c: c.data and c.data.startswith('wordle_difficulty_'))
async def wordle_difficulty_handler(call: CallbackQuery):
    difficulty = call.data.replace('wordle_difficulty_', '')
    difficulty_name = wordle.DIFFICULTY_NAMES.get(difficulty)
    if not difficulty_name:
        await call.answer("❌ Неизвестная сложность", show_alert=True)
        return

    success, response = wordle.start_chat_game(
        call.message.chat.id,
        call.from_user.id,
        DEFAULT_WORDLE_LENGTH,
        DEFAULT_WORDLE_ATTEMPTS,
        difficulty,
    )
    game_msg = await call.message.answer(response)
    if success:
        wordle.set_game_message(call.from_user.id, call.message.chat.id, game_msg.message_id)
        await call.message.delete()
    await call.answer()


@router.callback_query(lambda c: c.data and c.data.startswith('ttt_mode_'))
async def ttt_mode_handler(call: CallbackQuery):
    """Выбор режима TTT"""
    mode = call.data.replace("ttt_mode_", "")

    if mode == "bot":
        await start_ttt_bot(call)
    elif mode == "player":
        await create_ttt_challenge(call)

    await call.answer()


# ==================== КНБ С БОТОМ ====================

async def start_rps_bot(call: CallbackQuery):
    """Запуск КНБ с ботом"""
    save_activity(call.message.chat.id, call.from_user.id, 'games')

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🪨 Камень", callback_data="rps_rock"),
            InlineKeyboardButton(text="✂️ Ножницы", callback_data="rps_scissors"),
            InlineKeyboardButton(text="📄 Бумага", callback_data="rps_paper")
        ],
        [InlineKeyboardButton(text="◀️ Назад", callback_data="game_back_to_menu")]
    ])

    await call.message.edit_text(
        "🎮 <b>Камень-Ножницы-Бумага (с ботом)</b>\n\nСделайте выбор:",
        reply_markup=kb
    )


@router.callback_query(lambda c: c.data and c.data.startswith('rps_'))
async def rps_bot_handler(call: CallbackQuery):
    """Обработка выбора в КНБ с ботом"""
    choices = {
        'rps_rock': ('🪨', 'Камень', 'rock'),
        'rps_scissors': ('✂️', 'Ножницы', 'scissors'),
        'rps_paper': ('📄', 'Бумага', 'paper')
    }

    if call.data not in choices:
        await call.answer("❌ Неизвестный выбор", show_alert=True)
        return

    save_activity(call.message.chat.id, call.from_user.id, 'games')

    user_emoji, user_name, user_choice = choices[call.data]
    bot_choice = random.choice(['rock', 'scissors', 'paper'])

    bot_emojis = {'rock': '🪨', 'scissors': '✂️', 'paper': '📄'}
    bot_names = {'rock': 'Камень', 'scissors': 'Ножницы', 'paper': 'Бумага'}

    # Определяем победителя
    if user_choice == bot_choice:
        result = "🤝 Ничья!"
    elif (user_choice == 'rock' and bot_choice == 'scissors') or \
            (user_choice == 'scissors' and bot_choice == 'paper') or \
            (user_choice == 'paper' and bot_choice == 'rock'):
        result = "✅ Вы победили!"
    else:
        result = "❌ Победил бот!"

    # Статистика
    u = storage.get_user(call.message.chat.id, call.from_user.id)
    u['rps_games'] = u.get('rps_games', 0) + 1
    if 'победили' in result:
        u['rps_wins'] = u.get('rps_wins', 0) + 1
        u['rps_current_streak'] = u.get('rps_current_streak', 0) + 1
        u['rps_best_streak'] = max(u.get('rps_best_streak', 0), u['rps_current_streak'])
    elif 'бот' in result:
        u['rps_current_streak'] = 0

    storage.mark_dirty()
    await storage.save()

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎮 Играть ещё", callback_data="game_rps_bot")],
        [InlineKeyboardButton(text="◀️ В меню", callback_data="game_back_to_menu")]
    ])

    await call.message.edit_text(
        f"🎮 <b>Камень-Ножницы-Бумага</b>\n\n"
        f"Вы: {user_emoji} {user_name}\n"
        f"Бот: {bot_emojis[bot_choice]} {bot_names[bot_choice]}\n\n"
        f"{result}\n\n"
        f"📊 Побед: {u.get('rps_wins', 0)} | Игр: {u.get('rps_games', 0)}",
        reply_markup=kb
    )


# ==================== КНБ С ИГРОКОМ ====================

async def create_rps_challenge(call: CallbackQuery):
    """Создание вызова на КНБ"""
    now = time.time()
    # Чистим старые вызовы
    to_remove = [cid for cid, ch in pending_challenges.items()
                 if now - ch.get('timestamp', now) > 60]
    for cid in to_remove:
        pending_challenges.pop(cid, None)

    challenge_id = f"rps_{call.from_user.id}_{int(now)}"

    pending_challenges[challenge_id] = {
        'challenger': call.from_user.id,
        'opponent': None,
        'game_type': 'rps',
        'timestamp': now
    }

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Принять вызов", callback_data=f"game_accept_{challenge_id}")],
        [InlineKeyboardButton(text="❌ Отменить", callback_data="game_cancel_challenge")]
    ])

    await call.message.edit_text(
        f"🎮 <b>Камень-Ножницы-Бумага</b>\n\n"
        f"{mention(call.message.chat.id, call.from_user.id)} вызывает на бой!\n\n"
        f"Нажмите кнопку чтобы принять:",
        reply_markup=kb
    )


async def accept_challenge(call: CallbackQuery, challenge_id: str):
    """Принятие вызова"""
    challenge = pending_challenges.get(challenge_id)

    if not challenge:
        await call.answer("❌ Вызов устарел!", show_alert=True)
        return

    if challenge['challenger'] == call.from_user.id:
        await call.answer("❌ Нельзя принять свой вызов!", show_alert=True)
        return

    challenge['opponent'] = call.from_user.id

    if challenge['game_type'] == 'rps':
        await start_rps_duel(call, challenge)
    elif challenge['game_type'] == 'ttt':
        await start_ttt_duel(call, challenge)

    pending_challenges.pop(challenge_id, None)


async def start_rps_duel(call: CallbackQuery, challenge: dict):
    """Запуск дуэли КНБ"""
    p1, p2 = challenge['challenger'], challenge['opponent']
    game_id = f"rps_{p1}_{p2}_{int(time.time())}"

    # Отправляем ЛС каждому игроку
    for player in [p1, p2]:
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(text="🪨 Камень", callback_data=f"rpsduel_{game_id}_rock"),
                InlineKeyboardButton(text="✂️ Ножницы", callback_data=f"rpsduel_{game_id}_scissors"),
                InlineKeyboardButton(text="📄 Бумага", callback_data=f"rpsduel_{game_id}_paper")
            ]
        ])
        try:
            await bot.send_message(
                player,
                f"🎮 <b>Дуэль КНБ!</b>\n\n{mention(call.message.chat.id, p1)} vs {mention(call.message.chat.id, p2)}\n\nСделайте выбор:",
                reply_markup=kb
            )
        except:
            await call.message.answer(f"❌ Не могу написать {mention(call.message.chat.id, player)} в ЛС!")
            return

    active_games[game_id] = {
        'type': 'rps_duel',
        'players': [p1, p2],
        'choices': {},
        'chat_id': call.message.chat.id,
        'message_id': call.message.message_id,
        'started_at': time.time()
    }

    await call.message.edit_text(
        f"⚔️ <b>Дуэль началась!</b>\n\n{mention(call.message.chat.id, p1)} vs {mention(call.message.chat.id, p2)}\n\n"
        f"Проверьте ЛС и сделайте выбор!",
        reply_markup=None
    )


@router.callback_query(lambda c: c.data and c.data.startswith('rpsduel_'))
async def rps_duel_choice(call: CallbackQuery):
    """Обработка выбора в дуэли"""
    parts = call.data.split('_')
    # rpsduel_GAME_ID_choice
    choice = parts[-1]
    game_id = '_'.join(parts[1:-1])

    game = active_games.get(game_id)
    if not game:
        await call.answer("❌ Игра не найдена!", show_alert=True)
        return

    if call.from_user.id not in game['players']:
        await call.answer("❌ Это не ваша игра!", show_alert=True)
        return

    if call.from_user.id in game['choices']:
        await call.answer("✅ Вы уже сделали выбор!", show_alert=True)
        return

    game['choices'][call.from_user.id] = choice

    if len(game['choices']) == 2:
        # Оба выбрали - определяем победителя
        await resolve_rps_duel(game_id, game['chat_id'])

    await call.message.edit_text("✅ Выбор сделан! Ждите результата.", reply_markup=None)
    await call.answer("✅ Выбор принят!")


async def resolve_rps_duel(game_id: str, chat_id: int):
    """Определение победителя дуэли"""
    game = active_games.get(game_id)
    if not game:
        return

    p1, p2 = game['players']
    c1, c2 = game['choices'][p1], game['choices'][p2]

    emoji = {'rock': '🪨', 'scissors': '✂️', 'paper': '📄'}
    name = {'rock': 'Камень', 'scissors': 'Ножницы', 'paper': 'Бумага'}

    if c1 == c2:
        result = "🤝 Ничья!"
        winner = None
    elif (c1 == 'rock' and c2 == 'scissors') or \
            (c1 == 'scissors' and c2 == 'paper') or \
            (c1 == 'paper' and c2 == 'rock'):
        result = f"✅ Победил {mention(chat_id, p1)}!"
        winner = p1
    else:
        result = f"✅ Победил {mention(chat_id, p2)}!"
        winner = p2

    for pid in [p1, p2]:
        u = storage.get_user(chat_id, pid)
        u['rps_games'] = u.get('rps_games', 0) + 1
        if winner == pid:
            u['rps_wins'] = u.get('rps_wins', 0) + 1

    storage.mark_dirty()
    await storage.save()

    u1 = storage.get_user(chat_id, p1)
    u2 = storage.get_user(chat_id, p2)

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Реванш", callback_data=f"rpsrematch_{p1}_{p2}")],
        [InlineKeyboardButton(text="🎮 В меню", callback_data="game_back_to_menu")]
    ])

    await bot.send_message(
        chat_id,
        f"⚔️ <b>Результат дуэли!</b>\n\n"
        f"{mention(chat_id, p1)}: {emoji[c1]} {name[c1]}\n"
        f"{mention(chat_id, p2)}: {emoji[c2]} {name[c2]}\n\n{result}\n\n"
        f"📊 {mention(chat_id, p1)}: {u1.get('rps_wins', 0)} побед | "
        f"{mention(chat_id, p2)}: {u2.get('rps_wins', 0)} побед",
        reply_markup=kb
    )

    del active_games[game_id]


# ==================== КРЕСТИКИ-НОЛИКИ С БОТОМ ====================

async def start_ttt_bot(call: CallbackQuery):
    """Запуск TTT с ботом"""
    player = call.from_user.id
    game_id = f"tttbot_{player}_{int(time.time())}"

    board = [[' ' for _ in range(3)] for _ in range(3)]

    active_games[game_id] = {
        'type': 'ttt_bot',
        'player': player,
        'board': board,
        'current': 'player',
        'status': 'active',
        'chat_id': call.message.chat.id,
        'started_at': time.time()
    }

    await draw_ttt_board(call.message, game_id, "🎮 Крестики-Нолики с ботом\nВаш ход:")


async def draw_ttt_board(message, game_id: str, title: str):
    """Отрисовка доски TTT"""
    game = active_games.get(game_id)
    if not game:
        return

    board = game['board']
    keyboard = []

    for i in range(3):
        row = []
        for j in range(3):
            cell = board[i][j]
            if cell == 'X':
                text = '❌'
            elif cell == 'O':
                text = '⭕'
            else:
                text = '⬜'

            if cell == ' ' and game['status'] == 'active':
                row.append(InlineKeyboardButton(
                    text=text,
                    callback_data=f"ttt_{game_id}_{i}_{j}"
                ))
            else:
                row.append(InlineKeyboardButton(
                    text=text,
                    callback_data="ttt_noop"
                ))
        keyboard.append(row)

    keyboard.append([InlineKeyboardButton(
        text="◀️ Выйти",
        callback_data=f"tttexit_{game_id}"
    )])

    kb = InlineKeyboardMarkup(inline_keyboard=keyboard)

    try:
        await message.edit_text(title, reply_markup=kb)
    except:
        msg = await message.answer(title, reply_markup=kb)
        game['message_id'] = msg.message_id


@router.callback_query(lambda c: c.data and c.data.startswith('ttt_'))
async def ttt_move_handler(call: CallbackQuery):
    """Обработка хода в TTT"""
    parts = call.data.split('_')

    if len(parts) < 4:
        return

    row = int(parts[-2])
    col = int(parts[-1])
    game_id = '_'.join(parts[1:-2])

    game = active_games.get(game_id)
    if not game or game['status'] != 'active':
        await call.answer("❌ Игра не найдена!", show_alert=True)
        return

    # Проверка хода
    if game['type'] == 'ttt_bot':
        if game['current'] != 'player' or call.from_user.id != game['player']:
            await call.answer("❌ Не ваш ход!", show_alert=True)
            return
        symbol = 'X'
    else:
        if call.from_user.id != game['current']:
            await call.answer("❌ Не ваш ход!", show_alert=True)
            return
        symbol = 'X' if call.from_user.id == game['players'][0] else 'O'

    if game['board'][row][col] != ' ':
        await call.answer("❌ Клетка занята!", show_alert=True)
        return

    # Ход
    game['board'][row][col] = symbol
    await call.answer("✅")

    # Проверка победы
    winner = check_ttt_winner(game['board'])
    if winner:
        await end_ttt_game(game, game_id, winner, call.message)
        return

    # Проверка ничьей
    if all(cell != ' ' for row_board in game['board'] for cell in row_board):
        await end_ttt_game(game, game_id, None, call.message)
        return

    # Следующий ход
    if game['type'] == 'ttt_bot':
        game['current'] = 'bot'
        await draw_ttt_board(call.message, game_id, "🎮 Крестики-Нолики с ботом\nХод бота...")
        await asyncio.sleep(0.5)
        await bot_ttt_move(game_id, call.message)
    else:
        game['current'] = game['players'][1] if game['current'] == game['players'][0] else game['players'][0]
        await draw_ttt_board(call.message, game_id,
                             f"🎮 Крестики-Нолики\n{mention(call.message.chat.id, game['players'][0])} (❌) vs {mention(call.message.chat.id, game['players'][1])} (⭕)\n"
                             f"Ход: {mention(call.message.chat.id, game['current'])}")


def _ttt_minimax(board: list, depth: int, is_bot: bool) -> int:
    """Оценка позиции для минимакс-ИИ бота (O — бот, X — игрок)"""
    winner = check_ttt_winner(board)
    if winner == 'O':
        return 10 - depth
    if winner == 'X':
        return depth - 10
    if all(cell != ' ' for row in board for cell in row):
        return 0

    scores = []
    for i in range(3):
        for j in range(3):
            if board[i][j] == ' ':
                board[i][j] = 'O' if is_bot else 'X'
                scores.append(_ttt_minimax(board, depth + 1, not is_bot))
                board[i][j] = ' '

    return max(scores) if is_bot else min(scores)


def best_ttt_move(board: list) -> tuple:
    """Лучший ход бота: минимакс (побеждает/блокирует всегда, где возможно)"""
    empty = [(i, j) for i in range(3) for j in range(3) if board[i][j] == ' ']

    # Первый ход бота — сразу в центр, чтобы не гонять полное дерево впустую
    if len(empty) == 9:
        return (1, 1)

    best_score, best_move = -999, empty[0]
    for i, j in empty:
        board[i][j] = 'O'
        score = _ttt_minimax(board, 0, False)
        board[i][j] = ' '
        if score > best_score:
            best_score, best_move = score, (i, j)

    return best_move


async def bot_ttt_move(game_id: str, message):
    """Ход бота в TTT"""
    game = active_games.get(game_id)
    if not game or game['status'] != 'active':
        return

    empty = [(i, j) for i in range(3) for j in range(3) if game['board'][i][j] == ' ']
    if not empty:
        return

    row, col = best_ttt_move(game['board'])
    game['board'][row][col] = 'O'

    winner = check_ttt_winner(game['board'])
    if winner or all(cell != ' ' for row_board in game['board'] for cell in row_board):
        await end_ttt_game(game, game_id, winner, message)
        return

    game['current'] = 'player'
    await draw_ttt_board(message, game_id, "🎮 Крестики-Нолики с ботом\nВаш ход:")


async def end_ttt_game(game: dict, game_id: str, winner: str, message):
    """Завершение игры TTT"""
    game['status'] = 'finished'

    win_taunts = ["Ну вы даёте! 🔥", "Красиво сыграно!", "Чистая победа!", "Вот это комбо!"]
    bot_taunts = ["Бот в ударе сегодня 🤖", "Не повезло — реванш?", "Бот считает на 9 ходов вперёд 😏"]

    if game['type'] == 'ttt_bot':
        player = game['player']
        u = storage.get_user(message.chat.id, player)
        u['ttt_games'] = u.get('ttt_games', 0) + 1
        if winner == 'X':
            u['ttt_wins'] = u.get('ttt_wins', 0) + 1
            title = f"🎮 Крестики-Нолики\n✅ Вы победили! {random.choice(win_taunts)}"
        elif winner == 'O':
            title = f"🎮 Крестики-Нолики\n❌ Победил бот! {random.choice(bot_taunts)}"
        else:
            title = f"🎮 Крестики-Нолики\n🤝 Ничья! Бот с этим ИИ проигрывает крайне редко 👀"
        title += f"\n\n📊 Побед: {u.get('ttt_wins', 0)} | Игр: {u.get('ttt_games', 0)}"
    else:
        p1, p2 = game['players']
        for pid in [p1, p2]:
            u = storage.get_user(message.chat.id, pid)
            u['ttt_games'] = u.get('ttt_games', 0) + 1
            if winner and pid == (p1 if winner == 'X' else p2):
                u['ttt_wins'] = u.get('ttt_wins', 0) + 1

        u1 = storage.get_user(message.chat.id, p1)
        u2 = storage.get_user(message.chat.id, p2)

        if winner == 'X':
            title = f"🎮 Крестики-Нолики\n✅ Победил {mention(message.chat.id, p1)}!"
        elif winner == 'O':
            title = f"🎮 Крестики-Нолики\n✅ Победил {mention(message.chat.id, p2)}!"
        else:
            title = f"🎮 Крестики-Нолики\n🤝 Ничья!"
        title += (f"\n\n📊 {mention(message.chat.id, p1)}: {u1.get('ttt_wins', 0)} побед | "
                  f"{mention(message.chat.id, p2)}: {u2.get('ttt_wins', 0)} побед")

    storage.mark_dirty()
    await storage.save()

    # Финальная отрисовка с подсветкой выигрышной линии
    board = game['board']
    win_line = ttt_winning_line(board) if winner else None
    keyboard = []
    for i in range(3):
        row = []
        for j in range(3):
            cell = board[i][j]
            base = '❌' if cell == 'X' else '⭕' if cell == 'O' else '⬜'
            text = f"🔥{base}" if win_line and (i, j) in win_line else base
            row.append(InlineKeyboardButton(text=text, callback_data="ttt_noop"))
        keyboard.append(row)

    if game['type'] == 'ttt_bot':
        keyboard.append([InlineKeyboardButton(text="🔄 Реванш", callback_data="ttt_mode_bot")])
    else:
        keyboard.append([InlineKeyboardButton(
            text="🔄 Реванш",
            callback_data=f"tttrematch_{game['players'][0]}_{game['players'][1]}"
        )])
    keyboard.append([InlineKeyboardButton(text="🎮 В меню", callback_data="game_back_to_menu")])
    kb = InlineKeyboardMarkup(inline_keyboard=keyboard)

    await message.edit_text(title, reply_markup=kb)
    del active_games[game_id]


# ==================== КРЕСТИКИ-НОЛИКИ С ИГРОКОМ ====================

async def create_ttt_challenge(call: CallbackQuery):
    """Создание вызова на TTT"""
    now = time.time()
    to_remove = [cid for cid, ch in pending_challenges.items()
                 if now - ch.get('timestamp', now) > 60]
    for cid in to_remove:
        pending_challenges.pop(cid, None)

    challenge_id = f"ttt_{call.from_user.id}_{int(now)}"

    pending_challenges[challenge_id] = {
        'challenger': call.from_user.id,
        'opponent': None,
        'game_type': 'ttt',
        'timestamp': now
    }

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Принять вызов", callback_data=f"game_accept_{challenge_id}")],
        [InlineKeyboardButton(text="❌ Отменить", callback_data="game_cancel_challenge")]
    ])

    await call.message.edit_text(
        f"🎮 <b>Крестики-Нолики</b>\n\n"
        f"{mention(call.message.chat.id, call.from_user.id)} вызывает на бой!\n\n"
        f"Нажмите кнопку чтобы принять:",
        reply_markup=kb
    )


async def start_ttt_duel(call: CallbackQuery, challenge: dict):
    """Запуск дуэли TTT"""
    p1, p2 = challenge['challenger'], challenge['opponent']
    game_id = f"tttduel_{p1}_{p2}_{int(time.time())}"

    board = [[' ' for _ in range(3)] for _ in range(3)]

    active_games[game_id] = {
        'type': 'ttt_duel',
        'players': [p1, p2],
        'board': board,
        'current': p1,
        'status': 'active',
        'chat_id': call.message.chat.id,
        'started_at': time.time()
    }

    await draw_ttt_board(call.message, game_id,
                         f"🎮 Крестики-Нолики\n{mention(call.message.chat.id, p1)} (❌) vs {mention(call.message.chat.id, p2)} (⭕)\n"
                         f"Ход: {mention(call.message.chat.id, p1)}")


# ==================== ВЫХОД ИЗ TTT ====================

@router.callback_query(lambda c: c.data and c.data.startswith('tttexit_'))
async def ttt_exit_handler(call: CallbackQuery):
    """Завершает игру только по запросу одного из её участников."""
    game_id = '_'.join(call.data.split('_')[1:])
    game = active_games.get(game_id)
    if not game:
        await call.answer("❌ Игра уже завершена.", show_alert=True)
        return
    players = game.get('players', [])
    player = game.get('player')
    if call.from_user.id not in players and call.from_user.id != player:
        await call.answer("❌ Выйти из этой игры может только её участник.", show_alert=True)
        return

    active_games.pop(game_id, None)
    game['status'] = 'finished'
    if call.message:
        await call.message.edit_text("❌ Игра завершена по запросу участника.", reply_markup=None)
    await call.answer()


@router.callback_query(lambda c: c.data == 'ttt_noop')
async def ttt_noop_handler(call: CallbackQuery):
    """Нажатие на занятую клетку"""
    await call.answer("❌ Клетка занята!", show_alert=True)


@router.callback_query(lambda c: c.data and c.data.startswith('tttrematch_'))
async def ttt_rematch_handler(call: CallbackQuery):
    """Реванш в TTT-дуэли — перезапуск без повторного вызова/принятия"""
    parts = call.data.split('_')
    p1, p2 = int(parts[1]), int(parts[2])

    if call.from_user.id not in (p1, p2):
        await call.answer("❌ Это не ваша игра!", show_alert=True)
        return

    await start_ttt_duel(call, {'challenger': p1, 'opponent': p2})
    await call.answer("🔄 Реванш!")


@router.callback_query(lambda c: c.data and c.data.startswith('rpsrematch_'))
async def rps_rematch_handler(call: CallbackQuery):
    """Реванш в RPS-дуэли — перезапуск без повторного вызова/принятия"""
    parts = call.data.split('_')
    p1, p2 = int(parts[1]), int(parts[2])

    if call.from_user.id not in (p1, p2):
        await call.answer("❌ Это не ваша игра!", show_alert=True)
        return

    await start_rps_duel(call, {'challenger': p1, 'opponent': p2})
    await call.answer("🔄 Реванш!")


# ==================== ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ====================

def check_ttt_winner(board: list) -> str:
    """Проверка победителя. Возвращает 'X', 'O' или None"""
    for i in range(3):
        if board[i][0] == board[i][1] == board[i][2] != ' ':
            return board[i][0]
        if board[0][i] == board[1][i] == board[2][i] != ' ':
            return board[0][i]

    if board[0][0] == board[1][1] == board[2][2] != ' ':
        return board[0][0]
    if board[0][2] == board[1][1] == board[2][0] != ' ':
        return board[0][2]

    return None


def ttt_winning_line(board: list) -> list:
    """Возвращает список координат выигрышной линии, либо None"""
    lines = [[(i, 0), (i, 1), (i, 2)] for i in range(3)] + \
            [[(0, j), (1, j), (2, j)] for j in range(3)] + \
            [[(0, 0), (1, 1), (2, 2)], [(0, 2), (1, 1), (2, 0)]]

    for line in lines:
        a, b, c = (board[i][j] for i, j in line)
        if a == b == c != ' ':
            return line

    return None


async def cleanup_games():
    """Очистка старых игр"""
    while True:
        await asyncio.sleep(300)
        now = time.time()

        expired = [gid for gid, game in active_games.items()
                   if now - game.get('started_at', now) > 3600]
        for gid in expired:
            del active_games[gid]

        expired_ch = [cid for cid, ch in pending_challenges.items()
                      if now - ch.get('timestamp', now) > 60]
        for cid in expired_ch:
            del pending_challenges[cid]


# ==================== ТЕКСТОВЫЕ КОМАНДЫ ====================

async def cmd_game(msg: Message):
    """Текстовая команда для игр"""
    await cmd_games_menu(msg)


async def cmd_rps(msg: Message, cmd_name: str = 'кнб'):
    """Текстовая команда для КНБ"""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'games')

    text = msg.text.strip()
    text = strip_command_prefix(text, msg.chat.id)

    for cmd_word in ['кнб', 'кнб бот', 'камень ножницы бумага']:
        if text.lower().startswith(cmd_word):
            text = text[len(cmd_word):].strip()
            break

    choice_map = {
        'камень': 'rock', 'к': 'rock',
        'ножницы': 'scissors', 'н': 'scissors',
        'бумага': 'paper', 'б': 'paper'
    }

    user_choice = choice_map.get(text.lower())

    if user_choice:
        # Быстрая игра текстом
        choices = {'rock': ('🪨', 'Камень'), 'scissors': ('✂️', 'Ножницы'), 'paper': ('📄', 'Бумага')}
        bot_choice = random.choice(['rock', 'scissors', 'paper'])

        user_emoji, user_name = choices[user_choice]
        bot_emoji, bot_name = choices[bot_choice]

        if user_choice == bot_choice:
            result = "🤝 Ничья!"
        elif (user_choice == 'rock' and bot_choice == 'scissors') or \
                (user_choice == 'scissors' and bot_choice == 'paper') or \
                (user_choice == 'paper' and bot_choice == 'rock'):
            result = "✅ Вы победили!"
        else:
            result = "❌ Победил бот!"

        u = storage.get_user(msg.chat.id, msg.from_user.id)
        u['rps_games'] = u.get('rps_games', 0) + 1
        if 'победили' in result:
            u['rps_wins'] = u.get('rps_wins', 0) + 1
        storage.mark_dirty()
        await storage.save()

        await msg.answer(
            f"🎮 <b>КНБ</b>\n\n"
            f"Вы: {user_emoji} {user_name}\n"
            f"Бот: {bot_emoji} {bot_name}\n\n{result}"
        )
    else:
        # Открываем меню с кнопками
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(text="🪨 Камень", callback_data="rps_rock"),
                InlineKeyboardButton(text="✂️ Ножницы", callback_data="rps_scissors"),
                InlineKeyboardButton(text="📄 Бумага", callback_data="rps_paper")
            ]
        ])
        await msg.answer("🎮 <b>КНБ с ботом</b>\n\nВыберите или напишите: <code>кнб камень</code>", reply_markup=kb)


# ==================== Опросы ====================

async def cmd_poll(msg: Message, cmd_name: str = 'опрос'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    
    # Парсим текст: получаем всё после команды !опрос
    text = msg.text.strip()
    
    # Удаляем префикс команды если есть
    for prefix in ['!опрос', '!poll']:
        if text.lower().startswith(prefix):
            text = text[len(prefix):].strip()
            break
    
    if not text:
        return await msg.answer("❌ <code>!опрос Вопрос? | Да | Нет</code>")
    
    # Парсим по разделителю |
    parts = [p.strip() for p in text.split('|') if p.strip()]
    if len(parts) < 3:
        return await msg.answer("❌ Нужен вопрос и минимум 2 варианта ответа. Пример: <code>!опрос Это опрос? | Да | Нет</code>")
    
    question, options = parts[0], parts[1:11]
    if len(options) < 2:
        return await msg.answer("❌ Минимум 2 варианта ответа")
    
    # Проверяем что вопрос не пустой
    if not question or question == text:
        return await msg.answer("❌ Введите вопрос перед первым |")

    try:
        poll_msg = await msg.answer_poll(
            question=question,
            options=options,
            is_anonymous=False,
            type='regular',
            allows_multiple_answers=False,
        )
    except Exception as e:
        logger.exception("Ошибка создания реального опроса")
        return await msg.answer(f"❌ Не удалось создать опрос: {e}")

    polls = storage.get_chat(msg.chat.id, 'polls')
    if not isinstance(polls, list):
        polls = []
        storage.data['polls'][str(msg.chat.id)] = polls
    polls.append({
        'message_id': poll_msg.message_id,
        'chat_id': msg.chat.id,
        'creator': msg.from_user.id,
        'question': question,
        'options': options,
        'poll_id': poll_msg.poll.id,
        'created_at': time.time(),
    })
    storage.mark_dirty()
    await storage.save()
    
    # Удаляем исходное сообщение с командой
    try:
        await msg.delete()
    except Exception as e:
        logger.debug(f"Не удалось удалить сообщение с опросом: {e}")


@router.callback_query(F.data.startswith('poll_vote_'))
async def poll_vote_handler(call: CallbackQuery):
    polls = storage.get_chat(call.message.chat.id, 'polls')
    if not isinstance(polls, list):
        return await call.answer("Опрос не найден")
    poll = next((p for p in polls if p.get('message_id') == call.message.message_id), None)
    if not poll:
        return await call.answer("Опрос не найден")
    option_index = int(call.data.split('_')[-1])
    user_id = call.from_user.id
    if user_id in poll['voters']:
        if poll['voters'][user_id] == option_index:
            return await call.answer("Вы уже голосовали", show_alert=True)
        poll['votes'][poll['voters'][user_id]].remove(user_id)
    poll['votes'][option_index].append(user_id)
    poll['voters'][user_id] = option_index
    storage.mark_dirty();
    await storage.save()
    options_text = [f"{i + 1}. {opt} ({len(poll['votes'][i])})" for i, opt in enumerate(poll['options'])]
    kb = InlineKeyboardBuilder()
    for i, option in enumerate(poll['options']):
        kb.button(text=f"{option[:30]} ({len(poll['votes'][i])})", callback_data=f"poll_vote_{i}")
    kb.adjust(1)
    try:
        await call.message.edit_text(
            f"📊 <b>Опрос от {mention(call.message.chat.id, poll['creator'])}</b>\n\n❓ {poll['question']}\n\n" + "\n".join(
                options_text), reply_markup=kb.as_markup(), disable_web_page_preview=True)
    except:
        pass
    await call.answer("Голос учтён!")


# ==================== Интеграции ====================

async def cmd_time(msg: Message, region: str = '', cmd_name: str = 'время'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    try:
        region_name, region_timezone = resolve_time_region(region)
    except (ZoneInfoNotFoundError, ValueError):
        try:
            lookup_result = await lookup_time_region(region)
        except (ImportError, RuntimeError, ValueError, KeyError, TypeError) as exc:
            logger.warning("Не удалось определить время для региона %r: %s", region, exc)
            await msg.answer("❌ Не удалось получить время для региона. Попробуй ещё раз позже.")
            return
        if lookup_result is None:
            await msg.answer(
                "❌ Регион не найден. Укажи название города, например "
                "<code>!время Токио</code> или <code>!время Нью-Йорк</code>."
            )
            return
        region_name, local_time, offset = lookup_result
    else:
        local_time = datetime.now(region_timezone)
        offset = local_time.utcoffset()

    if offset is None:
        raise ValueError(f"Часовой пояс региона {region_name!r} не имеет UTC-смещения")
    offset_minutes = int(offset.total_seconds() // 60)
    offset_sign = '+' if offset_minutes >= 0 else '-'
    offset_hours, offset_minutes = divmod(abs(offset_minutes), 60)
    gmt_offset = f"GMT{offset_sign}{offset_hours:02d}:{offset_minutes:02d}"

    await msg.answer(
        f"🕒 Время в <b>{html.escape(region_name, quote=False)}</b>:\n"
        f"📅 {local_time.strftime('%d.%m.%Y %H:%M')} ({gmt_offset})"
    )


async def cmd_weather(msg: Message, cmd_name: str = 'погода'):
    """Погода через Open-Meteo (с редактированием сообщения)"""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    parts = msg.text.split(maxsplit=1)
    city = parts[1].strip() if len(parts) > 1 else 'Калининград'
    safe_city = html.escape(city, quote=False)

    # Отправляем сообщение "Ищу погоду..."
    status_msg = await msg.answer("🌤️ <i>Ищу погоду...</i>")

    try:
        import aiohttp

        # Получаем координаты города
        geo_url = "https://geocoding-api.open-meteo.com/v1/search"
        params = {
            'name': city,
            'count': 1,
            'language': 'ru',
            'format': 'json'
        }

        timeout = aiohttp.ClientTimeout(total=12)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            # Поиск города
            async with session.get(geo_url, params=params) as resp:
                if resp.status != 200:
                    await status_msg.edit_text(f"❌ Город '{safe_city}' не найден")
                    return

                geo_data = await resp.json()

            if not geo_data.get('results'):
                await status_msg.edit_text(f"❌ Город '{safe_city}' не найден")
                return

            location = geo_data['results'][0]
            lat = location['latitude']
            lon = location['longitude']
            city_name = location.get('name', city)
            country = location.get('country', '')
            safe_city_name = html.escape(str(city_name), quote=False)
            safe_country = html.escape(str(country), quote=False)

            # Обновляем статус
            await status_msg.edit_text(f"🌤️ <i>Получаю погоду для {safe_city_name}...</i>")

            # Получаем погоду
            weather_url = "https://api.open-meteo.com/v1/forecast"
            weather_params = {
                'latitude': lat,
                'longitude': lon,
                'current': 'temperature_2m,relative_humidity_2m,apparent_temperature,weather_code,wind_speed_10m,wind_gusts_10m,wind_direction_10m,pressure_msl,precipitation,rain,snowfall,uv_index',
                'daily': 'weather_code,temperature_2m_max,temperature_2m_min,precipitation_probability_max,precipitation_sum,sunrise,sunset,uv_index_max',
                'forecast_days': 3,
                'timezone': 'auto'
            }

            async with session.get(weather_url, params=weather_params) as resp:
                if resp.status != 200:
                    await status_msg.edit_text("❌ Сервис погоды временно недоступен")
                    return
                weather_data = await resp.json()

        current = weather_data['current']
        daily = weather_data.get('daily', {})

        # Коды погоды
        weather_codes = {
            0: ('☀️', 'Ясно'),
            1: ('🌤️', 'Преимущественно ясно'),
            2: ('⛅', 'Переменная облачность'),
            3: ('☁️', 'Пасмурно'),
            45: ('🌫️', 'Туман'),
            48: ('🌫️', 'Изморозь'),
            51: ('🌧️', 'Лёгкая морось'),
            53: ('🌧️', 'Морось'),
            55: ('🌧️', 'Сильная морось'),
            56: ('🌧️', 'Ледяная морось'),
            57: ('🌧️', 'Сильная ледяная морось'),
            61: ('🌧️', 'Небольшой дождь'),
            63: ('🌧️', 'Дождь'),
            65: ('🌧️', 'Сильный дождь'),
            66: ('🌧️', 'Ледяной дождь'),
            67: ('🌧️', 'Сильный ледяной дождь'),
            71: ('❄️', 'Небольшой снег'),
            73: ('❄️', 'Снег'),
            75: ('❄️', 'Сильный снег'),
            77: ('❄️', 'Снежные зёрна'),
            80: ('🌧️', 'Ливень'),
            81: ('🌧️', 'Сильный ливень'),
            82: ('🌧️', 'Очень сильный ливень'),
            85: ('❄️', 'Снегопад'),
            86: ('❄️', 'Сильный снегопад'),
            95: ('⛈️', 'Гроза'),
            96: ('⛈️', 'Гроза с градом'),
            99: ('⛈️', 'Сильная гроза с градом')
        }

        code = current.get('weather_code', 0)
        emoji, description = weather_codes.get(code, ('🌡️', 'Неизвестно'))

        # Направление ветра
        wind_dir = current.get('wind_direction_10m', 0)
        directions = ['⬆️ С', '↗️ СВ', '➡️ В', '↘️ ЮВ', '⬇️ Ю', '↙️ ЮЗ', '⬅️ З', '↖️ СЗ']
        wind_dir_text = directions[round(wind_dir / 45) % 8]

        # Давление
        pressure = current.get('pressure_msl', 0)
        precipitation = current.get('precipitation', 0)
        rain = current.get('rain', 0)
        snowfall = current.get('snowfall', 0)
        gusts = current.get('wind_gusts_10m', 0)
        uv_index = current.get('uv_index', 0)

        def format_clock(value: str) -> str:
            return value.split('T')[-1][:5] if value else '--:--'

        forecast_lines = []
        forecast_dates = daily.get('time', [])
        for index, forecast_date in enumerate(forecast_dates):
            forecast_code = daily.get('weather_code', [])[index]
            forecast_emoji, _ = weather_codes.get(forecast_code, ('🌡️', 'Неизвестно'))
            forecast_min = daily.get('temperature_2m_min', [])[index]
            forecast_max = daily.get('temperature_2m_max', [])[index]
            forecast_probability = daily.get('precipitation_probability_max', [])[index]
            forecast_sum = daily.get('precipitation_sum', [])[index]
            day_label = 'сегодня' if index == 0 else 'завтра' if index == 1 else forecast_date[5:]
            forecast_lines.append(
                f"{forecast_emoji} <b>{day_label}</b>: {forecast_min:.0f}...{forecast_max:.0f}°C, "
                f"осадки {forecast_probability}%, {forecast_sum:.1f} мм"
            )

        # Формируем ответ
        text = (
            f"{emoji} <b>Погода — {safe_city_name}{', ' + safe_country if safe_country else ''}</b>\n"
            f"{UI_LINE}\n"
            f"🌡 Температура: <b>{current['temperature_2m']}°C</b>\n"
            f"🤔 Ощущается: <b>{current['apparent_temperature']}°C</b>\n"
            f"📝 Описание: <b>{description}</b>\n"
            f"💧 Влажность: <b>{current['relative_humidity_2m']}%</b>\n"
            f"💨 Ветер: <b>{current['wind_speed_10m']} км/ч {wind_dir_text}</b>\n"
            f"💨 Порывы: <b>до {gusts} км/ч</b>\n"
            f"🌧 Осадки сейчас: <b>{precipitation:.1f} мм</b>"
            f"{f' (дождь {rain:.1f} мм)' if rain else ''}"
            f"{f' (снег {snowfall:.1f} мм)' if snowfall else ''}\n"
            f"☀️ UV-индекс: <b>{uv_index:.1f}</b>\n"
            f"🔵 Давление: <b>{pressure:.0f} гПа</b>\n"
            f"🌅 Восход: <b>{format_clock(daily.get('sunrise', [''])[0])}</b>  "
            f"🌇 Закат: <b>{format_clock(daily.get('sunset', [''])[0])}</b>\n\n"
            f"📅 <b>Прогноз на 3 дня</b>\n"
            + "\n".join(forecast_lines)
        )

        # Редактируем сообщение
        await status_msg.edit_text(text, disable_web_page_preview=True)

    except ImportError:
        await status_msg.edit_text("❌ Установите aiohttp: <code>pip install aiohttp</code>")
    except asyncio.TimeoutError:
        await status_msg.edit_text("⏳ Таймаут. Попробуйте позже.")
    except Exception as e:
        logger.error(f"Ошибка погоды: {e}")
        await status_msg.edit_text(f"❌ Не удалось получить погоду для '{safe_city}'")


async def cmd_random_joke(msg: Message, cmd_name: str = 'шутка'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    local_jokes = [
        "Я хотел рассказать шутку про уборку, но она пока лежит в черновиках.",
        "Мой будильник звонит так убедительно, что я каждый раз откладываю жизнь ещё на пять минут.",
        "Диалог с холодильником всегда заканчивается одинаково: он молчит, а я снова что-нибудь беру.",
        "Взрослая жизнь — это когда список дел длиннее, чем список причин всё отложить.",
        "Я не ленивый. Я просто экономлю энергию до действительно важного момента.",
    ]
    joke = html.escape(random.choice(local_jokes), quote=False)
    return await msg.answer(f"😂 <b>Шутка:</b>\n\n{joke}")


async def cmd_ship(msg: Message, cmd_name: str = 'шиперим'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    chat_users = storage.data.get('users', {}).get(str(msg.chat.id), {})
    user_ids = []
    for user_id, user_data in chat_users.items():
        if not isinstance(user_data, dict):
            continue
        try:
            parsed_user_id = int(user_id)
        except (TypeError, ValueError):
            continue
        if parsed_user_id > 0:
            user_ids.append(parsed_user_id)

    if len(user_ids) < 2:
        return await msg.answer(
            "💔 Пока не с кем шиперить: боту нужно узнать хотя бы двух участников чата."
        )

    first_id, second_id = random.sample(user_ids, 2)
    first = mention(msg.chat.id, first_id)
    second = mention(msg.chat.id, second_id)
    ship_texts = [
        f"💘 Кажется, между {first} и {second} пробежала искра! Или это просто статическое электричество.",
        f"🎬 {first} и {second} — главные герои нового сериала «Случайно оказались в одном чате».",
        f"🧲 Магнитное поле чата тянет {first} и {second} друг к другу. Учёные пока не вмешиваются.",
        f"🍿 {first} + {second}: чат уже запасся попкорном и ждёт продолжения.",
        f"🔮 Хрустальный шар предсказал: {first} и {second} однажды одновременно напишут «привет». Романтика!",
        f"🎵 Для пары {first} и {second} уже играет музыка. Правда, похоже, у кого-то включён микрофон.",
        f"🕵️ Детектив чата выяснил: {first} и {second} подозрительно хорошо смотрятся в одном сообщении.",
        f"📚 История {first} и {second} начинается с фразы: «А кто это тут у нас?»",
        f"💌 Купидон прицелился в {first} и {second}, но отвлёкся на уведомление.",
        f"🌟 Совместимость {first} и {second} проверена: вместе они создают отличную активность в чате!",
        f"🧪 Формула дня: {first} + {second} = химия. Химик ушёл за реактивами, так что это пока гипотеза.",
        f"🛳️ Корабль «{first} × {second}» отправляется в плавание! Спасательные круги — в закрепе.",
        f"🤝 {first} и {second} сегодня назначены самой неожиданной парой чата. Возражения принимаются у купидона.",
        f"🎲 Случай выбрал {first} и {second}. Даже кубик намекает: пора хотя бы поздороваться!",
        f"💫 Если бы у чата был романтический постер, на нём сегодня были бы {first} и {second}.",
    ]
    await msg.answer(random.choice(ship_texts), disable_web_page_preview=True)


@lru_cache(maxsize=1)
def load_uk_rf_articles() -> List[Dict[str, str]]:
    with UK_RF_ARTICLES_FILE.open(encoding='utf-8') as articles_file:
        article_data = json.load(articles_file)

    if not isinstance(article_data, dict) or not isinstance(article_data.get('articles'), list):
        raise ValueError(f'Некорректный формат файла статей УК РФ: {UK_RF_ARTICLES_FILE}')
    articles = article_data['articles']
    if not articles or any(
        not isinstance(article, dict)
        or not isinstance(article.get('number'), str)
        or not isinstance(article.get('title'), str)
        or not article['title'].strip()
        for article in articles
    ):
        raise ValueError(f'В файле статей УК РФ есть некорректные записи: {UK_RF_ARTICLES_FILE}')
    return articles


async def cmd_my_article(msg: Message, cmd_name: str = 'моя статья'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    articles = load_uk_rf_articles()
    today = datetime.now().date().isoformat()
    user = storage.get_user(msg.chat.id, msg.from_user.id, use_cache=False)
    state = user.get('my_article_state')
    article_by_number = {item['number']: item for item in articles}

    article_number = state.get('article_number') if isinstance(state, dict) else None
    article = (
        article_by_number.get(article_number)
        if isinstance(state, dict) and state.get('date') == today and isinstance(article_number, str)
        else None
    )
    if article is None:
        used_numbers = state.get('used_numbers', []) if isinstance(state, dict) else []
        if not isinstance(used_numbers, list):
            used_numbers = []
        used_numbers = list(dict.fromkeys(
            number for number in used_numbers if isinstance(number, str) and number in article_by_number
        ))

        if len(used_numbers) >= len(articles):
            previous_number = article_number
            used_numbers = []
            available_articles = [
                item for item in articles if item['number'] != previous_number
            ] or articles
        else:
            used_set = set(used_numbers)
            available_articles = [item for item in articles if item['number'] not in used_set]

        article = random.choice(available_articles)
        used_numbers.append(article['number'])
        user['my_article_state'] = {
            'date': today,
            'article_number': article['number'],
            'used_numbers': used_numbers,
        }
        storage.invalidate_user_cache(msg.chat.id, msg.from_user.id)
        storage.mark_dirty()
        await storage.save()

    target = mention(msg.chat.id, msg.from_user.id)
    verdict_openings = [
        f"Сегодня {target} приговаривается к",
        f"По решению суда чата сегодня {target} приговаривается к",
        f"После короткого заседания сегодня {target} приговаривается к",
        f"В этот судьбоносный день {target} приговаривается к",
        f"Народный суд постановил: сегодня {target} приговаривается к",
        f"Коллегия присяжных решила: сегодня {target} приговаривается к",
        f"Из зала суда сообщают: сегодня {target} приговаривается к",
        f"После тщательного изучения переписки {target} сегодня приговаривается к",
        f"Суд чата огласил вердикт: сегодня {target} приговаривается к",
        f"По итогам народного голосования {target} сегодня приговаривается к",
        f"Верховный чат постановил: сегодня {target} приговаривается к",
        f"Судья вынес решение: сегодня {target} приговаривается к",
        f"После совещания судей чата {target} сегодня приговаривается к",
        f"Судебное заседание завершено: сегодня {target} приговаривается к",
        f"Вердикт дня уже готов: сегодня {target} приговаривается к",
    ]
    opening = random.choice(verdict_openings)
    await msg.answer(
        f"📜 <b>Приговор дня</b>\n\n"
        f"{opening} "
        f"статье <b>{html.escape(article['number'], quote=False)}</b> — "
        f"{html.escape(article['title'], quote=False)}.",
        disable_web_page_preview=True,
    )


VALERA_CHANCE_TEMPLATES = (
    '🐻 Шанс на «{question}» — {chance}%.',
    '🔮 Валера прикинул: «{question}» случится с вероятностью {chance}%.',
    '📊 По медвежьим расчётам, шанс на «{question}» составляет {chance}%.',
    '🎲 Валера бросил воображаемый кубик: шанс на «{question}» — {chance}%.',
    '🧪 Лаборатория желейной вероятности оценивает «{question}» в {chance}%.',
    '🌟 Звёзды шепчут, что вероятность «{question}» — {chance}%.',
    '🍯 После консультации с мёдом Валера даёт «{question}» шанс {chance}%.',
    '🧸 Медвежий прогноз: «{question}» может произойти с шансом {chance}%.',
    '📈 Индекс Валеры для события «{question}» — {chance}%.',
    '🤔 Валера долго думал и постановил: шанс «{question}» равен {chance}%.',
    '🎯 Попадание в событие «{question}» оценивается в {chance}%.',
    '🌀 По версии желейной интуиции, вероятность «{question}» — {chance}%.',
    '📜 Валера вынес вердикт: «{question}» — шанс {chance}%.',
    '🐾 Следы ведут к вероятности {chance}% для события «{question}».',
    '✨ Предсказание готово: шанс, что «{question}», составляет {chance}%.',
)

VALERA_MENU_TEXT = (
    '🐻 <b>Валера на связи!</b>\n\n'
    'Вызвать можно командами <code>!валера</code>, <code>!валерка</code> или '
    '<code>!валерианыч</code>.\n\n'
    'Выбери функцию, чтобы узнать, как ей пользоваться:'
)


def valera_menu_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🎲 Бросить кубик", callback_data="valera_help_dice"),
            InlineKeyboardButton(text="🔮 Шанс события", callback_data="valera_help_chance"),
        ],
        [InlineKeyboardButton(text="🎱 Шар гадания", callback_data="valera_help_ball")],
        [
            InlineKeyboardButton(text="🪙 Монетка", callback_data="valera_help_coin"),
            InlineKeyboardButton(text="🎯 Выбор", callback_data="valera_help_choice"),
        ],
        [InlineKeyboardButton(text="💞 Совместимость", callback_data="valera_help_compatibility")],
    ])


@router.callback_query(F.data.startswith('valera_help_'))
async def valera_help_callback(call: CallbackQuery):
    action = call.data.replace('valera_help_', '', 1)
    if action == 'menu':
        await call.message.edit_text(VALERA_MENU_TEXT, reply_markup=valera_menu_keyboard())
        await call.answer()
        return
    if action == 'dice':
        text = (
            '🎲 <b>Бросок кубика</b>\n\n'
            'Нажми команду, чтобы бот отправил настоящий кубик Telegram:\n'
            '<code>!валера кубик</code>\n\n'
            'Также работают варианты <code>кость</code> и <code>кинь кубик</code>. '
            'Сообщение с командой бот удалит после броска.'
        )
    elif action == 'chance':
        text = (
            '🔮 <b>Шанс события</b>\n\n'
            'Добавь после команды событие, и Валера оценит его шуточную вероятность '
            'от 0 до 100% одной из 15 случайных фраз:\n'
            '<code>!валера инфо я сегодня съем гамбургер</code>\n\n'
            'Короткий вариант:\n'
            '<code>!валера вопрос я сегодня съем гамбургер</code>'
        )
    elif action == 'ball':
        text = (
            '🎱 <b>Шар гадания</b>\n\n'
            'Задай вопрос после слова «шар», и Валера ответит случайной фразой '
            'магического шара:\n'
            '<code>!валера шар я крутой?</code>\n\n'
            'Можно также написать <code>гадание</code> или '
            '<code>шар гадания</code>. Функция работает с алиасами '
            '<code>!валерка</code> и <code>!валерианыч</code> тоже.'
        )
    elif action == 'coin':
        text = (
            '🪙 <b>Монетка</b>\n\n'
            'Введи команду, и Валера случайно выберет орла или решку:\n'
            '<code>!валера монетка</code>\n\n'
            'Также работают команды <code>монета</code> и <code>монету</code>.'
        )
    elif action == 'choice':
        text = (
            '🎯 <b>Случайный выбор</b>\n\n'
            'Перечисли варианты через «или», вертикальную черту или запятую — '
            'Валера случайно выберет один:\n'
            '<code>!валера выбор пицца или суши</code>\n'
            '<code>!валера выбор гулять | смотреть кино</code>'
        )
    elif action == 'compatibility':
        text = (
            '💞 <b>Совместимость</b>\n\n'
            'Напиши имена или описание пары, и Валера выдаст шуточный процент '
            'совместимости от 0 до 100:\n'
            '<code>!валера совместимость я и Вася</code>'
        )
    else:
        await call.answer('Неизвестная функция', show_alert=True)
        return

    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="◀️ К функциям", callback_data="valera_help_menu")],
    ])
    await call.message.edit_text(text, reply_markup=keyboard)
    await call.answer()


async def cmd_iris(msg: Message, cmd_name: str = 'валера'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    command_text = strip_command_prefix(msg.text or '', msg.chat.id)
    query = command_text[len(cmd_name):].strip()
    normalized_query = query.casefold()

    if normalized_query in {'кость', 'кубик', 'кинь кубик'}:
        await msg.answer_dice(emoji='🎲')
        try:
            await msg.delete()
        except Exception:
            logger.debug("Не удалось удалить команду броска кубика", exc_info=True)
        return

    if normalized_query in {'монетка', 'монета', 'монету'}:
        await msg.answer('🪙')
        try:
            await msg.delete()
        except Exception:
            logger.debug("Не удалось удалить команду броска монетки", exc_info=True)
        return

    choice_prefixes = ('выбор', 'выбери')
    choice_prefix = next(
        (prefix for prefix in choice_prefixes
         if normalized_query == prefix or normalized_query.startswith(prefix + ' ')),
        None,
    )
    if choice_prefix:
        options_text = query[len(choice_prefix):].strip()
        options = [
            option.strip()
            for option in re.split(r'\s+или\s+|\s*\|\s*|,\s*', options_text, flags=re.IGNORECASE)
            if option.strip()
        ]
        if len(options) < 2:
            return await msg.answer(
                '🎯 Укажи хотя бы два варианта, например: '
                '<code>!валера выбор пицца или суши</code>'
            )
        selected = html.escape(random.choice(options), quote=False)
        return await msg.answer(f'🎯 Валера выбирает: <b>{selected}</b>!')

    compatibility_prefix = 'совместимость'
    if normalized_query == compatibility_prefix or normalized_query.startswith(compatibility_prefix + ' '):
        pair = query[len(compatibility_prefix):].strip()
        if not pair:
            return await msg.answer(
                '💞 Напиши, для кого посчитать совместимость, например: '
                '<code>!валера совместимость я и Вася</code>'
            )
        safe_pair = html.escape(pair, quote=False)
        percent = random.randint(0, 100)
        return await msg.answer(
            f'💞 Совместимость «{safe_pair}» — <b>{percent}%</b>!\n'
            f'{random.choice(("Любовь витает в воздухе!", "Звёзды одобряют!", "Валера верит в эту пару!", "Всё зависит от вас двоих!"))}'
        )

    ball_prefixes = ('шар гадания', 'шар', 'гадание', 'погадай')
    ball_prefix = next(
        (prefix for prefix in ball_prefixes
         if normalized_query == prefix or normalized_query.startswith(prefix + ' ')),
        None,
    )
    if ball_prefix:
        fortune_question = query[len(ball_prefix):].strip()
        if not fortune_question:
            return await msg.answer(
                '🎱 Задай вопрос после слова «шар», например: '
                '<code>!валера шар я крутой?</code>'
            )
        ball_answers = (
            'Бесспорно.',
            'Это предрешено.',
            'Никаких сомнений.',
            'Определённо да.',
            'Можешь быть уверен.',
            'Мне кажется — да.',
            'Скорее всего.',
            'Знаки говорят — да.',
            'Ответ туманный, попробуй позже.',
            'Спроси ещё раз.',
            'Пока неясно.',
            'Сейчас лучше не предсказывать.',
            'Даже шар затрудняется ответить.',
            'Не рассчитывай на это.',
            'Мой ответ — нет.',
            'Перспективы не очень.',
            'Весьма сомнительно.',
            'Шар говорит: «Лучше спроси после мёда».',
            'Судя по всему — да, но шар может ошибаться.',
            'Вероятность высока, но решать тебе.',
        )
        safe_question = html.escape(fortune_question, quote=False)
        answer = random.choice(ball_answers)
        return await msg.answer(
            f'🎱 <b>Шар гадания</b>\n'
            f'❔ «{safe_question}»\n'
            f'🔮 {answer}'
        )

    question = None
    if cmd_name.endswith(' вопрос'):
        question = query
    elif normalized_query == 'инфо' or normalized_query.startswith('инфо '):
        question = query[len('инфо'):].strip()
    elif normalized_query == 'вопрос' or normalized_query.startswith('вопрос '):
        question = query[len('вопрос'):].strip()

    if question is not None:
        if not question:
            return await msg.answer(
                '💬 Напиши событие для оценки, например: '
                '<code>!валера инфо я сегодня съем гамбургер</code> '
                'или <code>!валера вопрос я сегодня съем гамбургер</code>'
            )
        safe_question = html.escape(question, quote=False)
        chance = random.randint(0, 100)
        template = random.choice(VALERA_CHANCE_TEMPLATES)
        return await msg.answer(template.format(question=safe_question, chance=chance))

    await msg.answer(VALERA_MENU_TEXT, reply_markup=valera_menu_keyboard())


# ==================== Ранги ====================

async def cmd_promote(msg: Message, cmd_name: str = 'повысить'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not await require_telegram_admin(msg):
        return
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return await msg.answer("❌ Недостаточно прав!")

    parts = msg.text.split()

    tid = None
    rank_arg = None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            rank_arg = parts[1]
    else:
        if len(parts) < 2:
            return await msg.answer("❌ <code>повысить @user 3</code> или ответом")
        target_mention = get_target_mention_span(msg, parts[1])
        tid = await get_target(msg, parts[1])
        if not tid:
            return await msg.answer("❌ Пользователь не найден")
        if target_mention:
            trailing = msg.text[target_mention[2]:].strip().split()
            if trailing:
                rank_arg = trailing[0]
        elif len(parts) > 2:
            rank_arg = parts[2]

    if not tid:
        return await msg.answer("❌ Пользователь не найден")

    chat_owner = storage.data.get('chat_owners', {}).get(str(msg.chat.id), {})
    if isinstance(chat_owner, dict) and chat_owner.get('user_id') == tid:
        return await msg.answer("❌ Нельзя изменить ранг владельца чата.")

    current = storage.get_user(msg.chat.id, tid).get('rank', 0)
    actor_rank = storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0)
    if tid == msg.from_user.id or current >= actor_rank:
        return await msg.answer("❌ Нельзя менять свой ранг или ранг равного/старшего администратора.")
    try:
        if rank_arg and rank_arg.startswith('+'):
            new_rank = current + int(rank_arg[1:])
        elif rank_arg and rank_arg.startswith('-'):
            new_rank = max(0, current - int(rank_arg[1:]))
        elif rank_arg:
            new_rank = int(rank_arg)
        else:
            new_rank = current + 1
    except:
        return await msg.answer("❌ Неверный ранг. Используйте число, +N или -N")

    if new_rank < 0 or new_rank > MAX_RANK:
        return await msg.answer(f"❌ Ранг 0-{MAX_RANK}")
    if new_rank >= actor_rank:
        return await msg.answer("❌ Нельзя назначить ранг, равный вашему или выше.")

    storage.get_user(msg.chat.id, tid)['rank'] = new_rank
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"🎉 {mention(msg.chat.id, tid)}: {get_rank_name(msg.chat.id, current)} → {get_rank_name(msg.chat.id, new_rank)}",
                     disable_web_page_preview=True)


async def cmd_demote(msg: Message, cmd_name: str = 'понизить'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not await require_telegram_admin(msg):
        return
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return await msg.answer("❌ Недостаточно прав!")

    parts = msg.text.split()

    tid = None
    rank_arg = None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            rank_arg = parts[1]
    else:
        if len(parts) < 2:
            return await msg.answer("❌ <code>понизить @user</code> или ответом")
        target_mention = get_target_mention_span(msg, parts[1])
        tid = await get_target(msg, parts[1])
        if target_mention:
            trailing = msg.text[target_mention[2]:].strip().split()
            if trailing:
                rank_arg = trailing[0]
        elif len(parts) > 2:
            rank_arg = parts[2]

    if not tid:
        return await msg.answer("❌ <code>понизить @user</code> или ответом")

    chat_owner = storage.data.get('chat_owners', {}).get(str(msg.chat.id), {})
    if isinstance(chat_owner, dict) and chat_owner.get('user_id') == tid:
        return await msg.answer("❌ Нельзя изменить ранг владельца чата.")

    current = storage.get_user(msg.chat.id, tid).get('rank', 0)
    actor_rank = storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0)
    if tid == msg.from_user.id or current >= actor_rank:
        return await msg.answer("❌ Нельзя менять свой ранг или ранг равного/старшего администратора.")
    try:
        if rank_arg and rank_arg.startswith('+'):
            new_rank = current + int(rank_arg[1:])
        elif rank_arg and rank_arg.startswith('-'):
            new_rank = max(0, current - int(rank_arg[1:]))
        elif rank_arg:
            new_rank = int(rank_arg)
        else:
            new_rank = max(0, current - 1)
    except:
        return await msg.answer("❌ Неверный ранг. Используйте число, +N или -N")

    if new_rank < 0 or new_rank > MAX_RANK:
        return await msg.answer(f"❌ Ранг 0-{MAX_RANK}")
    if new_rank >= actor_rank:
        return await msg.answer("❌ Нельзя назначить ранг, равный вашему или выше.")

    storage.get_user(msg.chat.id, tid)['rank'] = new_rank
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"📉 {mention(msg.chat.id, tid)}: {get_rank_name(msg.chat.id, current)} → {get_rank_name(msg.chat.id, new_rank)}",
                     disable_web_page_preview=True)


# ==================== Погоняло и ник ====================

async def _get_native_tag_permissions(chat_id: int, target_id: int) -> Tuple[bool, bool, bool]:
    """Проверяет, можно ли менять нативные Telegram-теги в этом чате."""
    try:
        bot_member = await bot.get_chat_member(chat_id, bot.id)
        target_member = await bot.get_chat_member(chat_id, target_id)
    except Exception as e:
        logger.warning(f"Не удалось проверить права для Telegram-тега в {chat_id}: {e}")
        return False, False, False

    target_is_admin = target_member.status in ('administrator', 'creator')
    bot_can_set_title = (
        bot_member.status == 'creator'
        or (
            bot_member.status == 'administrator'
            and bool(getattr(bot_member, 'can_promote_members', False))
        )
    )
    bot_can_manage_tags = (
        bot_member.status == 'creator'
        or (
            bot_member.status == 'administrator'
            and bool(getattr(bot_member, 'can_manage_tags', False))
        )
    )
    return target_is_admin, target_is_admin and bot_can_set_title, bot_can_manage_tags

async def cmd_pogonialo(msg: Message, cmd_name: str = 'погоняло'):
    """Устанавливает/сбрасывает тег пользователя.
    Примеры:
      !погоняло Крутой чел
      !погоняло @user Крутой
      !погоняло сбросить
    """
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return

    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    raw = msg.text.strip()
    raw = strip_command_prefix(raw, msg.chat.id)

    args = raw[len(cmd_name):].strip() if raw.lower().startswith(cmd_name.lower()) else raw
    if not args:
        user_tag = html.escape((storage.get_user(msg.chat.id, msg.from_user.id).get('custom_tag') or '').strip(), quote=False)
        return await msg.answer(
            "🏷️ <b>Погоняло</b>\n\n"
            f"Текущий тег: <b>{user_tag or 'не установлен'}</b>\n\n"
            f"<code>!погоняло Крутой чел</code> — установить себе\n"
            f"<code>!погоняло @user Крутой</code> — для админа\n"
            f"<code>!погоняло сбросить</code> — убрать\n"
            f"<i>Лимит: до {MAX_TAG_LENGTH} символов</i>"
        )

    parts = args.split(maxsplit=2)
    target_id = None
    target_name = None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        target_id = msg.reply_to_message.from_user.id
        target_name = args.strip()
        is_other_user = target_id != msg.from_user.id
    elif parts and parts[0].startswith('@'):
        target_id = await get_target(msg, parts[0])
        is_other_user = target_id != msg.from_user.id if target_id else True
        if is_other_user and storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) < 1:
            return await msg.answer("❌ Сменить тег другому человеку могут только администраторы.")
        if not target_id:
            return await msg.answer("❌ Не удалось найти пользователя.")
        if len(parts) < 2:
            return await msg.answer("❌ Укажите тег после @user. Пример: <code>!погоняло @user Крутой</code>")
        target_name = parts[1].strip()
        if len(parts) > 2:
            target_name = ' '.join(parts[1:]).strip()
    else:
        target_id = msg.from_user.id
        target_name = args.strip()
        is_other_user = False

    if is_other_user and storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) < 1:
        return await msg.answer("❌ Сменить тег другому человеку могут только администраторы.")

    if target_name.lower() in ('сбросить', 'очистить', 'reset'):
        storage.get_user(msg.chat.id, target_id)['custom_tag'] = ''
        storage.invalidate_user_cache(msg.chat.id, target_id)
        mention_cache.invalidate(f"mention_{msg.chat.id}_{target_id}")
        storage.mark_dirty()
        await storage.save()

        target_is_admin, can_set_title, bot_can_manage_tags = await _get_native_tag_permissions(msg.chat.id, target_id)
        if can_set_title:
            try:
                await bot.set_chat_administrator_custom_title(msg.chat.id, target_id, "")
            except Exception:
                pass

        if target_is_admin:
            return await msg.answer(
                "💡 Это админский Telegram-тег. Бот не меняет его напрямую; "
                "изменяйте вручную через настройки администратора."
            )

        tag_error = None
        if bot_can_manage_tags:
            try:
                await bot.set_chat_member_tag(msg.chat.id, target_id, "")
            except Exception as e:
                tag_error = str(e)
                logger.warning(f"set_chat_member_tag (сброс) не сработал для {target_id} в {msg.chat.id}: {e}")
        else:
            return await msg.answer("❌ У бота нет права управления тегами участников Telegram.")

        if tag_error:
            return await msg.answer("✅ Тег сброшен.\n⚠️ Видимый тег в Telegram не удалось убрать. Проверьте права бота.")
        return await msg.answer("✅ Тег сброшен.")

    text = target_name.strip()
    if not text:
        return await msg.answer("❌ Тег не может быть пустым.")
    if len(text) > MAX_TAG_LENGTH:
        return await msg.answer(f"❌ Слишком длинный тег. Максимум {MAX_TAG_LENGTH} символов.")
    if len(text) > 16:
        return await msg.answer("❌ Админский тег Telegram может содержать максимум 16 символов.")

    storage.get_user(msg.chat.id, target_id)['custom_tag'] = text
    storage.invalidate_user_cache(msg.chat.id, target_id)
    mention_cache.invalidate(f"mention_{msg.chat.id}_{target_id}")
    storage.mark_dirty()
    await storage.save()

    tag_errors = []
    target_is_admin, can_set_title, bot_can_manage_tags = await _get_native_tag_permissions(msg.chat.id, target_id)
    if can_set_title:
        try:
            await bot.set_chat_administrator_custom_title(msg.chat.id, target_id, text)
        except Exception as e:
            logger.warning(f"set_chat_administrator_custom_title не сработал для {target_id} в {msg.chat.id}: {e}")

    if target_is_admin:
        if target_id == msg.from_user.id:
            result_msg = (
                "💡 Это админский Telegram-тег. Бот не меняет его напрямую."
                "\nОткройте список пользователей группы, выберите себя и"
                " измените админское звание/тег вручную."
            )
        else:
            result_msg = (
                "💡 Это админский Telegram-тег. Бот не меняет его напрямую для администраторов."
                f"\nДля {mention(msg.chat.id, target_id)} нужно менять вручную через настройки группы."
            )
        return await msg.answer(result_msg)

    if bot_can_manage_tags:
        try:
            await bot.set_chat_member_tag(msg.chat.id, target_id, text)
        except Exception as e:
            tag_errors.append(f"видимый тег: {e}")
            logger.warning(f"set_chat_member_tag не сработал для {target_id} в {msg.chat.id}: {e}")
    else:
        return await msg.answer("❌ У бота нет права управления тегами участников Telegram.")

    if target_id == msg.from_user.id:
        result_msg = f"✅ Погоняло изменено!\n🏷️ <b>{text}</b>"
    else:
        result_msg = f"✅ Погоняло для {mention(msg.chat.id, target_id)} изменено на <b>{text}</b>"

    if tag_errors:
        result_msg += "\n⚠️ Telegram не применил тег: <code>" + html.escape("; ".join(tag_errors)) + "</code>"

    return await msg.answer(result_msg)


async def cmd_nick(msg: Message, cmd_name: str = 'ник'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    text = msg.text.strip()

    # Очищаем от префиксов
    text = strip_command_prefix(text, msg.chat.id)

    # Убираем слово "ник"
    if text.lower().startswith('ник'):
        args = text[3:].strip()
    else:
        args = text

    if not args:
        u = storage.get_user(msg.chat.id, msg.from_user.id)
        custom = html.escape(str(u.get('custom_name') or ''), quote=False)
        return await msg.answer(
            f"👤 <b>Ваше отображаемое имя:</b> {get_display_name(msg.chat.id, msg.from_user.id)}\n"
            f"{'📝 Кастомное: ' + custom if custom else '💡 У вас нет кастомного ника'}\n\n"
            f"<code>ник Новое Имя</code> — установить ник\n"
            f"<code>ник @user</code> — посмотреть чужой ник\n"
            f"<code>ник @user Новое Имя</code> — изменить ник участника (администратору)\n"
            f"<code>ник Новое Имя</code> ответом на сообщение — изменить ник участника (администратору)\n"
            f"<code>ник сбросить</code> — убрать кастомный ник"
        )

    target_id = msg.from_user.id
    new_name = args
    if msg.reply_to_message and msg.reply_to_message.from_user:
        target_id = msg.reply_to_message.from_user.id
    elif args.split() and get_target_mention_span(msg, args.split(maxsplit=1)[0]):
        target_mention = get_target_mention_span(msg, args.split(maxsplit=1)[0])
        target_id = target_mention[0]
        new_name = msg.text[target_mention[2]:].strip()
        if not new_name:
            u = storage.get_user(msg.chat.id, target_id)
            custom_name = html.escape(str(u.get('custom_name') or 'не установлен'), quote=False)
            return await msg.answer(
                f"👤 <b>{mention(msg.chat.id, target_id)}</b>\n📝 Ник: {custom_name}",
                disable_web_page_preview=True,
            )
    elif args.startswith('@'):
        target_parts = args.split(maxsplit=1)
        target_arg = target_parts[0]
        if len(target_parts) == 1:
            tid = await get_target(msg, target_arg)
            if not tid:
                return await msg.answer("❌ Не удалось найти пользователя.")
            u = storage.get_user(msg.chat.id, tid)
            custom_name = html.escape(str(u.get('custom_name') or 'не установлен'), quote=False)
            return await msg.answer(
                f"👤 <b>{mention(msg.chat.id, tid)}</b>\n📝 Ник: {custom_name}",
                disable_web_page_preview=True)

        target_id = await get_target(msg, target_arg)
        if not target_id:
            return await msg.answer("❌ Не удалось найти пользователя.")
        new_name = target_parts[1].strip()

    if target_id != msg.from_user.id:
        rank = storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0)
        if rank < 1:
            return await msg.answer("❌ Изменять ник другим участникам могут только администраторы.")

    if new_name.lower() == 'сбросить':
        storage.get_user(msg.chat.id, target_id)['custom_name'] = ''
        storage.invalidate_user_cache(msg.chat.id, target_id)
        storage.mark_dirty()
        await storage.save()
        if target_id == msg.from_user.id:
            return await msg.answer("✅ Кастомный ник сброшен.")
        return await msg.answer(f"✅ Кастомный ник для {mention(msg.chat.id, target_id)} сброшен.")

    if len(new_name) > 64:
        return await msg.answer("❌ Слишком длинное имя (макс. 64 символа)")
    if not new_name:
        return await msg.answer("❌ Ник не может быть пустым.")

    old = get_display_name(msg.chat.id, target_id)
    storage.get_user(msg.chat.id, target_id)['custom_name'] = new_name
    storage.invalidate_user_cache(msg.chat.id, target_id)

    storage.mark_dirty()
    await storage.save()

    safe_new_name = html.escape(new_name, quote=False)
    if target_id == msg.from_user.id:
        return await msg.answer(f"✅ Ник изменён!\n📝 {old} → <b>{safe_new_name}</b>")
    return await msg.answer(
        f"✅ Ник для {mention(msg.chat.id, target_id)} изменён!\n📝 {old} → <b>{safe_new_name}</b>")


async def cmd_report(msg: Message, cmd_name: str = 'репорт'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    parts = (msg.text or '').split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        return await msg.answer("❌ Напишите текст жалобы: <code>!репорт описание</code>")

    report_text = html.escape(parts[1].strip()[:1500], quote=False)
    try:
        admins = await bot.get_chat_administrators(msg.chat.id)
    except Exception as exc:
        logger.error("Не удалось получить администраторов чата %s для репорта: %s", msg.chat.id, exc)
        return await msg.answer("❌ Не удалось найти администраторов чата. Попробуйте позже.")
    recipients = [admin.user for admin in admins if not admin.user.is_bot]
    if not recipients:
        return await msg.answer("❌ В этом чате не удалось найти администраторов для отправки жалобы.")

    notification = (
        f"🚨 <b>Жалоба из чата</b>\n"
        f"Чат: <code>{msg.chat.id}</code>\n"
        f"От: {mention(msg.chat.id, msg.from_user.id)}\n\n"
        f"{report_text}"
    )
    delivered = 0
    for admin in recipients:
        try:
            await bot.send_message(admin.id, notification, disable_web_page_preview=True)
            delivered += 1
        except Exception as exc:
            logger.warning(
                "Не удалось доставить репорт администратору %s чата %s: %s",
                admin.id, msg.chat.id, exc
            )

    user = storage.get_user(msg.chat.id, msg.from_user.id)
    user['reports_sent'] = user.get('reports_sent', 0) + 1
    storage.mark_dirty()
    await storage.save()

    if delivered:
        return await msg.answer(f"✅ Жалоба отправлена администраторам ({delivered}/{len(recipients)}).")
    return await msg.answer(
        "❌ Не удалось доставить жалобу администраторам. Возможно, они не открывали боту личный чат."
    )


async def cmd_anti_moderation(msg: Message, cmd_name: str = 'антимодерация'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    settings = storage.get_chat_settings(msg.chat.id)
    settings['anti_moderation'] = not settings.get('anti_moderation', True)
    storage.invalidate_chat_settings_cache(msg.chat.id);
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"Анти-модерация: {'🛡️ включена' if settings['anti_moderation'] else '⚠️ выключена'}")


async def cmd_anti_spam(msg: Message, cmd_name: str = 'антиспам'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return await msg.answer("❌ Недостаточно прав! Требуется ранг 5+")

    settings = storage.get_chat_settings(msg.chat.id)
    anti_spam_settings = settings.get('anti_spam', {})
    current = anti_spam_settings.get('enabled', True)

    anti_spam_settings['enabled'] = not current
    settings['anti_spam'] = anti_spam_settings
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()

    status = "🛡️ включена" if anti_spam_settings['enabled'] else "⚠️ выключена"
    await msg.answer(
        f"🛡️ <b>Анти-спам система</b>\n\n"
        f"Статус: {status}\n\n"
        "Проверяет сообщения и команды (12+ за 10 секунд или 31+ за минуту), "
        "повторы, короткий флуд, капс, ссылки, массовые упоминания, стикеры и GIF.\n"
        "Также отклоняет частые нажатия кнопок (11+ за 5 секунд). "
        "При спаме сообщениями удаляет их и временно ограничивает отправку."
    )


# ==================== ДК-система ====================

def get_all_commands() -> List[str]:
    """Возвращает отсортированный список уникальных команд"""
    return sorted(list(set(COMMANDS.keys())))


# Встроенный минимальный ранг для функций-обработчиков команд. Должен
# соответствовать значениям min_rank, передаваемым в check_access()
# внутри каждой функции.
FUNCTION_MIN_RANK = {
    'cmd_rank_rename': 5,
    'cmd_mute': 1, 'cmd_unmute': 1,
    'cmd_ban': 3, 'cmd_unban': 3,
    'cmd_warn': 1,
    'cmd_mute_list': 1,
    'cmd_ban_list': 3,
    'cmd_warn_list': 1,
    'cmd_unwarn': 2,
    'cmd_del': 1,
    'cmd_pin': 2,
    'cmd_purge': 2,
    'cmd_give_award': 4, 'cmd_rem_award': 4,
    'cmd_add_phrase': 1, 'cmd_del_phrase': 1,
    'cmd_welcome': 2, 'cmd_farewell': 2,
    'cmd_add_rule': 4, 'cmd_clear_rules': 4,
    'cmd_promote': 5, 'cmd_demote': 5,
    'cmd_anti_moderation': 5, 'cmd_anti_spam': 5,
    'cmd_dk_set': 5, 'cmd_dk_enable': 5, 'cmd_dk_disable': 5,
    'cmd_ldk_add': 5, 'cmd_ldk_rem': 5, 'cmd_dk_menu': 5,
    'cmd_ping': 5, 'cmd_backup': 5, 'cmd_restore': 5,
    'cmd_pic_toggle': 5,
    'cmd_forward': 3,
}

# Встроенный минимальный ранг по КАЖДОЙ команде/алиасу (не только
# "основному" названию) — строится автоматически из COMMANDS, чтобы
# алиасы одной функции (напр. "-мут"/"размут", "warn"/"пред") всегда
# показывали тот же реальный ранг, что и check_access(). Если команды
# нет здесь, по умолчанию она реально доступна всем (min_rank = 0).
DEFAULT_COMMAND_MIN_RANK = {
    cmd: FUNCTION_MIN_RANK[func]
    for cmd, func in COMMANDS.items()
    if func in FUNCTION_MIN_RANK
}


DK_CATEGORIES = {
    'info': ("📊 Инфо и статистика", [
        (['кто я', 'профиль'], None),
        (['кто ты'], None),
        (['кто админ'], None),
        (['ранг', 'ранги'], None),
        (['ид'], None),
        (['топ'], None),
        (['статистика чата', 'статистика'], None),
        (['опрос'], None),
        (['погода', 'п'], None),
        (['шутка'], None),
        (['шиперим'], None),
        (['моя статья'], None),
        (['валера'], None),
    ]),
    'moderation': ("🛡️ Модерация", [
        (['мут', 'размут', '-мут'], None),
        (['мутлист', 'муты', 'мутылист', 'список мутов', 'mutelist', 'mutes'], None),
        (['бан', 'разбан', '-бан'], None),
        (['банлист', 'баны', 'список банов', 'banlist', 'bans'], None),
        (['пред', 'варн', 'warn'], None),
        (['преды', 'варны', 'warns'], None),
        (['варнлист', 'предлист', 'варнылист', 'предупреждения', 'список предупреждений',
          'warnlist', 'warninglist', 'warningslist'], None),
        (['снятьпред', 'снятьварн', '-пред', '-варн', 'unwarn'], None),
        (['-смс'], None),
        (['пин'], None),
        (['очистить'], None),
        (['повысить'], None),
        (['понизить'], None),
        (['репорт'], None),
        (['ник'], None),
    ]),
    'awards': ("🏆 Награды и браки", [
        (['наградить', 'снять награду'], None),
        (['мои награды'], None),
        (['топ наград'], None),
        (['брак', 'принять брак', 'отклонить брак'], None),
        (['развод'], None),
        (['браки'], None),
    ]),
    'phrases': ("💬 Фразы, приветствия, правила", [
        (['добавить фразу', 'удалить фразу'], None),
        (['фразы'], None),
        (['статистика фраз'], None),
        (['показать фразу'], None),
        (['приветствие'], None),
        (['прощание текст'], None),
        (['правила'], None),
        (['добавитьправило'], None),
        (['очиститьправила'], None),
    ]),
    'games': ("🎮 Игры", [
        (['игры', 'игра', 'game', 'играть'], None),
        (['кнб', 'кнб бот'], None),
        (['камень', 'ножницы', 'бумага'], None),
        (['крестики нолики', 'ttt'], None),
        (['wordle', 'вордле', 'вордл', 'слово', 'угадай слово'], None),
    ]),
    'settings': ("⚙️ Настройки и ДК", [
        (['антимодерация'], None),
        (['антиспам'], None),
        (['дк'], None),
        (['+дк', '-дк'], None),
        (['+лдк', '-лдк'], None),
        (['дкм'], None),
    ]),
    'admin': ("🛠️ Админ", [
        (['общий сбор'], None),
        (['бэкап'], None),
        (['восстановить'], None),
        (['перед'], None),
        (['название ранга', 'переранг'], None),
        (['пик выкл', 'пик вкл', 'pic off', 'pic on'], None),
    ]),
}


def match_dk_command(tokens: List[str]) -> tuple:
    """Ищет команду ДК в начале списка токенов: команды могут состоять
    из 1 или 2 слов. Возвращает
    (найденная_команда, оставшиеся_токены) либо (None, tokens), если
    совпадение не найдено. Пробуем сначала 2 слова, чтобы не потерять
    составные команды."""
    if len(tokens) >= 2:
        two_word = f"{tokens[0]} {tokens[1]}".lower().strip()
        if two_word in COMMANDS:
            return two_word, tokens[2:]
    if tokens:
        one_word = tokens[0].lower().strip()
        if one_word in COMMANDS:
            return one_word, tokens[1:]
    return None, tokens


def dk_info_main_kb() -> InlineKeyboardMarkup:
    keys = list(DK_CATEGORIES.keys())
    rows = []
    for i in range(0, len(keys), 2):
        row = [InlineKeyboardButton(text=DK_CATEGORIES[k][0], callback_data=f"dkinfo_{k}")
               for k in keys[i:i + 2]]
        rows.append(row)
    rows.append([InlineKeyboardButton(text="❌ Закрыть", callback_data="dkinfo_close")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def dk_info_section_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="◀️ Назад", callback_data="dkinfo_back")]
    ])


def dk_info_section_text(chat_id: int, section: str) -> str:
    try:
        label, cmd_groups = DK_CATEGORIES[section]
        chat_id_str = str(chat_id)
        acc = storage.data['command_access'].get(chat_id_str, {})
        personal = storage.data['personal_access'].get(chat_id_str, {})

        lines = [f"🔐 <b>{label}</b>\n"]
        
        if not cmd_groups:
            return "\n".join(lines) + "\n(нет команд)"
        
        for cmd_entry in cmd_groups:
            # Каждый элемент cmd_groups — кортеж (variants_list, extra_info)
            if not isinstance(cmd_entry, (list, tuple)) or not cmd_entry:
                logger.warning(f"Пустой или невалидный cmd_entry в {section}")
                continue

            cmd_variants = cmd_entry[0]
            if not isinstance(cmd_variants, (list, tuple)) or not cmd_variants:
                logger.warning(f"Пустой или невалидный cmd_variants в {section}")
                continue

            primary_cmd = cmd_variants[0]
            if not primary_cmd:
                logger.warning(f"Пустая первая команда в {section}")
                continue
            
            try:
                level = acc.get(primary_cmd)
                if level is None:
                    default_rank = DEFAULT_COMMAND_MIN_RANK.get(primary_cmd, 0)
                    if default_rank:
                        status = f"🔒 уровень {default_rank}+ <i>(по умолчанию)</i>"
                    else:
                        status = "✅ доступна всем <i>(по умолчанию)</i>"
                elif level == 9:
                    status = "❌ отключена"
                elif level == 0:
                    status = "✅ доступна всем"
                else:
                    status = f"🔒 уровень {level}+"
                
                p_users = personal.get(primary_cmd, [])
                extra = f" · 👤 личный доступ: {len(p_users)}" if p_users else ""
                
                # Выводим все вариации команды с защитой от пустых строк
                cmd_list = [str(cmd).strip() for cmd in cmd_variants if cmd]
                if not cmd_list:
                    continue
                    
                cmd_str = " / ".join(f"<code>{cmd}</code>" for cmd in cmd_list)
                lines.append(f"• {cmd_str} — {status}{extra}")
            except Exception as e:
                logger.error(f"Ошибка обработки команды {primary_cmd}: {e}")
                lines.append(f"• <i>ошибка: {primary_cmd}</i>")
        
        text = "\n".join(lines)
        if not text or len(text) == 0:
            return "❌ Нет данных"
        return text
        
    except Exception as e:
        logger.error(f"dk_info_section_text ошибка в {section}: {e}", exc_info=True)
        return f"❌ Ошибка загрузки раздела: {str(e)[:100]}"


async def cmd_dk_set(msg: Message, cmd_name: str = 'дк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    parts = msg.text.split()
    if len(parts) >= 2 and parts[1].lower().strip() == 'инфо':
        return await cmd_dk_info(msg)
    if len(parts) < 3:
        all_cmds = get_all_commands()
        return await msg.answer("❌ <code>!дк команда 0-5/откл</code> или <code>!дк инфо</code>\n\n" + 
                               f"Доступно {len(all_cmds)} команд (первые 10): " + ', '.join(all_cmds[:10]))
    command, rest = match_dk_command(parts[1:])
    if command is None:
        return await msg.answer(f"❌ Неизвестная команда '{parts[1]}'\n\nУкажите команду из доступных")
    if not rest:
        return await msg.answer("❌ Уровень 0-5 или откл")
    level_token = rest[0]
    level = 9 if level_token == 'откл' else (int(level_token) if level_token.isdigit() else None)
    if level is None or not (0 <= level <= 5):
        return await msg.answer("❌ Уровень 0-5 или откл")
    command_access = storage.data['command_access'].setdefault(str(msg.chat.id), {})
    for alias in get_command_aliases(command):
        command_access[alias] = level
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"✅ Доступ к команде '{command}' установлен на уровень {level}")


async def cmd_dk_menu(msg: Message, cmd_name: str = 'дкм'):
    """Быстрый доступ к меню ДК (алиас '!дк инфо'), с той же проверкой доступа."""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    await cmd_dk_info(msg)


async def cmd_dk_info(msg: Message):
    acc = storage.data['command_access'].get(str(msg.chat.id), {})
    total = sum(len(cmd_groups) for _, cmd_groups in DK_CATEGORIES.values())
    text = (f"🔐 <b>Настройки ДК</b>\n\nВыберите раздел ниже 👇\n\n"
            f"📊 Настроено вручную: {len(acc)} из {total}")
    await msg.answer(text, reply_markup=dk_info_main_kb())


@router.callback_query(F.data.startswith('dkinfo_'))
async def dk_info_callback(call: CallbackQuery):
    try:
        action = call.data.replace('dkinfo_', '', 1)
        logger.info(f"dkinfo callback: action={action}, user={call.from_user.id}, chat={call.message.chat.id}")
        
        # Закрыть - всем доступно
        if action == 'close':
            try:
                await call.message.delete()
            except Exception as e:
                logger.debug(f"Не удалось удалить сообщение: {e}")
            await call.answer()
            return
        
        # Назад - всем доступно
        if action == 'back':
            try:
                acc = storage.data['command_access'].get(str(call.message.chat.id), {})
                total = sum(len(cmd_groups) for _, cmd_groups in DK_CATEGORIES.values())
                text = (f"🔐 <b>Настройки ДК</b>\n\nВыберите раздел ниже 👇\n\n"
                        f"📊 Настроено вручную: {len(acc)} из {total}")
                await call.message.edit_text(text, reply_markup=dk_info_main_kb())
                await call.answer()
            except Exception as e:
                logger.error(f"Ошибка в back: {type(e).__name__}: {e}")
                await call.answer(f"❌ Ошибка back: {str(e)[:100]}", show_alert=True)
            return
        
        # Открыть раздел - требует доступ
        if not check_access(call.from_user.id, call.message.chat.id, 'дк', 5):
            await call.answer("❌ Нет доступа к ДК", show_alert=True)
            return
        
        if action not in DK_CATEGORIES:
            logger.warning(f"Unknown dkinfo section: {action}")
            await call.answer(f"❌ Неизвестный раздел: {action}", show_alert=True)
            return
            
        try:
            logger.debug(f"Генерирую текст для {action}...")
            text = dk_info_section_text(call.message.chat.id, action)
            logger.debug(f"Текст сгенерирован ({len(text)} символов), редактирую сообщение...")
            await call.message.edit_text(text, reply_markup=dk_info_section_kb())
            logger.info(f"Успешно открыт раздел {action}")
            await call.answer()
        except Exception as e:
            logger.error(f"Ошибка в dkinfo_{action}: {type(e).__name__}: {e}", exc_info=True)
            await call.answer(f"❌ {type(e).__name__}: {str(e)[:80]}", show_alert=True)
        
    except Exception as e:
        logger.error(f"dk_info_callback критическая ошибка: {type(e).__name__}: {e}", exc_info=True)
        try:
            await call.answer(f"❌ Критическая ошибка: {str(e)[:80]}", show_alert=True)
        except:
            logger.error("Не удалось отправить алерт об ошибке")


async def cmd_dk_enable(msg: Message, cmd_name: str = '+дк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    command = ' '.join(msg.text.split()[1:]).lower().strip()
    if command not in COMMANDS:
        return await msg.answer(f"❌ Неизвестная команда '{command}'")
    command_access = storage.data['command_access'].setdefault(str(msg.chat.id), {})
    for alias in get_command_aliases(command):
        command_access[alias] = 0
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"✅ Команда '{command}' включена (доступна всем)")


async def cmd_dk_disable(msg: Message, cmd_name: str = '-дк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    command = ' '.join(msg.text.split()[1:]).lower().strip()
    if command not in COMMANDS:
        return await msg.answer(f"❌ Неизвестная команда '{command}'")
    command_access = storage.data['command_access'].setdefault(str(msg.chat.id), {})
    for alias in get_command_aliases(command):
        command_access[alias] = 9
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"❌ Команда '{command}' отключена")


async def cmd_ldk_add(msg: Message, cmd_name: str = '+лдк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    parts = msg.text.split()
    if len(parts) < 3:
        return await msg.answer("❌ <code>!+лдк команда @user</code>")
    command, rest = match_dk_command(parts[1:])
    if command is None:
        return await msg.answer(f"❌ Неизвестная команда '{parts[1]}'")
    if not rest:
        return await msg.answer("❌ <code>!+лдк команда @user</code>")
    tid = await get_target(msg, rest[0])
    if not tid:
        return await msg.answer("❌ Пользователь не найден")
    personal = storage.data['personal_access'].setdefault(str(msg.chat.id), {})
    aliases = get_command_aliases(command)
    if any(tid in personal.get(alias, []) for alias in aliases):
        return await msg.answer(f"⚠️ У {mention(msg.chat.id, tid)} уже есть личный доступ к команде '{command}'",
                                 disable_web_page_preview=True)
    for alias in aliases:
        personal.setdefault(alias, []).append(tid)
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"✅ Личный доступ к команде '{command}' выдан {mention(msg.chat.id, tid)}", disable_web_page_preview=True)


async def cmd_ldk_rem(msg: Message, cmd_name: str = '-лдк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    parts = msg.text.split()
    if len(parts) < 3:
        return await msg.answer("❌ <code>!-лдк команда @user</code>")
    command, rest = match_dk_command(parts[1:])
    if command is None:
        return await msg.answer(f"❌ Неизвестная команда '{parts[1]}'")
    if not rest:
        return await msg.answer("❌ <code>!-лдк команда @user</code>")
    tid = await get_target(msg, rest[0])
    if not tid:
        return await msg.answer("❌ Пользователь не найден")
    personal = storage.data['personal_access'].get(str(msg.chat.id), {})
    aliases = get_command_aliases(command)
    if any(tid in personal.get(alias, []) for alias in aliases):
        for alias in aliases:
            access_list = personal.get(alias, [])
            if tid in access_list:
                access_list.remove(tid)
        storage.mark_dirty();
        await storage.save()
        await msg.answer(f"✅ Доступ к команде '{command}' отозван у {mention(msg.chat.id, tid)}",
                         disable_web_page_preview=True)
    else:
        await msg.answer(f"❌ У {mention(msg.chat.id, tid)} нет личного доступа к команде '{command}'",
                         disable_web_page_preview=True)


# ==================== Админ-команды ====================

async def cmd_ping_check(msg: Message):
    """Проверяет задержку Telegram API и состояние локального хранилища."""
    storage_start = time.monotonic()
    storage.data.get('users', {})
    storage_latency = (time.monotonic() - storage_start) * 1000

    api_start = time.monotonic()
    test_msg = await msg.answer("🏓")
    send_latency = (time.monotonic() - api_start) * 1000

    edit_start = time.monotonic()
    await test_msg.edit_text("🏓 Проверка соединения…")
    edit_latency = (time.monotonic() - edit_start) * 1000

    delete_start = time.monotonic()
    await test_msg.delete()
    delete_latency = (time.monotonic() - delete_start) * 1000

    bot_info_start = time.monotonic()
    await bot.get_me()
    bot_info_latency = (time.monotonic() - bot_info_start) * 1000

    api_average = (send_latency + edit_latency + delete_latency + bot_info_latency) / 4
    if api_average < 100:
        status = "🟢 Отличное"
    elif api_average < 300:
        status = "🟡 Хорошее"
    elif api_average < 600:
        status = "🟠 Среднее"
    else:
        status = "🔴 Медленное"

    await msg.answer(
        "🏓 <b>Понг! Диагностика соединения</b>\n\n"
        f"📶 <b>Статус:</b> {status}\n\n"
        "📡 <b>Задержки Telegram API:</b>\n"
        f"├ 📤 Отправка сообщения: <code>{send_latency:.1f} мс</code>\n"
        f"├ ✏️ Редактирование: <code>{edit_latency:.1f} мс</code>\n"
        f"├ 🗑️ Удаление: <code>{delete_latency:.1f} мс</code>\n"
        f"├ 🤖 Информация о боте: <code>{bot_info_latency:.1f} мс</code>\n"
        f"└ 📊 Средняя задержка: <code>{api_average:.1f} мс</code>\n\n"
        "💾 <b>Хранилище:</b>\n"
        f"└ 📂 Чтение данных: <code>{storage_latency:.1f} мс</code>",
        disable_web_page_preview=True,
    )


async def cmd_ping(msg: Message, cmd_name: str = 'общий сбор'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    try:
        admins = await bot.get_chat_administrators(msg.chat.id)
        mentions_list = [mention(msg.chat.id, a.user) for a in admins[:20] if not a.user.is_bot]
        if mentions_list:
            await msg.answer("📢 " + ' '.join(mentions_list), disable_web_page_preview=True)
    except:
        pass


async def cmd_backup(msg: Message, cmd_name: str = 'бэкап'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    await storage.save()
    snapshot = json.loads(json.dumps(storage.data))
    snapshot['backups'] = []
    backup = {'ts': time.time(), 'data': snapshot}
    storage.data.setdefault('backups', []).append(backup)
    storage.data['backups'] = storage.data['backups'][-10:]
    filename = f"{BACKUP_DIR}/backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    temp_filename = f'{filename}.tmp'
    with open(temp_filename, 'w', encoding='utf-8') as f:
        json.dump(backup, f, ensure_ascii=False, indent=2)
        f.flush()
        os.fsync(f.fileno())
    os.replace(temp_filename, filename)
    await storage.save()
    await msg.answer(f"✅ Бэкап: {filename}")


async def cmd_restore(msg: Message, cmd_name: str = 'восстановить'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    backups = storage.data.get('backups')
    if not isinstance(backups, list) or not backups:
        return await msg.answer("❌ Нет бэкапов")
    backup = backups[-1]
    if not isinstance(backup, dict) or not isinstance(backup.get('ts'), (int, float)):
        logger.error("Последний бэкап не содержит корректную временную метку")
        return await msg.answer("❌ Последний бэкап повреждён или имеет неподдерживаемый формат.")
    backup_data = backup.get('data') if isinstance(backup, dict) else None
    if not validate_backup_data(backup_data):
        logger.error("Последний бэкап имеет некорректную структуру")
        return await msg.answer("❌ Последний бэкап повреждён или имеет неподдерживаемый формат.")

    keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text="✅ Да, восстановить",
            callback_data=f"restore_confirm_{msg.from_user.id}_{backup['ts']}",
        ),
        InlineKeyboardButton(
            text="❌ Отмена",
            callback_data=f"restore_cancel_{msg.from_user.id}_{backup['ts']}",
        ),
    ]])
    await msg.answer(
        "⚠️ <b>Подтвердите восстановление</b>\n"
        "Текущие данные будут заменены содержимым последнего бэкапа.",
        reply_markup=keyboard,
    )


def validate_backup_data(data: Any) -> bool:
    if not isinstance(data, dict):
        return False
    defaults = DataStorage._get_default_data()
    for key, default_value in defaults.items():
        if key in data and not isinstance(data[key], type(default_value)):
            return False
    users = data.get('users')
    if not isinstance(users, dict):
        return False
    for chat_users in users.values():
        if not isinstance(chat_users, dict):
            return False
        if any(not isinstance(user_data, dict) for user_data in chat_users.values()):
            return False
    return True


@router.callback_query(F.data.startswith('restore_'))
async def restore_backup_callback(call: CallbackQuery):
    if not call.message:
        return await call.answer("❌ Сообщение восстановления недоступно.", show_alert=True)

    try:
        _, action, requester_id, backup_ts = call.data.split('_', maxsplit=3)
        requester_id = int(requester_id)
        backup_ts = float(backup_ts)
    except (ValueError, AttributeError):
        logger.warning("Получены некорректные данные callback восстановления")
        return await call.answer("❌ Кнопка восстановления недействительна.", show_alert=True)

    if call.from_user.id != requester_id:
        return await call.answer("❌ Подтвердить восстановление может только инициатор.", show_alert=True)
    if not check_access(call.from_user.id, call.message.chat.id, 'восстановить', 5):
        return await call.answer("❌ Недостаточно прав.", show_alert=True)
    backups = storage.data.get('backups', [])
    backup = backups[-1] if isinstance(backups, list) and backups else None
    current_backup_ts = backup.get('ts') if isinstance(backup, dict) else None
    if (
        not isinstance(current_backup_ts, (int, float))
        or float(current_backup_ts) != backup_ts
    ):
        return await call.answer("❌ Список бэкапов изменился. Запустите восстановление заново.", show_alert=True)
    if action == 'cancel':
        await call.message.edit_text("✅ Восстановление отменено.", reply_markup=None)
        return await call.answer()
    if action != 'confirm':
        return await call.answer("❌ Неизвестное действие.", show_alert=True)

    backup_data = backup.get('data') if isinstance(backup, dict) else None
    if not validate_backup_data(backup_data):
        logger.error("Последний бэкап имеет некорректную структуру при подтверждении")
        await call.message.edit_text("❌ Бэкап повреждён или имеет неподдерживаемый формат.", reply_markup=None)
        return await call.answer("Восстановление не выполнено.", show_alert=True)

    restored_data = DataStorage._get_default_data()
    restored_data.update(backup_data)
    restored_data['backups'] = backups
    storage.data = restored_data
    user_cache.clear()
    chat_settings_cache.clear()
    mention_cache.clear()
    storage._chat_user_index.clear()
    storage.mark_dirty()
    await storage.save()
    await call.message.edit_text("✅ Данные восстановлены из последнего бэкапа.", reply_markup=None)
    await call.answer()


async def cmd_forward(msg: Message, cmd_name: str = 'перед'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 3):
        return
    parts = msg.text.split()

    tid = None
    if msg.reply_to_message:
        if len(parts) > 1:
            tid = await get_target(msg, parts[1])
        if not tid:
            return await msg.answer("❌ <code>!перед @user</code> ответом")
    else:
        return await msg.answer("❌ Ответьте на сообщение и укажите <code>!перед @user</code>")

    try:
        await msg.reply_to_message.forward(tid)
        await msg.answer("✅ Переслано")
    except Exception as e:
        logger.warning("Не удалось переслать сообщение пользователю %s: %s", tid, e)
        await msg.answer("❌ Не удалось переслать сообщение. Проверьте, что пользователь не заблокировал бота.")


# ==================== Репутация ====================

@router.message(F.reply_to_message)
async def reputation_handler(msg: Message):
    """Выдача репутации за ответ с + (работает БЕЗ !)"""

    # Игнорируем ботов
    if msg.from_user.is_bot:
        return

    # Проверяем что есть текст
    if not msg.text:
        return

    # Проверяем что ответили пользователю (не себе, не боту)
    if not msg.reply_to_message.from_user:
        return

    if msg.reply_to_message.from_user.is_bot:
        return

    if msg.from_user.id == msg.reply_to_message.from_user.id:
        return

    # Проверяем текст сообщения
    text = msg.text.strip()

    # Проверяем точное совпадение ИЛИ начинается с +
    if is_reputation_removal_message(text):
        logger.debug(f"Снижение репутации: {msg.from_user.id} -> {msg.reply_to_message.from_user.id}, текст='{text}'")
        await give_reputation(msg, remove=True)
        return
    if is_reputation_message(text):
        logger.debug(f"Репутация: {msg.from_user.id} -> {msg.reply_to_message.from_user.id}, текст='{text}'")
        await give_reputation(msg)
        return


async def give_reputation(msg: Message, remove: bool = False):
    """Начисляет или снимает один балл репутации."""
    try:
        giver_id = msg.from_user.id
        receiver_id = msg.reply_to_message.from_user.id

        giver = storage.get_user(msg.chat.id, giver_id, use_cache=False)
        receiver = storage.get_user(msg.chat.id, receiver_id, use_cache=False)

        now = time.time()
        today = datetime.now().strftime('%Y-%m-%d')
        action = 'Снижение репутации' if remove else 'Выдача репутации'
        cooldown = REPUTATION_REMOVE_COOLDOWN if remove else REPUTATION_COOLDOWN
        daily_limit = REPUTATION_REMOVE_DAILY_LIMIT if remove else REPUTATION_DAILY_LIMIT
        last_action_key = 'last_rep_removed_time_by_target' if remove else 'last_rep_time_by_target'
        daily_actions_key = 'rep_removed_today' if remove else 'rep_given_today'
        reply_to_receiver = "снимали" if remove else "повышали"

        logger.info(f"{action}: {giver_id} -> {receiver_id}")

        # Проверка кулдауна
        cooldowns = giver.get(last_action_key, {})
        if not isinstance(cooldowns, dict):
            cooldowns = {}
        cooldowns = {
            target_id: timestamp
            for target_id, timestamp in cooldowns.items()
            if now - timestamp < cooldown
        }
        last_action = cooldowns.get(str(receiver_id), 0)
        if now - last_action < cooldown:
            remaining = int(cooldown - (now - last_action))
            hours, remainder = divmod(remaining, 3600)
            minutes, seconds = divmod(remainder, 60)
            wait_parts = []
            if hours:
                wait_parts.append(f"{hours} ч")
            if minutes or hours:
                wait_parts.append(f"{minutes} мин")
            wait_parts.append(f"{seconds} сек")
            action_label = "-реп (снять 1 балл)" if remove else "+реп (добавить 1 балл)"
            msg_text = (
                f"⏳ Кулдаун на {action_label} для {mention(msg.chat.id, receiver_id)}.\n"
                f"Повторить действие можно через <b>{' '.join(wait_parts)}</b>.\n"
                "Кулдаун считается отдельно для каждого пользователя."
            )
            logger.debug(f"{action}: кулдаун для пары {giver_id} -> {receiver_id}")
            await msg.reply(msg_text, disable_web_page_preview=True)
            return

        # Проверка дневного лимита
        action_today = giver.get(daily_actions_key, {})
        today_count = action_today.get(today, 0)
        if today_count >= daily_limit:
            logger.debug(f"{action}: дневной лимит для {giver_id}")
            await msg.reply(f"❌ Дневной лимит исчерпан ({today_count}/{daily_limit})")
            return

        targets_by_day = action_today.get('targets_by_day', {})
        if not isinstance(targets_by_day, dict):
            targets_by_day = {}
        targets_today = targets_by_day.get(today, {})
        if not isinstance(targets_today, dict):
            targets_today = {}

        # Ограничиваем каждое направление одним изменением на пользователя в день.
        if str(receiver_id) in targets_today:
            logger.debug(f"{action}: {giver_id} уже изменял репутацию {receiver_id} сегодня")
            await msg.reply(f"⭐ Вы уже {reply_to_receiver} репутацию этому пользователю сегодня.")
            return

        current_reputation = receiver.get('reputation', 0)
        receiver['reputation'] = current_reputation - 1 if remove else current_reputation + 1
        logger.info(
            "✅ Репутация %s: %s -> %s, всего: %s",
            "снята" if remove else "выдана",
            giver_id,
            receiver_id,
            receiver['reputation'],
        )

        # Обновляем данные дающего
        cooldowns[str(receiver_id)] = now
        giver[last_action_key] = cooldowns

        if today not in action_today:
            action_today[today] = 0
        action_today[today] = today_count + 1

        targets_today[str(receiver_id)] = True
        action_today['targets_by_day'] = {today: targets_today}

        giver[daily_actions_key] = action_today
        total_key = 'rep_removed_total' if remove else 'rep_given_total'
        giver[total_key] = giver.get(total_key, 0) + 1

        # Сохраняем активность
        save_activity(msg.chat.id, receiver_id, 'reputation', amount=-1 if remove else 1)

        # Очищаем кэш
        storage.invalidate_user_cache(msg.chat.id, giver_id)
        storage.invalidate_user_cache(msg.chat.id, receiver_id)
        storage.mark_dirty()
        await storage.save()

        # Отправляем подтверждение
        total_rep = receiver['reputation']
        await msg.reply(
            f"⭐ {'-1' if remove else '+1'} {mention(msg.chat.id, receiver_id)}\n"
            f"📊 Репутация: {total_rep}",
            disable_web_page_preview=True
        )

    except Exception as e:
        logger.error(f"Ошибка выдачи репутации: {type(e).__name__}: {e}", exc_info=True)
        try:
            await msg.reply(f"❌ Ошибка репутации: {str(e)[:80]}")
        except:
            pass


# ==================== Проверка мутов ====================

async def check_mutes():
    while True:
        await asyncio.sleep(MUTE_CHECK_INTERVAL)
        try:
            now = time.time()
            for cid in list(storage.data.get('mutes', {}).keys()):
                mutes = storage.data['mutes'][cid]
                if not isinstance(mutes, list):
                    continue
                expired = [
                    m for m in mutes
                    if m.get('permanent') is not True
                    and isinstance(m.get('expire_time'), (int, float))
                    and now >= m['expire_time']
                ]
                removed_any = False
                for m in expired:
                    try:
                        await bot.restrict_chat_member(int(cid), m['user_id'], ChatPermissions(
                            can_send_messages=True,
                            can_send_media_messages=True,
                            can_send_other_messages=True,
                            can_add_web_page_previews=True
                        ))
                    except Exception as e:
                        logger.error(
                            "Не удалось снять истёкший мут пользователя %s в чате %s: %s",
                            m.get('user_id'), cid, e
                        )
                    else:
                        mutes.remove(m)
                        removed_any = True
                        try:
                            user_id = int(m['user_id'])
                            is_anti_spam_mute = (
                                m.get('auto_mute') is True
                                or m.get('muted_by') == 'auto'
                                or str(m.get('reason') or '').startswith('Антиспам:')
                            )
                            user_data = storage.get_user(int(cid), user_id)
                            username = str(user_data.get('username') or '').strip().lstrip('@')
                            display_user = (
                                f"@{html.escape(username, quote=False)}"
                                if username
                                else f"{html.escape(str(user_data.get('first_name') or 'Участник'), quote=False)} "
                                     f"(ID <code>{user_id}</code>)"
                            )
                            reason = html.escape(
                                str(m.get('reason') or ('Антиспам' if is_anti_spam_mute else 'Без причины')),
                                quote=False,
                            )
                            issued_by = m.get('muted_by')
                            if is_anti_spam_mute or issued_by == 'auto':
                                issuer_text = 'антиспам-система'
                            elif isinstance(issued_by, int):
                                issuer_data = storage.get_user(int(cid), issued_by)
                                issuer_username = str(issuer_data.get('username') or '').strip().lstrip('@')
                                issuer_text = (
                                    f"@{html.escape(issuer_username, quote=False)}"
                                    if issuer_username
                                    else f"{html.escape(str(issuer_data.get('first_name') or 'Администратор'), quote=False)} "
                                         f"(ID <code>{issued_by}</code>)"
                                )
                            else:
                                issuer_text = 'неизвестно'

                            duration_minutes = m.get('duration_minutes')
                            if not isinstance(duration_minutes, (int, float)):
                                issued_at = m.get('issued_at')
                                if isinstance(issued_at, (int, float)):
                                    duration_minutes = max(1, round((m['expire_time'] - issued_at) / 60))
                                else:
                                    duration_minutes = None
                            duration_text = (
                                html.escape(format_mute_duration(int(duration_minutes)), quote=False)
                                if duration_minutes is not None
                                else 'не указана'
                            )
                            ended_at = datetime.fromtimestamp(m['expire_time']).strftime('%d.%m.%Y %H:%M')
                            notice = await bot.send_message(
                                int(cid),
                                (
                                    f"🔊 <b>Мут автоматически снят</b>\n"
                                    f"👤 Пользователь: {display_user}\n"
                                    f"⏱ Длительность: {duration_text}\n"
                                    f"📝 Причина: {reason}\n"
                                    f"👮 Выдал: {issuer_text}\n"
                                    f"🕒 Истёк: {ended_at}"
                                ),
                                disable_web_page_preview=True,
                            )
                            asyncio.create_task(
                                delete_message_after(notice, 10 if is_anti_spam_mute else 60)
                            )
                        except Exception as e:
                            logger.warning(
                                "Не удалось уведомить об окончании мута пользователя %s в чате %s: %s",
                                m.get('user_id'), cid, e
                            )
                if removed_any:
                    storage.mark_dirty()
                    await storage.save()
        except Exception as e:
            logger.error(f"Ошибка проверки мутов: {e}")


# ==================== Автосохранение ====================

async def auto_save_task():
    while True:
        await asyncio.sleep(AUTO_SAVE_INTERVAL)
        if storage._dirty:
            await storage.save()


def signal_handler(signum, frame):
    storage.save_sync()
    sys.exit(0)


# ==================== Команды с префиксом ! ====================

@router.message(F.new_chat_members)
async def new_member_handler(msg: Message):
    """Приветствие новых участников"""
    cid = str(msg.chat.id)
    settings = storage.data['welcome_settings'].get(cid, {})
    if not settings.get('enabled', True):
        return

    for new_member in msg.new_chat_members:
        if new_member.is_bot:
            continue
        if new_member.id == bot.id:
            continue

        name = mention(msg.chat.id, new_member)
        text = settings.get('text')
        if text:
            text = text.replace('{name}', name).replace('{имя}', name)
        else:
            text = f"👋 Добро пожаловать, {name}!"

        try:
            image_url = settings.get('image_url')
            if image_url:
                try:
                    await bot.send_photo(msg.chat.id, photo=image_url, caption=text)
                except Exception:
                    await msg.answer(text)
            else:
                await msg.answer(text)
        except:
            pass

        try:
            await msg.delete()
        except:
            pass


@router.message(F.left_chat_member)
async def left_member_handler(msg: Message):
    """Прощание при выходе участника"""
    cid = str(msg.chat.id)
    settings = storage.data['welcome_settings'].get(cid, {})
    if not settings.get('farewell_enabled', True):
        return

    left_member = msg.left_chat_member
    if not left_member or left_member.is_bot:
        return

    name = mention(msg.chat.id, left_member)
    text = settings.get('farewell_text')
    if text:
        text = text.replace('{name}', name).replace('{имя}', name)
    else:
        text = f"👋 Пока, {name}! Будем ждать тебя снова."

    try:
        image_url = settings.get('farewell_image_url')
        if image_url:
            try:
                await bot.send_photo(msg.chat.id, photo=image_url, caption=text)
            except Exception:
                await msg.answer(text)
        else:
            await msg.answer(text)
    except:
        pass

    try:
        await msg.delete()
    except:
        pass


# ==================== Настройка команд бота ====================

async def setup_bot_commands():
    """Регистрирует стандартные команды в меню Telegram."""
    commands = [
        BotCommand(command='start', description='Старт'),
        BotCommand(command='help', description='Помощь'),
        BotCommand(command='time', description='Время в регионе'),
        BotCommand(command='graphtheme', description='Тема графика активности'),
        BotCommand(command='game', description='Игры и мини-игры'),
        BotCommand(command='profile', description='Профиль пользователя'),
        BotCommand(command='top', description='Топ игроков'),
    ]
    try:
        await bot.set_my_commands(commands)
    except Exception as e:
        logger.warning(f"Не удалось настроить команды бота: {e}")


# ==================== Запуск ====================

async def main():
    logger.info("🐻 Обкуренный Валера v3.0 запускается...")
    signal.signal(signal.SIGTERM, signal_handler)
    signal.signal(signal.SIGINT, signal_handler)
    await setup_bot_commands()
    asyncio.create_task(check_mutes())
    asyncio.create_task(auto_save_task())
    asyncio.create_task(cleanup_games())
    await dp.start_polling(bot)


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        storage.save_sync()
    except Exception as e:
        print(f"❌ Ошибка: {e}")
        storage.save_sync()
