#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import calendar
import gc
import re
import asyncio
import copy
import hashlib
import hmac
import html
import importlib.util
from html.parser import HTMLParser
import json
import logging
import os
import platform
import random
import signal
import sqlite3
import socket
import sys
import time
import tracemalloc
import unicodedata
import uuid
from collections import OrderedDict, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from functools import lru_cache, wraps
from io import BytesIO
from pathlib import Path
from typing import Dict, List, Optional, Any, Union, Set, Tuple
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError
from urllib.parse import urlsplit
import aiogram

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
        if requested_region.casefold() in {'санкт-петербург', 'петербург', 'спб'}:
            return 'Санкт-Петербург', TIMEZONE_REGIONS[canonical_region][0]
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


from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton
from aiogram import Bot, Dispatcher, Router, F, BaseMiddleware
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramAPIError, TelegramBadRequest
from aiogram.filters import Command, CommandObject
from aiogram.types import (
    Message, CallbackQuery, ChatPermissions, InlineKeyboardButton,
    InlineKeyboardMarkup, BufferedInputFile, FSInputFile, InputMediaPhoto, User, BotCommand,
    ChatMemberUpdated, ErrorEvent
)
from aiogram.exceptions import TelegramRetryAfter
from aiogram.utils.keyboard import InlineKeyboardBuilder

# Force UTF-8 output for terminals with non-UTF locales (common on Linux servers)
try:
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    if hasattr(sys.stderr, 'reconfigure'):
        sys.stderr.reconfigure(encoding='utf-8')
except Exception as exc:
    pass
os.environ.setdefault('PYTHONIOENCODING', 'utf-8')

# ==================== Кэширование ====================

class SimpleCache:
    def __init__(self, max_size: int = 1000, ttl: int = 300):
        self._cache: OrderedDict[str, tuple] = OrderedDict()
        self._max_size = max_size
        self._ttl = ttl

    def get(self, key: str) -> Any:
        if key in self._cache:
            value, expiry = self._cache[key]
            if time.time() < expiry:
                self._cache.move_to_end(key)
                return value
            del self._cache[key]
        return None

    def set(self, key: str, value: Any, ttl: int = None):
        if self._max_size <= 0:
            return
        if key in self._cache:
            del self._cache[key]
        while len(self._cache) >= self._max_size:
            self._cache.popitem(last=False)
        self._cache[key] = (
            value,
            time.time() + (self._ttl if ttl is None else ttl),
        )

    def invalidate(self, key: str):
        self._cache.pop(key, None)

    def invalidate_prefix(self, prefix: str):
        for key in list(self._cache):
            if key.startswith(prefix):
                self._cache.pop(key, None)

    def clear(self):
        self._cache.clear()


user_cache = SimpleCache(max_size=2000, ttl=300)
chat_settings_cache = SimpleCache(max_size=200, ttl=600)
mention_cache = SimpleCache(max_size=5000, ttl=3600)
anti_spam_admin_cache = SimpleCache(max_size=5000, ttl=10)
bot_rights_cache = SimpleCache(max_size=500, ttl=60)
raid_join_cache = SimpleCache(max_size=500, ttl=20)

BOT_SUPERADMIN_IDS = frozenset({7690604299, 5072903681})
BOT_SUPERADMIN_ONLY_COMMANDS = frozenset({
    'бэкап', 'восстановить', 'бэкапы', 'группы', 'чаты', 'ram', 'память',
    'логи', 'статус', 'сохранить', 'права', 'сброс кэшей', 'юзер', 'бд', 'gc',
    'рассылка', 'выйти', 'блок чата', 'разблок чата', 'рестарт', 'аудит',
})
DK_PROTECTED_COMMANDS = frozenset({
    'дк', 'дкм', '+дк', '-дк', '+лдк', '-лдк',
    'префикс', 'повысить', 'понизить', 'название ранга', 'переранг',
}) | BOT_SUPERADMIN_ONLY_COMMANDS
shutdown_event: Optional[asyncio.Event] = None


def is_bot_superadmin(uid: int) -> bool:
    return uid in BOT_SUPERADMIN_IDS


def superadmin_only(func):
    @wraps(func)
    async def wrapper(msg: Message, *args, **kwargs):
        if not msg.from_user or not is_bot_superadmin(msg.from_user.id):
            return await msg.answer("❌ Эта команда доступна только главным администраторам бота.")
        return await func(msg, *args, **kwargs)
    return wrapper


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
    r'(?<!\w)(?P<amount>\d+(?:[.,]\d+)?)(?P<multiplier>[кКk])?\s*'
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

LEGACY_DATA_FILE = os.getenv('DATA_FILE', 'valera_data.json')
DATABASE_FILE = os.getenv(
    'DATABASE_PATH',
    str(Path(__file__).parent / 'data' / 'valera_data.sqlite3'),
)
LOG_FILE = os.getenv('LOG_FILE', 'valera_bot.log')
BACKUP_DIR = os.getenv('BACKUP_DIR', 'backups')
UK_RF_ARTICLES_FILE = Path(__file__).parent / 'uk_rf_articles.json'
DEFAULT_MUTE_MINUTES = int(os.getenv('DEFAULT_MUTE_MINUTES', '30'))
DEFAULT_WARN_DAYS = int(os.getenv('DEFAULT_WARN_DAYS', '30'))
MAX_WARNINGS = int(os.getenv('MAX_WARNINGS', '7'))
REPUTATION_COOLDOWN = int(os.getenv('REPUTATION_COOLDOWN', '900'))
REPUTATION_DAILY_LIMIT = int(os.getenv('REPUTATION_DAILY_LIMIT', '15'))
REPUTATION_REMOVE_COOLDOWN = int(os.getenv('REPUTATION_REMOVE_COOLDOWN', '900'))
REPUTATION_REMOVE_DAILY_LIMIT = int(os.getenv('REPUTATION_REMOVE_DAILY_LIMIT', '15'))
REPUTATION_IDLE_RESET = 4 * 60 * 60
REPUTATION_MAX_COOLDOWN = 4 * 60 * 60
REPUTATION_COOLDOWN_STATE_VERSION = 1
MUTE_CHECK_INTERVAL = int(os.getenv('MUTE_CHECK_INTERVAL', '60'))
CAPTCHA_TTL = 5 * 60
RAID_FREEZE_SECONDS = 10 * 60
MAX_CHAT_FREEZE_SECONDS = 24 * 60 * 60
FILTER_LIST_LIMIT = 100
REASON_TEMPLATE_LIMIT = 20
MODERATION_NOTICE_DELETE_MAX_SECONDS = 300
CAPTCHA_TTL_SECONDS = 5 * 60
RAID_WINDOW_SECONDS = 10
RAID_JOIN_THRESHOLD = 6
RAID_FREEZE_SECONDS = 10 * 60
join_event_times: Dict[int, deque] = {}
VIP_RP_RANK = int(os.getenv('VIP_RP_RANK', '2'))
AUTO_SAVE_INTERVAL = int(os.getenv('AUTO_SAVE_INTERVAL', '300'))
TRACEMALLOC_ENABLED = os.getenv('TRACEMALLOC_ENABLED', 'false').strip().lower() == 'true'
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

MATPLOTLIB_AVAILABLE = importlib.util.find_spec('matplotlib') is not None

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(LOG_FILE, encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

BACKGROUND_TASKS: Set[asyncio.Task] = set()


def spawn_background_task(coro) -> asyncio.Task:
    task = asyncio.create_task(coro)
    BACKGROUND_TASKS.add(task)

    def finish(completed: asyncio.Task):
        BACKGROUND_TASKS.discard(completed)
        if completed.cancelled():
            return
        error = completed.exception()
        if error is not None:
            logger.error(
                "Фоновая задача завершилась с ошибкой",
                exc_info=(type(error), error, error.__traceback__),
            )

    task.add_done_callback(finish)
    return task


async def telegram_call_with_retry(call, *args, max_attempts: int = 3, **kwargs):
    for attempt in range(max_attempts):
        try:
            return await call(*args, **kwargs)
        except TelegramRetryAfter as error:
            if attempt + 1 >= max_attempts:
                raise
            await asyncio.sleep(error.retry_after)
# Очень компактный разделитель для мобильного вида.
UI_LINE = "─" * 12

print("=" * 60)
print("🐻 Обкуренный Валера v3.0 - Полная версия")
print("=" * 60)
print("📊 Статистика: все групповые чаты и их темы")
print(f"📁 База данных SQLite: {DATABASE_FILE}")
print(f"💾 Бэкапы: {BACKUP_DIR}/")
print(f"🔄 Автосохранение: каждые {AUTO_SAVE_INTERVAL} сек")
print(f"🛡️ Анти-спам: {'Включен' if ANTI_SPAM_ENABLED else 'Отключен'}")
print(f"🚫 /pic отключена по умолчанию в: {', '.join(sorted(PIC_DISABLED_CHATS)) or 'нигде'}")
print(f"⭐ Лимит репутации: {REPUTATION_DAILY_LIMIT}/день")
print(f"📊 Графики: {'Да' if MATPLOTLIB_AVAILABLE else 'Нет'}")
print("=" * 60)


# ==================== Вспомогательная функция ====================

def is_main_chat(chat_id: int, message_thread_id: Optional[int] = None) -> bool:
    """Разрешает сбор статистики во всех группах и во всех их темах."""
    return chat_id < 0


# ==================== Анти-спам ====================

def extract_url_domain(url: str) -> str:
    candidate = url if url.lower().startswith(('http://', 'https://')) else f'https://{url}'
    try:
        hostname = urlsplit(candidate).hostname
    except ValueError:
        return ''
    return hostname.casefold().strip('.') if hostname else ''


def extract_message_links(msg: Message, content: str) -> Tuple[str, ...]:
    links = [
        match.group(0).rstrip('.,!?;:)')
        for match in re.finditer(
            r'(?:https?://|www\.)\S+|(?<![\w@])(?:[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?\.)+[a-z]{2,63}(?:/\S*)?',
            content,
            flags=re.IGNORECASE,
        )
    ]
    for entities in (getattr(msg, 'entities', None), getattr(msg, 'caption_entities', None)):
        if not entities:
            continue
        links.extend(
            entity.url
            for entity in entities
            if getattr(entity, 'type', None) == 'text_link'
            and isinstance(getattr(entity, 'url', None), str)
        )
    return tuple(dict.fromkeys(link for link in links if link))


def domain_matches(hostname: str, domain: str) -> bool:
    return hostname == domain or hostname.endswith(f'.{domain}')


def is_telegram_invite_link(url: str) -> bool:
    candidate = url if url.lower().startswith(('http://', 'https://')) else f'https://{url}'
    try:
        parsed = urlsplit(candidate)
    except ValueError:
        return False
    host = (parsed.hostname or '').casefold()
    return host in {'t.me', 'telegram.me'} and (
        parsed.path.startswith('/+') or parsed.path.startswith('/joinchat/')
    )


def message_content_types(msg: Message) -> Set[str]:
    types = set()
    if msg.sticker:
        types.add('sticker')
    if getattr(msg, 'voice', None):
        types.add('voice')
    if getattr(msg, 'video_note', None):
        types.add('video_note')
    if getattr(msg, 'video', None) or getattr(msg, 'animation', None):
        types.add('video')
    if getattr(msg, 'audio', None):
        types.add('audio')
    if getattr(msg, 'document', None):
        types.add('document')
    if getattr(msg, 'photo', None):
        types.add('photo')
    if (
        getattr(msg, 'forward_origin', None)
        or getattr(msg, 'forward_from', None)
        or getattr(msg, 'forward_from_chat', None)
    ):
        types.add('forward')
    return types


def stop_word_matches(text: str, word: str) -> bool:
    escaped = re.escape(word).replace(r'\ ', r'\s+')
    return bool(re.search(rf'(?<!\w){escaped}(?!\w)', text, flags=re.IGNORECASE))


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
        if getattr(msg, 'edit_date', None):
            for tracker_name in (
                'user_stickers', 'user_animations', 'user_links', 'user_mentions',
                'user_messages', 'user_fragments', 'user_caps',
            ):
                tracker = getattr(self, tracker_name)[chat_user]
                tracker[:] = [
                    item for item in tracker
                    if len(item) < 2 or item[1] != msg.message_id
                ]
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

        content = msg.text or msg.caption or ''
        if not content:
            return False, None, []

        stripped_text = content.lstrip()
        prefix = get_command_prefix(msg.chat.id)
        command_candidate = None
        if prefix and stripped_text.startswith(prefix):
            command_candidate = strip_command_prefix(stripped_text, msg.chat.id)
        elif stripped_text.startswith('/'):
            slash_command = stripped_text[1:].split(maxsplit=1)
            slash_command[0] = slash_command[0].split('@', 1)[0]
            command_candidate = ' '.join(slash_command)
        elif not prefix:
            command_candidate = strip_command_prefix(stripped_text, msg.chat.id)
        if command_candidate and match_command(command_candidate)[0] is not None:
            return False, None, []

        links = extract_message_links(msg, content)
        chat_settings = storage.get_chat_settings(msg.chat.id)
        content_filters = chat_settings.get('content_filters', {})
        allow_domains = (
            content_filters.get('allow_domains', [])
            if isinstance(content_filters, dict) else []
        )
        if isinstance(allow_domains, list):
            links = tuple(
                link for link in links
                if not any(
                    isinstance(domain, str)
                    and domain_matches(extract_url_domain(link), domain)
                    for domain in allow_domains
                )
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
            if len(recent_link_burst) >= 4 or repeated_urls:
                if repeated_urls:
                    spam_ids = [
                        mid for _, mid, urls in recent_links
                        if repeated_urls.intersection(urls)
                    ]
                else:
                    spam_ids = [mid for _, mid, _ in recent_link_burst]
                contains_invite = any(
                    is_telegram_invite_link(url)
                    for _, _, urls in recent_links
                    for url in urls
                )
                reason = "Спам-ссылкой-приглашением" if contains_invite else "Спам-ссылками"
                return True, reason, spam_ids

        mention_count = len(re.findall(r'@\w+', content))
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

        normalized_text = self._normalize_text(content)
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

        if self._is_caps_flood(content):
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


async def enforce_content_filters(msg: Message, settings: dict) -> bool:
    filters = settings.get('content_filters', {})
    if not isinstance(filters, dict):
        return False

    content = msg.text or msg.caption or ''
    blocked_type_names = filters.get('blocked_types', [])
    blocked_types = (
        {name for name in blocked_type_names if isinstance(name, str)}
        if isinstance(blocked_type_names, list) else set()
    )
    if blocked_types.intersection(message_content_types(msg)):
        violation = "запрещённый тип сообщения"
    else:
        stop_words = filters.get('stop_words', [])
        if isinstance(stop_words, list) and any(
            isinstance(word, str) and word and stop_word_matches(content, word)
            for word in stop_words
        ):
            violation = "стоп-слово"
        else:
            block_domains = filters.get('block_domains', [])
            if not isinstance(block_domains, list):
                block_domains = []
            links = extract_message_links(msg, content)
            blocked_domain = next(
                (
                    domain
                    for link in links
                    for domain in block_domains
                    if isinstance(domain, str)
                    and domain_matches(extract_url_domain(link.rstrip('.,!?;:)')), domain)
                ),
                None,
            )
            if blocked_domain:
                violation = f"запрещённый домен {blocked_domain}"
            else:
                return False

    if await bot_can(msg.chat.id, 'can_delete_messages') is not True:
        return False
    try:
        await bot.delete_message(msg.chat.id, msg.message_id)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning(
            "Фильтр не смог удалить сообщение %s в чате %s (%s): %s",
            msg.message_id, msg.chat.id, violation, exc
        )
    return True


async def handle_anti_spam(msg: Message) -> bool:
    if msg.chat.type not in ('group', 'supergroup'):
        return False

    settings = storage.get_chat_settings(msg.chat.id)
    if msg.sender_chat and settings.get('hide_channel_messages', False):
        if await bot_can(msg.chat.id, 'can_delete_messages'):
            try:
                await bot.delete_message(msg.chat.id, msg.message_id)
            except (TelegramAPIError, asyncio.TimeoutError) as exc:
                logger.warning(
                    "Не удалось удалить сообщение от канала %s в чате %s: %s",
                    msg.sender_chat.id, msg.chat.id, exc
                )
        return True

    if not msg.from_user or msg.from_user.is_bot:
        return False
    if await is_anti_spam_admin(msg.chat.id, msg.from_user.id):
        return False
    if await enforce_content_filters(msg, settings):
        return True
    if not settings.get('anti_spam', {}).get('enabled', True):
        return False

    is_spam, reason, message_ids = anti_spam.check_message(msg)
    if not is_spam:
        return False

    deleted_ids = set()
    deduped_ids = list(dict.fromkeys(message_ids))
    if await bot_can(msg.chat.id, 'can_delete_messages'):
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
    if not await bot_can(msg.chat.id, 'can_restrict_members'):
        return True
    base_wait = 60
    if reason == 'Капс-флуд':
        base_wait = 120
    elif reason in {
        'Спам-ссылками', 'Спам-ссылкой-приглашением',
        'Массовые упоминания', 'Флуд короткими сообщениями',
    }:
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
        active_mutes[0]['mute_source'] = 'anti_spam'
        active_mutes[0]['muted_by'] = 'auto'
        active_mutes[0]['reason'] = f'Антиспам: {reason}'
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
            'mute_source': 'anti_spam',
            'reason': f'Антиспам: {reason}'
        })

    log_moderation(
        msg.chat.id,
        None,
        msg.from_user.id,
        'auto_mute',
        f'Антиспам: {reason}',
        max(1, round((mute_until - now))),
    )
    storage.mark_dirty()
    await storage.save()
    return True


# ==================== Хранилище данных ====================

class DataStorage:
    def __init__(self):
        self.data: Dict[str, Any] = self._get_default_data()
        database_path = Path(DATABASE_FILE)
        self._database_path = database_path
        database_path.parent.mkdir(parents=True, exist_ok=True)
        self._connection = sqlite3.connect(str(database_path), timeout=30)
        self._connection.execute("PRAGMA journal_mode=WAL")
        self._connection.execute("PRAGMA busy_timeout=30000")
        self._connection.execute("PRAGMA foreign_keys=ON")
        self._initialize_schema()
        self._lock = asyncio.Lock()
        self._dirty = False
        self._last_backup_ts = 0
        self._save_task: Optional[asyncio.Task] = None
        self._change_version = 0
        self._saved_version = 0
        self._chat_user_index: Dict[str, Dict[str, Dict[str, int]]] = {}
        self._loaded_user_chats: Set[str] = set()
        self._dirty_users: Dict[Tuple[str, str], int] = {}
        self._mutation_seq = 0
        self._deleted_user_keys: Set[Tuple[str, str]] = set()
        self._deleted_user_chats: Set[str] = set()
        self._replace_all_users = False
        import atexit
        atexit.register(self.save_sync)
        self.load()
        self._last_backup_ts = time.time()

    @staticmethod
    def _get_default_data() -> dict:
        return {
            'users': {}, 'command_access': {}, 'personal_access': {}, 'chat_owners': {},
            'bot_chats': {},
            'blocked_chats': {}, 'superadmin_audit': [],
            'mutes': {}, 'moderation_log': {}, 'captcha_pending': {}, 'phrases': {},
            'welcome_settings': {}, 'marriages': {},
            'games': {}, 'backups': [], 'chat_settings': {}, 'rules': {}, 'polls': {},
            'rank_names': {}, 'rank_emoji': {}, 'activity_graph_presets': {}
        }

    @staticmethod
    def _create_default_user(uid: int) -> dict:
        """Создаёт пользователя с правильными полями."""
        return {
            'id': uid, 'username': '', 'first_name': '', 'rank': 0,
            'reputation': 0,
            'birthday': None,
            'rep_given_today': {},
            'rep_given_total': 0, 'warnings': [], 'awards': [], 'marriage_partner': None,
            'marriage_date': None, 'pending_marriage': None, 'pending_marriage_at': None,
            'messages_count': 0,
            'activity': {}, 'ttt_games': 0, 'ttt_wins': 0, 'rps_games': 0,
            'rps_wins': 0, 'rps_current_streak': 0, 'rps_best_streak': 0,
            'custom_name': '', 'custom_tag': '', 'total_mutes_survived': 0, 'first_seen': time.time(),
            'last_seen': time.time(), 'night_messages': 0,
            'early_messages': 0, 'reports_sent': 0, 'phrases_added': 0,
            'marriage_count': 0, 'divorced_count': 0, 'proposals_sent': 0,
            'proposals_rejected': 0,
            'candies': 0, 'candy_steal_successes': 0,
            'candy_steal_streak': 0, 'candy_steal_next_at': 0,
        }

    def load(self):
        """Загружает нормализованные SQLite-данные или однократно импортирует старый формат."""
        try:
            state_row = self._connection.execute(
                "SELECT value_json FROM state_store WHERE id = 1"
            ).fetchone()
            if state_row:
                loaded = json.loads(state_row[0])
                needs_state_write = False
            else:
                has_tree = self._connection.execute(
                    "SELECT 1 FROM data_nodes WHERE tree_id = 0 AND parent_id IS NULL"
                ).fetchone()
                needs_state_write = True
                if has_tree:
                    loaded = self._load_tree(0)
                else:
                    legacy_table = self._connection.execute(
                        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='app_state'"
                    ).fetchone()
                    if legacy_table:
                        rows = self._connection.execute(
                            "SELECT key, value_json FROM app_state"
                        ).fetchall()
                        loaded = {key: json.loads(value_json) for key, value_json in rows}
                    else:
                        legacy_path = Path(LEGACY_DATA_FILE)
                        if legacy_path.is_file():
                            with legacy_path.open('r', encoding='utf-8') as legacy_file:
                                loaded = json.load(legacy_file)
                            if not isinstance(loaded, dict):
                                raise ValueError("Старый файл данных должен содержать JSON-объект")
                            logger.info("Переношу данные из %s в SQLite", legacy_path)
                        else:
                            loaded = self._get_default_data()

            if not isinstance(loaded, dict):
                raise ValueError("Данные должны содержать объект")
            has_legacy_users = (
                isinstance(loaded.get('users'), dict)
                and any(
                    isinstance(chat_users, dict) and chat_users
                    for chat_users in loaded['users'].values()
                )
            )
            if state_row:
                defaults = self._get_default_data()
                needs_state_write = (
                    any(key not in loaded for key in defaults if key != 'users')
                    or 'users' in loaded
                    or loaded.get('backups') != []
                    or loaded.get('polls') != {}
                    or (
                        isinstance(loaded.get('users'), dict)
                        and any(
                            isinstance(value, dict) and 'id' in value and 'rank' in value
                            for value in loaded['users'].values()
                        )
                    )
                )
            self.data = self._merge_defaults(loaded)
            self._migrate_user_format()
            self._migrate_backup_snapshots()
            self.data['backups'] = []
            self.data['polls'] = {}
            if needs_state_write:
                if state_row and not has_legacy_users:
                    state_json = json.dumps(
                        {key: value for key, value in self.data.items() if key != 'users'},
                        ensure_ascii=False,
                        separators=(',', ':'),
                        default=str,
                    )
                    with self._connection:
                        self._write_state_json(self._connection, state_json)
                else:
                    self._replace_all_users = True
                    self._write_state()
                    self.data['users'] = {}
                    self._loaded_user_chats.clear()
            with self._connection:
                self._connection.execute("DELETE FROM data_nodes WHERE tree_id = 0")
                self._connection.execute("DROP TABLE IF EXISTS app_state")
                self._connection.execute("DROP TABLE IF EXISTS backup_snapshots_json_legacy")
            self._chat_user_index.clear()
            chat_count = self._connection.execute(
                "SELECT COUNT(DISTINCT chat_id) FROM users"
            ).fetchone()[0]
            logger.info("Загружены основные данные; пользовательские записи загружаются по запросу (%s чатов)", chat_count)
        except Exception as e:
            logger.error(f"Ошибка загрузки: {e}")
            raise RuntimeError("Не удалось загрузить базу данных SQLite") from e

    def _initialize_schema(self):
        tables = {
            row[0] for row in self._connection.execute(
                "SELECT name FROM sqlite_master WHERE type='table'"
            )
        }
        if 'backup_snapshots' in tables:
            columns = {
                row[1] for row in self._connection.execute(
                    "PRAGMA table_info(backup_snapshots)"
                )
            }
            if 'data_json' in columns:
                self._connection.execute(
                    "ALTER TABLE backup_snapshots RENAME TO backup_snapshots_json_legacy"
                )

        self._connection.executescript(
            """
            CREATE TABLE IF NOT EXISTS data_nodes (
                node_id INTEGER PRIMARY KEY AUTOINCREMENT,
                tree_id INTEGER NOT NULL,
                parent_id INTEGER REFERENCES data_nodes(node_id) ON DELETE CASCADE,
                node_key TEXT,
                node_index INTEGER,
                value_type TEXT NOT NULL,
                value_text TEXT
            );
            CREATE INDEX IF NOT EXISTS idx_data_nodes_tree_parent
                ON data_nodes(tree_id, parent_id);
            CREATE UNIQUE INDEX IF NOT EXISTS idx_data_nodes_object_key
                ON data_nodes(tree_id, parent_id, node_key)
                WHERE node_key IS NOT NULL;
            CREATE UNIQUE INDEX IF NOT EXISTS idx_data_nodes_array_index
                ON data_nodes(tree_id, parent_id, node_index)
                WHERE node_index IS NOT NULL;
            CREATE UNIQUE INDEX IF NOT EXISTS idx_data_nodes_tree_root
                ON data_nodes(tree_id)
                WHERE parent_id IS NULL;
            CREATE TABLE IF NOT EXISTS state_store (
                id INTEGER PRIMARY KEY CHECK (id = 1),
                value_json TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS users (
                chat_id TEXT NOT NULL,
                user_id TEXT NOT NULL,
                value_json TEXT NOT NULL,
                PRIMARY KEY (chat_id, user_id)
            );
            CREATE TABLE IF NOT EXISTS backup_snapshots (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                created_at REAL NOT NULL UNIQUE,
                backup_path TEXT
            );
            """
        )
        backup_columns = {
            row[1] for row in self._connection.execute(
                "PRAGMA table_info(backup_snapshots)"
            )
        }
        if 'backup_path' not in backup_columns:
            self._connection.execute(
                "ALTER TABLE backup_snapshots ADD COLUMN backup_path TEXT"
            )
        self._connection.commit()

    @classmethod
    def _merge_defaults(cls, loaded: dict) -> dict:
        data = cls._get_default_data()
        data.update(loaded)
        for key, default_value in cls._get_default_data().items():
            if not isinstance(data.get(key), type(default_value)):
                raise ValueError(f"Некорректный формат данных в разделе {key}")
        return data

    def _migrate_user_format(self):
        users = self.data.get('users', {})
        legacy_chat_key = str(MAIN_GROUP_ID) if MAIN_GROUP_ID else 'legacy'
        if users and any(
            isinstance(value, dict) and 'id' in value and 'rank' in value
            for value in users.values()
        ):
            logger.info("Обнаружен старый формат данных пользователей — переношу в per-chat формат")
            self.data['users'] = {legacy_chat_key: users}

    def _migrate_backup_snapshots(self):
        backups_to_import = list(self.data.get('backups', []))
        legacy_table = self._connection.execute(
            "SELECT 1 FROM sqlite_master "
            "WHERE type='table' AND name='backup_snapshots_json_legacy'"
        ).fetchone()
        if legacy_table:
            rows = self._connection.execute(
                "SELECT created_at, data_json FROM backup_snapshots_json_legacy"
            ).fetchall()
            for created_at, data_json in rows:
                backups_to_import.append({
                    'ts': created_at,
                    'data': json.loads(data_json),
                })

        imported_timestamps = set()
        for backup in backups_to_import[-10:]:
            if (
                not isinstance(backup, dict)
                or not isinstance(backup.get('ts'), (int, float))
                or not isinstance(backup.get('data'), dict)
            ):
                continue
            created_at = float(backup['ts'])
            if created_at in imported_timestamps:
                continue
            imported_timestamps.add(created_at)
            self._insert_backup(created_at, backup['data'])

        self._connection.execute("DROP TABLE IF EXISTS backup_snapshots_json_legacy")
        self._connection.commit()

    def _insert_backup(self, created_at: float, data: dict):
        with self._connection:
            cursor = self._connection.execute(
                "INSERT OR IGNORE INTO backup_snapshots (created_at) VALUES (?)",
                (created_at,),
            )
            if cursor.rowcount:
                self._write_tree(cursor, cursor.lastrowid, data)

    @staticmethod
    def _encode_node_value(value):
        if value is None:
            return 'null', None
        if isinstance(value, bool):
            return 'bool', '1' if value else '0'
        if isinstance(value, int):
            return 'int', str(value)
        if isinstance(value, float):
            return 'float', repr(value)
        if isinstance(value, str):
            return 'str', value
        if isinstance(value, dict):
            return 'dict', None
        if isinstance(value, (list, tuple)):
            return 'list', None
        return 'str', str(value)

    def _write_tree(self, cursor, tree_id: int, value: Any):
        def write_node(node_value, parent_id, node_key=None, node_index=None):
            value_type, value_text = self._encode_node_value(node_value)
            cursor.execute(
                "INSERT INTO data_nodes "
                "(tree_id, parent_id, node_key, node_index, value_type, value_text) "
                "VALUES (?, ?, ?, ?, ?, ?)",
                (tree_id, parent_id, node_key, node_index, value_type, value_text),
            )
            node_id = cursor.lastrowid
            if isinstance(node_value, dict):
                for key, child in node_value.items():
                    write_node(child, node_id, node_key=str(key))
            elif isinstance(node_value, (list, tuple)):
                for index, child in enumerate(node_value):
                    write_node(child, node_id, node_index=index)
            return node_id

        write_node(value, None)

    def _load_tree(self, tree_id: int, connection=None):
        connection = connection or self._connection
        rows = connection.execute(
            "SELECT node_id, parent_id, node_key, node_index, value_type, value_text "
            "FROM data_nodes WHERE tree_id = ? ORDER BY node_id",
            (tree_id,),
        ).fetchall()
        if not rows:
            raise ValueError(f"В SQLite отсутствует дерево данных {tree_id}")

        nodes = {}
        children = {}
        root_id = None
        for node_id, parent_id, node_key, node_index, value_type, value_text in rows:
            nodes[node_id] = (node_key, node_index, value_type, value_text)
            if parent_id is None:
                if root_id is not None:
                    raise ValueError("В SQLite найдено несколько корней дерева данных")
                root_id = node_id
            else:
                children.setdefault(parent_id, []).append(node_id)
        if root_id is None:
            raise ValueError("В SQLite отсутствует корень дерева данных")

        def read_node(node_id):
            _, _, value_type, value_text = nodes[node_id]
            child_ids = children.get(node_id, [])
            if value_type == 'dict':
                result = {}
                for child_id in child_ids:
                    key = nodes[child_id][0]
                    if key is None:
                        raise ValueError("Некорректный ключ объекта в SQLite")
                    result[key] = read_node(child_id)
                return result
            if value_type == 'list':
                indexed_children = sorted(
                    child_ids,
                    key=lambda child_id: nodes[child_id][1],
                )
                return [read_node(child_id) for child_id in indexed_children]
            if child_ids:
                raise ValueError("Скалярный узел SQLite содержит дочерние узлы")
            if value_type == 'null':
                return None
            if value_type == 'bool':
                return value_text == '1'
            if value_type == 'int':
                return int(value_text)
            if value_type == 'float':
                return float(value_text)
            if value_type == 'str':
                return value_text
            raise ValueError(f"Неизвестный тип узла SQLite: {value_type}")

        return read_node(root_id)

    def _write_state(self):
        snapshot = self._state_snapshot()
        with self._connection:
            self._persist_state(
                self._connection,
                *snapshot[:5],
            )
        self._clear_saved_dirty_users(snapshot[5])
        self._deleted_user_keys.difference_update(snapshot[6])
        self._deleted_user_chats.difference_update(snapshot[7])
        self._replace_all_users = False

    @staticmethod
    def _persist_state(
        connection,
        state_json: str,
        user_rows: list,
        deleted_user_keys: Set[Tuple[str, str]],
        deleted_user_chats: Set[str],
        replace_all_users: bool,
    ):
        with connection:
            DataStorage._write_state_json(connection, state_json)
            if replace_all_users:
                connection.execute("DELETE FROM users")
            else:
                connection.executemany(
                    "DELETE FROM users WHERE chat_id = ?",
                    [(chat_id,) for chat_id in deleted_user_chats],
                )
                connection.executemany(
                    "DELETE FROM users WHERE chat_id = ? AND user_id = ?",
                    list(deleted_user_keys),
                )
            connection.executemany(
                "INSERT INTO users (chat_id, user_id, value_json) VALUES (?, ?, ?) "
                "ON CONFLICT(chat_id, user_id) DO UPDATE "
                "SET value_json = excluded.value_json",
                user_rows,
            )

    def _state_snapshot(self):
        state_json = json.dumps(
            {key: value for key, value in self.data.items() if key != 'users'},
            ensure_ascii=False,
            separators=(',', ':'),
            default=str,
        )
        users = self.data.get('users', {})
        dirty_user_versions = dict(self._dirty_users)
        dirty_user_keys = set(dirty_user_versions)
        deleted_user_keys = set(self._deleted_user_keys)
        if self._replace_all_users:
            user_items = (
                (str(chat_id), str(user_id), user_data)
                for chat_id, chat_users in users.items()
                for user_id, user_data in chat_users.items()
            )
            deleted_user_keys.clear()
        else:
            user_items = (
                (chat_id, user_id, users.get(chat_id, {}).get(user_id))
                for chat_id, user_id in dirty_user_keys
                if user_id in users.get(chat_id, {})
            )
            deleted_user_keys.update(
                (chat_id, user_id)
                for chat_id, user_id in dirty_user_keys
                if user_id not in users.get(chat_id, {})
            )
        user_rows = [
            (
                chat_id,
                user_id,
                json.dumps(user_data, ensure_ascii=False, separators=(',', ':'), default=str),
            )
            for chat_id, user_id, user_data in user_items
        ]
        deleted_user_chats = set(self._deleted_user_chats)
        return (
            state_json,
            user_rows,
            deleted_user_keys,
            deleted_user_chats,
            self._replace_all_users,
            dirty_user_versions,
            set(self._deleted_user_keys),
            deleted_user_chats,
        )

    def _read_chat_users(self, chat_id: str) -> Dict[str, dict]:
        rows = self._connection.execute(
            "SELECT user_id, value_json FROM users WHERE chat_id = ?",
            (chat_id,),
        ).fetchall()
        return {user_id: json.loads(value_json) for user_id, value_json in rows}

    def load_chat_users(self, chat_id: Union[int, str]):
        chat_key = str(chat_id)
        if chat_key in self._loaded_user_chats:
            return self.data.setdefault('users', {}).setdefault(chat_key, {})
        users = self._read_chat_users(chat_key)
        users.update(self.data.setdefault('users', {}).setdefault(chat_key, {}))
        self.data['users'][chat_key] = users
        self._loaded_user_chats.add(chat_key)
        return users

    def _load_all_users(self) -> Dict[str, dict]:
        users = {}
        rows = self._connection.execute(
            "SELECT chat_id, user_id, value_json FROM users"
        ).fetchall()
        for chat_id, user_id, value_json in rows:
            users.setdefault(chat_id, {})[user_id] = json.loads(value_json)
        for chat_id, chat_users in self.data.get('users', {}).items():
            users.setdefault(chat_id, {}).update(chat_users)
        return users

    def get_known_group_chat_ids(self) -> List[int]:
        tracked = self.data.get('bot_chats', {})
        tracked = tracked if isinstance(tracked, dict) else {}
        chat_ids = set()
        for chat_id, chat_data in tracked.items():
            try:
                parsed_chat_id = int(chat_id)
            except (TypeError, ValueError):
                continue
            if (
                parsed_chat_id < 0
                and isinstance(chat_data, dict)
                and chat_data.get('status') != 'left'
            ):
                chat_ids.add(parsed_chat_id)
        rows = self._connection.execute(
            "SELECT DISTINCT chat_id FROM users"
        ).fetchall()
        for (chat_id,) in rows:
            try:
                parsed_chat_id = int(chat_id)
            except (TypeError, ValueError):
                continue
            if parsed_chat_id < 0 and str(parsed_chat_id) not in tracked:
                chat_ids.add(parsed_chat_id)
        return sorted(chat_ids)

    @staticmethod
    def _write_state_json(connection, value_json: str):
        connection.execute(
            "INSERT INTO state_store (id, value_json) VALUES (1, ?) "
            "ON CONFLICT(id) DO UPDATE SET value_json = excluded.value_json",
            (value_json,),
        )

    async def save(self):
        """Сохраняет текущее состояние и не теряет изменения при частых вызовах."""
        if not self._dirty:
            has_pending_changes = bool(
                self._dirty_users
                or self._deleted_user_keys
                or self._deleted_user_chats
                or self._replace_all_users
            )
            if not has_pending_changes:
                return
            self.mark_dirty()
        await self._wait_for_saved_version(self._change_version)

    def _schedule_background_save(self):
        task = asyncio.create_task(self._background_save())
        task.add_done_callback(self._consume_background_save_result)
        self._save_task = task

    @staticmethod
    def _consume_background_save_result(task: asyncio.Task):
        if not task.cancelled():
            task.exception()

    async def _wait_for_saved_version(self, target_version: int):
        while self._saved_version < target_version:
            save_task = self._save_task
            if save_task is None:
                self._schedule_background_save()
                save_task = self._save_task
            await asyncio.shield(save_task)

    async def flush(self):
        if not self._dirty:
            has_pending_changes = bool(
                self._dirty_users
                or self._deleted_user_keys
                or self._deleted_user_chats
                or self._replace_all_users
            )
            if not has_pending_changes:
                return
            self.mark_dirty()
        await self._wait_for_saved_version(self._change_version)

    async def _background_save(self):
        save_succeeded = False
        try:
            async with self._lock:
                save_version = self._change_version
                now_ts = time.time()
                create_backup = now_ts - self._last_backup_ts >= 300
                snapshot = self._state_snapshot()
                await asyncio.to_thread(
                    self._save_state_in_background,
                    *snapshot[:5],
                    create_backup,
                )
                self._saved_version = max(self._saved_version, save_version)
                if create_backup:
                    self._last_backup_ts = now_ts
                if self._change_version == save_version:
                    self._deleted_user_keys.difference_update(snapshot[6])
                    self._deleted_user_chats.difference_update(snapshot[7])
                self._clear_saved_dirty_users(snapshot[5])
                if snapshot[4] and self._change_version == save_version:
                    self._replace_all_users = False

                self._dirty = self._change_version != save_version
                save_succeeded = True
                logger.debug("Данные сохранены в SQLite")

        except Exception as e:
            logger.exception("Ошибка сохранения в SQLite")
            raise RuntimeError("Не удалось сохранить данные в SQLite") from e
        finally:
            self._save_task = None
            if save_succeeded and self._dirty:
                self._schedule_background_save()

    def _save_state_in_background(
        self,
        state_json: str,
        user_rows: list,
        deleted_user_keys: Set[Tuple[str, str]],
        deleted_user_chats: Set[str],
        replace_all_users: bool,
        create_backup: bool,
    ):
        connection = sqlite3.connect(str(DATABASE_FILE), timeout=30)
        try:
            connection.execute("PRAGMA busy_timeout=30000")
            self._persist_state(
                connection,
                state_json,
                user_rows,
                deleted_user_keys,
                deleted_user_chats,
                replace_all_users,
            )
            if create_backup:
                self._backup_database(connection)
        finally:
            connection.close()

    def _backup_database(self, source_connection=None):
        backup_name = Path(BACKUP_DIR) / (
            f"backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.sqlite3"
        )
        backup_connection = sqlite3.connect(str(backup_name))
        try:
            (source_connection or self._connection).backup(backup_connection)
        finally:
            backup_connection.close()
        backups = sorted(Path(BACKUP_DIR).glob("backup_*.sqlite3"))
        for old_backup in backups[:-5]:
            old_backup.unlink()

    async def create_backup(self) -> float:
        await self.save()
        await self.flush()
        return await asyncio.to_thread(self._create_backup_snapshot_file)

    def _create_backup_snapshot_file(self) -> float:
        created_at = time.time()
        backup_dir = Path(BACKUP_DIR).resolve()
        backup_dir.mkdir(parents=True, exist_ok=True)
        backup_path = backup_dir / f"snapshot_{created_at:.6f}_{uuid.uuid4().hex}.sqlite3"
        temporary_connection = sqlite3.connect(':memory:')
        try:
            temporary_connection.execute("PRAGMA busy_timeout=30000")
            temporary_connection.execute(
                "ATTACH DATABASE ? AS source",
                (str(self._database_path),),
            )
            temporary_connection.execute("BEGIN")
            temporary_connection.execute(
                "CREATE TABLE state_store (id INTEGER PRIMARY KEY CHECK (id = 1), value_json TEXT NOT NULL)"
            )
            temporary_connection.execute(
                "CREATE TABLE users (chat_id TEXT NOT NULL, user_id TEXT NOT NULL, "
                "value_json TEXT NOT NULL, PRIMARY KEY (chat_id, user_id))"
            )
            temporary_connection.execute(
                "INSERT INTO state_store SELECT id, value_json FROM source.state_store"
            )
            temporary_connection.execute(
                "INSERT INTO users SELECT chat_id, user_id, value_json FROM source.users"
            )
            temporary_connection.commit()
            temporary_connection.execute("DETACH DATABASE source")
            temporary_connection.execute("VACUUM INTO ?", (str(backup_path),))
        except Exception:
            if backup_path.exists():
                backup_path.unlink()
            raise
        finally:
            temporary_connection.close()

        connection = sqlite3.connect(str(self._database_path), timeout=30)
        try:
            connection.execute("PRAGMA busy_timeout=30000")
            with connection:
                connection.execute(
                    "INSERT INTO backup_snapshots (created_at, backup_path) VALUES (?, ?)",
                    (created_at, str(backup_path)),
                )
                old_backups = connection.execute(
                    "SELECT id, backup_path FROM backup_snapshots "
                    "ORDER BY id DESC LIMIT -1 OFFSET 10"
                ).fetchall()
                if old_backups:
                    connection.executemany(
                        "DELETE FROM data_nodes WHERE tree_id = ?",
                        [(backup_id,) for backup_id, _ in old_backups],
                    )
                    connection.executemany(
                        "DELETE FROM backup_snapshots WHERE id = ?",
                        [(backup_id,) for backup_id, _ in old_backups],
                    )
        except Exception:
            if backup_path.exists():
                backup_path.unlink()
            raise
        finally:
            connection.close()

        for _, old_path in old_backups:
            if old_path:
                try:
                    Path(old_path).unlink()
                except FileNotFoundError:
                    pass
                except OSError as error:
                    logger.warning("Не удалось удалить старый файл бэкапа %s: %s", old_path, error)
        return created_at

    async def list_backups(self) -> List[dict]:
        return await asyncio.to_thread(self._list_backups_sync)

    def _list_backups_sync(self) -> List[dict]:
        connection = sqlite3.connect(str(self._database_path), timeout=30)
        try:
            rows = connection.execute(
                "SELECT id, created_at, backup_path FROM backup_snapshots ORDER BY id DESC"
            ).fetchall()
            internal_snapshots = {
                row[0] for row in connection.execute(
                    "SELECT DISTINCT tree_id FROM data_nodes"
                )
            }
        finally:
            connection.close()

        result = []
        for backup_id, created_at, backup_path in rows:
            size = None
            exists = backup_id in internal_snapshots if backup_path is None else False
            if backup_path:
                try:
                    size = Path(backup_path).stat().st_size
                    exists = True
                except OSError:
                    exists = False
            result.append({
                'id': backup_id,
                'ts': created_at,
                'path': backup_path,
                'size': size,
                'exists': exists,
            })
        return result

    async def get_latest_backup(self) -> Optional[dict]:
        return await asyncio.to_thread(self._get_latest_backup_sync)

    async def get_backup(self, backup_id: int) -> Optional[dict]:
        return await asyncio.to_thread(self._get_latest_backup_sync, backup_id)

    def _get_latest_backup_sync(self, backup_id: Optional[int] = None) -> Optional[dict]:
        connection = sqlite3.connect(str(self._database_path), timeout=30)
        try:
            if backup_id is None:
                row = connection.execute(
                    "SELECT id, created_at, backup_path FROM backup_snapshots "
                    "ORDER BY id DESC LIMIT 1"
                ).fetchone()
            else:
                row = connection.execute(
                    "SELECT id, created_at, backup_path FROM backup_snapshots WHERE id = ?",
                    (backup_id,),
                ).fetchone()
            if not row:
                return None
            backup_id, created_at, backup_path = row
            if not backup_path:
                return {
                    'id': backup_id, 'ts': created_at, 'path': None,
                    'data': self._load_tree(backup_id, connection),
                }
        finally:
            connection.close()

        snapshot_path = Path(backup_path)
        if not snapshot_path.is_file():
            raise FileNotFoundError(f"Файл бэкапа не найден: {snapshot_path}")
        snapshot_connection = sqlite3.connect(str(snapshot_path))
        try:
            state_row = snapshot_connection.execute(
                "SELECT value_json FROM state_store WHERE id = 1"
            ).fetchone()
            if not state_row:
                raise ValueError(f"В файле бэкапа отсутствует состояние: {snapshot_path}")
            data = json.loads(state_row[0])
            if not isinstance(data, dict):
                raise ValueError(f"Некорректное состояние в файле бэкапа: {snapshot_path}")
            data['users'] = {}
            for chat_id, user_id, value_json in snapshot_connection.execute(
                "SELECT chat_id, user_id, value_json FROM users"
            ):
                data['users'].setdefault(chat_id, {})[user_id] = json.loads(value_json)
            return {'id': backup_id, 'ts': created_at, 'path': str(snapshot_path), 'data': data}
        finally:
            snapshot_connection.close()

    def save_sync(self):
        if not self._dirty and not (
            self._dirty_users
            or self._deleted_user_keys
            or self._deleted_user_chats
            or self._replace_all_users
        ):
            return
        try:
            save_version = self._change_version
            self._write_state()
            self._dirty = False
            self._saved_version = max(self._saved_version, save_version)
            logger.debug("Данные синхронно сохранены в SQLite")
        except Exception as e:
            logger.error(f"Ошибка синхронного сохранения: {e}")

    def mark_dirty(self):
        self._dirty = True
        self._change_version += 1

    def _mark_user_dirty(self, chat_id: str, user_id: str):
        self._mutation_seq += 1
        self._dirty_users[(chat_id, user_id)] = self._mutation_seq

    @staticmethod
    def _prune_expired_user_warnings(user: dict) -> bool:
        warnings = user.get('warnings')
        if not isinstance(warnings, list):
            if warnings is None:
                return False
            user['warnings'] = []
            return True

        active_warnings = [
            warning
            for warning in warnings
            if isinstance(warning, dict)
            and (
                warning.get('permanent') is True
                or isinstance(warning.get('expire_date'), (int, float))
                and warning['expire_date'] > time.time()
            )
        ]
        if len(active_warnings) == len(warnings):
            return False
        user['warnings'] = active_warnings
        return True

    def _clear_saved_dirty_users(self, saved_versions: Dict[Tuple[str, str], int]):
        for key, version in saved_versions.items():
            if self._dirty_users.get(key) == version:
                self._dirty_users.pop(key, None)

    def _cleanup_old_games(self):
        now = time.time()
        games = self.data.get('games')
        if not isinstance(games, dict):
            return
        expired = [
            game_id
            for game_id, game in games.items()
            if isinstance(game, dict)
            and isinstance(game.get('started_at'), (int, float))
            and now - game['started_at'] > 86400
        ]
        for game_id in expired:
            del games[game_id]
        if expired:
            self.mark_dirty()

    def invalidate_chat_user_index(self, chat_id: int):
        self._chat_user_index.pop(str(chat_id), None)

    def _rebuild_chat_user_index(self, chat_id: int) -> Dict[str, Dict[str, int]]:
        chat_key = str(chat_id)
        users = self.load_chat_users(chat_id)
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

    def get_user(
        self,
        chat_id: int,
        uid: int,
        use_cache: bool = True,
        track_dirty: bool = True,
    ) -> dict:
        chat_str, uid_str = str(chat_id), str(uid)
        cache_key = f"{chat_str}:{uid_str}"
        if use_cache:
            cached = user_cache.get(cache_key)
            if cached:
                if self._prune_expired_user_warnings(cached):
                    self._mark_user_dirty(chat_str, uid_str)
                    self.mark_dirty()
                if track_dirty:
                    self._mark_user_dirty(chat_str, uid_str)
                return cached

        if (
            chat_id < 0
            and chat_str not in self.data['users']
            and self._connection.execute(
                "SELECT 1 FROM users WHERE chat_id = 'legacy' LIMIT 1"
            ).fetchone()
        ):
            self.load_chat_users('legacy')
            self.data['users'][chat_str] = self.data['users'].pop('legacy')
            self._loaded_user_chats.discard('legacy')
            self._loaded_user_chats.add(chat_str)
            self._deleted_user_chats.add('legacy')
            for user_id in self.data['users'][chat_str]:
                self._mark_user_dirty(chat_str, user_id)
            self._chat_user_index.clear()
            self.mark_dirty()
        if chat_str not in self.data['users']:
            self.data['users'][chat_str] = {}
        if chat_str not in self._loaded_user_chats and uid_str not in self.data['users'][chat_str]:
            row = self._connection.execute(
                "SELECT value_json FROM users WHERE chat_id = ? AND user_id = ?",
                (chat_str, uid_str),
            ).fetchone()
            if row:
                self.data['users'][chat_str][uid_str] = json.loads(row[0])
        if uid_str not in self.data['users'][chat_str]:
            self.data['users'][chat_str][uid_str] = self._create_default_user(uid)

        user = self.data['users'][chat_str][uid_str]
        if not isinstance(user, dict):
            user = self._create_default_user(uid)
            self.data['users'][chat_str][uid_str] = user

        default_fields = {
            'night_messages': 0,
            'early_messages': 0,
            'reports_sent': 0,
            'phrases_added': 0,
            'marriage_count': 0,
            'divorced_count': 0,
            'proposals_sent': 0,
            'proposals_rejected': 0,
            'candies': 0,
            'candy_steal_successes': 0,
            'candy_steal_streak': 0,
            'candy_steal_next_at': 0,
            'total_mutes_survived': 0,
            'custom_tag': '',
            'custom_name': '',
            'first_name': '',
            'username': '',
            'rank': 0,
            'reputation': 0,
            'warnings': [],
            'awards': [],
            'activity': {},
            'marriage_partner': None,
            'pending_marriage_at': None,
            'birthday': None,
        }
        for field, default_value in default_fields.items():
            if field not in user:
                user[field] = default_value
        removed_legacy_fields = False
        for field in (
            'chats_activity',
            'rp_victims_sex',
            'rp_victims_kill',
            'last_rep_time_by_target',
            'last_rep_removed_time_by_target',
        ):
            if field in user:
                del user[field]
                removed_legacy_fields = True
        if self._prune_expired_user_warnings(user):
            removed_legacy_fields = True

        if removed_legacy_fields:
            self._mark_user_dirty(chat_str, uid_str)
            self.mark_dirty()

        if track_dirty:
            self._mark_user_dirty(chat_str, uid_str)
        if use_cache:
            user_cache.set(cache_key, user)
        return user

    def peek_user(self, chat_id: int, uid: int) -> dict:
        return self.get_user(chat_id, uid, track_dirty=False)

    def invalidate_user_cache(self, chat_id: int, uid: int):
        user_cache.invalidate(f"{chat_id}:{uid}")
        mention_cache.invalidate(f"mention_{chat_id}_{uid}")

    def invalidate_user_identity_cache(self, chat_id: int):
        self.invalidate_chat_user_index(chat_id)

    def update_user_from_message(self, msg: Message):
        if msg.from_user.is_bot:
            return False

        u = self.get_user(msg.chat.id, msg.from_user.id)
        changed = False
        identity_changed = False

        if is_main_chat(msg.chat.id, msg.message_thread_id):
            hour = kaliningrad_now().hour
            if hour >= 23 or hour <= 4:
                u['night_messages'] = u.get('night_messages', 0) + 1
            elif hour >= 5 and hour <= 7:
                u['early_messages'] = u.get('early_messages', 0) + 1

        if msg.from_user.username and u.get('username') != msg.from_user.username:
            u['username'] = msg.from_user.username
            changed = True
            identity_changed = True
        if msg.from_user.first_name and u.get('first_name') != msg.from_user.first_name:
            u['first_name'] = msg.from_user.first_name
            changed = True
            identity_changed = True
        u['last_seen'] = time.time()
        changed = True

        if changed:
            self.invalidate_user_cache(msg.chat.id, msg.from_user.id)
        if identity_changed:
            self.invalidate_user_identity_cache(msg.chat.id)
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
                'join_request_mode': 'off',
                'captcha_enabled': False,
                'raid_mode': False,
                'hide_channel_messages': False,
                'reason_templates': [],
                'moderation_notice_delete_seconds': 0,
                'content_filters': {
                    'stop_words': [],
                    'blocked_types': [],
                    'allow_domains': [],
                    'block_domains': [],
                },
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
            'message_id': None,
            'difficulty': difficulty,
            'started_at': time.time(),
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

    def exit_chat_game(self, chat_id: int, user_id: Optional[int] = None) -> bool:
        key = f"wordle_chat_{chat_id}"
        game = self.games.get(key)
        if not game or user_id is not None and game.get('user_id') != user_id:
            return False
        del self.games[key]
        return True

    def set_game_message(self, user_id: int, chat_id: int, message_id: int):
        game = self.get_chat_game(chat_id)
        if game is not None:
            game['message_id'] = message_id

    def get_chat_game(self, chat_id: int):
        return self.games.get(f"wordle_chat_{chat_id}")

wordle = WordleGame()
MARRIAGE_PROPOSAL_TTL = 60 * 60


def clear_pending_marriage(chat_id: int, user_id: int, user: dict) -> None:
    partner_id = user.get('pending_marriage')
    user['pending_marriage'] = None
    user['pending_marriage_at'] = None
    if partner_id is not None:
        try:
            partner = storage.get_user(chat_id, int(partner_id))
        except (TypeError, ValueError):
            partner = None
        if partner and str(partner.get('pending_marriage')) == str(user_id):
            partner['pending_marriage'] = None
            partner['pending_marriage_at'] = None
    storage.mark_dirty()


def marriage_proposal_expired(user: dict) -> bool:
    created_at = user.get('pending_marriage_at')
    return (
        not isinstance(created_at, (int, float))
        or time.time() - created_at >= MARRIAGE_PROPOSAL_TTL
    )


# ==================== Бот ====================

BOT_START_TIME = time.monotonic()
bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
dp = Dispatcher()
router = Router()
dp.include_router(router)


@router.errors()
async def handle_router_error(event: ErrorEvent):
    error = event.exception
    if isinstance(error, TelegramBadRequest) and 'message is not modified' in str(error).casefold():
        callback = event.update.callback_query
        if callback:
            try:
                await callback.answer()
            except TelegramAPIError as answer_error:
                logger.debug("Не удалось подтвердить callback после повторного редактирования: %s", answer_error)
        return True

    logger.error(
        "Необработанная ошибка обработчика",
        exc_info=(type(error), error, error.__traceback__),
    )
    return False

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
            u = storage.peek_user(chat_id, user)
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
    except Exception:
        return str(user)


def get_display_name(chat_id: int, uid: int) -> str:
    """Возвращает кастомное или реальное имя пользователя."""
    u = storage.peek_user(chat_id, uid)
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
    Получить ID цели. Явный аргумент цели имеет приоритет над ответом на сообщение.
    Поддерживает @username, Telegram ID и кликабельные упоминания без username.
    """
    if arg:
        arg = arg.strip()
        mention_span = get_target_mention_span(msg, arg)
        if mention_span:
            return mention_span[0]

    if arg and arg.casefold().startswith('id:') and arg[3:].isdigit():
        return int(arg[3:])

    # Если это @username
    if arg and arg.startswith('@'):
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
    if arg and arg.isdigit():
        return int(arg)

    # Поиск по имени (только в сохранённых)
    if arg:
        uid = storage.get_user_by_name(msg.chat.id, arg.casefold())
        if uid is not None:
            return uid
        return None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        return msg.reply_to_message.from_user.id

    return None


def has_explicit_target(msg: Message, arg: Optional[str]) -> bool:
    if not arg:
        return False
    if arg.casefold().startswith('id:') and arg[3:].isdigit():
        return True
    if get_target_mention_span(msg, arg) or arg.startswith('@') or arg.isdigit():
        return True
    return storage.get_user_by_name(msg.chat.id, arg.strip().casefold()) is not None


CHAT_DEFAULT_PERMISSIONS_CACHE_TTL = 60
CHAT_DEFAULT_PERMISSIONS_CACHE_MAX_SIZE = 1000
chat_default_permissions_cache: Dict[int, Tuple[float, ChatPermissions]] = {}


def _prune_chat_default_permissions_cache(now: float):
    expired_ids = [
        chat_id
        for chat_id, (expires_at, _) in chat_default_permissions_cache.items()
        if expires_at <= now
    ]
    for chat_id in expired_ids:
        chat_default_permissions_cache.pop(chat_id, None)
    if len(chat_default_permissions_cache) >= CHAT_DEFAULT_PERMISSIONS_CACHE_MAX_SIZE:
        oldest_ids = sorted(
            chat_default_permissions_cache,
            key=lambda chat_id: chat_default_permissions_cache[chat_id][0],
        )[:len(chat_default_permissions_cache) - CHAT_DEFAULT_PERMISSIONS_CACHE_MAX_SIZE + 1]
        for chat_id in oldest_ids:
            chat_default_permissions_cache.pop(chat_id, None)


async def restore_chat_default_permissions(chat_id: int, user_id: int) -> None:
    now = time.monotonic()
    _prune_chat_default_permissions_cache(now)
    cached = chat_default_permissions_cache.get(chat_id)
    if cached and now < cached[0]:
        permissions = cached[1]
    else:
        chat = await bot.get_chat(chat_id)
        if chat.permissions is None:
            raise RuntimeError(f"В чате {chat_id} Telegram не вернул права участников по умолчанию")
        permissions = chat.permissions
        chat_default_permissions_cache[chat_id] = (
            now + CHAT_DEFAULT_PERMISSIONS_CACHE_TTL,
            permissions,
        )
    await bot.restrict_chat_member(chat_id, user_id, permissions)


CHAT_OWNER_CACHE_TTL = 60
CHAT_OWNER_CACHE_MAX_SIZE = 1000
chat_owner_sync_cache: Dict[int, Tuple[float, Optional[int]]] = {}
chat_owner_sync_locks: Dict[int, asyncio.Lock] = {}
chat_owner_sync_lock_users: Dict[int, int] = {}


def _prune_chat_owner_sync_cache():
    if len(chat_owner_sync_cache) < CHAT_OWNER_CACHE_MAX_SIZE:
        return
    now = time.monotonic()
    expired_ids = [
        chat_id for chat_id, (expires_at, _) in chat_owner_sync_cache.items()
        if expires_at <= now
    ]
    for chat_id in expired_ids:
        chat_owner_sync_cache.pop(chat_id, None)
    if len(chat_owner_sync_cache) >= CHAT_OWNER_CACHE_MAX_SIZE:
        oldest_ids = sorted(
            chat_owner_sync_cache,
            key=lambda chat_id: chat_owner_sync_cache[chat_id][0],
        )[:len(chat_owner_sync_cache) - CHAT_OWNER_CACHE_MAX_SIZE + 1]
        for chat_id in oldest_ids:
            chat_owner_sync_cache.pop(chat_id, None)


async def sync_chat_owner(chat_id: int):
    """Keeps rank 5 assigned to the current Telegram chat owner."""
    _prune_chat_owner_sync_cache()
    now = time.monotonic()
    cached = chat_owner_sync_cache.get(chat_id)
    if cached and cached[0] > now:
        return

    lock = chat_owner_sync_locks.setdefault(chat_id, asyncio.Lock())
    chat_owner_sync_lock_users[chat_id] = chat_owner_sync_lock_users.get(chat_id, 0) + 1
    try:
        await _sync_chat_owner_locked(chat_id, lock)
    finally:
        remaining_users = chat_owner_sync_lock_users[chat_id] - 1
        if remaining_users:
            chat_owner_sync_lock_users[chat_id] = remaining_users
        else:
            chat_owner_sync_lock_users.pop(chat_id, None)
            if chat_owner_sync_locks.get(chat_id) is lock:
                chat_owner_sync_locks.pop(chat_id, None)


def remember_bot_group_chat(chat, status: str = 'member') -> bool:
    if chat.type not in ('group', 'supergroup'):
        return False

    chats = storage.data.setdefault('bot_chats', {})
    chat_key = str(chat.id)
    record = {
        'title': chat.title or str(chat.id),
        'username': chat.username or '',
        'type': chat.type,
        'status': status,
    }
    if chats.get(chat_key) == record:
        return False
    chats[chat_key] = record
    storage.mark_dirty()
    return True


def mark_bot_group_chat_left(chat):
    if chat.type not in ('group', 'supergroup'):
        return False
    chats = storage.data.setdefault('bot_chats', {})
    chat_key = str(chat.id)
    previous = chats.get(chat_key, {})
    if not isinstance(previous, dict):
        previous = {}
    record = {
        'title': chat.title or previous.get('title') or str(chat.id),
        'username': chat.username or previous.get('username') or '',
        'type': chat.type,
        'status': 'left',
    }
    if chats.get(chat_key) == record:
        return False
    chats[chat_key] = record
    storage.mark_dirty()
    return True


async def _sync_chat_owner_locked(chat_id: int, lock: asyncio.Lock):
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


@router.my_chat_member()
async def handle_my_chat_member_update(update: ChatMemberUpdated):
    chat_owner_sync_cache.pop(update.chat.id, None)
    anti_spam_admin_cache.invalidate_prefix(f"{update.chat.id}:")
    bot_rights_cache.invalidate_prefix(f"{update.chat.id}:")
    new_member = update.new_chat_member
    if new_member.status in ('left', 'kicked') or (
        new_member.status == 'restricted' and not new_member.is_member
    ):
        changed = mark_bot_group_chat_left(update.chat)
    else:
        changed = remember_bot_group_chat(update.chat)
    if changed:
        await storage.save()


def check_access(uid: int, chat_id: int, cmd: str, min_rank: int = 0) -> bool:
    chat_id_str = str(chat_id)
    command_func = COMMANDS.get(cmd)
    aliases = (
        [alias for alias, func in COMMANDS.items() if func == command_func]
        if command_func else [cmd]
    )
    if any(alias in DK_PROTECTED_COMMANDS for alias in aliases):
        return is_bot_superadmin(uid) or storage.peek_user(chat_id, uid).get('rank', 0) >= min_rank

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
    return storage.peek_user(chat_id, uid).get('rank', 0) >= required_rank if required_rank else True


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


async def bot_can(chat_id: int, right: str) -> Optional[bool]:
    cache_key = f"{chat_id}:{right}"
    cached = bot_rights_cache.get(cache_key)
    if cached is not None:
        return None if cached == 'error' else cached

    try:
        member = await bot.get_chat_member(chat_id, bot.id)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning(
            "Не удалось проверить право %s бота в чате %s: %s",
            right, chat_id, exc
        )
        bot_rights_cache.set(cache_key, 'error', ttl=10)
        return None

    allowed = member.status == 'creator' or (
        member.status == 'administrator' and bool(getattr(member, right, False))
    )
    if not allowed:
        logger.warning("У бота нет права %s в чате %s", right, chat_id)
    bot_rights_cache.set(cache_key, allowed)
    return allowed


async def require_bot_right(msg: Message, right: str, action: str) -> bool:
    allowed = await bot_can(msg.chat.id, right)
    if allowed is True:
        return True
    if allowed is None:
        await msg.answer(
            "❌ Не удалось проверить права бота через Telegram. "
            "Попробуйте выполнить действие позже."
        )
        return False
    await msg.answer(
        f"❌ Боту нужны права администратора Telegram для действия «{action}». "
        "Проверьте права бота в настройках чата."
    )
    return False


async def require_target_not_telegram_admin(msg: Message, target_id: int) -> bool:
    try:
        member = await bot.get_chat_member(msg.chat.id, target_id)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning(
            "Не удалось проверить статус цели %s в чате %s: %s",
            target_id, msg.chat.id, exc
        )
        await msg.answer(
            "❌ Не удалось проверить статус пользователя в Telegram. "
            "Попробуйте ещё раз позже."
        )
        return False

    if member.status in ('administrator', 'creator'):
        await msg.answer("❌ Нельзя наказать администратора Telegram.")
        return False
    return True


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
    initiator_rank = storage.peek_user(chat_id, initiator_id).get('rank', 0)
    target_rank = storage.peek_user(chat_id, target_id).get('rank', 0)
    if initiator_rank == 0 and target_rank == 0:
        return True
    if target_rank == 0:
        return True
    if initiator_rank > target_rank:
        return True
    return False


def save_activity(chat_id: int, uid: int, atype: str = 'messages', amount: int = 1):
    """Сохраняет активность пользователя в конкретном групповом чате."""
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
    for path in _get_local_meme_emoji_fonts():
        path = str(path)
        try:
            glyphs = FT2Font(path).get_charmap()
        except (OSError, RuntimeError):
            continue
        fonts.append((path, glyphs))
        seen_paths.add(path)

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
    font_family: str = 'DejaVu Sans',
    font_options: Optional[Dict[str, str]] = None,
) -> None:
    """Draw text with installed emoji fonts and readable fallback for unsupported emoji."""
    try:
        from matplotlib.font_manager import FontProperties
        from matplotlib.textpath import TextToPath
    except ImportError:
        fig.text(x, y, text, color=color, fontsize=fontsize, fontweight=fontweight)
        return

    text_to_path = TextToPath()
    selected_fonts = GRAPH_FONT_OPTIONS if font_options is None else font_options
    font_path = selected_fonts.get(font_family)
    default_font = (
        FontProperties(fname=font_path, weight=fontweight, size=fontsize)
        if font_path
        else FontProperties(family=font_family, weight=fontweight, size=fontsize)
    )
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
            width, _, _ = text_to_path.get_text_width_height_descent(
                display, properties, ismath=False
            )
            x += width / (fig.get_figwidth() * 72)
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
            width, _, _ = text_to_path.get_text_width_height_descent(
                display, default_font, ismath=False
            )
            x += width / (fig.get_figwidth() * 72)


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
        event_chat = getattr(event, 'chat', None)
        blocked_chats = storage.data.get('blocked_chats', {})
        if (
            event_chat
            and isinstance(blocked_chats, dict)
            and str(event_chat.id) in blocked_chats
        ):
            return None

        if isinstance(event, Message) and event.from_user and not event.from_user.is_bot:
            if event.chat.type in ('group', 'supergroup'):
                remember_bot_group_chat(event.chat)
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


class PrivateCommandRestrictionMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        if not isinstance(event, Message) or event.chat.type != 'private' or not event.text:
            return await handler(event, data)

        text = event.text.strip()
        first_token = text.split(maxsplit=1)[0].split('@', 1)[0].casefold()
        if first_token == '/start':
            return await handler(event, data)

        prefix = get_command_prefix(event.chat.id)
        cleaned = strip_command_prefix(text, event.chat.id)
        command_name, _ = match_command(cleaned)
        if (
            first_token in {'/help', '/info'}
            or command_name in {'инфо', 'помощь', 'help', 'info'}
        ):
            return await handler(event, data)

        normalized_command = cleaned.casefold()
        is_rp_command = any(
            normalized_command == action or normalized_command.startswith(action + ' ')
            for action in ALL_RP
        )
        is_command = (
            text.startswith('/')
            or text.startswith('!')
            or bool(prefix and text.startswith(prefix))
            or command_name is not None
            or is_rp_command
        )
        if is_command:
            if (
                event.from_user
                and is_bot_superadmin(event.from_user.id)
                and command_name in BOT_SUPERADMIN_ONLY_COMMANDS
            ):
                return await handler(event, data)
            await event.answer("Команды можно использовать только в группе. Добавьте меня в группу и вызывайте их там.")
            return None

        return await handler(event, data)


router.message.outer_middleware(MessageStatsMiddleware())
router.message.outer_middleware(PrivateCommandRestrictionMiddleware())


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
GRAPH_FONTS_DIR = Path(__file__).parent / 'fonts'


def load_graph_font_options() -> Dict[str, str]:
    if not MATPLOTLIB_AVAILABLE or not GRAPH_FONTS_DIR.is_dir():
        return {}
    from matplotlib import font_manager

    fonts = {}
    registered_paths = {
        str(Path(entry.fname).resolve())
        for entry in font_manager.fontManager.ttflist
        if entry.fname
    }
    for font_path in sorted(GRAPH_FONTS_DIR.iterdir()):
        if not font_path.is_file() or font_path.suffix.casefold() not in {'.ttf', '.otf'}:
            continue
        try:
            resolved_path = str(font_path.resolve())
            if resolved_path not in registered_paths:
                font_manager.fontManager.addfont(resolved_path)
                registered_paths.add(resolved_path)
            family = font_manager.FontProperties(fname=str(font_path)).get_name()
            fonts[family] = str(font_path)
        except (OSError, RuntimeError, ValueError):
            logger.exception("Не удалось загрузить шрифт графика %s", font_path)
    return fonts


GRAPH_FONT_OPTIONS: Dict[str, str] = {}
DEFAULT_GRAPH_FONT = 'DejaVu Sans'
_GRAPH_FONTS_LOADED = False


def _initialize_graph_fonts():
    global DEFAULT_GRAPH_FONT, _GRAPH_FONTS_LOADED
    if _GRAPH_FONTS_LOADED:
        return
    fonts = load_graph_font_options()
    GRAPH_FONT_OPTIONS.update(fonts)
    DEFAULT_GRAPH_FONT = 'Carlito' if 'Carlito' in fonts else next(
        iter(fonts), 'DejaVu Sans'
    )
    _GRAPH_FONTS_LOADED = True


def refresh_graph_fonts() -> bool:
    global DEFAULT_GRAPH_FONT, _GRAPH_FONTS_LOADED
    if GRAPH_RENDER_LOCK.locked():
        return False
    fonts = load_graph_font_options()
    changed = fonts != GRAPH_FONT_OPTIONS
    GRAPH_FONT_OPTIONS.clear()
    GRAPH_FONT_OPTIONS.update(fonts)
    _GRAPH_FONTS_LOADED = True
    DEFAULT_GRAPH_FONT = 'Carlito' if 'Carlito' in GRAPH_FONT_OPTIONS else next(
        iter(GRAPH_FONT_OPTIONS), 'DejaVu Sans'
    )
    return changed


def graph_font_token(name: str, path: str) -> str:
    return hashlib.sha1(f'{name}\0{path}'.encode('utf-8')).hexdigest()[:12]


def blend_graph_colors(first: str, second: str, first_ratio: float) -> str:
    first_rgb = tuple(int(first[index:index + 2], 16) for index in (1, 3, 5))
    second_rgb = tuple(int(second[index:index + 2], 16) for index in (1, 3, 5))
    mixed = tuple(
        round(a * first_ratio + b * (1 - first_ratio))
        for a, b in zip(first_rgb, second_rgb)
    )
    return '#' + ''.join(f'{channel:02x}' for channel in mixed)


def derive_graph_colors(background: str) -> Tuple[List[str], str]:
    background = background.lower()
    red, green, blue = (
        int(background[index:index + 2], 16)
        for index in (1, 3, 5)
    )
    brightness = (0.299 * red ** 2 + 0.587 * green ** 2 + 0.114 * blue ** 2) ** 0.5
    is_light = brightness >= 127.5

    if is_light:
        theme_id = 'light_default'
        panel = blend_graph_colors(background, '#000000', 0.96)
        accent = '#4f46e5'
        grid = blend_graph_colors(background, '#23272a', 0.84)
        secondary = blend_graph_colors(background, '#59636e', 0.55)
        text = '#23272a'
    else:
        theme_id = 'dark_default'
        panel = blend_graph_colors(background, '#ffffff', 0.94)
        accent = '#a5b4fc'
        grid = blend_graph_colors(background, '#f4f5ff', 0.75)
        secondary = blend_graph_colors(background, '#aeb5d0', 0.55)
        text = '#f4f5ff'

    return [background, panel, accent, grid, secondary, text], theme_id
GRAPH_RENDER_LOCK = asyncio.Lock()
activity_graph_wizards: Dict[Tuple[int, int], dict] = {}
ACTIVITY_GRAPH_WIZARD_TTL = 10 * 60


def get_activity_graph_preset_data(uid: int, create: bool = True) -> dict:
    all_presets = storage.data.setdefault('activity_graph_presets', {})
    if not isinstance(all_presets, dict):
        all_presets = {}
        storage.data['activity_graph_presets'] = all_presets
    user_data = all_presets.get(str(uid))
    if user_data is None and not create:
        return {}
    if user_data is None:
        user_data = {}
        all_presets[str(uid)] = user_data
    if not isinstance(user_data, dict):
        user_data = {}
        all_presets[str(uid)] = user_data
    user_data.setdefault('global', [])
    user_data.setdefault('chats', {})
    user_data.setdefault('active_global', None)
    user_data.setdefault('active_chats', {})
    return user_data


def get_activity_graph_settings(chat_id: int, uid: int) -> dict:
    preset_data = get_activity_graph_preset_data(uid, create=False)
    active_chats = preset_data.get('active_chats', {})
    chat_preset_id = active_chats.get(str(chat_id)) if isinstance(active_chats, dict) else None
    chat_presets_by_id = preset_data.get('chats', {})
    chat_presets = (
        chat_presets_by_id.get(str(chat_id), [])
        if isinstance(chat_presets_by_id, dict)
        else []
    )
    global_preset_id = preset_data.get('active_global')
    global_presets = preset_data.get('global', [])
    if not isinstance(chat_presets, list):
        chat_presets = []
    if not isinstance(global_presets, list):
        global_presets = []
    preset = next(
        (item for item in chat_presets if isinstance(item, dict) and item.get('id') == chat_preset_id),
        None,
    ) or next(
        (item for item in global_presets if isinstance(item, dict) and item.get('id') == global_preset_id),
        None,
    )
    if preset:
        return {
            'theme_id': preset.get('theme_id', 'dark_default'),
            'colors': preset.get('colors'),
            'font': preset.get('font', DEFAULT_GRAPH_FONT),
            'chart_type': preset.get('chart_type', 'line'),
        }
    user = storage.peek_user(chat_id, uid)
    return {
        'theme_id': user.get('activity_graph_theme', 'dark_default'),
        'colors': None,
        'font': DEFAULT_GRAPH_FONT,
        'chart_type': 'line',
    }


def generate_preview_activity(days: int) -> List[int]:
    """Возвращает предсказуемые демо-данные с плато, всплесками и нулём."""
    if days <= 0:
        return []

    pattern = [
        40, 40, 40, 40, 44, 72, 43, 41, 39, 40,
        20, 42, 44, 40, 40, 40, 0, 40, 43, 38,
        40, 74, 41, 39, 40, 40, 18, 42, 40, 40,
    ]
    return [pattern[index % len(pattern)] for index in range(days)]


def create_graph(
    user_data: dict,
    uid: int,
    days: int = 7,
    settings: Optional[dict] = None,
    preview: bool = False,
    font_options: Optional[Dict[str, str]] = None,
) -> Optional[BytesIO]:
    if not MATPLOTLIB_AVAILABLE:
        return None
    try:
        from matplotlib.backends.backend_agg import FigureCanvasAgg
        from matplotlib.figure import Figure
        from matplotlib.ticker import MaxNLocator
        _initialize_graph_fonts()
    except ImportError:
        logger.exception("Matplotlib недоступен для создания графика")
        return None
    act = user_data.get('activity', {})
    if not act and not preview:
        return None
    font_options = dict(GRAPH_FONT_OPTIONS) if font_options is None else font_options
    today = kaliningrad_now().date()
    dates, messages = [], []
    for i in range(days):
        d = today - timedelta(days=days - 1 - i)
        ds = d.strftime('%Y-%m-%d')
        dates.append(d)
        messages.append(max(0, act.get(ds, {}).get('messages', 0)))
    if preview:
        messages = generate_preview_activity(days)

    try:
        settings = settings or {
            'theme_id': user_data.get('activity_graph_theme', 'dark_default'),
            'colors': None,
            'font': DEFAULT_GRAPH_FONT,
            'chart_type': 'line',
        }
        theme_id = settings.get('theme_id', user_data.get('activity_graph_theme', 'dark_default'))
        if not isinstance(theme_id, str):
            theme_id = 'dark_default'
        theme = ACTIVITY_GRAPH_THEMES.get(theme_id, ACTIVITY_GRAPH_THEMES['dark_default'])
        _, _, background, panel, accent, fill, muted, text_color = theme
        custom_colors = settings.get('colors')
        if isinstance(custom_colors, (list, tuple)) and len(custom_colors) == 6:
            background, panel, accent, fill, muted, text_color = custom_colors
        font_name = settings.get('font', DEFAULT_GRAPH_FONT)
        if font_name not in font_options:
            font_name = DEFAULT_GRAPH_FONT
        fig = Figure(figsize=(10, 4.8), facecolor=background)
        FigureCanvasAgg(fig)
        ax = fig.subplots()
        fig.subplots_adjust(left=0.09, right=0.97, top=0.77, bottom=0.19)
        ax.set_facecolor(panel)
        graph_name = str(
            user_data.get('custom_name')
            or user_data.get('first_name')
            or user_data.get('username')
            or f'ID:{uid}'
        ).strip() or f'ID:{uid}'
        add_graph_text(
            fig,
            f'Активность · {graph_name}',
            0.09, 0.91, color=text_color, fontsize=17, fontweight='bold',
            font_family=font_name, font_options=font_options,
        )
        total_messages = sum(messages)
        active_days = sum(1 for count in messages if count > 0)
        average = total_messages / days if days else 0
        add_graph_text(
            fig,
            f'{total_messages:,} сообщений     ·     '
            f'{active_days}/{days} активных дней     ·     '
            f'{round(average):,} в день',
            0.09, 0.83, color=muted, fontsize=10,
            font_family=font_name, font_options=font_options,
        )

        maximum = max(messages, default=0)
        positions = list(range(len(dates)))
        if settings.get('chart_type') == 'bar':
            ax.bar(positions, messages, color=accent, edgecolor=background, linewidth=1.2, zorder=3)
        else:
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
        ax.yaxis.grid(True, color=fill, alpha=0.65, linewidth=0.8)
        ax.set_axisbelow(True)
        ax.tick_params(axis='y', colors=muted, labelsize=8, length=0, pad=8)
        ax.tick_params(
            axis='x', colors=muted, labelsize=8, length=3, pad=8,
            top=False, bottom=True, direction='in',
        )
        ax.set_yticks(MaxNLocator(nbins=4, integer=True).tick_values(0, max(maximum, 1)))
        label_step = max(1, (len(dates) + 5) // 6)
        date_label_indices = [
            index for index in positions
            if index % label_step == 0 or index == len(dates) - 1
        ]
        ax.set_xticks(date_label_indices)
        ax.set_xticklabels([dates[index].strftime('%d.%m') for index in date_label_indices])
        for label in ax.get_xticklabels() + ax.get_yticklabels():
            label.set_fontfamily(font_name)
        for spine in ax.spines.values():
            spine.set_visible(False)
        for index, count in enumerate(messages):
            if count > 0:
                if settings.get('chart_type') == 'bar':
                    offset, vertical_alignment = (0, 6), 'bottom'
                else:
                    if index > 0:
                        rising = count >= messages[index - 1]
                    elif index + 1 < len(messages):
                        rising = messages[index + 1] >= count
                    else:
                        rising = True
                    offset, vertical_alignment = (0, 6), 'bottom'
                    if not rising:
                        offset, vertical_alignment = (0, -6), 'top'
                        steep_fall = (
                            index + 1 < len(messages)
                            and count - messages[index + 1] >= max(maximum * 0.2, 1)
                        )
                        if steep_fall:
                            offset, vertical_alignment = (0, 6), 'bottom'
                ax.annotate(
                    f'{count:,}',
                    (positions[index], count),
                    xytext=offset, textcoords='offset points',
                    ha='center', va=vertical_alignment, color=text_color,
                    fontsize=7, fontweight='bold', fontfamily=font_name, zorder=6,
                    bbox={'facecolor': panel, 'edgecolor': 'none', 'alpha': 0.9, 'pad': 0.2},
                )
        buf = BytesIO()
        fig.savefig(buf, format='png', dpi=120, facecolor=background)
        buf.seek(0)
        return buf
    except Exception:
        logger.exception("Не удалось создать график активности пользователя %s", uid)
        return None


async def create_graph_async(
    chat_id: int,
    uid: int,
    days: int = 7,
    settings: Optional[dict] = None,
    preview: bool = False,
) -> Optional[BytesIO]:
    user_data = storage.peek_user(chat_id, uid)
    user_data = dict(user_data)
    activity = user_data.get('activity')
    user_data['activity'] = dict(activity) if isinstance(activity, dict) else {}
    graph_settings = copy.deepcopy(settings) if settings else get_activity_graph_settings(chat_id, uid)
    try:
        _initialize_graph_fonts()
    except ImportError:
        logger.exception("Шрифты Matplotlib недоступны для создания графика")
        return None
    graph_fonts = dict(GRAPH_FONT_OPTIONS)
    async with GRAPH_RENDER_LOCK:
        return await asyncio.to_thread(
            create_graph,
            user_data,
            uid,
            days,
            graph_settings,
            preview,
            graph_fonts,
        )


def get_user_status(uid: int, user_data: dict) -> str:
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
    'кастрировать': (['кастрировал(а)', 'лишил(а) достоинства'], '🔪'),

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
    'предложить близость': (
        [
            'бережно предложил(а) близость, оставив решение за партнёром',
            'честно поговорил(а) о желании стать ближе',
            'тактично предложил(а) провести время наедине',
            'сначала спросил(а), комфортно ли партнёру сблизиться',
            'предложил(а) близость и подчеркнул(а), что отказ — это нормально',
        ],
        '💞',
    ),
    'выебать': (['выебал(а)', 'оттрахал(а)'], '🔞'),
    'трахнуть': (['трахнул(а)', 'оттрахал(а)'], '🔞'),
    'отдаться': (['отдался(лась)', 'полностью отдался(лась)'], '💫'),
}

# Объединяем все команды
def ensure_rp_phrase_variants(commands: dict, modifiers: tuple) -> dict:
    expanded = {}
    for action, (phrases, emoji) in commands.items():
        variants = list(dict.fromkeys(phrases))[:5]
        modifier_index = 0
        while len(variants) < 5:
            phrase = phrases[modifier_index % len(phrases)]
            modifier = modifiers[modifier_index % len(modifiers)]
            variant = f"{modifier} {phrase}"
            modifier_index += 1
            if variant not in variants:
                variants.append(variant)
        expanded[action] = (tuple(variants), emoji)
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
SORTED_RP_ACTIONS = tuple(sorted(ALL_RP, key=len, reverse=True))

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
    'хуйня', 'говно', 'дерьмо', 'говнище',
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
    text = raw_text.casefold()

    for act in SORTED_RP_ACTIONS:
        if text == act or text.startswith(act + ' '):
            target_arg = raw_text[len(act):].strip()
            target_query = (
                target_arg.split(maxsplit=1)[0]
                if target_arg.startswith('@')
                else target_arg
            )
            tid = await get_target(msg, target_query)

            if not tid:
                await msg.answer(
                    "Кого именно? Ответь этой командой на сообщение или укажи "
                    "@username / полное имя участника."
                )
                return True

            if act in VIP_RP and storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) < VIP_RP_RANK:
                await msg.answer(f"❌ Нужен ранг {VIP_RP_RANK}+")
                return True
            if act in LOVE_RP:
                partner_id = storage.get_user(msg.chat.id, msg.from_user.id).get('marriage_partner')
                target_partner_id = storage.get_user(msg.chat.id, tid).get('marriage_partner')
                if str(partner_id) != str(tid) or str(target_partner_id) != str(msg.from_user.id):
                    await msg.answer("❌ Эти команды доступны только между супругами.")
                    return True
            if tid == msg.from_user.id and act not in ['извиниться', 'поздравить']:
                await msg.answer("❌ Нельзя с собой")
                return True

            action_text = random.choice(ALL_RP[act][0])
            emoji = ALL_RP[act][1]
            target_mention = mention(msg.chat.id, tid)
            save_activity(msg.chat.id, msg.from_user.id, 'commands')

            await msg.answer(
                f"{emoji} {mention(msg.chat.id, msg.from_user)} {action_text} {target_mention}",
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
    'ram': 'cmd_ram',
    'память': 'cmd_ram',
    'логи': 'cmd_logs',
    'бэкапы': 'cmd_backups',
    'статус': 'cmd_status',
    'сохранить': 'cmd_save_now',
    'права': 'cmd_bot_rights',
    'сброс кэшей': 'cmd_reset_caches',
    'юзер': 'cmd_export_user',
    'бд': 'cmd_database_info',
    'gc': 'cmd_gc',
    'рассылка': 'cmd_broadcast',
    'выйти': 'cmd_leave_chat',
    'блок чата': 'cmd_block_chat',
    'разблок чата': 'cmd_unblock_chat',
    'рестарт': 'cmd_restart',
    'аудит': 'cmd_superadmin_audit',
    'др': 'cmd_birthday',
    'день рождение': 'cmd_birthday',
    'birthday': 'cmd_birthday',
    'bd': 'cmd_birthday',
    'топ': 'cmd_top',
    'статистика чата': 'cmd_chat_stats',
    'статистика': 'cmd_stats',
    'мут': 'cmd_mute',
    'размут': 'cmd_unmute',
    'бан': 'cmd_ban',
    'разбан': 'cmd_unban',
    'кик': 'cmd_kick',
    'история': 'cmd_moderation_history',
    'лог': 'cmd_moderation_log',
    'модстат': 'cmd_moderation_stats',
    'причины': 'cmd_reason_templates',
    'автоудаление': 'cmd_moderation_auto_delete',
    'заявки': 'cmd_join_requests',
    'фильтр': 'cmd_filters',
    'капча': 'cmd_captcha',
    'рейд': 'cmd_raid_mode',
    'закрыть': 'cmd_freeze_chat',
    'открыть': 'cmd_unfreeze_chat',
    'каналы': 'cmd_channel_autohide',
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
    'варннастройка': 'cmd_warn_actions',
    'настройка варнов': 'cmd_warn_actions',
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
    'дуэль': 'cmd_duel',
    'кнб': 'cmd_rps_menu',
    'кнб бот': 'cmd_rps_with_bot',
    'камень': 'cmd_rps_choice',
    'ножницы': 'cmd_rps_choice',
    'бумага': 'cmd_rps_choice',
    'крестики нолики': 'cmd_ttt_menu',
    'ttt': 'cmd_ttt_menu',
    'сапёр': 'cmd_minesweeper',
    'сапер': 'cmd_minesweeper',
    'рп': 'cmd_rp_list',
    'погода': 'cmd_weather',
    'п': 'cmd_weather',
    'время': 'cmd_time',
    'который час': 'cmd_time',
    'сколько времени': 'cmd_time',
    'тема графика': 'cmd_activity_graph_theme',
    'график тема': 'cmd_activity_graph_theme',
    'график': 'cmd_activity_graph_theme',
    'шутка': 'cmd_random_joke',
    'украсть': 'cmd_steal_candy',
    'баланс': 'cmd_candy_balance',
    'конфеты': 'cmd_candy_balance',
    'мем': 'cmd_meme',
    'мемер': 'cmd_meme',
    'meme': 'cmd_meme',
    'memer': 'cmd_meme',
    'шиперим': 'cmd_ship',
    'шипперим': 'cmd_ship',
    'моя статья': 'cmd_my_article',
    'опрос': 'cmd_poll',
    'poll': 'cmd_poll',
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
    'группы': 'cmd_list_bot_chats',
    'чаты': 'cmd_list_bot_chats',
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

SORTED_COMMAND_NAMES = sorted(COMMANDS, key=len, reverse=True)

COMMAND_ERROR_HINTS = {
    'кто я': '!кто я',
    'кто ты': '!кто ты @user',
    'кто админ': '!кто админ',
    'дуэль': '!дуэль @username (или ответом на сообщение)',
    'мут': '!мут @user 30м флуд',
    'размут': '!размут @user',
    'бан': '!бан @user реклама',
    'разбан': '!разбан @user',
    'пред': '!пред @user 7 флуд',
    'варн': '!пред @user 7 флуд',
    'снятьпред': '!снятьпред @user',
    'варннастройка': '!варннастройка 3 мут 60',
    'погоняло': '!погоняло @user Крутой',
    'мем': '!мем',
    'мемер': '!мемер',
    'meme': '!meme',
    'memer': '!memer',
    'топ': '!топ день',
    'статистика': '!статистика',
    'помощь': '!помощь',
    'погода': '!погода',
    'опрос': '!опрос Вопрос?',
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
    spawn_background_task(delete_message_after(error_msg, 4))


async def delete_message_after(msg: Message, delay: int):
    await asyncio.sleep(delay)
    try:
        await telegram_call_with_retry(msg.delete)
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

    for cmd in SORTED_COMMAND_NAMES:
        if text_lower == cmd or text_lower.startswith(cmd + ' '):
            return cmd, text[len(cmd):].strip()

    return None, None


@router.message(Command('start'))
async def cmd_start(msg: Message):
    storage.update_user_from_message(msg)
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    if msg.chat.type == 'private':
        try:
            sticker_set = await bot.get_sticker_set(name='S_drugom_meme_xD')
            if len(sticker_set.stickers) < 39:
                raise ValueError("В наборе меньше 39 стикеров")
            await msg.answer_sticker(sticker_set.stickers[38].file_id)
            await asyncio.sleep(0.7)
        except (TelegramAPIError, ValueError) as exc:
            logger.warning("Не удалось отправить 39-й стикер приветствия: %s", exc)

        bot_info = await bot.get_me()
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(text="ℹ️ !инфо", callback_data="private_start_info"),
                InlineKeyboardButton(
                    text="➕ Добавить в группу",
                    url=f"https://t.me/{bot_info.username}?startgroup=true",
                ),
            ],
        ])
        await msg.answer(
            f"🐻 <b>Йо, {html.escape(msg.from_user.full_name, quote=False)}! Рад тебя видеть!</b>\n\n"
            "Я — Обкуренный Валера: помогаю наводить порядок в чате, показываю статистику "
            "и не даю заскучать с играми и шуточками. 🐻✨\n\n"
            "Загляни в мои возможности через «!инфо» или добавь меня в свою группу — "
            "там и начнётся самое интересное! 👇",
            reply_markup=keyboard,
        )
        return

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


@router.callback_query(F.data == 'private_start_info')
async def private_start_info_callback(call: CallbackQuery):
    if not call.message or call.message.chat.type != 'private':
        await call.answer("Эта кнопка доступна только в личном сообщении с ботом.", show_alert=True)
        return

    show_bot_admin = is_bot_superadmin(call.from_user.id)
    show_moderation = (
        show_bot_admin or (
            call.message.chat.type == 'private'
            or storage.get_user(call.message.chat.id, call.from_user.id).get('rank', 0) >= 1
        )
    )
    await call.message.answer(
        help_main_text(show_moderation, show_bot_admin),
        reply_markup=help_main_kb(show_moderation, show_bot_admin, call.from_user.id),
    )



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
    'info': ("👤 Профиль и статистика",
             "👤 <b>Профиль и статистика</b>\n"
             f"{UI_LINE}\n\n"
             "🪪 <b>Профиль</b>\n"
             "  <code>!кто я</code> / <code>!профиль</code> — ваш профиль (<code>/profile</code>)\n"
             "  <code>!др</code> / <code>!день рождение</code> / <code>!birthday</code> / <code>!bd</code> — настроить день рождения или посмотреть, сколько осталось\n"
             "  <code>!кто ты @user</code> — информация о пользователе\n"
             "  <code>!кто админ</code> — администрация и ранги чата\n"
             "  <code>!ид</code> — ваш ID и ID чата; ответом — ID автора сообщения\n\n"
             "🏅 <b>Ранги и активность</b>\n"
             "  <code>!ранг</code> — ваш ранг; <code>!ранги</code> — список рангов\n"
             "  <code>!топ [день/неделя/месяц/год/всё]</code> — рейтинг активности (<code>/top</code>)\n"
             "  <code>!статистика</code> — ваша статистика\n"
             "  <code>!статистика чата</code> — статистика чата\n"
             "  <code>!тема графика</code> — выбрать светлую или тёмную тему графика активности профиля\n\n"
             "Для справки: <code>!помощь</code> / <code>!help</code> / <code>!инфо</code> / <code>!info</code>"),
    'community': ("🤝 Общение и сообщество",
             "🤝 <b>Общение и сообщество</b>\n"
             f"{UI_LINE}\n\n"
             "🗳️ <b>Опросы и обращения</b>\n"
             "  <code>!опрос Вопрос?</code> — быстрый опрос с вариантами «Да» и «Нет»; свои варианты: <code>!опрос Вопрос? / Вариант 1 / Вариант 2</code> (также можно использовать <code>\\</code>)\n"
             "  <code>!репорт текст</code> — отправить жалобу администраторам чата\n\n"
             "🏷️ <b>Имя и тег</b>\n"
             "  <code>!ник Имя</code> — изменить своё отображаемое имя\n"
             "  Пользователь с рангом 1+ может изменить имя участника командой <code>!ник @user Имя</code> "
             "или ответом на его сообщение\n"
             "  <code>!погоняло Текст</code> — установить себе тег; "
             "<code>!погоняло сбросить</code> — убрать его"),
    'moderation': ("🛡️ Наказания и порядок",
             "🛡️ <b>Наказания и порядок</b>\n"
             f"{UI_LINE}\n\n"
             "🔇 <b>Мут и бан</b>\n"
             "  <code>!мут @user 30м причина</code> — ограничить участника (ранг 1+); можно ответом или кликабельным упоминанием имени без @username\n"
             "  При ответе число до года считается сроком мута; числовой ID указывайте явно: <code>id:123456</code>\n"
             "  <code>!мут @user навсегда причина</code> — бессрочный мут; временный срок — не более 1 года\n"
             "  <code>!размут @user</code> / <code>!-мут @user</code> — снять мут\n"
             "  <code>!бан @user причина</code> — заблокировать (ранг 3+); чтобы забанить канал, ответьте на его сообщение командой <code>!бан причина</code>\n"
             "  <code>!разбан @user</code> / <code>!-бан @user</code> — снять бан; канал разбанивается ответом на его сообщение командой <code>!разбан</code>\n\n"
             "  <code>!кик @user причина</code> — удалить участника из чата без блокировки (ранг 3+)\n"
             "  <code>!бан @user 2ч причина</code> — временно заблокировать до года; срок необязателен\n"
             "  <code>!история @user</code> — 20 действий пользователя за 90 дней; <code>!лог</code> — 20 последних записей чата (ранг 1+)\n\n"
             "  <code>!модстат</code> — действия за неделю (ранг 1+)\n"
             "  <code>!причины add флуд</code> — добавить шаблон; <code>!пред @user 1</code> — применить его (ранг 2+)\n"
             "  <code>!автоудаление 30</code> — удалять ответы и команды через 30 секунд; <code>0</code> отключает (ранг 5+)\n\n"
             "  <code>!заявки off|on|admin</code> — выключить, автоодобрять или отправлять кнопки Telegram-админам (ранг 5+)\n\n"
             "🧩 <b>Защита чата</b>\n"
             "  <code>!капча on|off</code> — проверка новичков кнопкой; кик через 5 минут (ранг 5+)\n"
             "  <code>!рейд on|off</code> — сохраняемый режим; авто при 6 входах за 10 секунд (ранг 5+)\n"
             "  <code>!закрыть 10м</code> / <code>!открыть</code> — заморозить чат и восстановить его разрешения (ранг 5+)\n"
             "  <code>!фильтр</code> — слова, типы сообщений, домены; <code>!каналы on|off</code> — скрывать сообщения каналов (ранг 5+)\n\n"
             "⚠️ <b>Предупреждения</b>\n"
             "  <code>!пред @user причина</code> / <code>!варн</code> / <code>!warn</code> — выдать предупреждение (ранг 1+)\n"
             "  <code>!преды @user</code> / <code>!варны</code> / <code>!warns</code> — посмотреть предупреждения\n"
             "  <code>!варннастройка</code> — просмотреть действия; <code>!варннастройка 3 мут 60</code> — задать мут за 3 предупреждения\n"
             "  Действие также можно настроить командами <code>!варннастройка 5 бан</code>, <code>!варннастройка 3 кик</code> или <code>!варннастройка 3 выкл</code>; <code>!варннастройка сбросить</code> возвращает настройки по умолчанию (ранг 2+)\n"
             "  <code>!варнлист</code> / <code>!предлист</code> / <code>!варнылист</code> / <code>!предупреждения</code> / <code>!список предупреждений</code> / <code>!warnlist</code> / <code>!warninglist</code> / <code>!warningslist</code> — все активные предупреждения\n"
             "  <code>!снятьпред @user [номер]</code> / <code>!снятьварн</code> / <code>!-пред</code> / <code>!-варн</code> / <code>!unwarn</code> — снять предупреждение (ранг 2+)\n\n"
             "🔎 <b>Списки наказаний</b>\n"
             "  <code>!мутлист</code> / <code>!муты</code> / <code>!мутылист</code> / <code>!список мутов</code> / <code>!mutelist</code> / <code>!mutes</code> — активные муты (ранг 1+)\n"
             "  <code>!банлист</code> / <code>!баны</code> / <code>!список банов</code> / <code>!banlist</code> / <code>!bans</code> — действующие баны из списка бота (ранг 3+)\n\n"
             "🧹 <b>Сообщения</b>\n"
             "  <code>!-смс</code> — удалить сообщение ответом (ранг 1+)\n"
             "  <code>!очистить</code> — удалить сообщения от выбранного и выше (ранг 2+)\n"
             "  <code>!пин</code> — закрепить сообщение ответом (ранг 2+)\n\n"
             "🪜 <b>Ранги</b>\n"
             "  <code>!повысить @user [ранг]</code> / <code>!понизить @user [ранг]</code> — изменить ранг (требуется ранг 5)\n"
             "  Владелец Telegram-чата автоматически получает ранг 5; его ранг нельзя изменить этими командами.\n\n"
             "📝 <b>Теги участников</b>\n"
             "  <code>!погоняло @user Текст</code> — изменить тег другого участника (ранг 1+)\n\n"
             "Эта справка доступна для чтения в личке. Модераторские команды выполняются только в группе и требуют указанный ранг; для мута и бана также нужны права администратора Telegram. Ответ на сообщение часто заменяет <code>@user</code>."),
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
    'reputation': ("⭐ Репутация",
             "⭐ <b>Репутация</b>\n"
             f"{UI_LINE}\n\n"
             "Ответьте на сообщение символом <code>+</code> или словом/эмодзи одобрения, чтобы повысить репутацию; символом <code>-</code> или дизлайком — снять балл.\n"
             "Положительный или отрицательный эмодзи на стикере тоже изменяет репутацию сразу.\n\n"
             "После изменения следующий кулдаун того же типа — 15 минут, затем он удваивается до максимума в 4 часа. Для <code>+</code> и <code>-</code> серии независимы: действие одного типа не увеличивает кулдаун другого. После 4 часов без любых изменений обе серии сбрасываются. Сохраняются дневные лимиты и ограничение на повтор для того же участника.\n"
             "Некоторые действия доступны с рангом или только участникам в браке."),
    'phrases': ("💬 Фразы и правила",
             "💬 <b>Фразы, приветствия и правила</b>\n"
             f"{UI_LINE}\n\n"
             "🗨️ <b>Фразы</b>\n"
             "  <code>!добавить фразу [-any] слово ответ</code> — добавить автоответ (ранг 1+)\n"
             "  <code>!удалить фразу слово [ответ]</code> — удалить фразу (ранг 1+)\n"
             "  <code>!фразы</code> — список фраз\n"
             "  <code>!показать фразу слово</code> — ответы на триггер\n"
             "  <code>!статистика фраз</code> — частота использования\n\n"
             "👋 <b>Приветствие и прощание</b>\n"
             "  <code>!приветствие вкл/выкл</code>, <code>!приветствие текст ...</code> или <code>!приветствие картинка URL</code> — настроить приветствие (ранг 2+)\n"
             "  <code>!прощание вкл/выкл</code> / <code>!прощание текст ...</code> / <code>!прощание картинка URL</code> — настроить прощание (ранг 2+)\n\n"
             "📜 <b>Правила</b>\n"
             "  <code>!правила</code> — посмотреть правила\n"
             "  <code>!добавитьправило текст</code> — добавить правило (ранг 4+)\n"
             "  <code>!очиститьправила</code> — удалить правила (ранг 4+)"),
    'fun': ("🎲 Разное и развлечения",
             "🎲 <b>Разное и развлечения</b>\n"
             f"{UI_LINE}\n\n"
             "🌦️ <b>Полезное</b>\n"
             "  <code>!погода</code> / <code>!п</code> — узнать погоду (<code>/weather</code>)\n"
             "  <code>!время [город или регион]</code> / <code>!который час [город или регион]</code> "
             "— узнать местное время; по умолчанию используется Калининград, например "
             "<code>!время Токио</code>\n"
             "  <code>!пинг</code> / <code>!ping</code> — проверить отклик бота (<code>/ping</code>)\n"
             "  <code>1 доллар</code> — пересчитать сумму в рубли, евро и другие валюты\n\n"
             "✨ <b>Для настроения</b>\n"
             "  <code>!шутка</code> — случайная шутка\n"
             "  <code>!украсть</code> — вместе с Валерой стащить конфеты у Паши: сначала 1–3, затем добыча растёт с каждой подряд успешной кражей до 10–50 🍬. Успех: кулдаун 24 часа; провал (15%): потеря 10% запаса (округление вверх), сброс серии и кулдаун 3 часа.\n"
             "  <code>!баланс</code> / <code>!конфеты</code> — посмотреть запас, серию и диапазон следующей добычи Валеры\n"
             "  <code>!мем</code> / <code>!мемер</code> / <code>!meme</code> / <code>!memer</code> — меню мема с текстом и демотиватора; первый поддерживает фото, GIF, MP4, стикеры и эмодзи\n"
             "  Для MP4 можно выбрать GIF или видео с исходным звуком; демотиватор оформляется на чёрном фоне с подписью шрифтом Times New Roman.\n"
             "  <code>!шиперим</code> — случайно выбрать пару из знакомых боту участников чата\n"
             "  <code>!моя статья</code> — получить случайную статью УК РФ в шуточном приговоре\n"
             "  <code>!валера</code> / <code>!валерка</code> / <code>!валерианыч</code> — меню функций Валеры"),
    'games': ("🕹️ Игры и РП",
             "🕹️ <b>Игры и РП</b>\n"
             f"{UI_LINE}\n\n"
             "🕹️ <b>Игры</b>\n"
             "  <code>!игры</code> / <code>!игра</code> / <code>!играть</code> / <code>!game</code> — меню игр (<code>/game</code>)\n"
             "  <code>!дуэль @username</code> или ответом <code>!дуэль</code> на сообщение — вызвать игрока на групповую боевую дуэль\n"
             "  В дуэли оба игрока выбирают удар, сильный удар или защиту кнопками в чате; личка не нужна.\n"
             "  <code>!кнб</code> — камень-ножницы-бумага; <code>!кнб бот</code> — против бота\n"
             "  <code>!камень</code> / <code>!ножницы</code> / <code>!бумага</code> — ход в КНБ\n"
             "  <code>!сапёр</code> — игра в сапёра с выбором сложности: 5×5, 7×7 или 8×9\n"
             "  <code>!крестики нолики</code> / <code>!ttt</code> — крестики-нолики\n"
             "  <code>!wordle</code> / <code>!вордле</code> / <code>!вордл</code> / <code>!слово</code> / <code>!угадай слово</code> — Wordle\n"
             "  В Wordle отвечайте словом на сообщение игры; <code>!wordle exit</code> — выйти, <code>!wordle stop</code> — остановить.\n\n"
             "🎭 <b>РП</b>\n"
             "  <code>!рп</code> — меню РП-команд\n"
             "  Используйте команду РП с <code>@user</code> или ответом на его сообщение.\n\n"
             "Используйте игровые команды в групповом чате и следуйте подсказкам бота."),
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
             "Настройки анти-модерации, анти-спама и ДК доступны пользователям с рангом 5."),
    'admin': ("⚙️ Администрирование чата",
             "⚙️ <b>Администрирование чата</b>\n"
             f"{UI_LINE}\n\n"
             "⚙️ <b>Команды и параметры чата</b>\n"
             "  <code>!префикс</code> — показать текущий префикс\n"
             "  <code>!префикс .</code> — установить префикс (1–16 знаков)\n"
             "  <code>!префикс откл</code> — отключить префикс; команды будут работать без него\n"
             "  Настройка префикса доступна рангу 5+.\n\n"
             "📢 <b>Инструменты администратора</b>\n"
             "  <code>!общий сбор</code> — упомянуть администраторов (ранг 5)\n"
             "  <code>!перед @user</code> — переслать сообщение в ответ на него\n"
             "  <code>!название ранга 0-5 Название</code> / <code>!переранг 0-5 Название</code> — переименовать ранг (ранг 5)\n"
             "  <code>!пик выкл</code> / <code>!pic off</code> — отключить ответы на <code>/pic</code> (ранг 5+)\n"
             "  <code>!пик вкл</code> / <code>!pic on</code> — снова включить ответы (ранг 5+)\n\n"
             "Владелец Telegram-чата автоматически получает ранг 5; его ранг нельзя изменить командами повышения или понижения.\n"
             "Для команд модерации также могут потребоваться права администратора Telegram."),
    'bot_admin': ("👑 Команды главных администраторов",
             "👑 <b>Команды главных администраторов бота</b>\n"
             f"{UI_LINE}\n\n"
             "Этот раздел и все перечисленные здесь команды доступны только главным администраторам бота.\n\n"
             "💾 <b>Резервные копии</b>\n"
             "  <code>!бэкап</code> — создать резервную копию\n"
             "  <code>!бэкапы</code> — список копий с датой/размером и выбором для восстановления\n"
             "  <code>!восстановить [id]</code> — запросить восстановление последней или выбранной копии\n"
             "  <code>!бэкап файл</code> — создать копию и отправить SQLite-файл в личный чат\n\n"
             "🛠️ <b>Диагностика и обслуживание</b>\n"
             "  <code>!логи [уровень] [N]</code> — хвост лог-файла (только в личке)\n"
             "  <code>!статус</code> — аптайм, версия, БД, кэши, задачи и RSS\n"
             "  <code>!сохранить</code> — принудительно записать состояние в SQLite\n"
             "  <code>!права &lt;chat_id&gt;</code> — проверить права бота в чате\n"
             "  <code>!сброс кэшей</code>, <code>!юзер chat_id user_id</code>, <code>!бд</code>, <code>!gc</code>\n\n"
             "📡 <b>Управление ботом</b>\n"
             "  <code>!рассылка текст</code> — предпросмотр и подтверждение перед отправкой\n"
             "  <code>!выйти chat_id</code>, <code>!блок чата chat_id</code>, <code>!разблок чата chat_id</code>\n"
             "  <code>!рестарт</code> — graceful shutdown; перезапуск выполняет настроенный супервизор\n"
             "  <code>!аудит</code> — последние действия главных администраторов\n"
             "  <code>!группы</code> / <code>!чаты</code> — показать группы, где находится бот\n"
             "Экспорт бэкапа, !логи, !юзер, !бд и !рассылка доступны только в личном чате. "
             "Главные администраторы бота не становятся владельцами или администраторами Telegram-чатов."),
}


HELP_CATEGORIES = {
    'society': ("👥 Общество", ('info', 'community', 'awards', 'reputation', 'phrases')),
    'entertainment': ("🎮 Развлечения", ('fun', 'games')),
    'moderation': ("🛡️ Модерство", ('moderation', 'settings', 'admin')),
    'bot_admin': ("👑 Админ", ('bot_admin',)),
}


def help_visible_categories(show_moderation: bool, show_bot_admin: bool) -> List[str]:
    return [
        key for key in HELP_CATEGORIES
        if (show_moderation or key != 'moderation')
        and (show_bot_admin or key != 'bot_admin')
    ]


def help_main_text(show_moderation: bool = True, show_bot_admin: bool = True) -> str:
    total_cmds = len(COMMANDS)
    counter_line = (
        f"📦 <b>{total_cmds} вариантов команд</b> (включая алиасы)\n\n"
        if total_cmds else ""
    )
    category_list = "\n".join(
        f"• {HELP_CATEGORIES[key][0]}"
        for key in help_visible_categories(show_moderation, show_bot_admin)
    )
    return (
        "🐻 <b>ОБКУРЕННЫЙ ВАЛЕРА</b>\n"
        f"{UI_LINE}\n"
        "🧭 <b>Помощь и информация</b>\n\n"
        "Выберите категорию, затем нужный раздел 👇\n\n"
        f"{counter_line}"
        f"{category_list}\n"
        f"{UI_LINE}\n"
        "💡 Префикс команд можно настроить через <code>!префикс</code>\n"
        "📌 Примеры: <code>!кто я</code>, <code>!топ</code>, <code>!игры</code>"
    )


def help_main_kb(
    show_moderation: bool,
    show_bot_admin: bool,
    owner_id: int,
) -> InlineKeyboardMarkup:
    keys = help_visible_categories(show_moderation, show_bot_admin)
    rows = []
    for i in range(0, len(keys), 2):
        row = []
        for k in keys[i:i + 2]:
            row.append(InlineKeyboardButton(
                text=HELP_CATEGORIES[k][0],
                callback_data=f"help_category_{k}_{owner_id}",
            ))
        rows.append(row)
    rows.append([InlineKeyboardButton(text="❌ Закрыть", callback_data=f"help_close_{owner_id}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def help_category_text(category: str) -> str:
    title, section_keys = HELP_CATEGORIES[category]
    section_list = "\n".join(
        f"• {HELP_SECTIONS[key][0]}" for key in section_keys
    )
    return (
        f"🐻 <b>{title}</b>\n"
        f"{UI_LINE}\n\n"
        "Выберите раздел 👇\n\n"
        f"{section_list}"
    )


def help_category_kb(category: str, owner_id: int) -> InlineKeyboardMarkup:
    _, section_keys = HELP_CATEGORIES[category]
    rows = [
        [InlineKeyboardButton(
            text=HELP_SECTIONS[key][0],
            callback_data=f"help_section_{key}_{owner_id}",
        )]
        for key in section_keys
    ]
    rows.append([InlineKeyboardButton(
        text="◀️ К категориям",
        callback_data=f"help_back_{owner_id}",
    )])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def help_section_kb(category: str, owner_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(
            text=f"◀️ К разделам: {HELP_CATEGORIES[category][0]}",
            callback_data=f"help_category_{category}_{owner_id}",
        )]
    ])


@router.callback_query(F.data.startswith('help_'))
async def help_callback(call: CallbackQuery):
    try:
        if not call.message:
            return await call.answer("❌ Сообщение справки недоступно.", show_alert=True)

        try:
            action, owner_id = call.data.removeprefix('help_').rsplit('_', 1)
            owner_id = int(owner_id)
        except (AttributeError, ValueError):
            return await call.answer("❌ Эта кнопка справки устарела.", show_alert=True)
        if call.from_user.id != owner_id:
            return await call.answer("Эта справка открыта другим пользователем.", show_alert=True)

        show_bot_admin = is_bot_superadmin(call.from_user.id)
        show_moderation = (
            show_bot_admin or (
                call.message.chat.type == 'private'
                or storage.get_user(call.message.chat.id, call.from_user.id).get('rank', 0) >= 1
            )
        )
        
        if action == 'close':
            try:
                await call.message.delete()
            except Exception:
                pass
        elif action == 'back':
            await call.message.edit_text(
                help_main_text(show_moderation, show_bot_admin),
                reply_markup=help_main_kb(show_moderation, show_bot_admin, owner_id),
            )
        elif action.startswith('category_'):
            category = action.removeprefix('category_')
            if category not in help_visible_categories(show_moderation, show_bot_admin):
                await call.answer("Раздел недоступен.", show_alert=True)
                return
            await call.message.edit_text(
                help_category_text(category),
                reply_markup=help_category_kb(category, owner_id),
            )
        elif action.startswith('section_'):
            section = action.removeprefix('section_')
            category = next(
                (
                    key for key in help_visible_categories(show_moderation, show_bot_admin)
                    if section in HELP_CATEGORIES[key][1]
                ),
                None,
            )
            if category is None or section not in HELP_SECTIONS:
                await call.answer("Раздел недоступен.", show_alert=True)
                return
            await call.message.edit_text(
                HELP_SECTIONS[section][1],
                reply_markup=help_section_kb(category, owner_id),
            )
        
        await call.answer()
    except Exception as e:
        logger.error(f"help_callback ошибка: {e}", exc_info=True)
        try:
            await call.answer("❌ Ошибка", show_alert=True)
        except Exception:
            pass


async def cmd_help(msg: Message):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    show_bot_admin = is_bot_superadmin(msg.from_user.id)
    show_moderation = (
        show_bot_admin or (
            msg.chat.type == 'private'
            or storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) >= 1
        )
    )
    await msg.answer(
        help_main_text(show_moderation, show_bot_admin),
        reply_markup=help_main_kb(show_moderation, show_bot_admin, msg.from_user.id),
    )


@router.message(Command('help'))
async def slash_help(msg: Message):
    await cmd_help(msg)


@router.message(Command('info'))
async def slash_info(msg: Message):
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
    amount = float(match.group('amount').replace(',', '.'))
    if match.group('multiplier'):
        amount *= 1000
    return amount, currency_code


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


MEME_FONT_PATH = Path(__file__).resolve().parent / 'fonts' / 'ofont.ru_Impact.ttf'
DEMOTIVATOR_FONT_PATH = Path(__file__).resolve().parent / 'fonts' / 'timesnewromanpsmt.ttf'
MEME_EMOJI_FONT_DIR = Path(__file__).resolve().parent / 'fonts'
MEME_SESSION_TTL = 10 * 60
MEME_MAX_IMAGE_BYTES = 20 * 1024 * 1024
MEME_MAX_IMAGE_PIXELS = 12_000_000
MEME_MAX_RENDER_DIMENSION = 1600
MEME_MAX_ANIMATION_BYTES = 50 * 1024 * 1024
MEME_MAX_TEXT_LENGTH = 400
meme_sessions: Dict[Tuple[int, int], dict] = {}
MEME_RENDER_SEMAPHORE = asyncio.Semaphore(1)


@lru_cache(maxsize=512)
def _get_meme_emoji_font(cluster: str, size: int):
    from PIL import ImageFont

    codepoints = {
        ord(char) for char in cluster
        if char not in {'\ufe0f', '\ufe0e', '\u200d'}
        and not 0x1F3FB <= ord(char) <= 0x1F3FF
    }
    local_font_error = None
    for path in _get_local_meme_emoji_fonts():
        try:
            return ImageFont.truetype(str(path), size)
        except OSError as exc:
            local_font_error = exc

    for path, glyphs in get_graph_emoji_fonts():
        if codepoints and codepoints.issubset(glyphs):
            return ImageFont.truetype(path, size)
    if local_font_error:
        raise RuntimeError(
            'Не удалось загрузить emoji-шрифт из папки fonts в нужном размере.'
        ) from local_font_error
    return None


@lru_cache(maxsize=1)
def _get_local_meme_emoji_fonts() -> Tuple[Path, ...]:
    if not MEME_EMOJI_FONT_DIR.is_dir():
        return ()
    paths = [
        path for path in MEME_EMOJI_FONT_DIR.iterdir()
        if path.is_file()
        and path.suffix.casefold() in {'.ttf', '.ttc', '.otf'}
        and (
            'emoji' in path.stem.casefold()
            or path.stem.casefold().startswith('seguiemj')
        )
    ]
    return tuple(sorted(
        paths,
        key=lambda path: (
            'variablefont' not in path.stem.casefold(),
            'color' in path.stem.casefold(),
            path.name.casefold(),
        ),
    ))


def _meme_text_runs(text: str, font) -> List[Tuple[str, Any, bool]]:
    runs = []
    for cluster, is_emoji in split_graph_text(text):
        is_emoji = is_emoji or '\u20e3' in cluster
        run_font = _get_meme_emoji_font(cluster, font.size) if is_emoji else font
        if is_emoji and run_font is None:
            raise RuntimeError(
                'Не найден emoji-шрифт. Добавьте масштабируемый emoji-шрифт '
                '(например NotoEmoji-VariableFont_wght.ttf) в папку fonts.'
            )
        if runs and runs[-1][1] is run_font:
            runs[-1] = (runs[-1][0] + cluster, run_font, is_emoji)
        else:
            runs.append((cluster, run_font, is_emoji))
    return runs


def _meme_text_layout(draw, text: str, font, stroke_width: int):
    runs = _meme_text_runs(text, font)
    x = 0
    boxes = []
    for run_text, run_font, is_emoji in runs:
        run_stroke = 0 if is_emoji else stroke_width
        box = draw.textbbox((x, 0), run_text, font=run_font, stroke_width=run_stroke)
        boxes.append(box)
        x += draw.textlength(run_text, font=run_font)
    if not boxes:
        return runs, (0, 0, 0, 0)
    return runs, (
        min(box[0] for box in boxes),
        min(box[1] for box in boxes),
        max(x, *(box[2] for box in boxes)),
        max(box[3] for box in boxes),
    )


def _draw_meme_text(
    draw,
    position: Tuple[int, int],
    text: str,
    font,
    fill,
    stroke_width: int = 0,
    stroke_fill=None,
):
    runs, box = _meme_text_layout(draw, text, font, stroke_width)
    line_height = box[3] - box[1]
    x = 0
    for run_text, run_font, is_emoji in runs:
        run_stroke = 0 if is_emoji else stroke_width
        run_box = draw.textbbox(
            (x, 0),
            run_text,
            font=run_font,
            stroke_width=run_stroke,
        )
        run_height = run_box[3] - run_box[1]
        try:
            draw.text(
                (
                    position[0] + x - box[0],
                    position[1] + (line_height - run_height) // 2 - run_box[1],
                ),
                run_text,
                font=run_font,
                fill=fill,
                stroke_width=run_stroke,
                stroke_fill=stroke_fill,
                embedded_color=is_emoji,
            )
        except OSError as exc:
            if not is_emoji or 'SVG hooks have not been set' not in str(exc):
                raise
            draw.text(
                (
                    position[0] + x - box[0],
                    position[1] + (line_height - run_height) // 2 - run_box[1],
                ),
                run_text,
                font=run_font,
                fill=fill,
                stroke_width=run_stroke,
                stroke_fill=stroke_fill,
                embedded_color=False,
            )
        x += draw.textlength(run_text, font=run_font)


def _wrap_meme_line(draw, text: str, font, max_width: int, stroke_width: int) -> List[str]:
    lines = []
    current = ''
    for word in text.split():
        candidate = f'{current} {word}'.strip()
        _, candidate_box = _meme_text_layout(draw, candidate, font, stroke_width)
        if candidate_box[2] - candidate_box[0] <= max_width:
            current = candidate
            continue

        if current:
            lines.append(current)
            current = ''
        _, word_box = _meme_text_layout(draw, word, font, stroke_width)
        if word_box[2] - word_box[0] <= max_width:
            current = word
            continue

        fragment = ''
        for character, _ in split_graph_text(word):
            candidate = fragment + character
            _, candidate_box = _meme_text_layout(draw, candidate, font, stroke_width)
            if fragment and candidate_box[2] - candidate_box[0] > max_width:
                lines.append(fragment)
                fragment = character
            else:
                fragment = candidate
        current = fragment

    if current:
        lines.append(current)
    return lines


def _fit_meme_text(draw, text: str, max_width: int, max_height: int, font_path: Path):
    from PIL import ImageFont

    max_size = max(8, int(min(max_width * 0.15, max_height * 0.48)))
    min_size = max(7, int(max_size * 0.22))
    for size in range(max_size, min_size - 1, -1):
        font = ImageFont.truetype(str(font_path), size)
        stroke_width = max(1, size // 16)
        lines = []
        for paragraph in text.splitlines() or [text]:
            paragraph = paragraph.strip()
            lines.extend(_wrap_meme_line(draw, paragraph, font, max_width, stroke_width) or [''])

        boxes = [
            _meme_text_layout(draw, line or ' ', font, stroke_width)[1]
            for line in lines
        ]
        heights = [box[3] - box[1] for box in boxes]
        line_gap = max(2, size // 8)
        total_height = sum(heights) + line_gap * max(0, len(lines) - 1)
        if total_height <= max_height:
            return font, stroke_width, lines, boxes, heights, line_gap
    raise ValueError('Текст слишком длинный для этой картинки. Сократите его.')


def render_meme_image(
    image_data: bytes,
    top_text: str,
    bottom_text: str,
    *,
    preserve_alpha: bool = False,
    max_dimension: int = MEME_MAX_RENDER_DIMENSION,
) -> bytes:
    from PIL import Image, ImageDraw, ImageFont, ImageOps

    if not MEME_FONT_PATH.is_file():
        raise FileNotFoundError('Не найден шрифт fonts/ofont.ru_Impact.ttf.')
    top_text = top_text.upper()
    bottom_text = bottom_text.upper()
    if len(top_text) + len(bottom_text) > MEME_MAX_TEXT_LENGTH:
        raise ValueError(f'Текст мема должен быть не длиннее {MEME_MAX_TEXT_LENGTH} символов.')

    with Image.open(BytesIO(image_data)) as source:
        if source.width * source.height > MEME_MAX_IMAGE_PIXELS:
            raise ValueError('Изображение слишком большое. Пришлите картинку меньшего размера.')
        source.draft('RGB', (max_dimension, max_dimension))
        image = ImageOps.exif_transpose(source)
        image.thumbnail((max_dimension, max_dimension), Image.Resampling.LANCZOS)
        image = image.convert('RGBA' if preserve_alpha else 'RGB')

    width, height = image.size
    draw = ImageDraw.Draw(image)
    margin_x = max(4, int(width * 0.04))
    max_width = max(1, width - margin_x * 2)
    margin_y = max(4, int(height * 0.025))
    region_height = max(1, int(height * 0.30))
    top_region_start = margin_y
    bottom_region_start = max(margin_y, height - margin_y - region_height)

    def draw_caption(text: str, region_start: int, align_bottom: bool):
        if not text.strip():
            return
        font, stroke_width, lines, boxes, line_heights, line_gap = _fit_meme_text(
            draw, text, max_width, region_height, MEME_FONT_PATH
        )
        total_height = sum(line_heights) + line_gap * max(0, len(lines) - 1)
        y = region_start + region_height - total_height if align_bottom else region_start
        for line, box, line_height in zip(lines, boxes, line_heights):
            line_width = box[2] - box[0]
            x = (width - line_width) // 2
            _draw_meme_text(
                draw,
                (x, y),
                line,
                font,
                'white',
                stroke_width,
                'black',
            )
            y += line_height + line_gap

    draw_caption(top_text, top_region_start, False)
    draw_caption(bottom_text, bottom_region_start, True)

    output = BytesIO()
    image.save(output, format='PNG')
    return output.getvalue()


def render_demotivator_image(image_data: bytes, caption: str) -> bytes:
    from PIL import Image, ImageDraw, ImageFont, ImageOps

    caption = caption.strip()
    if not caption:
        raise ValueError('Добавьте подпись к демотиватору.')
    if len(caption) > MEME_MAX_TEXT_LENGTH:
        raise ValueError(f'Подпись не должна быть длиннее {MEME_MAX_TEXT_LENGTH} символов.')
    if not DEMOTIVATOR_FONT_PATH.is_file():
        raise FileNotFoundError('Не найден шрифт fonts/timesnewromanpsmt.ttf.')

    with Image.open(BytesIO(image_data)) as source:
        if source.width * source.height > MEME_MAX_IMAGE_PIXELS:
            raise ValueError('Изображение слишком большое. Пришлите картинку меньшего размера.')
        image = ImageOps.exif_transpose(source)
        image.thumbnail((MEME_MAX_RENDER_DIMENSION, MEME_MAX_RENDER_DIMENSION), Image.Resampling.LANCZOS)
        image = image.convert('RGB')

    canvas_width = max(400, min(MEME_MAX_RENDER_DIMENSION, round(image.width / 0.68)))
    canvas_height = round(canvas_width * 0.75)
    photo = image.copy()
    photo.thumbnail(
        (round(canvas_width * 0.68), round(canvas_height * 0.64)),
        Image.Resampling.LANCZOS,
    )

    canvas = Image.new('RGB', (canvas_width, canvas_height), 'black')
    photo_x = (canvas_width - photo.width) // 2
    photo_y = round(canvas_height * 0.06)
    canvas.paste(photo, (photo_x, photo_y))
    draw = ImageDraw.Draw(canvas)
    border = max(1, round(canvas_width / 500))
    draw.rectangle(
        (
            photo_x - border,
            photo_y - border,
            photo_x + photo.width - 1 + border,
            photo_y + photo.height - 1 + border,
        ),
        outline='white',
        width=border,
    )

    text_top = photo_y + photo.height + round(canvas_height * 0.045)
    text_bottom = canvas_height - round(canvas_height * 0.06)
    max_text_width = round(canvas_width * 0.88)
    max_text_height = max(1, text_bottom - text_top)
    max_font_size = max(16, round(canvas_width * 0.06))
    min_font_size = max(12, round(canvas_width * 0.025))
    for font_size in range(max_font_size, min_font_size - 1, -1):
        font = ImageFont.truetype(str(DEMOTIVATOR_FONT_PATH), font_size)
        lines = []
        for paragraph in caption.splitlines() or [caption]:
            lines.extend(_wrap_meme_line(draw, paragraph, font, max_text_width, 0) or [''])
        boxes = [
            _meme_text_layout(draw, line or ' ', font, 0)[1]
            for line in lines
        ]
        line_heights = [box[3] - box[1] for box in boxes]
        line_gap = max(2, round(font_size * 0.16))
        total_height = sum(line_heights) + line_gap * max(0, len(lines) - 1)
        if total_height <= max_text_height:
            break
    else:
        raise ValueError('Подпись слишком длинная для демотиватора. Сократите её.')

    y = text_top + (max_text_height - total_height) // 2
    for line, box, line_height in zip(lines, boxes, line_heights):
        line_width = box[2] - box[0]
        x = (canvas_width - line_width) // 2
        _draw_meme_text(draw, (x, y), line, font, 'white')
        y += line_height + line_gap

    output = BytesIO()
    canvas.save(output, format='PNG')
    return output.getvalue()


def render_meme_sticker(image_data: bytes, top_text: str, bottom_text: str) -> bytes:
    from PIL import Image

    rendered_png = render_meme_image(
        image_data,
        top_text,
        bottom_text,
        preserve_alpha=True,
        max_dimension=512,
    )
    with Image.open(BytesIO(rendered_png)) as image:
        image.thumbnail((512, 512), Image.Resampling.LANCZOS)
        if max(image.size) < 512:
            scale = 512 / max(image.size)
            image = image.resize(
                (round(image.width * scale), round(image.height * scale)),
                Image.Resampling.LANCZOS,
            )
        output = BytesIO()
        for quality in (90, 80, 70, 60, 50, 40):
            output.seek(0)
            output.truncate()
            image.save(output, format='WEBP', quality=quality, method=6)
            if output.tell() <= 512 * 1024:
                return output.getvalue()
    raise ValueError('Не удалось подготовить стикер в пределах лимита Telegram (512 КБ).')


def render_mp4_meme(animation_data: bytes, top_text: str, bottom_text: str) -> bytes:
    import math
    import subprocess
    import tempfile
    from PIL import Image
    import imageio_ffmpeg

    if len(animation_data) > MEME_MAX_ANIMATION_BYTES:
        raise ValueError('Видео слишком большое для обработки.')

    with tempfile.TemporaryDirectory(prefix='meme_mp4_') as temp_dir:
        temp_path = Path(temp_dir)
        source_path = temp_path / 'source.mp4'
        rendered_path = temp_path / 'rendered.mp4'
        output_path = temp_path / 'meme.mp4'
        source_path.write_bytes(animation_data)

        reader = imageio_ffmpeg.read_frames(
            str(source_path),
            pix_fmt='rgb24',
            bits_per_pixel=24,
        )
        writer = None
        rendered_frames = 0
        try:
            metadata = next(reader)
            source_width, source_height = metadata['size']
            if (
                source_width < 1
                or source_height < 1
                or source_width * source_height > MEME_MAX_IMAGE_PIXELS
            ):
                raise ValueError('Разрешение MP4 слишком большое для обработки.')

            source_fps = max(1.0, float(metadata.get('fps') or 24))
            target_fps = max(1, min(30, round(source_fps)))
            duration = max(0.01, float(metadata.get('duration') or 3.0))
            frame_count = max(1, math.ceil(duration * target_fps))
            scale = min(1.0, 640 / max(source_width, source_height))
            output_width = max(2, round(source_width * scale / 2) * 2)
            output_height = max(2, round(source_height * scale / 2) * 2)

            blank = Image.new('RGBA', (output_width, output_height), (0, 0, 0, 0))
            blank_data = BytesIO()
            blank.save(blank_data, format='PNG')
            overlay_data = render_meme_image(
                blank_data.getvalue(),
                top_text,
                bottom_text,
                preserve_alpha=True,
                max_dimension=max(output_width, output_height),
            )
            with Image.open(BytesIO(overlay_data)) as overlay_source:
                overlay = overlay_source.convert('RGBA')

            writer = imageio_ffmpeg.write_frames(
                str(rendered_path),
                (output_width, output_height),
                pix_fmt_in='rgb24',
                pix_fmt_out='yuv420p',
                fps=target_fps,
                codec='libx264',
                quality=None,
                bitrate='1000k',
                output_params=['-preset', 'veryfast', '-movflags', '+faststart'],
            )
            writer.send(None)

            current_source_index = 0
            current_frame = next(reader)
            for frame_index in range(frame_count):
                source_index = int(frame_index * source_fps / target_fps)
                try:
                    while current_source_index < source_index:
                        current_frame = next(reader)
                        current_source_index += 1
                except StopIteration:
                    break

                with Image.frombytes(
                    'RGB',
                    (source_width, source_height),
                    current_frame,
                ) as source_frame:
                    frame = source_frame.resize(
                        (output_width, output_height),
                        Image.Resampling.LANCZOS,
                    ).convert('RGBA')
                frame.alpha_composite(overlay)
                writer.send(frame.convert('RGB').tobytes())
                rendered_frames += 1
        except StopIteration:
            pass
        finally:
            reader.close()
            if writer is not None:
                writer.close()

        if rendered_frames == 0:
            raise ValueError('В MP4 не найдено кадров для обработки.')

        mux_result = subprocess.run(
            [
                imageio_ffmpeg.get_ffmpeg_exe(),
                '-hide_banner',
                '-loglevel', 'error',
                '-y',
                '-i', str(rendered_path),
                '-i', str(source_path),
                '-map', '0:v:0',
                '-map', '1:a:0?',
                '-c:v', 'copy',
                '-c:a', 'aac',
                '-t', f'{rendered_frames / target_fps:.3f}',
                '-shortest',
                '-movflags', '+faststart',
                str(output_path),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
            check=False,
        )
        if mux_result.returncode:
            error = mux_result.stderr.decode('utf-8', errors='replace').strip()
            raise RuntimeError(
                f"Не удалось собрать MP4 со звуком: {error[:500]}"
            )

        result = output_path.read_bytes()
        if len(result) > MEME_MAX_ANIMATION_BYTES:
            raise ValueError('Готовое MP4 превышает лимит в 50 МБ.')
        return result


def render_animated_meme(
    animation_data: bytes,
    top_text: str,
    bottom_text: str,
    output_format: str,
    source_format: str = 'webm',
) -> bytes:
    import math
    import tempfile
    from pathlib import Path
    from PIL import Image

    if output_format not in {'gif', 'animated_sticker', 'mp4'}:
        raise ValueError('Неизвестный формат анимированного мема.')
    if len(animation_data) > MEME_MAX_ANIMATION_BYTES:
        raise ValueError('Анимация слишком большая для обработки.')

    if animation_data.startswith(b'\x1f\x8b'):
        source_format = 'tgs'
    if source_format not in {'tgs', 'webm', 'gif', 'mp4'}:
        raise ValueError('Неподдерживаемый формат исходной анимации.')
    if output_format == 'mp4':
        if source_format != 'mp4':
            raise ValueError('MP4-вывод доступен только для MP4-исходника.')
        return render_mp4_meme(animation_data, top_text, bottom_text)

    target_fps = 20 if output_format == 'gif' else 30
    max_frames = target_fps * 3 if output_format == 'animated_sticker' else None
    frames = []

    with tempfile.TemporaryDirectory(prefix='meme_animation_') as temp_dir:
        input_path = Path(temp_dir) / f'source.{source_format}'
        input_path.write_bytes(animation_data)

        if source_format == 'tgs':
            try:
                from rlottie_python import LottieAnimation
            except ImportError as exc:
                raise RuntimeError(
                    'Для обработки TGS установите зависимости из requirements-meme-animation.txt.'
                ) from exc

            animation = LottieAnimation.from_tgs(str(input_path))
            source_fps = max(1.0, float(animation.lottie_animation_get_framerate()))
            source_frame_count = int(animation.lottie_animation_get_totalframe())
            if source_frame_count < 1:
                raise ValueError('В TGS-стикере не найдено кадров для обработки.')
            duration = float(animation.lottie_animation_get_duration())
            frame_count = max(1, math.ceil(duration * target_fps))
            if max_frames is not None:
                frame_count = min(max_frames, frame_count)
            for frame_index in range(frame_count):
                source_index = min(
                    source_frame_count - 1,
                    int(frame_index * source_fps / target_fps),
                )
                frames.append(animation.render_pillow_frame(
                    frame_num=source_index,
                    width=512,
                    height=512,
                ).convert('RGBA'))
            animation = None
        else:
            try:
                import imageio_ffmpeg
            except ImportError as exc:
                raise RuntimeError(
                    'Для обработки WebM установите зависимости из requirements-meme-animation.txt.'
                ) from exc

            reader = imageio_ffmpeg.read_frames(
                str(input_path),
                pix_fmt='rgba',
                bits_per_pixel=32,
            )
            try:
                metadata = next(reader)
                source_width, source_height = metadata['size']
                source_fps = max(1.0, float(metadata.get('fps') or target_fps))
                duration = float(metadata.get('duration') or 3.0)
                frame_count = max(1, math.ceil(duration * target_fps))
                if max_frames is not None:
                    frame_count = min(max_frames, frame_count)
                current_source_index = 0
                current_frame = next(reader)
                for frame_index in range(frame_count):
                    source_index = int(frame_index * source_fps / target_fps)
                    while current_source_index < source_index:
                        current_frame = next(reader)
                        current_source_index += 1
                    frame = Image.frombytes(
                        'RGBA',
                        (source_width, source_height),
                        current_frame,
                    )
                    frame.thumbnail((512, 512), Image.Resampling.LANCZOS)
                    frames.append(frame)
            except StopIteration:
                if not frames:
                    raise ValueError('Не удалось прочитать кадры анимации.')
            finally:
                reader.close()

        if not frames:
            raise ValueError('В анимации не найдено кадров для обработки.')

        canvas_size = (512, 512)
        if output_format == 'gif':
            frame_width, frame_height = frames[0].size
            scale = 512 / max(frame_width, frame_height)
            canvas_size = (
                max(1, round(frame_width * scale)),
                max(1, round(frame_height * scale)),
            )
            frames = [
                frame.resize(canvas_size, Image.Resampling.LANCZOS)
                if frame.size != canvas_size else frame
                for frame in frames
            ]

        blank = Image.new('RGBA', canvas_size, (0, 0, 0, 0))
        blank_data = BytesIO()
        blank.save(blank_data, format='PNG')
        overlay_data = render_meme_image(
            blank_data.getvalue(),
            top_text,
            bottom_text,
            preserve_alpha=True,
            max_dimension=max(canvas_size),
        )
        with Image.open(BytesIO(overlay_data)) as overlay_source:
            overlay = overlay_source.convert('RGBA')

        for frame_index, frame in enumerate(frames):
            frame = frame.convert('RGBA')
            if output_format == 'gif':
                canvas = frame
            else:
                frame.thumbnail((512, 512), Image.Resampling.LANCZOS)
                canvas = Image.new('RGBA', (512, 512), (0, 0, 0, 0))
                canvas.alpha_composite(
                    frame,
                    ((512 - frame.width) // 2, (512 - frame.height) // 2),
                )
            canvas.alpha_composite(overlay)
            frames[frame_index] = canvas

        if output_format == 'gif':
            for max_dimension in (512, 384, 256, 192, 128, 96, 64):
                encoded_frames = []
                for frame in frames:
                    scale = min(1.0, max_dimension / max(frame.size))
                    size = (
                        max(1, round(frame.width * scale)),
                        max(1, round(frame.height * scale)),
                    )
                    encoded_frames.append(
                        frame.resize(size, Image.Resampling.LANCZOS)
                        if frame.size != size else frame
                    )

                output = BytesIO()
                encoded_frames[0].save(
                    output,
                    format='GIF',
                    save_all=True,
                    append_images=encoded_frames[1:],
                    duration=round(1000 / target_fps),
                    loop=0,
                    disposal=2,
                    optimize=True,
                )
                result = output.getvalue()
                if len(result) <= MEME_MAX_ANIMATION_BYTES:
                    return result
            raise ValueError(
                'Готовая GIF-анимация превышает лимит в 50 МБ даже после сжатия.'
            )

        try:
            import imageio_ffmpeg
        except ImportError as exc:
            raise RuntimeError(
                'Для создания анимированного стикера установите зависимости из '
                'requirements-meme-animation.txt.'
            ) from exc

        output_path = Path(temp_dir) / 'meme.webm'
        encoding_profiles = (
            (512, '256k'),
            (512, '160k'),
            (512, '96k'),
            (512, '64k'),
            (384, '96k'),
            (384, '64k'),
            (256, '64k'),
            (256, '48k'),
            (192, '48k'),
            (128, '32k'),
        )
        for dimension, bitrate in encoding_profiles:
            encoded_frames = []
            for frame in frames:
                if dimension < 512:
                    frame = frame.resize((dimension, dimension), Image.Resampling.LANCZOS)
                    frame = frame.resize((512, 512), Image.Resampling.LANCZOS)
                encoded_frames.append(frame)
            writer = imageio_ffmpeg.write_frames(
                str(output_path),
                (512, 512),
                pix_fmt_in='rgba',
                pix_fmt_out='yuva420p',
                fps=target_fps,
                quality=None,
                bitrate=bitrate,
                codec='libvpx-vp9',
                macro_block_size=1,
                ffmpeg_timeout=60,
                output_params=[
                    '-auto-alt-ref', '0',
                    '-metadata:s:v:0', 'alpha_mode=1',
                    '-deadline', 'realtime',
                    '-cpu-used', '8',
                ],
            )
            writer.send(None)
            try:
                for frame in encoded_frames:
                    writer.send(frame.tobytes())
            finally:
                writer.close()
            result = output_path.read_bytes()
            if len(result) <= 256 * 1024:
                return result
        raise ValueError(
            'Анимированный стикер превышает лимит Telegram в 256 КБ даже после сжатия.'
        )


def _meme_session_key(chat_id: int, user_id: int) -> Tuple[int, int]:
    return chat_id, user_id


def _split_meme_text(text: str) -> Tuple[str, str]:
    if '.' not in text:
        return text.strip(), ''
    top_text, bottom_text = text.split('.', 1)
    return top_text.strip(), bottom_text.strip()


MEME_COMMAND_ALIASES = frozenset({'мем', 'мемер', 'meme', 'memer'})


def _parse_meme_caption(caption: str, chat_id: int) -> Optional[Tuple[str, str]]:
    command, args = match_command(strip_command_prefix(caption, chat_id))
    if command not in MEME_COMMAND_ALIASES:
        return None
    return command, args or ''


def _get_message_image(message: Optional[Message]):
    if not message:
        return None
    if message.photo:
        return message.photo[-1]
    document = message.document
    if document and (document.mime_type or '').startswith('image/'):
        return document
    return None


def _get_message_animation(message: Optional[Message]) -> Optional[Tuple[Any, str]]:
    if not message:
        return None

    media_items = (
        (getattr(message, 'animation', None), 'mp4'),
        (getattr(message, 'video', None), 'mp4'),
        (message.document, None),
    )
    for media, default_format in media_items:
        if not media:
            continue
        filename = str(getattr(media, 'file_name', '') or '')
        suffix = Path(filename).suffix.casefold()
        mime_type = str(getattr(media, 'mime_type', '') or '').casefold()
        if suffix == '.gif' or mime_type == 'image/gif':
            return media, 'gif'
        if suffix == '.mp4' or mime_type == 'video/mp4':
            return media, 'mp4'
        if suffix == '.webm' or mime_type == 'video/webm':
            return media, 'webm'
        if default_format and (
            mime_type.startswith('video/') or not mime_type
        ):
            return media, default_format
    return None


async def _ask_for_meme_photo(
    message: Message,
    user_id: int,
    top_text: str = '',
    bottom_text: str = '',
    *,
    style: str = 'classic',
    edit_message: bool = False,
):
    if style == 'demotivator':
        prompt_text = (
            '🖼️ <b>Демотиватор — шаг 1 из 2</b>\n\n'
            'Ответьте на это сообщение обычной фотографией или изображением.'
        )
    else:
        prompt_text = (
            '🖼️ <b>Шаг 1 из 2 — изображение</b>\n\n'
            'Ответьте на это сообщение изображением, GIF, MP4-видео или стикером для мема.'
        )
    if top_text or bottom_text:
        prompt_text += (
            '\n\n✍️ Текст сохранён — после получения картинки сразу создам мем. '
            'Для анимации предложу выбрать формат отправки.'
        )
    else:
        prompt_text += (
            '\n\nПосле картинки попрошу вас добавить подпись.'
            if style == 'demotivator'
            else '\n\nПосле картинки попрошу вас добавить текст.'
        )
    if edit_message:
        prompt = await message.edit_text(
            prompt_text,
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[]),
        )
    else:
        prompt = await message.answer(prompt_text)
    meme_sessions[_meme_session_key(message.chat.id, user_id)] = {
        'step': 'await_photo',
        'created_at': time.time(),
        'prompt_message_id': prompt.message_id,
        'top_text': top_text,
        'bottom_text': bottom_text,
        'style': style,
    }


async def _ask_for_meme_text(
    message: Message,
    user_id: int,
    file_id: str,
    *,
    source_animated: bool = False,
    source_format: str = 'webm',
    style: str = 'classic',
    source_type: Optional[str] = None,
    edit_message: bool = False,
):
    source_type = source_type or (
        'sticker' if message.sticker else 'animation' if source_animated else 'photo'
    )
    accepted_text = (
        'Анимация принята' if source_type == 'animation'
        else 'Стикер принят' if source_type == 'sticker'
        else 'Картинка принята'
    )
    text_instructions = (
        '✍️ <b>Шаг 2 из 2 — подпись</b>\n'
        'Отправьте текст, который появится под рамкой изображения.'
        if style == 'demotivator'
        else
        '✍️ <b>Шаг 2 из 2 — текст</b>\n'
        'Отправьте надписи одним сообщением: <code>сверху.снизу</code>.\n'
        'Если нужна только нижняя надпись, начните с точки: <code>.текст</code>.'
    )
    prompt_text = f'✅ <b>{accepted_text}</b>\n\n{text_instructions}'
    if edit_message:
        prompt = await message.edit_text(
            prompt_text,
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[]),
        )
    else:
        prompt = await message.answer(prompt_text)
    meme_sessions[_meme_session_key(message.chat.id, user_id)] = {
        'step': 'await_text',
        'created_at': time.time(),
        'file_id': file_id,
        'source_type': source_type,
        'source_animated': source_animated or bool(
            message.sticker and (message.sticker.is_animated or message.sticker.is_video)
        ),
        'source_format': (
            'tgs' if message.sticker and message.sticker.is_animated
            else 'webm' if message.sticker
            else source_format
        ),
        'prompt_message_id': prompt.message_id,
        'style': style,
    }


async def _ask_for_meme_output_mode(
    message: Message,
    user_id: int,
    file_id: str,
    top_text: str,
    bottom_text: str,
    *,
    source_animated: bool = False,
    source_format: str = 'webm',
):
    if source_animated:
        if source_format == 'gif':
            prompt_text = '🪄 <b>Результат будет отправлен в формате GIF.</b>'
            buttons = [
                InlineKeyboardButton(
                    text='🎞️ GIF',
                    callback_data=f'meme_gif_{user_id}',
                ),
            ]
        elif source_format == 'mp4':
            prompt_text = (
                '🪄 <b>Выберите формат результата:</b>\n'
                'MP4 сохранит исходный звук, GIF будет без звука.'
            )
            buttons = [
                InlineKeyboardButton(
                    text='🎞️ GIF',
                    callback_data=f'meme_gif_{user_id}',
                ),
                InlineKeyboardButton(
                    text='🎬 MP4',
                    callback_data=f'meme_mp4_{user_id}',
                ),
            ]
        else:
            prompt_text = (
                '🪄 <b>Как отправить результат?</b>\n'
                'Выберите формат анимированного мема:'
            )
            buttons = [
                InlineKeyboardButton(
                    text='🎞️ GIF',
                    callback_data=f'meme_gif_{user_id}',
                ),
                InlineKeyboardButton(
                    text='✨ Стикер',
                    callback_data=f'meme_animated_{user_id}',
                ),
            ]
    else:
        prompt_text = (
            '🪄 <b>Как отправить результат?</b>\n'
            'Выберите формат для вашего стикера:'
        )
        buttons = [
            InlineKeyboardButton(
                text='🖼️ Фото с текстом',
                callback_data=f'meme_photo_{user_id}',
            ),
            InlineKeyboardButton(
                text='✨ Стикер',
                callback_data=f'meme_sticker_{user_id}',
            ),
        ]
    prompt = await message.answer(
        prompt_text,
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[buttons]),
    )
    meme_sessions[_meme_session_key(message.chat.id, user_id)] = {
        'step': 'await_output_mode',
        'created_at': time.time(),
        'file_id': file_id,
        'top_text': top_text,
        'bottom_text': bottom_text,
        'source_type': 'animation' if source_animated else 'sticker',
        'source_animated': source_animated,
        'source_format': source_format,
        'prompt_message_id': prompt.message_id,
    }


async def _create_meme_for_message(
    message: Message,
    file_id: str,
    top_text: str,
    bottom_text: str,
    *,
    output_as_sticker: bool = False,
    output_as_animation: Optional[str] = None,
    source_format: str = 'webm',
    demotivator_caption: Optional[str] = None,
) -> bool:
    try:
        downloaded = await bot.download(file_id)
        image_data = downloaded.getvalue() if hasattr(downloaded, 'getvalue') else downloaded.read()
        if output_as_animation:
            if len(image_data) > MEME_MAX_ANIMATION_BYTES:
                raise ValueError('Анимация слишком большая. Максимальный размер — 50 МБ.')
            async with MEME_RENDER_SEMAPHORE:
                meme_data = await asyncio.to_thread(
                    render_animated_meme,
                    image_data,
                    top_text,
                    bottom_text,
                    output_as_animation,
                    source_format,
                )
            if output_as_animation == 'gif':
                await message.answer_animation(
                    BufferedInputFile(meme_data, filename='meme.gif'),
                    caption='✨ <b>Готово!</b> Ваш анимированный мем.',
                )
            elif output_as_animation == 'mp4':
                await message.answer_video(
                    BufferedInputFile(meme_data, filename='meme.mp4'),
                    caption='✨ <b>Готово!</b> Ваше видео с надписью и исходным звуком, если он был.',
                )
            else:
                sticker_message = await message.answer_sticker(
                    BufferedInputFile(meme_data, filename='meme.webm'),
                )
                await sticker_message.reply(
                    '✨ <b>Готово! Анимированный стикер с надписью.</b>'
                )
        elif len(image_data) > MEME_MAX_IMAGE_BYTES:
            raise ValueError('Изображение слишком большое. Максимальный размер — 20 МБ.')
        elif demotivator_caption is not None:
            async with MEME_RENDER_SEMAPHORE:
                meme_data = await asyncio.to_thread(
                    render_demotivator_image,
                    image_data,
                    demotivator_caption,
                )
            await message.answer_photo(
                BufferedInputFile(meme_data, filename='demotivator.png'),
                caption='🖼️ <b>Демотиватор готов.</b>',
            )
        elif output_as_sticker:
            async with MEME_RENDER_SEMAPHORE:
                meme_data = await asyncio.to_thread(
                    render_meme_sticker,
                    image_data,
                    top_text,
                    bottom_text,
                )
            sticker_message = await message.answer_sticker(
                BufferedInputFile(meme_data, filename='meme.webp'),
            )
            await sticker_message.reply('✨ <b>Готово! Новый стикер с надписью.</b>')
        else:
            async with MEME_RENDER_SEMAPHORE:
                meme_data = await asyncio.to_thread(
                    render_meme_image,
                    image_data,
                    top_text,
                    bottom_text,
                )
            await message.answer_photo(
                BufferedInputFile(meme_data, filename='meme.png'),
                caption='✨ <b>Готово!</b> Ваш мем.',
            )
        return True
    except FileNotFoundError:
        logger.exception('Не найден шрифт для создания мема')
        await message.answer(
            (
                '⚠️ <b>Не найден шрифт демотиватора</b>\n'
                'Проверьте файл <code>fonts/timesnewromanpsmt.ttf</code>.'
                if demotivator_caption is not None
                else
                '⚠️ <b>Не найден шрифт Impact</b>\n'
                'Проверьте файл <code>fonts/ofont.ru_Impact.ttf</code>.'
            )
        )
    except ImportError:
        logger.exception('Pillow недоступен для создания мема')
        await message.answer('⚠️ <b>Создание мема недоступно</b>\nНа сервере не установлен Pillow.')
    except (OSError, ValueError, RuntimeError, TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning('Не удалось создать мем: %s', exc, exc_info=True)
        await message.answer(f'⚠️ <b>Не удалось создать мем</b>\n{html.escape(str(exc))}')
    except Exception:
        logger.exception('Непредвиденная ошибка при создании мема')
        await message.answer(
            '⚠️ <b>При создании мема произошла ошибка</b>\n'
            'Попробуйте другое изображение или сократите текст.'
        )
    return False


def _get_meme_session(chat_id: int, user_id: int) -> Optional[dict]:
    now = time.time()
    expired = [
        key for key, session in meme_sessions.items()
        if now - session.get('created_at', 0) > MEME_SESSION_TTL
    ]
    for key in expired:
        meme_sessions.pop(key, None)
    return meme_sessions.get(_meme_session_key(chat_id, user_id))


async def _show_meme_menu(
    message: Message,
    user_id: int,
    *,
    selected_media: Optional[dict] = None,
):
    style_buttons = [
        InlineKeyboardButton(text='🖼️ Мем с текстом', callback_data=f'meme_classic_{user_id}'),
    ]
    if not selected_media or not selected_media.get('source_animated'):
        style_buttons.append(
            InlineKeyboardButton(text='🖼️ Демотиватор', callback_data=f'meme_demotivator_{user_id}')
        )
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        style_buttons,
        [InlineKeyboardButton(text='✖️ Закрыть', callback_data=f'meme_close_{user_id}')],
    ])
    menu = await message.answer(
        '🎨 <b>МЕМ-МЕНЮ</b>\n'
        'Выберите стиль. Для мема с текстом доступны фото, GIF, MP4 и стикеры; '
        'демотиватор создаётся из фото или изображения.',
        reply_markup=keyboard,
    )
    if selected_media:
        meme_sessions[_meme_session_key(message.chat.id, user_id)] = {
            'step': 'await_style',
            'created_at': time.time(),
            'menu_message_id': menu.message_id,
            **selected_media,
        }


async def cmd_meme(msg: Message, args: str = '', cmd_name: str = 'мем'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    owner_id = msg.from_user.id
    key = _meme_session_key(msg.chat.id, owner_id)
    meme_sessions.pop(key, None)
    save_activity(msg.chat.id, owner_id, 'commands')

    top_text, bottom_text = _split_meme_text(args)
    reply_animation = _get_message_animation(msg.reply_to_message)
    if reply_animation:
        media, source_format = reply_animation
        if media.file_size and media.file_size > MEME_MAX_ANIMATION_BYTES:
            await msg.answer('⚠️ <b>Анимация слишком большая</b>\nМаксимальный размер — 50 МБ.')
            return
        if top_text or bottom_text:
            await _ask_for_meme_output_mode(
                msg,
                owner_id,
                media.file_id,
                top_text,
                bottom_text,
                source_animated=True,
                source_format=source_format,
            )
        else:
            await _show_meme_menu(
                msg,
                owner_id,
                selected_media={
                    'file_id': media.file_id,
                    'source_type': 'animation',
                    'source_animated': True,
                    'source_format': source_format,
                },
            )
        return

    image_file = _get_message_image(msg.reply_to_message)
    if image_file:
        if top_text or bottom_text:
            await _create_meme_for_message(msg, image_file.file_id, top_text, bottom_text)
        else:
            await _show_meme_menu(
                msg,
                owner_id,
                selected_media={
                    'file_id': image_file.file_id,
                    'source_type': 'photo',
                    'source_animated': False,
                    'source_format': 'webp',
                },
            )
        return
    reply_sticker = msg.reply_to_message.sticker if msg.reply_to_message else None
    if reply_sticker:
        if top_text or bottom_text:
            await _ask_for_meme_output_mode(
                msg,
                owner_id,
                reply_sticker.file_id,
                top_text,
                bottom_text,
                source_animated=bool(reply_sticker.is_animated or reply_sticker.is_video),
                source_format='tgs' if reply_sticker.is_animated else 'webm',
            )
        else:
            is_animated = bool(reply_sticker.is_animated or reply_sticker.is_video)
            await _show_meme_menu(
                msg,
                owner_id,
                selected_media={
                    'file_id': reply_sticker.file_id,
                    'source_type': 'sticker',
                    'source_animated': is_animated,
                    'source_format': 'tgs' if reply_sticker.is_animated else 'webm',
                },
            )
        return
    if top_text or bottom_text:
        await _ask_for_meme_photo(msg, owner_id, top_text, bottom_text)
        return

    await _show_meme_menu(msg, owner_id)


@router.callback_query(F.data.startswith('meme_'))
async def meme_callback(call: CallbackQuery):
    if not call.from_user or not call.message:
        await call.answer()
        return
    try:
        action, owner_id_text = call.data.rsplit('_', 1)
        owner_id = int(owner_id_text)
    except (AttributeError, TypeError, ValueError):
        await call.answer('Эта кнопка больше не действует.', show_alert=True)
        return

    if call.from_user.id != owner_id:
        await call.answer('Эту кнопку нажал другой пользователь.', show_alert=True)
        return

    key = _meme_session_key(call.message.chat.id, owner_id)
    if action == 'meme_close':
        meme_sessions.pop(key, None)
        await call.message.edit_text(
            '✖️ <b>МЕМ-МАСТЕРСКАЯ ЗАКРЫТА</b>\n'
            'Если передумаете, снова отправьте <code>!мем</code>.',
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[]),
        )
        await call.answer()
        return

    if action in {'meme_photo', 'meme_sticker', 'meme_gif', 'meme_animated', 'meme_mp4'}:
        if not check_access(owner_id, call.message.chat.id, 'мем', 0):
            await call.answer('Создание мемов отключено в этом чате.', show_alert=True)
            return
        session = _get_meme_session(call.message.chat.id, owner_id)
        if not session or session.get('step') != 'await_output_mode':
            await call.answer('Этот выбор уже устарел. Отправьте !мем ещё раз.', show_alert=True)
            return

        is_animated_source = bool(session.get('source_animated'))
        source_format = session.get('source_format', 'webm')
        allowed_animation_actions = {
            'gif': {'meme_gif'},
            'mp4': {'meme_gif', 'meme_mp4'},
        }.get(source_format, {'meme_gif', 'meme_animated'})
        if (
            is_animated_source
            and action not in allowed_animation_actions
            or not is_animated_source
            and action not in {'meme_photo', 'meme_sticker'}
        ):
            await call.answer('Этот формат не подходит для исходного файла.', show_alert=True)
            return
        await call.message.delete()
        await call.answer()
        waiting_message = await call.message.answer(
            '⏳ <b>Создаю мем…</b>\nПожалуйста, подождите немного.'
        )
        try:
            await _create_meme_for_message(
                waiting_message,
                session['file_id'],
                session['top_text'],
                session['bottom_text'],
                output_as_sticker=action == 'meme_sticker',
                output_as_animation=(
                    'gif' if action == 'meme_gif'
                    else 'animated_sticker' if action == 'meme_animated'
                    else 'mp4' if action == 'meme_mp4'
                    else None
                ),
                source_format=session.get('source_format', 'webm'),
            )
        finally:
            try:
                await waiting_message.delete()
            except TelegramAPIError as exc:
                logger.warning('Не удалось удалить сообщение ожидания мема: %s', exc)

        meme_sessions.pop(key, None)
        return

    if action not in {'meme_create', 'meme_classic', 'meme_demotivator'}:
        await call.answer('Неизвестное действие.', show_alert=True)
        return
    if not check_access(owner_id, call.message.chat.id, 'мем', 0):
        await call.answer('Создание мемов отключено в этом чате.', show_alert=True)
        return

    session = _get_meme_session(call.message.chat.id, owner_id)
    if session and session.get('step') == 'await_style':
        style = 'demotivator' if action == 'meme_demotivator' else 'classic'
        if style == 'demotivator' and session.get('source_animated'):
            await call.answer('Демотиватор поддерживает только статичные изображения.', show_alert=True)
            return
        await _ask_for_meme_text(
            call.message,
            owner_id,
            session['file_id'],
            source_animated=bool(session.get('source_animated')),
            source_format=session.get('source_format', 'webm'),
            style=style,
            source_type=session.get('source_type'),
            edit_message=True,
        )
        await call.answer()
        return
    if session:
        await call.answer('У вас уже есть активный запрос на создание мема.', show_alert=True)
        return

    style = 'demotivator' if action == 'meme_demotivator' else 'classic'
    await _ask_for_meme_photo(
        call.message,
        owner_id,
        style=style,
        edit_message=True,
    )
    await call.answer()


async def _handle_meme_animation_message(
    msg: Message,
    media: Any,
    source_format: str,
):
    if media.file_size and media.file_size > MEME_MAX_ANIMATION_BYTES:
        await msg.answer('⚠️ <b>Анимация слишком большая</b>\nМаксимальный размер — 50 МБ.')
        return

    key = _meme_session_key(msg.chat.id, msg.from_user.id)
    meme_command = _parse_meme_caption(msg.caption or '', msg.chat.id)
    if meme_command:
        command_name, args = meme_command
        if not check_access(msg.from_user.id, msg.chat.id, command_name, 0):
            await msg.answer('⚠️ <b>Создание мемов отключено</b> в этом чате.')
            return
        save_activity(msg.chat.id, msg.from_user.id, 'commands')
        meme_sessions.pop(key, None)
        top_text, bottom_text = _split_meme_text(args)
        if top_text or bottom_text:
            await _ask_for_meme_output_mode(
                msg,
                msg.from_user.id,
                media.file_id,
                top_text,
                bottom_text,
                source_animated=True,
                source_format=source_format,
            )
        else:
            await _ask_for_meme_text(
                msg,
                msg.from_user.id,
                media.file_id,
                source_animated=True,
                source_format=source_format,
            )
        return

    session = _get_meme_session(msg.chat.id, msg.from_user.id)
    if not session or session.get('step') != 'await_photo':
        return
    if (
        not msg.reply_to_message
        or msg.reply_to_message.message_id != session.get('prompt_message_id')
    ):
        await msg.answer(
            '↩️ <b>Нужно отправить файл ответом</b>\n'
            'Ответьте именно на сообщение бота с просьбой о картинке.'
        )
        return

    if session.get('style') == 'demotivator':
        await msg.answer('Для демотиватора нужна статичная фотография или изображение, не анимация.')
        return

    top_text = session.get('top_text', '')
    bottom_text = session.get('bottom_text', '')
    if top_text or bottom_text:
        await _ask_for_meme_output_mode(
            msg,
            msg.from_user.id,
            media.file_id,
            top_text,
            bottom_text,
            source_animated=True,
            source_format=source_format,
        )
    else:
        await _ask_for_meme_text(
            msg,
            msg.from_user.id,
            media.file_id,
            source_animated=True,
            source_format=source_format,
        )


@router.message(F.photo | F.document | F.video | F.animation)
async def meme_photo_handler(msg: Message):
    if not msg.from_user or msg.from_user.is_bot:
        return
    animation = _get_message_animation(msg)
    if animation:
        media, source_format = animation
        await _handle_meme_animation_message(msg, media, source_format)
        return

    image_file = _get_message_image(msg)
    if not image_file:
        return
    if image_file.file_size and image_file.file_size > MEME_MAX_IMAGE_BYTES:
        await msg.answer('⚠️ <b>Изображение слишком большое</b>\nМаксимальный размер — 20 МБ.')
        return

    key = _meme_session_key(msg.chat.id, msg.from_user.id)
    meme_command = _parse_meme_caption(msg.caption or '', msg.chat.id)
    if meme_command:
        command_name, args = meme_command
        if not check_access(msg.from_user.id, msg.chat.id, command_name, 0):
            await msg.answer('⚠️ <b>Создание мемов отключено</b> в этом чате.')
            return
        save_activity(msg.chat.id, msg.from_user.id, 'commands')
        meme_sessions.pop(key, None)
        top_text, bottom_text = _split_meme_text(args)
        if top_text or bottom_text:
            await _create_meme_for_message(msg, image_file.file_id, top_text, bottom_text)
        else:
            await _ask_for_meme_text(msg, msg.from_user.id, image_file.file_id)
        return

    session = _get_meme_session(msg.chat.id, msg.from_user.id)
    if not session or session.get('step') != 'await_photo':
        return
    if (
        not msg.reply_to_message
        or msg.reply_to_message.message_id != session.get('prompt_message_id')
    ):
        await msg.answer(
            '↩️ <b>Нужно отправить изображение ответом</b>\n'
            'Ответьте именно на сообщение бота с просьбой о картинке.'
        )
        return

    if session.get('style') == 'demotivator':
        if msg.caption and msg.caption.strip():
            if await _create_meme_for_message(
                msg,
                image_file.file_id,
                '',
                '',
                demotivator_caption=msg.caption.strip(),
            ):
                meme_sessions.pop(key, None)
            return
        await _ask_for_meme_text(
            msg,
            msg.from_user.id,
            image_file.file_id,
            style='demotivator',
        )
        return

    top_text = session.get('top_text', '')
    bottom_text = session.get('bottom_text', '')
    if top_text or bottom_text:
        if await _create_meme_for_message(msg, image_file.file_id, top_text, bottom_text):
            meme_sessions.pop(key, None)
        return
    await _ask_for_meme_text(msg, msg.from_user.id, image_file.file_id)


async def handle_meme_text(msg: Message) -> bool:
    if not msg.from_user or not msg.text:
        return False
    session = _get_meme_session(msg.chat.id, msg.from_user.id)
    if not session or session.get('step') != 'await_text':
        return False

    text = msg.text.strip()
    if not text:
        return False

    prefix = get_command_prefix(msg.chat.id)
    if prefix and text.startswith(prefix):
        return False
    if not prefix and match_command(strip_command_prefix(text, msg.chat.id))[0]:
        return False

    top_text, bottom_text = _split_meme_text(text)
    if not top_text and not bottom_text:
        await msg.answer('Напишите текст для мема.')
        return True

    if session.get('style') == 'demotivator':
        if await _create_meme_for_message(
            msg,
            session['file_id'],
            '',
            '',
            demotivator_caption=text,
        ):
            meme_sessions.pop(_meme_session_key(msg.chat.id, msg.from_user.id), None)
        return True

    if session.get('source_type') == 'sticker' or session.get('source_animated'):
        await _ask_for_meme_output_mode(
            msg,
            msg.from_user.id,
            session['file_id'],
            top_text,
            bottom_text,
            source_animated=session.get('source_animated', False),
            source_format=session.get('source_format', 'webm'),
        )
        return True

    if await _create_meme_for_message(msg, session['file_id'], top_text, bottom_text):
        meme_sessions.pop(_meme_session_key(msg.chat.id, msg.from_user.id), None)
    return True


@router.message(F.sticker)
async def sticker_reputation_handler(msg: Message):
    if not msg.from_user or msg.from_user.is_bot:
        return

    session = _get_meme_session(msg.chat.id, msg.from_user.id)
    if (
        session
        and session.get('step') == 'await_photo'
        and msg.reply_to_message
        and msg.reply_to_message.message_id == session.get('prompt_message_id')
    ):
        sticker = msg.sticker
        if session.get('style') == 'demotivator':
            await msg.answer('Для демотиватора нужна статичная фотография или изображение, не стикер.')
            return
        if sticker.file_size and sticker.file_size > MEME_MAX_IMAGE_BYTES:
            await msg.answer('⚠️ <b>Стикер слишком большой</b>\nМаксимальный размер — 20 МБ.')
            return
        top_text = session.get('top_text', '')
        bottom_text = session.get('bottom_text', '')
        if top_text or bottom_text:
            await _ask_for_meme_output_mode(
                msg,
                msg.from_user.id,
                sticker.file_id,
                top_text,
                bottom_text,
                source_animated=bool(sticker.is_animated or sticker.is_video),
                source_format='tgs' if sticker.is_animated else 'webm',
            )
        else:
            await _ask_for_meme_text(msg, msg.from_user.id, sticker.file_id)
        return

    if not msg.reply_to_message:
        return
    receiver = msg.reply_to_message.from_user
    if not receiver or receiver.is_bot or receiver.id == msg.from_user.id:
        return

    emoji = msg.sticker.emoji or ''
    if is_reputation_removal_message(emoji):
        await give_reputation(msg, remove=True)
    elif is_reputation_message(emoji):
        await give_reputation(msg)


@router.message(F.text)
async def main_text_handler(msg: Message):
    if not msg.text or not msg.from_user or msg.from_user.is_bot:
        return
    if await handle_meme_text(msg):
        return
    if await handle_activity_graph_wizard_text(msg):
        return

    chat_id = msg.chat.id
    main_chat = is_main_chat(chat_id, msg.message_thread_id)

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
            unknown_command = cleaned.split(maxsplit=1)[0] if cleaned.split(maxsplit=1) else text
            await report_command_error(
                msg,
                unknown_command,
                'Неизвестная команда',
                f"Команда <code>{html.escape(unknown_command, quote=False)}</code> не найдена или недоступна в этом чате.",
                '!помощь',
            )
            return

    if msg.reply_to_message and msg.reply_to_message.from_user:
        if not msg.reply_to_message.from_user.is_bot and msg.from_user.id != msg.reply_to_message.from_user.id:
            if is_reputation_removal_message(text):
                await give_reputation(msg, remove=True)
                return
            if is_reputation_message(text):
                await give_reputation(msg)
                return

    phrase_text = text.casefold()
    matching_phrases = get_matching_phrases(chat_id, phrase_text)
    if matching_phrases:
        phrase = random.choice(matching_phrases)
        phrase['uses'] = phrase.get('uses', 0) + 1
        storage.mark_dirty()
        await storage.save()
        await msg.answer(str(phrase.get('response', '')), parse_mode=None)
        return

    if await rp_handler(msg):
        return

    currency_query = parse_currency_amount(text)
    if currency_query:
        await answer_currency_amount(msg, *currency_query)
        return


phrase_match_cache = SimpleCache(max_size=500, ttl=3600)


def invalidate_phrase_match_cache(chat_id: int):
    phrase_match_cache.invalidate(str(chat_id))


def get_matching_phrases(chat_id: int, phrase_text: str) -> list:
    chat_key = str(chat_id)
    phrase_text = phrase_text.casefold()
    phrases = storage.get_chat(chat_id, 'phrases')
    cached = phrase_match_cache.get(chat_key)
    if cached is None or cached[0] is not phrases:
        exact_index: Dict[str, list] = {}
        anywhere_nodes = [{'next': {}, 'fail': 0, 'output': []}]
        if isinstance(phrases, list):
            for phrase_index, phrase in enumerate(phrases):
                if not isinstance(phrase, dict):
                    continue
                trigger = phrase.get('trigger')
                if not isinstance(trigger, str) or not trigger:
                    continue
                normalized_trigger = trigger.casefold()
                if phrase.get('anywhere'):
                    state = 0
                    for character in normalized_trigger:
                        next_state = anywhere_nodes[state]['next'].get(character)
                        if next_state is None:
                            next_state = len(anywhere_nodes)
                            anywhere_nodes[state]['next'][character] = next_state
                            anywhere_nodes.append({'next': {}, 'fail': 0, 'output': []})
                        state = next_state
                    anywhere_nodes[state]['output'].append((phrase_index, phrase))
                else:
                    exact_index.setdefault(normalized_trigger, []).append(phrase)

        pending_states = deque(anywhere_nodes[0]['next'].values())
        while pending_states:
            state = pending_states.popleft()
            for character, next_state in anywhere_nodes[state]['next'].items():
                pending_states.append(next_state)
                fallback = anywhere_nodes[state]['fail']
                while fallback and character not in anywhere_nodes[fallback]['next']:
                    fallback = anywhere_nodes[fallback]['fail']
                anywhere_nodes[next_state]['fail'] = anywhere_nodes[fallback]['next'].get(character, 0)
                anywhere_nodes[next_state]['output'].extend(
                    anywhere_nodes[anywhere_nodes[next_state]['fail']]['output']
                )

        cached = (phrases, exact_index, anywhere_nodes)
        phrase_match_cache.set(chat_key, cached)

    matches = list(cached[1].get(phrase_text, ()))
    anywhere_matches = {}
    state = 0
    for character in phrase_text:
        while state and character not in cached[2][state]['next']:
            state = cached[2][state]['fail']
        state = cached[2][state]['next'].get(character, 0)
        anywhere_matches.update(cached[2][state]['output'])
    matches.extend(anywhere_matches[index] for index in sorted(anywhere_matches))
    return matches



@superadmin_only
async def cmd_ram(msg: Message, args: str = '', cmd_name: str = 'ram'):
    if not is_bot_superadmin(msg.from_user.id):
        return await msg.answer("❌ Эта команда доступна только главным администраторам бота.")

    rss_mb = _get_rss_mb()

    users = storage.data.get('users', {})
    users_in_ram = sum(
        len(chat_users)
        for chat_users in users.values()
        if isinstance(chat_users, dict)
    )
    lines = [
        f"RSS: <b>{rss_mb:.1f} МБ</b>" if rss_mb is not None else "RSS: недоступен",
        f"Загружено чатов: {len(storage._loaded_user_chats)}",
        f"Пользователей в RAM: {users_in_ram}",
        f"_dirty_users: <b>{len(storage._dirty_users)}</b>",
        f"user_cache: {len(user_cache._cache)} / mention_cache: {len(mention_cache._cache)}",
        f"игры: {len(active_games)} / сапёр: {len(minesweeper_games)} / мемы: {len(meme_sessions)}",
        f"визарды: др {len(birthday_wizards)}, график {len(activity_graph_wizards)}, "
        f"GC objects: {len(gc.get_objects())}",
    ]
    if tracemalloc.is_tracing():
        snapshot = tracemalloc.take_snapshot()
        lines.extend(
            f"<code>{html.escape(str(stat), quote=False)}</code>"
            for stat in snapshot.statistics('lineno')[:8]
        )
    await msg.answer("\n".join(lines))


COMMAND_HANDLERS = {
    'cmd_help': lambda msg, args, cmd_name: cmd_help(msg),
    'cmd_ram': lambda msg, args, cmd_name: cmd_ram(msg, args, cmd_name),
    'cmd_logs': lambda msg, args, cmd_name: cmd_logs(msg, args),
    'cmd_backups': lambda msg, args, cmd_name: cmd_backups(msg),
    'cmd_status': lambda msg, args, cmd_name: cmd_status(msg),
    'cmd_save_now': lambda msg, args, cmd_name: cmd_save_now(msg),
    'cmd_bot_rights': lambda msg, args, cmd_name: cmd_bot_rights(msg, args),
    'cmd_reset_caches': lambda msg, args, cmd_name: cmd_reset_caches(msg),
    'cmd_export_user': lambda msg, args, cmd_name: cmd_export_user(msg, args),
    'cmd_database_info': lambda msg, args, cmd_name: cmd_database_info(msg),
    'cmd_gc': lambda msg, args, cmd_name: cmd_gc(msg),
    'cmd_broadcast': lambda msg, args, cmd_name: cmd_broadcast(msg, args),
    'cmd_leave_chat': lambda msg, args, cmd_name: cmd_leave_chat(msg, args),
    'cmd_block_chat': lambda msg, args, cmd_name: cmd_block_chat(msg, args),
    'cmd_unblock_chat': lambda msg, args, cmd_name: cmd_block_chat(msg, args, unblock=True),
    'cmd_restart': lambda msg, args, cmd_name: cmd_restart(msg),
    'cmd_superadmin_audit': lambda msg, args, cmd_name: cmd_superadmin_audit(msg),
    'cmd_prefix': lambda msg, args, cmd_name: cmd_prefix(msg, args),
    'cmd_rp_list': lambda msg, args, cmd_name: cmd_rp_list(msg),
    'who_am_i': lambda msg, args, cmd_name: who_am_i(msg, cmd_name),
    'who_are_you': lambda msg, args, cmd_name: who_are_you(msg, args, cmd_name),
    'who_admin': lambda msg, args, cmd_name: who_admin(msg),
    'cmd_rank': lambda msg, args, cmd_name: cmd_rank(msg),
    'cmd_ranks_list': lambda msg, args, cmd_name: cmd_ranks_list(msg),
    'cmd_rank_rename': lambda msg, args, cmd_name: cmd_rank_rename(msg, cmd_name, args),
    'cmd_id': lambda msg, args, cmd_name: cmd_id(msg, cmd_name),
    'cmd_birthday': lambda msg, args, cmd_name: cmd_birthday(msg),
    'cmd_top': lambda msg, args, cmd_name: cmd_top(msg, args, cmd_name),
    'cmd_chat_stats': lambda msg, args, cmd_name: cmd_chat_stats(msg, cmd_name),
    'cmd_stats': lambda msg, args, cmd_name: cmd_stats(msg, args, cmd_name),
    'cmd_mute': lambda msg, args, cmd_name: cmd_mute(msg, cmd_name),
    'cmd_unmute': lambda msg, args, cmd_name: cmd_unmute(msg, cmd_name),
    'cmd_ban': lambda msg, args, cmd_name: cmd_ban(msg, cmd_name),
    'cmd_unban': lambda msg, args, cmd_name: cmd_unban(msg, cmd_name),
    'cmd_kick': lambda msg, args, cmd_name: cmd_kick(msg, cmd_name),
    'cmd_moderation_history': lambda msg, args, cmd_name: cmd_moderation_history(msg, cmd_name),
    'cmd_moderation_log': lambda msg, args, cmd_name: cmd_moderation_log(msg, cmd_name),
    'cmd_moderation_stats': lambda msg, args, cmd_name: cmd_moderation_stats(msg, cmd_name),
    'cmd_reason_templates': lambda msg, args, cmd_name: cmd_reason_templates(msg, args, cmd_name),
    'cmd_moderation_auto_delete': lambda msg, args, cmd_name: cmd_moderation_auto_delete(msg, args, cmd_name),
    'cmd_join_requests': lambda msg, args, cmd_name: cmd_join_requests(msg, args, cmd_name),
    'cmd_filters': lambda msg, args, cmd_name: cmd_filters(msg, args, cmd_name),
    'cmd_captcha': lambda msg, args, cmd_name: cmd_captcha(msg, args, cmd_name),
    'cmd_raid_mode': lambda msg, args, cmd_name: cmd_raid_mode(msg, args, cmd_name),
    'cmd_freeze_chat': lambda msg, args, cmd_name: cmd_freeze_chat(msg, args, cmd_name),
    'cmd_unfreeze_chat': lambda msg, args, cmd_name: cmd_unfreeze_chat(msg, cmd_name),
    'cmd_channel_autohide': lambda msg, args, cmd_name: cmd_channel_autohide(msg, args, cmd_name),
    'cmd_warn': lambda msg, args, cmd_name: cmd_warn(msg, cmd_name),
    'cmd_warn_actions': lambda msg, args, cmd_name: cmd_warn_actions(msg, cmd_name),
    'show_warnings': lambda msg, args, cmd_name: show_warnings(msg, cmd_name),
    'cmd_mute_list': lambda msg, args, cmd_name: cmd_mute_list(msg, cmd_name),
    'cmd_ban_list': lambda msg, args, cmd_name: cmd_ban_list(msg, cmd_name),
    'cmd_warn_list': lambda msg, args, cmd_name: cmd_warn_list(msg, cmd_name),
    'cmd_unwarn': lambda msg, args, cmd_name: cmd_unwarn(msg, cmd_name),
    'cmd_del': lambda msg, args, cmd_name: cmd_del(msg, cmd_name),
    'cmd_pin': lambda msg, args, cmd_name: cmd_pin(msg, cmd_name),
    'cmd_purge': lambda msg, args, cmd_name: cmd_purge(msg, cmd_name),
    'cmd_promote': lambda msg, args, cmd_name: cmd_promote(msg, cmd_name),
    'cmd_demote': lambda msg, args, cmd_name: cmd_demote(msg, cmd_name),
    'cmd_give_award': lambda msg, args, cmd_name: cmd_give_award(msg, cmd_name),
    'cmd_rem_award': lambda msg, args, cmd_name: cmd_rem_award(msg, cmd_name),
    'cmd_my_awards': lambda msg, args, cmd_name: cmd_my_awards(msg, cmd_name),
    'cmd_top_awards': lambda msg, args, cmd_name: cmd_top_awards(msg, cmd_name),
    'cmd_marry': lambda msg, args, cmd_name: cmd_marry(msg, cmd_name),
    'cmd_accept_marry': lambda msg, args, cmd_name: cmd_accept_marry(msg, cmd_name),
    'cmd_reject_marry': lambda msg, args, cmd_name: cmd_reject_marry(msg, cmd_name),
    'cmd_divorce': lambda msg, args, cmd_name: cmd_divorce(msg, cmd_name),
    'cmd_marriages_list': lambda msg, args, cmd_name: cmd_marriages_list(msg),
    'cmd_add_phrase': lambda msg, args, cmd_name: cmd_add_phrase(msg, cmd_name),
    'cmd_del_phrase': lambda msg, args, cmd_name: cmd_del_phrase(msg, cmd_name),
    'cmd_list_phrases': lambda msg, args, cmd_name: cmd_list_phrases(msg, cmd_name),
    'cmd_phrase_stats': lambda msg, args, cmd_name: cmd_phrase_stats(msg),
    'cmd_phrase_show': lambda msg, args, cmd_name: cmd_phrase_show(msg, cmd_name),
    'cmd_welcome': lambda msg, args, cmd_name: cmd_welcome(msg, cmd_name),
    'cmd_farewell': lambda msg, args, cmd_name: cmd_farewell(msg, cmd_name),
    'cmd_rules': lambda msg, args, cmd_name: cmd_rules(msg),
    'cmd_add_rule': lambda msg, args, cmd_name: cmd_add_rule(msg, cmd_name),
    'cmd_clear_rules': lambda msg, args, cmd_name: cmd_clear_rules(msg, cmd_name),
    'cmd_games_menu': lambda msg, args, cmd_name: cmd_games_menu(msg, cmd_name),
    'cmd_duel': lambda msg, args, cmd_name: cmd_duel(msg, args, cmd_name),
    'cmd_rps_menu': lambda msg, args, cmd_name: cmd_rps(msg, cmd_name),
    'cmd_rps_with_bot': lambda msg, args, cmd_name: cmd_rps(msg, cmd_name),
    'cmd_rps_choice': lambda msg, args, cmd_name: cmd_rps(msg, cmd_name),
    'cmd_ttt_menu': lambda msg, args, cmd_name: cmd_games_menu(msg, cmd_name),
    'cmd_minesweeper': lambda msg, args, cmd_name: cmd_minesweeper(msg),
    'cmd_wordle': lambda msg, args, cmd_name: cmd_wordle(msg),
    'cmd_weather': lambda msg, args, cmd_name: cmd_weather(msg, cmd_name),
    'cmd_time': lambda msg, args, cmd_name: cmd_time(msg, args, cmd_name),
    'cmd_activity_graph_theme': lambda msg, args, cmd_name: cmd_activity_graph_theme(msg, cmd_name),
    'cmd_random_joke': lambda msg, args, cmd_name: cmd_random_joke(msg, cmd_name),
    'cmd_steal_candy': lambda msg, args, cmd_name: cmd_steal_candy(msg, args, cmd_name),
    'cmd_candy_balance': lambda msg, args, cmd_name: cmd_candy_balance(msg, cmd_name),
    'cmd_meme': lambda msg, args, cmd_name: cmd_meme(msg, args, cmd_name),
    'cmd_ship': lambda msg, args, cmd_name: cmd_ship(msg, cmd_name),
    'cmd_my_article': lambda msg, args, cmd_name: cmd_my_article(msg, cmd_name),
    'cmd_poll': lambda msg, args, cmd_name: cmd_poll(msg, cmd_name),
    'cmd_iris': lambda msg, args, cmd_name: cmd_iris(msg, cmd_name),
    'cmd_report': lambda msg, args, cmd_name: cmd_report(msg, cmd_name),
    'cmd_nick': lambda msg, args, cmd_name: cmd_nick(msg, cmd_name),
    'cmd_pogonialo': lambda msg, args, cmd_name: cmd_pogonialo(msg, cmd_name),
    'cmd_anti_spam': lambda msg, args, cmd_name: cmd_anti_spam(msg, cmd_name),
    'cmd_anti_moderation': lambda msg, args, cmd_name: cmd_anti_moderation(msg, cmd_name),
    'cmd_ping_check': lambda msg, args, cmd_name: cmd_ping_check(msg),
    'cmd_pic_toggle': lambda msg, args, cmd_name: cmd_pic_toggle(msg, cmd_name),
    'cmd_ping': lambda msg, args, cmd_name: cmd_ping(msg, cmd_name),
    'cmd_backup': lambda msg, args, cmd_name: cmd_backup(msg, args, cmd_name),
    'cmd_restore': lambda msg, args, cmd_name: cmd_restore(msg, args, cmd_name),
    'cmd_list_bot_chats': lambda msg, args, cmd_name: cmd_list_bot_chats(msg),
    'cmd_dk_set': lambda msg, args, cmd_name: cmd_dk_set(msg, cmd_name),
    'cmd_dk_enable': lambda msg, args, cmd_name: cmd_dk_enable(msg, cmd_name),
    'cmd_dk_disable': lambda msg, args, cmd_name: cmd_dk_disable(msg, cmd_name),
    'cmd_ldk_add': lambda msg, args, cmd_name: cmd_ldk_add(msg, cmd_name),
    'cmd_ldk_rem': lambda msg, args, cmd_name: cmd_ldk_rem(msg, cmd_name),
    'cmd_dk_menu': lambda msg, args, cmd_name: cmd_dk_menu(msg, cmd_name),
    'cmd_forward': lambda msg, args, cmd_name: cmd_forward(msg, cmd_name),
}


async def execute_command(cmd_name: str, args: str, msg: Message, main_chat: bool):
    """Выполняет команду по её имени"""

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

    if func_name not in COMMAND_HANDLERS:
        await report_command_error(
            msg,
            cmd_name,
            'Команда не подключена',
            f"Команда <code>{html.escape(str(cmd_name), quote=False)}</code> есть в списке, но пока не подключена к обработчику.",
            '!помощь',
        )
        return

    try:
        await COMMAND_HANDLERS[func_name](msg, args, cmd_name)
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

BDAY_MONTHS = (
    'Январь', 'Февраль', 'Март', 'Апрель', 'Май', 'Июнь',
    'Июль', 'Август', 'Сентябрь', 'Октябрь', 'Ноябрь', 'Декабрь',
)
BDAY_MONTHS_GENITIVE = (
    'января', 'февраля', 'марта', 'апреля', 'мая', 'июня',
    'июля', 'августа', 'сентября', 'октября', 'ноября', 'декабря',
)
BDAY_PHRASES = (
    'Пусть ожидание будет лёгким, а праздник — незабываемым ✨',
    'Календарь уже тихонько отсчитывает дни 🎈',
    'Самое время присмотреть праздничный торт 🍰',
    'Впереди день, когда можно официально принимать поздравления 🎁',
    'Пусть каждый день приближает что-то хорошее 🌟',
    'Праздничное настроение уже где-то рядом 🎉',
    'Запасайся желаниями — скоро пригодятся 🕯️',
    'Кажется, календарь готовит для тебя кое-что особенное 👀',
    'До личного праздника осталось совсем немного терпения 🎂',
    'Пора потихоньку выбирать музыку для праздника 🎶',
    'Пусть ожидание будет таким же приятным, как сам праздник 💛',
    'Скоро будет отличный повод улыбаться чаще 😊',
    'Ещё немного — и можно загадывать желание ✨',
    'Пусть приближающийся день принесёт много радости 🌷',
    'Праздник уже маячит на горизонте 🎊',
    'Самое время придумать, чем себя порадовать 🎁',
    'Календарь намекает: впереди особенный день 📅',
    'Пусть в этот день сбудется что-нибудь очень хорошее 🍀',
    'Скоро станет на один повод для торта больше 🍰',
    'Отсчёт до улыбок, подарков и тёплых слов уже идёт 💫',
    'Вишлист сам себя не составит 😉',
    'Пусть приближение праздника добавляет настроения каждый день ☀️',
    'Скоро все хорошие слова будут адресованы тебе 💌',
    'День рождения приближается — готовься сиять 🌟',
    'Небольшое ожидание делает праздник ещё слаще 🍬',
    'Каждый лист календаря приближает твой звёздный час 🌠',
    'Пусть впереди будет побольше приятных сюрпризов 🎀',
    'Праздничный режим уже можно включать понемногу 🥳',
    'Скоро появится законный повод загадать самое смелое желание 💭',
    'Твой личный праздник уже движется к тебе на полной скорости 🚀',
    'Хорошее настроение записано в план на этот день ✅',
    'Пусть ожидание будет наполнено маленькими радостями 🌈',
    'Где-то уже выбирают открытку именно для тебя 💌',
    'Ещё один повод собрать рядом любимых людей 🤗',
    'Праздничный сезон для одного очень классного человека скоро начнётся 🎊',
    'Пусть этот день будет ярче гирлянды и слаще торта ✨',
    'Скоро можно будет принимать комплименты без ограничений 😎',
    'Время подумать о праздничном меню — торт сам себя не выберет 🍓',
    'Новый год жизни уже готовит для тебя много интересного 🎁',
    'Пусть впереди будет день, который захочется повторить 💖',
    'Отсчёт идёт, а поводов для радости становится больше 🎈',
    'Совсем скоро календарь поставит рядом с датой праздничную звёздочку ⭐',
    'Пусть этот день принесёт целую охапку тёплых слов 🌻',
    'Твой праздник уже на подходе — держи улыбку наготове 😄',
    'У каждого супергероя есть свой особенный день 🦸',
    'Скоро можно будет загадать желание и задуть свечи 🕯️',
    'Впереди день, когда даже понедельник не испортит настроение 😉',
    'Пусть дорога к празднику будет лёгкой и красивой 🌺',
    'Пусть впереди будет побольше моментов, которые захочется сохранить 📸',
    'До твоего дня рождения календарь считает дни, а мы — хорошие поводы 🎉',
)
BDAY_UTC_OFFSETS = tuple(sorted(set(
    list(range(-12 * 60, 14 * 60 + 1, 60))
    + [
        -9 * 60 - 30, -3 * 60 - 30, 3 * 60 + 30, 4 * 60 + 30,
        5 * 60 + 30, 5 * 60 + 45, 6 * 60 + 30, 8 * 60 + 45,
        9 * 60 + 30, 10 * 60 + 30, 12 * 60 + 45,
    ]
)))
BDAY_WIZARD_TTL = 15 * 60
BDAY_NOTIFICATION_INTERVAL = 5 * 60
birthday_wizards: Dict[Tuple[int, int], dict] = {}
BDAY_CONGRATULATIONS = (
    'С днём рождения! Желаю много радости, тепла и исполнения желаний 🎂',
    'Пусть каждый день приносит счастье, улыбки и приятные сюрпризы! 🎁',
    'Желаю крепкого здоровья, ярких впечатлений и верных друзей рядом! 🌟',
    'Пусть всё задуманное получается, а поводов для радости будет больше! 🎈',
    'Желаю незабываемого года, полного удачи, любви и новых побед! 🥳',
    'Пусть мечты сбываются, настроение будет отличным, а торт — вкусным! 🍰',
    'Желаю побольше счастливых моментов и людей, с которыми ими хочется делиться! 💛',
    'Пусть впереди ждут только хорошие новости, большие успехи и чудеса! ✨',
    'Желаю яркого праздника и целого года, который будет лучше предыдущего! 🎊',
    'Пусть в жизни всегда найдётся место приключениям, смеху и исполнению желаний! 🌈',
)


def _birthday_offset_label(offset_minutes: int) -> str:
    sign = '+' if offset_minutes >= 0 else '-'
    hours, minutes = divmod(abs(offset_minutes), 60)
    suffix = f':{minutes:02d}' if minutes else ''
    return f'UTC{sign}{hours:02d}{suffix}'


def _birthday_intro_keyboard(uid: int, configured: bool = False) -> InlineKeyboardMarkup:
    if configured:
        rows = [[InlineKeyboardButton(
            text='🔄 Изменить дату',
            callback_data=f'bday:edit:{uid}',
        )]]
    else:
        rows = [[InlineKeyboardButton(
            text='🎂 Настроить день рождения',
            callback_data=f'bday:create:{uid}',
        )]]
    rows.append([InlineKeyboardButton(text='✖️ Закрыть', callback_data=f'bday:close:{uid}')])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _birthday_month_keyboard(uid: int) -> InlineKeyboardMarkup:
    rows = []
    for start in range(0, len(BDAY_MONTHS), 3):
        rows.append([
            InlineKeyboardButton(
                text=BDAY_MONTHS[index],
                callback_data=f'bday:month:{uid}:{index + 1}',
            )
            for index in range(start, min(start + 3, len(BDAY_MONTHS)))
        ])
    rows.append([
        InlineKeyboardButton(text='◀️ Назад', callback_data=f'bday:back:{uid}:intro'),
        InlineKeyboardButton(text='✖️ Закрыть', callback_data=f'bday:close:{uid}'),
    ])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _birthday_day_keyboard(uid: int, month: int) -> InlineKeyboardMarkup:
    days_in_month = calendar.monthrange(2024, month)[1]
    rows = []
    for start in range(1, days_in_month + 1, 7):
        rows.append([
            InlineKeyboardButton(
                text=str(day),
                callback_data=f'bday:day:{uid}:{day}',
            )
            for day in range(start, min(start + 7, days_in_month + 1))
        ])
    rows.append([
        InlineKeyboardButton(text='◀️ Назад', callback_data=f'bday:back:{uid}:month'),
        InlineKeyboardButton(text='✖️ Закрыть', callback_data=f'bday:close:{uid}'),
    ])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _birthday_timezone_keyboard(uid: int, page: int = 0) -> InlineKeyboardMarkup:
    per_page = 12
    page_count = (len(BDAY_UTC_OFFSETS) + per_page - 1) // per_page
    page = max(0, min(page, page_count - 1))
    start = page * per_page
    offsets = BDAY_UTC_OFFSETS[start:start + per_page]
    rows = [
        [
            InlineKeyboardButton(
                text=_birthday_offset_label(offset),
                callback_data=f'bday:tz:{uid}:{offset}',
            )
            for offset in offsets[index:index + 3]
        ]
        for index in range(0, len(offsets), 3)
    ]
    navigation = []
    if page:
        navigation.append(InlineKeyboardButton(
            text='◀️',
            callback_data=f'bday:tzpage:{uid}:{page - 1}',
        ))
    navigation.append(InlineKeyboardButton(
        text=f'{page + 1}/{page_count}',
        callback_data=f'bday:noop:{uid}',
    ))
    if page + 1 < page_count:
        navigation.append(InlineKeyboardButton(
            text='▶️',
            callback_data=f'bday:tzpage:{uid}:{page + 1}',
        ))
    rows.append(navigation)
    rows.append([
        InlineKeyboardButton(text='◀️ Назад', callback_data=f'bday:back:{uid}:day'),
        InlineKeyboardButton(text='✖️ Закрыть', callback_data=f'bday:close:{uid}'),
    ])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _birthday_days_remaining(birthday: dict, now: Optional[datetime] = None) -> int:
    offset = int(birthday.get('utc_offset_minutes', 0))
    birthday_tz = timezone(timedelta(minutes=offset))
    now = now or datetime.now(timezone.utc)
    local_today = now.astimezone(birthday_tz).date()
    month = int(birthday['month'])
    day = int(birthday['day'])
    if (local_today.month, local_today.day) == (month, day):
        return 0
    for year in range(local_today.year, local_today.year + 9):
        try:
            birthday_date = datetime(year, month, day, tzinfo=birthday_tz).date()
        except ValueError:
            continue
        if birthday_date > local_today:
            return (birthday_date - local_today).days
    raise ValueError('Не удалось вычислить дату следующего дня рождения.')


def _valid_birthday(value: object) -> bool:
    if not isinstance(value, dict):
        return False
    month = value.get('month')
    day = value.get('day')
    offset = value.get('utc_offset_minutes')
    if (
        not isinstance(month, int) or isinstance(month, bool)
        or not isinstance(day, int) or isinstance(day, bool)
        or not isinstance(offset, int) or isinstance(offset, bool)
        or offset not in BDAY_UTC_OFFSETS
        or not 1 <= month <= 12
    ):
        return False
    return 1 <= day <= calendar.monthrange(2024, month)[1]


def _birthday_countdown_text(birthday: dict) -> str:
    days = _birthday_days_remaining(birthday)
    date_text = f"{int(birthday['day'])} {BDAY_MONTHS_GENITIVE[int(birthday['month']) - 1]}"
    if days == 0:
        return f"🎂 День рождения: <b>{date_text}</b> <i>(сегодня!)</i>"

    if days % 10 == 1 and days % 100 != 11:
        days_text = f'{days} день'
    elif days % 10 in (2, 3, 4) and days % 100 not in (12, 13, 14):
        days_text = f'{days} дня'
    else:
        days_text = f'{days} дней'
    phrase = BDAY_PHRASES[days % len(BDAY_PHRASES)]
    return (
        f"🎂 День рождения: <b>{date_text}</b> <i>(через {days_text})</i>\n"
        f"✨ {phrase}"
    )


async def birthday_notifications_task():
    while True:
        try:
            now = datetime.now(timezone.utc)
            for chat_id in storage.get_known_group_chat_ids():
                chat_users = storage.load_chat_users(chat_id)
                for user_id_text, user_data in list(chat_users.items()):
                    birthday = user_data.get('birthday') if isinstance(user_data, dict) else None
                    if not _valid_birthday(birthday):
                        continue
                    try:
                        user_id = int(user_id_text)
                    except (TypeError, ValueError):
                        logger.warning(
                            "Некорректный ID пользователя с днём рождения в чате %s: %r",
                            chat_id, user_id_text,
                        )
                        continue

                    birthday_tz = timezone(timedelta(minutes=birthday['utc_offset_minutes']))
                    local_today = now.astimezone(birthday_tz).date()
                    birthday_mention = (
                        f'<a href="tg://user?id={user_id}">'
                        f'{get_display_name(chat_id, user_id)}</a>'
                    )
                    birthday_is_today = (
                        local_today.month == birthday['month']
                        and local_today.day == birthday['day']
                    )

                    if birthday_is_today:
                        year = local_today.year
                        if birthday.get('_greeting_emoji_year') != year:
                            try:
                                await bot.send_message(chat_id, '🎉')
                            except (TelegramAPIError, asyncio.TimeoutError) as exc:
                                logger.warning(
                                    "Не удалось отправить смайл ко дню рождения пользователя %s в чате %s: %s",
                                    user_id, chat_id, exc,
                                )
                                continue
                            birthday['_greeting_emoji_year'] = year
                            storage.get_user(chat_id, user_id, use_cache=False)
                            await storage.save()

                        if birthday.get('_greeting_year') != year:
                            greeting = random.choice(BDAY_CONGRATULATIONS)
                            try:
                                await bot.send_message(
                                    chat_id,
                                    f"🎂 {birthday_mention}! {greeting}",
                                )
                            except (TelegramAPIError, asyncio.TimeoutError) as exc:
                                logger.warning(
                                    "Не удалось поздравить пользователя %s в чате %s: %s",
                                    user_id, chat_id, exc,
                                )
                                continue
                            birthday['_greeting_year'] = year
                            storage.get_user(chat_id, user_id, use_cache=False)
                            await storage.save()
                        continue

                    reminder_day = min(
                        birthday['day'],
                        calendar.monthrange(local_today.year, local_today.month)[1],
                    )
                    month_key = f'{local_today.year:04d}-{local_today.month:02d}'
                    if (
                        local_today.day < reminder_day
                        or birthday.get('_reminder_month') == month_key
                    ):
                        continue
                    try:
                        await bot.send_message(
                            chat_id,
                            f"🎂 Ежемесячное напоминание для {birthday_mention}!\n"
                            f"{_birthday_countdown_text(birthday)}",
                        )
                    except (TelegramAPIError, asyncio.TimeoutError) as exc:
                        logger.warning(
                            "Не удалось отправить напоминание о дне рождения пользователя %s в чате %s: %s",
                            user_id, chat_id, exc,
                        )
                        continue
                    birthday['_reminder_month'] = month_key
                    storage.get_user(chat_id, user_id, use_cache=False)
                    await storage.save()
        except Exception:
            logger.exception("Ошибка проверки дней рождения")
        await asyncio.sleep(BDAY_NOTIFICATION_INTERVAL)


async def cmd_birthday(msg: Message):
    if not msg.from_user:
        return
    user = storage.get_user(msg.chat.id, msg.from_user.id)
    birthday = user.get('birthday')
    if _valid_birthday(birthday):
        await msg.answer(
            "🎈 <b>Твой особенный день уже отмечен в календаре!</b>\n"
            f"{UI_LINE}\n"
            f"{_birthday_countdown_text(birthday)}",
            reply_markup=_birthday_intro_keyboard(msg.from_user.id, configured=True),
        )
        return

    birthday_wizards[(msg.chat.id, msg.from_user.id)] = {
        'step': 'intro',
        'created_at': time.time(),
    }
    await msg.answer(
        "🎂 <b>Давай отметим твой день рождения!</b>\n"
        f"{UI_LINE}\n\n"
        "Настроим дату один раз — и я буду знать, когда поздравлять и сколько осталось до праздника ✨",
        reply_markup=_birthday_intro_keyboard(msg.from_user.id),
    )


@router.callback_query(F.data.startswith('bday:'))
async def birthday_callback(call: CallbackQuery):
    if not call.message or not call.from_user:
        await call.answer()
        return
    parts = call.data.split(':')
    if len(parts) < 3 or parts[0] != 'bday':
        await call.answer('Эта кнопка больше не действует.', show_alert=True)
        return
    try:
        owner_id = int(parts[2])
    except ValueError:
        await call.answer('Эта кнопка больше не действует.', show_alert=True)
        return
    if call.from_user.id != owner_id:
        await call.answer('Эта настройка открыта другим пользователем.', show_alert=True)
        return

    chat_id = call.message.chat.id
    key = (chat_id, owner_id)
    action = parts[1]
    wizard = birthday_wizards.get(key)
    if action == 'noop':
        await call.answer()
        return
    if action == 'close':
        birthday_wizards.pop(key, None)
        await call.message.edit_text(
            'Настройка дня рождения закрыта.',
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[]),
        )
        await call.answer()
        return
    if action in {'create', 'edit'}:
        birthday_wizards[key] = {'step': 'month', 'created_at': time.time()}
        await call.message.edit_text(
            "🗓️ <b>Вы настраиваете свой день рождения</b>\n"
            f"{UI_LINE}\n\n"
            "Сначала выберите месяц:",
            reply_markup=_birthday_month_keyboard(owner_id),
        )
        await call.answer()
        return
    if not wizard or time.time() - wizard.get('created_at', 0) > BDAY_WIZARD_TTL:
        birthday_wizards.pop(key, None)
        await call.answer('Настройка истекла. Отправьте !др, чтобы начать заново.', show_alert=True)
        return

    if action == 'back':
        destination = parts[3] if len(parts) > 3 else ''
        if destination == 'intro':
            birthday_wizards[key]['step'] = 'intro'
            await call.message.edit_text(
                "🎂 <b>Давай отметим твой день рождения!</b>\n"
                f"{UI_LINE}\n\n"
                "Настроим дату один раз — и я буду знать, когда поздравлять и сколько осталось до праздника ✨",
                reply_markup=_birthday_intro_keyboard(owner_id),
            )
        elif destination == 'month':
            birthday_wizards[key]['step'] = 'month'
            await call.message.edit_text(
                "🗓️ <b>Вы настраиваете свой день рождения</b>\n"
                f"{UI_LINE}\n\n"
                "Сначала выберите месяц:",
                reply_markup=_birthday_month_keyboard(owner_id),
            )
        elif destination == 'day' and isinstance(wizard.get('month'), int):
            birthday_wizards[key]['step'] = 'day'
            await call.message.edit_text(
                f"📅 Месяц выбран: <b>{BDAY_MONTHS[wizard['month'] - 1]}</b>\n"
                "Теперь выберите день:",
                reply_markup=_birthday_day_keyboard(owner_id, wizard['month']),
            )
        else:
            await call.answer('К предыдущему шагу вернуться не удалось.', show_alert=True)
            return
        await call.answer()
        return

    if action == 'month':
        if wizard.get('step') != 'month' or len(parts) != 4:
            await call.answer('Выберите месяц на текущем шаге.', show_alert=True)
            return
        try:
            month = int(parts[3])
        except ValueError:
            await call.answer('Некорректный месяц.', show_alert=True)
            return
        if not 1 <= month <= 12:
            await call.answer('Некорректный месяц.', show_alert=True)
            return
        wizard.update(step='day', month=month)
        await call.message.edit_text(
            f"📅 Месяц выбран: <b>{BDAY_MONTHS[month - 1]}</b>\n"
            "Теперь выберите день:",
            reply_markup=_birthday_day_keyboard(owner_id, month),
        )
        await call.answer()
        return

    if action == 'day':
        if wizard.get('step') != 'day' or len(parts) != 4:
            await call.answer('Выберите день на текущем шаге.', show_alert=True)
            return
        try:
            day = int(parts[3])
            month = int(wizard['month'])
            if not 1 <= day <= calendar.monthrange(2024, month)[1]:
                raise ValueError
        except (KeyError, TypeError, ValueError):
            await call.answer('Некорректный день.', show_alert=True)
            return
        wizard.update(step='timezone', day=day)
        await call.message.edit_text(
            f"🎂 Вы выбрали <b>{day} {BDAY_MONTHS_GENITIVE[month - 1]}</b>.\n"
            "Теперь выберите свой часовой пояс:",
            reply_markup=_birthday_timezone_keyboard(owner_id),
        )
        await call.answer()
        return

    if action == 'tzpage':
        if wizard.get('step') != 'timezone' or len(parts) != 4:
            await call.answer('Выберите часовой пояс на текущем шаге.', show_alert=True)
            return
        try:
            page = int(parts[3])
        except ValueError:
            await call.answer('Некорректная страница.', show_alert=True)
            return
        await call.message.edit_reply_markup(
            reply_markup=_birthday_timezone_keyboard(owner_id, page),
        )
        await call.answer()
        return

    if action == 'tz':
        if wizard.get('step') != 'timezone' or len(parts) != 4:
            await call.answer('Выберите часовой пояс на текущем шаге.', show_alert=True)
            return
        try:
            offset = int(parts[3])
            if offset not in BDAY_UTC_OFFSETS:
                raise ValueError
        except ValueError:
            await call.answer('Некорректный часовой пояс.', show_alert=True)
            return
        birthday = {
            'month': int(wizard['month']),
            'day': int(wizard['day']),
            'utc_offset_minutes': offset,
        }
        user = storage.get_user(chat_id, owner_id)
        user['birthday'] = birthday
        storage.invalidate_user_cache(chat_id, owner_id)
        storage.mark_dirty()
        await storage.save()
        birthday_wizards.pop(key, None)
        await call.message.edit_text(
            "🎉 <b>Ура, день рождения сохранён!</b>\n"
            f"{UI_LINE}\n"
            f"{_birthday_countdown_text(birthday)}\n\n"
            f"Часовой пояс: <b>{_birthday_offset_label(offset)}</b>",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[]),
        )
        await call.answer('Дата сохранена!')
        return

    await call.answer('Неизвестный шаг настройки.', show_alert=True)


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
    first_seen_date = datetime.fromtimestamp(first_seen, KALININGRAD_TZ)
    days_since = (kaliningrad_now().date() - first_seen_date.date()).days

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
    birthday = u.get('birthday')
    if _valid_birthday(birthday):
        birthday_text = (
            f"{int(birthday['day'])} {BDAY_MONTHS_GENITIVE[int(birthday['month']) - 1]}"
        )
        remaining = _birthday_days_remaining(birthday)
        if remaining == 0:
            countdown = 'сегодня'
        elif remaining == 1:
            countdown = 'завтра'
        else:
            countdown = f'через {remaining} дн.'
        lines.append(f"🎂 День рождения: <b>{birthday_text}</b> <i>({countdown})</i>")
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


async def send_profile(msg: Message, text: str, graph: Optional[BytesIO], filename: str):
    if not graph:
        return await msg.answer(text, disable_web_page_preview=True)
    if len(text) <= 1024:
        return await msg.answer_photo(
            BufferedInputFile(graph.read(), filename),
            caption=text,
        )
    await msg.answer_photo(BufferedInputFile(graph.read(), filename))
    return await msg.answer(text, disable_web_page_preview=True)


async def who_am_i(msg: Message, cmd_name: str = 'кто я'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!кто я'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    uid = msg.from_user.id
    u = storage.get_user(msg.chat.id, uid)

    text = build_profile_text(msg.chat.id, uid, u, show_last_active=True)

    graph = await create_graph_async(msg.chat.id, uid, 30)
    await send_profile(msg, text, graph, 'profile_graph.png')


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
        preset_data = get_activity_graph_preset_data(call.from_user.id)
        preset_data['active_global'] = None
        preset_data['active_chats'] = {}
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


def graph_wizard_button(label: str, action: str, uid: int, value: str = '') -> InlineKeyboardButton:
    suffix = f":{value}" if value else ''
    return InlineKeyboardButton(text=label, callback_data=f"graphwiz:{action}:{uid}{suffix}")


def graph_preset_lists(uid: int) -> Tuple[List[dict], Dict[str, List[dict]]]:
    preset_data = get_activity_graph_preset_data(uid)
    global_presets = preset_data.get('global', [])
    chat_presets = preset_data.get('chats', {})
    return (
        global_presets if isinstance(global_presets, list) else [],
        chat_presets if isinstance(chat_presets, dict) else {},
    )


def find_graph_preset(uid: int, chat_id: int, scope: str, preset_id: str) -> Optional[dict]:
    global_presets, chats = graph_preset_lists(uid)
    if scope == 'global':
        candidates = global_presets
    elif scope == 'local':
        local_presets = chats.get(str(chat_id), [])
        candidates = local_presets if isinstance(local_presets, list) else []
    else:
        return None
    return next(
        (
            preset for preset in candidates
            if isinstance(preset, dict) and preset.get('id') == preset_id
        ),
        None,
    )


def graph_preset_categories_keyboard(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            graph_wizard_button('💬 Локальные', 'preset_local', uid),
            graph_wizard_button('🌐 Общие', 'preset_global', uid),
        ],
        [graph_wizard_button('◀️ Назад', 'menu', uid)],
    ])


def graph_preset_list_keyboard(
    uid: int,
    chat_id: int,
    scope: str,
) -> InlineKeyboardMarkup:
    global_presets, chats = graph_preset_lists(uid)
    if scope == 'global':
        presets = global_presets
        prefix = '🌐'
    else:
        local_presets = chats.get(str(chat_id), [])
        presets = local_presets if isinstance(local_presets, list) else []
        prefix = '💬'
    preset_data = get_activity_graph_preset_data(uid)
    active_id = (
        preset_data.get('active_global')
        if scope == 'global'
        else preset_data.get('active_chats', {}).get(str(chat_id))
    )
    buttons = [
        graph_wizard_button(
            f"{'✅ ' if preset.get('id') == active_id else ''}{prefix} "
            f"{str(preset.get('name') or 'Без названия')[:35]}",
            f"preset_view_{scope}",
            uid,
            str(preset['id']),
        )
        for preset in presets
        if isinstance(preset, dict) and preset.get('id')
    ]
    rows = [buttons[index:index + 2] for index in range(0, len(buttons), 2)]
    if not buttons:
        rows.append([graph_wizard_button('Здесь пока нет пресетов', 'presets', uid)])
    rows.append([graph_wizard_button('◀️ Назад', 'presets', uid)])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def graph_preset_detail_keyboard(
    uid: int,
    scope: str,
    preset_id: str,
    active: bool = False,
) -> InlineKeyboardMarkup:
    rows = [
        [
            graph_wizard_button(
                '✅ Активировано' if active else '▶️ Использовать',
                f"preset_use_{scope}",
                uid,
                preset_id,
            ),
            graph_wizard_button('🗑 Удалить', f"preset_delete_{scope}", uid, preset_id),
        ],
        [graph_wizard_button('◀️ Назад', f"preset_{scope}", uid)],
    ]
    return InlineKeyboardMarkup(inline_keyboard=rows)


def graph_preset_delete_confirmation_keyboard(
    uid: int,
    scope: str,
    preset_id: str,
) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            graph_wizard_button('🗑 Да, удалить', f"preset_delete_yes_{scope}", uid, preset_id),
            graph_wizard_button('↩️ Отмена', f"preset_delete_no_{scope}", uid, preset_id),
        ],
    ])


def graph_theme_menu_keyboard(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [graph_wizard_button('☀️ Светлая', 'theme', uid, 'light'),
         graph_wizard_button('🌙 Тёмная', 'theme', uid, 'dark')],
        [graph_wizard_button('🎨 Кастомная', 'theme', uid, 'custom')],
    ])


def graph_builtin_mode_keyboard(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            graph_wizard_button('☀️ Светлая', 'builtin_mode', uid, 'light'),
            graph_wizard_button('🌙 Тёмная', 'builtin_mode', uid, 'dark'),
        ],
        [graph_wizard_button('◀️ Назад', 'menu', uid)],
    ])


def graph_builtin_theme_keyboard(
    uid: int,
    mode: str,
    back_action: str = 'builtin',
    direct: bool = False,
) -> InlineKeyboardMarkup:
    theme_action = 'builtin_direct_theme' if direct else 'builtin_theme'
    buttons = [
        graph_wizard_button(
            theme[0], theme_action, uid, theme_id,
        )
        for theme_id, theme in ACTIVITY_GRAPH_THEMES.items()
        if theme[1] == mode
    ]
    rows = [buttons[index:index + 2] for index in range(0, len(buttons), 2)]
    rows.append([graph_wizard_button('◀️ Назад', back_action, uid)])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def graph_start_keyboard(uid: int, chat_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [graph_wizard_button('📁 Пресеты', 'presets', uid)],
        [graph_wizard_button('➕ Создать пресет', 'create', uid)],
        [graph_wizard_button('🎨 Выбрать готовую тему', 'builtin', uid)],
    ])


def graph_font_keyboard(uid: int) -> InlineKeyboardMarkup:
    refresh_graph_fonts()
    rows = [
        [graph_wizard_button(name[:30], 'font', uid, graph_font_token(name, path))]
        for name, path in GRAPH_FONT_OPTIONS.items()
    ]
    rows.append([graph_wizard_button('🔄 Обновить список шрифтов', 'font_refresh', uid)])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def graph_chart_keyboard(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [graph_wizard_button('📈 Линейный', 'chart', uid, 'line'),
         graph_wizard_button('📊 Столбчатый', 'chart', uid, 'bar')],
    ])


def graph_preview_keyboard(uid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [graph_wizard_button('🎨 Тема', 'edit_theme', uid),
         graph_wizard_button('🔤 Шрифт', 'edit_font', uid),
         graph_wizard_button('📊 Вид графика', 'edit_chart', uid)],
        [graph_wizard_button('💾 Сохранить пресет', 'save', uid)],
    ])


async def graph_show_theme_picker(message, uid: int, text: str):
    if getattr(message, 'photo', None):
        await message.edit_caption(caption=text, reply_markup=graph_theme_menu_keyboard(uid))
    else:
        await message.edit_text(text, reply_markup=graph_theme_menu_keyboard(uid))


async def graph_show_prompt(
    message,
    text: str,
    keyboard: Optional[InlineKeyboardMarkup] = None,
) -> Message:
    if getattr(message, 'photo', None):
        return await message.edit_caption(caption=text, reply_markup=keyboard)
    return await message.edit_text(text, reply_markup=keyboard)


async def graph_show_font_picker(message, uid: int):
    text = "🔤 Выберите шрифт для графика:"
    if getattr(message, 'photo', None):
        await message.edit_caption(caption=text, reply_markup=graph_font_keyboard(uid))
    else:
        await message.edit_text(text, reply_markup=graph_font_keyboard(uid))


async def graph_show_chart_picker(message, uid: int):
    text = "📊 Выберите вид графика:"
    if getattr(message, 'photo', None):
        await message.edit_caption(caption=text, reply_markup=graph_chart_keyboard(uid))
    else:
        await message.edit_text(text, reply_markup=graph_chart_keyboard(uid))


async def graph_render_preview(message, uid: int, chat_id: int, settings: dict):
    graph = await create_graph_async(chat_id, uid, 30, settings=settings, preview=True)
    if graph is None:
        raise RuntimeError("Не удалось создать превью графика")
    media = InputMediaPhoto(
        media=BufferedInputFile(graph.read(), 'activity_graph_preview.png'),
        caption=(
            "👀 <b>Предпросмотр графика</b>\n"
            "Если всё устраивает, сохраните пресет. Настройки можно изменить кнопками ниже."
        ),
    )
    keyboard = graph_preview_keyboard(uid)
    if getattr(message, 'photo', None):
        await message.edit_media(media=media, reply_markup=keyboard)
    else:
        await message.answer_photo(media.media, caption=media.caption, reply_markup=keyboard)


async def graph_render_saved_preset_preview(
    message,
    uid: int,
    chat_id: int,
    preset: dict,
    scope: str,
    preset_id: str,
    active: bool,
):
    settings = {
        'theme_id': preset.get('theme_id', 'dark_default'),
        'colors': preset.get('colors'),
        'font': preset.get('font', DEFAULT_GRAPH_FONT),
        'chart_type': preset.get('chart_type', 'line'),
    }
    graph = await create_graph_async(chat_id, uid, 30, settings=settings, preview=True)
    if graph is None:
        raise RuntimeError("Не удалось создать превью графика")
    name = html.escape(str(preset.get('name') or 'Без названия'), quote=False)
    media = InputMediaPhoto(
        media=BufferedInputFile(graph.read(), 'activity_graph_preset_preview.png'),
        caption=(
            f"👀 <b>{name}</b>\n"
            "Демо-превью за 30 дней. Числа случайные и не отражают реальную активность."
        ),
    )
    keyboard = graph_preset_detail_keyboard(uid, scope, preset_id, active)
    if getattr(message, 'photo', None):
        await message.edit_media(media=media, reply_markup=keyboard)
    else:
        await message.answer_photo(media.media, caption=media.caption, reply_markup=keyboard)


async def cmd_activity_graph_theme(msg: Message, cmd_name: str = 'тема графика'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    global_presets, chats = graph_preset_lists(msg.from_user.id)
    chat_presets = chats.get(str(msg.chat.id), [])
    if not global_presets and not chat_presets:
        return await msg.answer(
            "📊 <b>График активности</b>\n\n"
            "У тебя пока нет сохранённых пресетов.\n"
            "Создай пресет, чтобы настроить график и сохранить его, "
            "или выбери готовую тему без сохранения.\n\n"
            "<i>Без пресета доступны только готовые темы.</i>",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [graph_wizard_button('✨ Создать пресет', 'create', msg.from_user.id)],
                [graph_wizard_button('🎨 Выбрать тему без пресета', 'builtin', msg.from_user.id)],
            ]),
        )
    await msg.answer(
        "📊 <b>График активности</b>\n"
        "Выбери пресет, создай новый или настрой готовую тему.",
        reply_markup=graph_start_keyboard(msg.from_user.id, msg.chat.id),
    )


@router.callback_query(F.data.startswith('graphwiz:'))
async def activity_graph_wizard_callback(call: CallbackQuery):
    parts = call.data.split(':')
    if len(parts) < 3 or not parts[2].isdigit():
        return await call.answer('Некорректная настройка графика.', show_alert=True)
    action, uid = parts[1], int(parts[2])
    if uid != call.from_user.id:
        return await call.answer('Эти настройки открыты другим пользователем.', show_alert=True)

    chat_id = call.message.chat.id
    key = (chat_id, uid)
    wizard = activity_graph_wizards.setdefault(key, {
        'created_at': time.time(),
        'settings': {
            'theme_id': 'dark_default',
            'colors': None,
            'font': DEFAULT_GRAPH_FONT,
            'chart_type': 'line',
        }
    })
    settings = wizard['settings']
    value = parts[3] if len(parts) > 3 else ''

    if action == 'presets':
        await graph_show_prompt(
            call.message,
            "📁 <b>Твои пресеты</b>\nВыбери, какие пресеты показать:",
            graph_preset_categories_keyboard(uid),
        )
    elif action in ('preset_local', 'preset_global'):
        scope = action.removeprefix('preset_')
        title = '💬 <b>Локальные пресеты</b>' if scope == 'local' else '🌐 <b>Общие пресеты</b>'
        description = (
            'Доступны только в этом чате.'
            if scope == 'local'
            else 'Доступны во всех чатах.'
        )
        await graph_show_prompt(
            call.message,
            f"{title}\n{description}\nВыбери пресет для просмотра:",
            graph_preset_list_keyboard(uid, chat_id, scope),
        )
    elif action in ('preset_view_local', 'preset_view_global'):
        scope = action.removeprefix('preset_view_')
        preset = find_graph_preset(uid, chat_id, scope, value)
        if preset is None:
            return await call.answer('Пресет не найден.', show_alert=True)
        preset_data = get_activity_graph_preset_data(uid)
        active_id = (
            preset_data.get('active_global')
            if scope == 'global'
            else preset_data.get('active_chats', {}).get(str(chat_id))
        )
        await graph_render_saved_preset_preview(
            call.message, uid, chat_id, preset, scope, value, active_id == value,
        )
    elif action in ('preset_use_local', 'preset_use_global'):
        scope = action.removeprefix('preset_use_')
        preset = find_graph_preset(uid, chat_id, scope, value)
        if preset is None:
            return await call.answer('Пресет не найден.', show_alert=True)
        preset_data = get_activity_graph_preset_data(uid)
        if scope == 'global':
            preset_data['active_global'] = value
            preset_data['active_chats'] = {}
        else:
            preset_data.setdefault('active_chats', {})[str(chat_id)] = value
        storage.mark_dirty()
        await storage.save()
        await graph_render_saved_preset_preview(
            call.message, uid, chat_id, preset, scope, value, True,
        )
    elif action in ('preset_delete_local', 'preset_delete_global'):
        scope = action.removeprefix('preset_delete_')
        preset = find_graph_preset(uid, chat_id, scope, value)
        if preset is None:
            return await call.answer('Пресет не найден.', show_alert=True)
        safe_name = html.escape(str(preset.get('name') or 'Без названия'), quote=False)
        await graph_show_prompt(
            call.message,
            f"⚠️ <b>Удалить пресет «{safe_name}»?</b>\nЭто действие нельзя отменить.",
            graph_preset_delete_confirmation_keyboard(uid, scope, value),
        )
    elif action in ('preset_delete_no_local', 'preset_delete_no_global'):
        scope = action.removeprefix('preset_delete_no_')
        preset = find_graph_preset(uid, chat_id, scope, value)
        if preset is None:
            return await call.answer('Пресет не найден.', show_alert=True)
        preset_data = get_activity_graph_preset_data(uid)
        active_id = (
            preset_data.get('active_global')
            if scope == 'global'
            else preset_data.get('active_chats', {}).get(str(chat_id))
        )
        await graph_render_saved_preset_preview(
            call.message, uid, chat_id, preset, scope, value, active_id == value,
        )
    elif action in ('preset_delete_yes_local', 'preset_delete_yes_global'):
        scope = action.removeprefix('preset_delete_yes_')
        preset_data = get_activity_graph_preset_data(uid)
        preset = find_graph_preset(uid, chat_id, scope, value)
        if preset is None:
            return await call.answer('Пресет уже удалён или не найден.', show_alert=True)
        if scope == 'global':
            preset_data['global'] = [
                item for item in preset_data.get('global', [])
                if not isinstance(item, dict) or item.get('id') != value
            ]
            if preset_data.get('active_global') == value:
                preset_data['active_global'] = None
        else:
            chat_key = str(chat_id)
            chat_presets = preset_data.get('chats', {}).get(chat_key, [])
            preset_data['chats'][chat_key] = [
                item for item in chat_presets
                if not isinstance(item, dict) or item.get('id') != value
            ]
            active_chats = preset_data.get('active_chats', {})
            if isinstance(active_chats, dict) and active_chats.get(chat_key) == value:
                active_chats.pop(chat_key, None)
        storage.mark_dirty()
        await storage.save()
        title = '💬 <b>Локальные пресеты</b>' if scope == 'local' else '🌐 <b>Общие пресеты</b>'
        await graph_show_prompt(
            call.message,
            f"✅ Пресет «{html.escape(str(preset.get('name') or 'Без названия'), quote=False)}» удалён.\n\n"
            f"{title}\nВыбери другой пресет:",
            graph_preset_list_keyboard(uid, chat_id, scope),
        )
    elif action == 'create':
        wizard['step'] = 'theme'
        wizard['builtin_direct'] = False
        wizard.pop('editing_setting', None)
        settings.update({'theme_id': 'dark_default', 'colors': None, 'font': DEFAULT_GRAPH_FONT, 'chart_type': 'line'})
        await graph_show_theme_picker(
            call.message, uid,
            "Вы создаёте пресет. В нём можно настроить тему, шрифт и вид графика.\nСначала выберите тему:",
        )
    elif action == 'builtin':
        wizard['builtin_direct'] = True
        await graph_show_prompt(
            call.message,
            'Вы выбираете готовую тему графика. Создать кастомную тему без пресета нельзя.\n'
            'Сначала выберите светлое или тёмное оформление:',
            graph_builtin_mode_keyboard(uid),
        )
    elif action == 'menu':
        await graph_show_prompt(
            call.message,
            "📊 <b>График активности</b>\n"
            "Выбери пресет, создай новый или настрой готовую тему.",
            graph_start_keyboard(uid, chat_id),
        )
    elif action == 'theme':
        if value in ('light', 'dark'):
            wizard['builtin_mode'] = value
            await graph_show_prompt(
                call.message,
                f"Выберите предустановленную {'светлую' if value == 'light' else 'тёмную'} тему:",
                graph_builtin_theme_keyboard(
                    uid,
                    value,
                    'back_theme',
                    direct=bool(wizard.get('builtin_direct')),
                ),
            )
        elif value == 'custom':
            await graph_show_prompt(
                call.message,
                "🎨 Вы создаёте кастомную тему. Выберите способ настройки:",
                InlineKeyboardMarkup(inline_keyboard=[
                    [graph_wizard_button('Простая', 'simple', uid),
                     graph_wizard_button('Расширенная', 'advanced', uid)],
                    [graph_wizard_button('Выйти', 'exit_custom', uid)],
                ]),
            )
        else:
            return await call.answer('Неизвестная тема.', show_alert=True)
    elif action == 'exit_custom':
        await graph_show_theme_picker(
            call.message, uid,
            "Вы создаёте пресет. В нём можно настроить тему, шрифт и вид графика.\nСначала выберите тему:",
        )
    elif action == 'simple':
        wizard['step'] = 'simple_color'
        prompt = await graph_show_prompt(
            call.message,
            "Отправьте один HEX-цвет для фона графика, например <code>#5865F2</code>.\n"
            "Этот цвет станет фоном. Бот определит, светлый он или тёмный, и подберёт "
            "контрастные цвета панели, графика, сетки и текста.\n\n"
            "↩️ <b>Ответьте HEX-кодом именно на это сообщение бота.</b>",
        )
        wizard['reply_prompt_message_id'] = prompt.message_id
    elif action == 'advanced':
        wizard['step'] = 'colors'
        prompt = await graph_show_prompt(
            call.message,
            "Задайте все 6 цветов темы в одной строке, разделив их пробелами. Каждый цвет — "
            "HEX-код из символа <code>#</code> и шести цифр или букв от A до F.\n\n"
            "Порядок значений:\n"
            "1. <b>Фон всего изображения</b> — за пределами области графика.\n"
            "2. <b>Фон области графика</b> — цвет панели, на которой нарисованы данные.\n"
            "3. <b>Акцентный цвет</b> — линия или столбцы графика.\n"
            "4. <b>Цвет сетки/заливки</b> — сетка и полупрозрачная область под линией.\n"
            "5. <b>Вторичный текст</b> — подписи и сводная статистика.\n"
            "6. <b>Основной текст</b> — заголовок и числа на графике.\n\n"
            "Светлый пример:\n"
            "<code>#ffffff #f5f6f8 #5865f2 #d9defa #747f8d #23272a</code>\n"
            "Тёмный пример:\n"
            "<code>#161821 #202331 #8b9cff #414a75 #aeb5d0 #f4f5ff</code>\n\n"
            "↩️ <b>Ответьте строкой из 6 HEX-кодов именно на это сообщение бота.</b>\n"
            "Чтобы отменить создание пресета, отправьте <code>отмена</code>.",
        )
        wizard['reply_prompt_message_id'] = prompt.message_id
    elif action == 'builtin_mode':
        if value not in ('light', 'dark'):
            return await call.answer('Выберите светлую или тёмную тему.', show_alert=True)
        wizard['builtin_mode'] = value
        await graph_show_prompt(
            call.message,
            f"Выберите предустановленную {'светлую' if value == 'light' else 'тёмную'} тему:",
            graph_builtin_theme_keyboard(
                uid, value, direct=bool(wizard.get('builtin_direct')),
            ),
        )
    elif action == 'back_theme':
        wizard['builtin_direct'] = False
        await graph_show_theme_picker(
            call.message, uid,
            "Вы создаёте пресет. В нём можно настроить тему, шрифт и вид графика.\nСначала выберите тему:",
        )
    elif action in ('builtin_theme', 'builtin_direct_theme'):
        if value not in ACTIVITY_GRAPH_THEMES:
            return await call.answer('Неизвестная тема.', show_alert=True)
        selected_mode = wizard.get('builtin_mode')
        if selected_mode and ACTIVITY_GRAPH_THEMES[value][1] != selected_mode:
            return await call.answer('Эта тема не относится к выбранному оформлению.', show_alert=True)
        if action == 'builtin_direct_theme' or wizard.get('builtin_direct'):
            user = storage.get_user(chat_id, uid)
            user['activity_graph_theme'] = value
            preset_data = get_activity_graph_preset_data(uid)
            preset_data['active_global'] = None
            preset_data['active_chats'] = {}
            storage.invalidate_user_cache(chat_id, uid)
            storage.mark_dirty()
            await storage.save()
            activity_graph_wizards.pop(key, None)
            await call.message.edit_text(
                f"✅ Предустановленная тема графика сохранена: "
                f"<b>{ACTIVITY_GRAPH_THEME_NAMES[value]}</b>."
            )
        else:
            settings['theme_id'] = value
            settings['colors'] = None
            if wizard.pop('editing_setting', None) == 'theme':
                await graph_render_preview(call.message, uid, chat_id, settings)
            else:
                await graph_show_font_picker(call.message, uid)
    elif action == 'edit_theme':
        wizard['editing_setting'] = 'theme'
        await graph_show_theme_picker(call.message, uid, 'Выберите новую тему:')
    elif action == 'edit_font':
        wizard['editing_setting'] = 'font'
        await graph_show_font_picker(call.message, uid)
    elif action == 'font_refresh':
        changed = refresh_graph_fonts()
        await graph_show_prompt(
            call.message,
            f"{'Список шрифтов обновлён.' if changed else 'Новых шрифтов не найдено.'}\nВыберите шрифт:",
            graph_font_keyboard(uid),
        )
    elif action == 'edit_chart':
        wizard['editing_setting'] = 'chart'
        await graph_show_chart_picker(call.message, uid)
    elif action == 'font':
        refresh_graph_fonts()
        font_name = next(
            (
                name for name, path in GRAPH_FONT_OPTIONS.items()
                if graph_font_token(name, path) == value
            ),
            None,
        )
        if font_name is None:
            return await call.answer('Неизвестный шрифт.', show_alert=True)
        settings['font'] = font_name
        if wizard.pop('editing_setting', None) == 'font':
            await graph_render_preview(call.message, uid, chat_id, settings)
        else:
            await graph_show_chart_picker(call.message, uid)
    elif action == 'chart':
        if value not in ('line', 'bar'):
            return await call.answer('Неизвестный вид графика.', show_alert=True)
        settings['chart_type'] = value
        wizard.pop('editing_setting', None)
        await graph_render_preview(call.message, uid, chat_id, settings)
    elif action == 'use':
        global_presets, chats = graph_preset_lists(uid)
        candidates = list(global_presets) + list(chats.get(str(chat_id), []))
        preset = next((item for item in candidates if isinstance(item, dict) and item.get('id') == value), None)
        if preset is None:
            return await call.answer('Пресет не найден.', show_alert=True)
        preset_data = get_activity_graph_preset_data(uid)
        if preset.get('scope') == 'global':
            preset_data['active_global'] = value
            preset_data['active_chats'] = {}
        else:
            preset_data.setdefault('active_chats', {})[str(chat_id)] = value
        storage.mark_dirty()
        await storage.save()
        await call.message.edit_text(
            f"✅ Активирован пресет «{html.escape(str(preset.get('name') or ''), quote=False)}»."
        )
    elif action == 'save':
        wizard['step'] = 'name'
        if getattr(call.message, 'photo', None):
            prompt = await call.message.edit_caption(
                caption="Назовите ваш пресет.\n\n"
                "↩️ <b>Ответьте названием именно на это сообщение бота.</b>",
                reply_markup=None,
            )
        else:
            prompt = await call.message.edit_text(
                "Назовите ваш пресет.\n\n"
                "↩️ <b>Ответьте названием именно на это сообщение бота.</b>",
                reply_markup=None,
            )
        wizard['reply_prompt_message_id'] = prompt.message_id
    elif action == 'scope':
        if value not in ('global', 'chat'):
            return await call.answer('Неизвестная область действия.', show_alert=True)
        name = wizard.get('pending_name', '').strip()
        if not name:
            return await call.answer('Не указано название пресета.', show_alert=True)
        preset_data = get_activity_graph_preset_data(uid)
        preset = {
            'id': uuid.uuid4().hex[:10],
            'name': name[:40],
            'scope': value,
            'chat_id': chat_id if value == 'chat' else None,
            'theme_id': settings.get('theme_id', 'dark_default'),
            'colors': list(settings['colors']) if settings.get('colors') else None,
            'font': settings.get('font', DEFAULT_GRAPH_FONT),
            'chart_type': settings.get('chart_type', 'line'),
        }
        if value == 'global':
            preset_data.setdefault('global', []).append(preset)
            preset_data['active_global'] = preset['id']
        else:
            preset_data.setdefault('chats', {}).setdefault(str(chat_id), []).append(preset)
            preset_data.setdefault('active_chats', {})[str(chat_id)] = preset['id']
        storage.mark_dirty()
        await storage.save()
        activity_graph_wizards.pop(key, None)
        await call.message.edit_text(
            f"✅ Пресет «{html.escape(name, quote=False)}» сохранён и включён "
            f"{'во всех чатах' if value == 'global' else 'только в этом чате'}."
        )
    else:
        return await call.answer('Неизвестное действие.', show_alert=True)

    await call.answer()


async def handle_activity_graph_wizard_text(msg: Message) -> bool:
    if not msg.from_user or msg.from_user.is_bot:
        return False
    now = time.time()
    expired_keys = [
        wizard_key
        for wizard_key, pending_wizard in activity_graph_wizards.items()
        if not isinstance(pending_wizard.get('created_at'), (int, float))
        or now - pending_wizard['created_at'] > ACTIVITY_GRAPH_WIZARD_TTL
    ]
    for wizard_key in expired_keys:
        activity_graph_wizards.pop(wizard_key, None)
    key = (msg.chat.id, msg.from_user.id)
    wizard = activity_graph_wizards.get(key)
    reply_steps = {'simple_color', 'colors', 'name'}
    waiting_for_reply = [
        (wizard_uid, pending_wizard)
        for (wizard_chat_id, wizard_uid), pending_wizard in activity_graph_wizards.items()
        if wizard_chat_id == msg.chat.id
        and pending_wizard.get('step') in reply_steps
        and pending_wizard.get('reply_prompt_message_id') is not None
    ]
    if not wizard and not waiting_for_reply:
        return False
    text = msg.text.strip()
    if wizard and wizard.get('step') in reply_steps and text.casefold() in {'отмена', '!отмена', 'cancel'}:
        activity_graph_wizards.pop(key, None)
        await msg.answer('Создание пресета отменено.')
        return True

    reply_owner_id = None
    if msg.reply_to_message and msg.reply_to_message.from_user and msg.reply_to_message.from_user.is_bot:
        reply_owner_id = next(
            (
                pending_uid for pending_uid, pending_wizard in waiting_for_reply
                if pending_wizard.get('reply_prompt_message_id') == msg.reply_to_message.message_id
            ),
            None,
        )
    if reply_owner_id is not None and reply_owner_id != msg.from_user.id:
        error_message = await msg.answer("❌ Это сообщение ожидает ответ от другого пользователя.")
        spawn_background_task(delete_message_after(error_message, 3))
        return True
    if reply_owner_id != msg.from_user.id:
        if not wizard or wizard.get('step') not in reply_steps:
            return False
        return False

    if wizard.get('step') == 'simple_color':
        if not re.fullmatch(r'#[0-9a-fA-F]{6}', text):
            await msg.answer(
                "Нужен один HEX-цвет в формате <code>#RRGGBB</code>, например <code>#5865F2</code>."
            )
            return True
        wizard.pop('reply_prompt_message_id', None)
        colors, theme_id = derive_graph_colors(text)
        wizard['settings']['colors'] = colors
        wizard['settings']['theme_id'] = theme_id
        if wizard.pop('editing_setting', None) == 'theme':
            wizard['step'] = 'preview'
            await graph_render_preview(msg, msg.from_user.id, msg.chat.id, wizard['settings'])
            return True
        wizard['step'] = 'font'
        await msg.answer(
            f"Цвет фона принят. Определено оформление: "
            f"{'светлое' if theme_id == 'light_default' else 'тёмное'}. "
            "Остальные цвета подобраны автоматически. Выберите шрифт:",
            reply_markup=graph_font_keyboard(msg.from_user.id),
        )
        return True

    if wizard.get('step') == 'colors':
        colors = text.split()
        if len(colors) != 6 or any(not re.fullmatch(r'#[0-9a-fA-F]{6}', color) for color in colors):
            await msg.answer(
                "Нужно указать ровно 6 HEX-цветов вида <code>#a1b2c3</code>, разделённых пробелами."
            )
            return True
        wizard.pop('reply_prompt_message_id', None)
        wizard['settings']['colors'] = colors
        brightness = sum(int(colors[0][index:index + 2], 16) for index in (1, 3, 5))
        wizard['settings']['theme_id'] = 'light_default' if brightness > 3 * 127 else 'dark_default'
        if wizard.pop('editing_setting', None) == 'theme':
            wizard['step'] = 'preview'
            await graph_render_preview(msg, msg.from_user.id, msg.chat.id, wizard['settings'])
            return True
        wizard['step'] = 'font'
        await msg.answer("Цвета сохранены. Выберите шрифт:", reply_markup=graph_font_keyboard(msg.from_user.id))
        return True

    if wizard.get('step') == 'name':
        if not text:
            await msg.answer('Название пресета не может быть пустым.')
            return True
        wizard.pop('reply_prompt_message_id', None)
        wizard['pending_name'] = text[:40]
        wizard['step'] = 'scope'
        chat_name = html.escape(str(msg.chat.title or 'этот чат'), quote=False)
        await msg.answer(
            f"Создать пресет на все чаты или только на этот ({chat_name})?",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [graph_wizard_button('🌐 На все чаты', 'scope', msg.from_user.id, 'global')],
                [graph_wizard_button('💬 Только на этот чат', 'scope', msg.from_user.id, 'chat')],
            ]),
        )
        return True
    return False


async def who_are_you(msg: Message, args: str = None, cmd_name: str = 'кто ты'):
    if not await require_access(msg, cmd_name, 0, example='!кто ты @user'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    tid = None
    target_arg = None
    if args:
        stripped_args = args.strip()
        mention_span = get_target_mention_span(msg, stripped_args)
        first_arg = stripped_args.split(maxsplit=1)[0]
        target_arg = (
            stripped_args if mention_span
            else first_arg if first_arg.startswith(('@', 'id:'))
            else stripped_args
        )
    if target_arg and has_explicit_target(msg, target_arg):
        tid = await get_target(msg, target_arg)
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

    if not tid:
        return await msg.answer(ui_error("Не указан пользователь", "Укажи пользователя через @user или ответь на сообщение пользователя.", "!кто ты @user"), disable_web_page_preview=True)

    u = storage.peek_user(msg.chat.id, tid)
    text = build_profile_text(msg.chat.id, tid, u, show_last_active=False)

    graph = await create_graph_async(msg.chat.id, tid, 30)
    await send_profile(msg, text, graph, 'profile_graph.png')


async def who_admin(msg: Message):
    if not await require_access(msg, 'кто админ', 0, example='!кто админ'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    admins = []
    storage.load_chat_users(msg.chat.id)
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
            status = get_user_status(uid, user_data)
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

    await send_chunked_text(msg, txt)


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
    if msg.reply_to_message and msg.reply_to_message.from_user:
        return await msg.answer(f"🆔 <code>{msg.reply_to_message.from_user.id}</code>")
    if msg.reply_to_message and msg.reply_to_message.sender_chat:
        return await msg.answer(f"🆔 Канал-отправитель: <code>{msg.reply_to_message.sender_chat.id}</code>")
    await msg.answer(f"🆔 Ваш: <code>{msg.from_user.id}</code>\n💬 Чат: <code>{msg.chat.id}</code>")


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

    storage.load_chat_users(msg.chat.id)
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

    await send_chunked_text(msg, txt)


async def cmd_chat_stats(msg: Message, cmd_name: str = 'статистика чата'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!статистика чата'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    chat_users = storage.load_chat_users(msg.chat.id)
    total_msgs = sum(d.get('messages_count', 0) for d in chat_users.values())
    total_rep = sum(d.get('reputation', 0) for d in chat_users.values())
    moders = sum(1 for d in chat_users.values() if d.get('rank', 0) >= 1)
    marriages = len(storage.get_chat(msg.chat.id, 'marriages'))
    await msg.answer(
        f"📊 <b>Статистика чата</b>\n\n👥 Пользователей: {len(chat_users)}\n👑 Модераторов: {moders}\n💬 Сообщений: {total_msgs}\n⭐ Репутации: {total_rep}\n💍 Браков: {marriages}")


async def cmd_stats(msg: Message, args: str = "", cmd_name: str = 'статистика'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!статистика'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    parts = args.split()

    days = 7
    if parts and parts[0].isdigit():
        days = int(parts[0])
        target_parts = parts[1:]
    else:
        target_parts = parts

    tid = msg.from_user.id
    target_arg = ' '.join(target_parts).strip()
    if target_parts and (
        target_parts[0].startswith(('@', 'id:'))
        or get_target_mention_span(msg, target_parts[0])
    ):
        target_arg = target_parts[0]
    if target_arg:
        target = await get_target(msg, target_arg)
        if not target:
            return await msg.answer(
                ui_error("Пользователь не найден", f"Не удалось найти пользователя «{target_arg}».", "!статистика @user"),
                disable_web_page_preview=True,
            )
        tid = target
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

    u = storage.get_user(msg.chat.id, tid)
    act = u.get('activity', {})
    total_msgs = sum(d.get('messages', 0) for d in act.values())
    total_rep = sum(d.get('reputation', 0) for d in act.values())

    info = (
        f"📊 <b>{mention(msg.chat.id, tid)}</b>\n\n"
        f"📝 Сообщений: {total_msgs}\n"
        f"⭐ Репутации: +{total_rep}\n"
        f" TTT: {u.get('ttt_wins', 0)}/{u.get('ttt_games', 0)}\n"
        f"🎯 КНБ: {u.get('rps_wins', 0)}/{u.get('rps_games', 0)}\n"
        f"🥊 Дуэли: {u.get('duel_wins', 0)}/{u.get('duel_games', 0)}"
    )

    graph = await create_graph_async(msg.chat.id, tid, days)
    if graph:
        await msg.answer_photo(BufferedInputFile(graph.read(), 'graph.png'), caption=info)
    else:
        await msg.answer(info, disable_web_page_preview=True)


# ==================== Модерация ====================

def log_moderation(
    chat_id: int,
    actor_id: Optional[int],
    target_id: int,
    action: str,
    reason: str = '',
    duration: Optional[Union[int, float]] = None,
    target_label: Optional[str] = None,
) -> None:
    now = time.time()
    logs = storage.data.setdefault('moderation_log', {})
    if not isinstance(logs, dict):
        logger.warning("Некорректное хранилище журнала модерации; создаю новое")
        logs = {}
        storage.data['moderation_log'] = logs

    chat_key = str(chat_id)
    entries = logs.get(chat_key, [])
    if not isinstance(entries, list):
        logger.warning("Некорректный журнал модерации в чате %s; создаю новый", chat_id)
        entries = []

    cutoff = now - 90 * 86400
    valid_entries = [
        entry for entry in entries
        if isinstance(entry, dict)
        and isinstance(entry.get('ts'), (int, float))
        and entry['ts'] > cutoff
    ]
    valid_entries.append({
        'ts': now,
        'actor': actor_id,
        'target': target_id,
        'action': str(action)[:32],
        'reason': str(reason or '')[:500],
        'duration': duration,
        'target_label': str(target_label)[:100] if target_label else None,
    })
    logs[chat_key] = valid_entries[-500:]
    storage.mark_dirty()


CHAT_PERMISSION_FIELDS = (
    'can_send_messages', 'can_send_audios', 'can_send_documents', 'can_send_photos',
    'can_send_videos', 'can_send_video_notes', 'can_send_voice_notes',
    'can_send_polls', 'can_send_other_messages', 'can_add_web_page_previews',
    'can_change_info', 'can_invite_users', 'can_pin_messages', 'can_manage_topics',
)


def snapshot_chat_permissions(permissions: Optional[ChatPermissions]) -> Optional[dict]:
    if permissions is None:
        return None
    snapshot = {
        field: getattr(permissions, field)
        for field in CHAT_PERMISSION_FIELDS
        if getattr(permissions, field, None) is not None
    }
    return snapshot or None


async def freeze_chat(chat_id: int, duration_seconds: int) -> bool:
    if await bot_can(chat_id, 'can_restrict_members') is not True:
        return False
    settings = storage.get_chat_settings(chat_id)
    previous_state = settings.get('chat_freeze')
    if isinstance(previous_state, dict) and isinstance(previous_state.get('permissions'), dict):
        saved_permissions = previous_state['permissions']
    else:
        try:
            chat = await bot.get_chat(chat_id)
        except (TelegramAPIError, asyncio.TimeoutError) as exc:
            logger.warning("Не удалось получить разрешения чата %s для заморозки: %s", chat_id, exc)
            return False
        saved_permissions = snapshot_chat_permissions(getattr(chat, 'permissions', None))
        if not saved_permissions:
            logger.error("Telegram не вернул исходные разрешения чата %s; заморозка отменена", chat_id)
            return False

    now = time.time()
    previous_expiry = (
        previous_state.get('expires_at')
        if isinstance(previous_state, dict) and isinstance(previous_state.get('expires_at'), (int, float))
        else 0
    )
    settings['chat_freeze'] = {
        'permissions': dict(saved_permissions),
        'expires_at': max(previous_expiry, now + duration_seconds),
        'next_retry_at': 0,
    }
    storage.invalidate_chat_settings_cache(chat_id)
    storage.mark_dirty()
    await storage.save()
    try:
        await bot.set_chat_permissions(
            chat_id,
            ChatPermissions(can_send_messages=False),
        )
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        if isinstance(previous_state, dict):
            settings['chat_freeze'] = previous_state
        else:
            settings.pop('chat_freeze', None)
        storage.invalidate_chat_settings_cache(chat_id)
        storage.mark_dirty()
        await storage.save()
        logger.warning("Не удалось заморозить чат %s: %s", chat_id, exc)
        return False
    return True


async def restore_chat_freeze(chat_id: int) -> bool:
    settings = storage.get_chat_settings(chat_id)
    state = settings.get('chat_freeze')
    if not isinstance(state, dict):
        return False
    permissions = state.get('permissions')
    if not isinstance(permissions, dict) or not permissions:
        logger.error("Некорректные сохранённые разрешения замороженного чата %s", chat_id)
        return False
    if await bot_can(chat_id, 'can_restrict_members') is not True:
        state['next_retry_at'] = time.time() + MUTE_CHECK_INTERVAL
        storage.mark_dirty()
        await storage.save()
        return False
    try:
        await bot.set_chat_permissions(chat_id, ChatPermissions(**permissions))
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        state['next_retry_at'] = time.time() + MUTE_CHECK_INTERVAL
        storage.mark_dirty()
        await storage.save()
        logger.warning("Не удалось восстановить исходные разрешения чата %s: %s", chat_id, exc)
        return False
    settings.pop('chat_freeze', None)
    storage.invalidate_chat_settings_cache(chat_id)
    storage.mark_dirty()
    await storage.save()
    return True


async def require_chat_configuration_access(msg: Message, cmd_name: str, example: str) -> bool:
    if not await require_telegram_admin(msg):
        return False
    return await require_access(
        msg, cmd_name, 5, title='Недостаточно прав',
        message='Настраивать эту функцию могут администраторы ранга 5.',
        example=example,
    )


def normalize_filter_domain(value: str) -> Optional[str]:
    candidate = value.strip()
    if not candidate:
        return None
    if not candidate.lower().startswith(('http://', 'https://')):
        candidate = f'https://{candidate}'
    try:
        parsed = urlsplit(candidate)
        if parsed.port is not None:
            return None
    except ValueError:
        return None
    hostname = (parsed.hostname or '').casefold().rstrip('.')
    if parsed.path not in ('', '/') or parsed.query or parsed.fragment or parsed.username or parsed.password:
        return None
    if not re.fullmatch(r'(?=.{1,253}$)(?:[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?\.)+[a-z]{2,63}', hostname):
        return None
    return hostname


async def send_moderation_notice(msg: Message, text: str, **kwargs) -> Message:
    notice = await msg.answer(text, **kwargs)
    seconds = storage.get_chat_settings(msg.chat.id).get('moderation_notice_delete_seconds', 0)
    if isinstance(seconds, int) and 1 <= seconds <= MODERATION_NOTICE_DELETE_MAX_SECONDS:
        spawn_background_task(delete_message_after(notice, seconds))
        spawn_background_task(delete_message_after(msg, seconds))
    return notice


async def cmd_moderation_auto_delete(msg: Message, args: str = '', cmd_name: str = 'автоудаление'):
    if not await require_chat_configuration_access(msg, cmd_name, '!автоудаление 30'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    settings = storage.get_chat_settings(msg.chat.id)
    raw = args.strip()
    if not raw:
        seconds = settings.get('moderation_notice_delete_seconds', 0)
        if not isinstance(seconds, int) or not 0 <= seconds <= MODERATION_NOTICE_DELETE_MAX_SECONDS:
            logger.warning("Некорректный срок автоудаления в чате %s: %r", msg.chat.id, seconds)
            return await msg.answer("❌ Настройка автоудаления повреждена.")
        return await msg.answer(
            f"🧹 Автоудаление ответов и команд модерации: <b>{seconds} сек.</b> "
            "(0 — выключено)."
        )
    if not raw.isdigit():
        return await msg.answer("❌ Укажите число секунд от 0 до 300.")
    seconds = int(raw)
    if not 0 <= seconds <= MODERATION_NOTICE_DELETE_MAX_SECONDS:
        return await msg.answer("❌ Допустимый срок автоудаления: от 0 до 300 секунд.")
    settings['moderation_notice_delete_seconds'] = seconds
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    await msg.answer(
        "✅ Автоудаление выключено." if seconds == 0
        else f"✅ Ответы и команды модерации будут удаляться через {seconds} сек."
    )


async def cmd_moderation_log(msg: Message, cmd_name: str = 'лог'):
    if not await require_access(
        msg, cmd_name, 1, title='Недостаточно прав',
        message='Журнал модерации доступен модераторам и выше.',
        example='!лог'
    ):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    logs = storage.data.get('moderation_log', {})
    if not isinstance(logs, dict):
        logger.error("Некорректное хранилище журнала модерации")
        return await msg.answer("❌ Не удалось прочитать журнал модерации.")
    entries = logs.get(str(msg.chat.id), [])
    await send_moderation_history(msg, entries, title='🧾 Последние действия модерации')


async def cmd_moderation_stats(msg: Message, cmd_name: str = 'модстат'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(
        msg, cmd_name, 1, title='Недостаточно прав',
        message='Статистика модерации доступна модераторам и выше.',
        example='!модстат'
    ):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    logs = storage.data.get('moderation_log', {})
    entries = logs.get(str(msg.chat.id), []) if isinstance(logs, dict) else None
    if not isinstance(entries, list):
        logger.error("Некорректный журнал модерации при подсчёте статистики чата %s", msg.chat.id)
        return await msg.answer("❌ Не удалось прочитать журнал модерации.")
    cutoff = time.time() - 7 * 86400
    counts = defaultdict(int)
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get('ts'), (int, float)):
            continue
        if entry['ts'] >= cutoff and isinstance(entry.get('actor'), int):
            counts[entry['actor']] += 1
    if not counts:
        return await msg.answer("📊 За последние 7 дней действий модерации нет.")
    ranked = sorted(counts.items(), key=lambda item: (-item[1], item[0]))[:20]
    lines = ["📊 <b>Действия модерации за 7 дней</b>", UI_LINE]
    lines.extend(
        f"{index}. {mention(msg.chat.id, actor_id)} — <b>{count}</b>"
        for index, (actor_id, count) in enumerate(ranked, start=1)
    )
    await send_chunked_text(msg, '\n'.join(lines))


async def cmd_reason_templates(msg: Message, args: str = '', cmd_name: str = 'причины'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(
        msg, cmd_name, 2, title='Недостаточно прав',
        message='Настраивать шаблоны причин могут модераторы ранга 2+.',
        example='!причины add флуд',
    ):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    settings = storage.get_chat_settings(msg.chat.id)
    templates = settings.get('reason_templates', [])
    if not isinstance(templates, list) or not all(isinstance(item, str) for item in templates):
        logger.error("Некорректные шаблоны причин в чате %s", msg.chat.id)
        return await msg.answer("❌ Не удалось прочитать шаблоны причин.")

    parts = args.strip().split(maxsplit=1)
    if not parts:
        lines = ["📝 <b>Шаблоны причин</b>", UI_LINE]
        lines.extend(
            f"<code>{index}</code> — {html.escape(reason, quote=False)}"
            for index, reason in enumerate(templates, start=1)
        )
        if not templates:
            lines.append("Список пуст.")
        lines.append("\nДобавить: <code>!причины add текст</code>; удалить: <code>!причины remove номер</code>.")
        lines.append("Применить: <code>!пред @user номер</code> (по умолчанию срок предупреждения).")
        return await send_chunked_text(msg, '\n'.join(lines))

    action = parts[0].casefold()
    if action == 'add':
        if len(parts) != 2 or not parts[1].strip() or len(parts[1].strip()) > 120:
            return await msg.answer("❌ Укажите шаблон длиной от 1 до 120 символов.")
        reason = parts[1].strip()
        if len(templates) >= REASON_TEMPLATE_LIMIT:
            return await msg.answer(f"❌ Можно настроить не больше {REASON_TEMPLATE_LIMIT} шаблонов.")
        if reason.casefold() in {item.casefold() for item in templates}:
            return await msg.answer("ℹ️ Такой шаблон уже существует.")
        templates.append(reason)
        result = "✅ Шаблон причины добавлен."
    elif action == 'remove':
        if len(parts) != 2 or not parts[1].isdigit():
            return await msg.answer("❌ Формат удаления: <code>!причины remove номер</code>.")
        index = int(parts[1])
        if not 1 <= index <= len(templates):
            return await msg.answer("❌ Шаблон с таким номером не найден.")
        templates.pop(index - 1)
        result = "✅ Шаблон причины удалён; номера оставшихся шаблонов изменились."
    else:
        return await msg.answer("❌ Используйте <code>add текст</code> или <code>remove номер</code>.")

    settings['reason_templates'] = templates
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    await msg.answer(result)


async def cmd_join_requests(msg: Message, args: str = '', cmd_name: str = 'заявки'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(
        msg, cmd_name, 5, title='Недостаточно прав',
        message='Настраивать обработку заявок могут администраторы ранга 5.',
        example='!заявки admin'
    ):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    raw = strip_command_prefix(msg.text or '', msg.chat.id)
    parts = raw.split(maxsplit=1)
    mode = parts[1].strip().casefold() if len(parts) > 1 else ''
    settings = storage.get_chat_settings(msg.chat.id)
    if not mode:
        current = settings.get('join_request_mode', 'off')
        return await msg.answer(
            f"📨 Режим заявок: <b>{html.escape(str(current), quote=False)}</b>\n"
            "Варианты: <code>off</code>, <code>on</code> (автоодобрение), "
            "<code>admin</code> (решение кнопками Telegram-администраторов)."
        )
    if mode not in {'off', 'on', 'admin'}:
        return await msg.answer("❌ Выберите режим: <code>off</code>, <code>on</code> или <code>admin</code>.")
    if mode != 'off' and not await require_bot_right(
        msg, 'can_invite_users', 'одобрения заявок на вступление'
    ):
        return

    settings['join_request_mode'] = mode
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    descriptions = {
        'off': 'обработка выключена',
        'on': 'заявки будут одобряться автоматически',
        'admin': 'Telegram-администраторы смогут одобрять или отклонять заявки кнопками',
    }
    await msg.answer(f"✅ Режим заявок изменён: {descriptions[mode]}.")


async def cmd_filters(msg: Message, args: str = '', cmd_name: str = 'фильтр'):
    if not await require_chat_configuration_access(msg, cmd_name, '!фильтр слово add реклама'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    settings = storage.get_chat_settings(msg.chat.id)
    filters = settings.get('content_filters', {})
    if not isinstance(filters, dict):
        logger.error("Некорректные фильтры содержимого в чате %s", msg.chat.id)
        return await msg.answer("❌ Не удалось прочитать настройки фильтров.")

    parts = args.strip().split(maxsplit=2)
    if not parts:
        lines = ["🧹 <b>Фильтры содержимого</b>", UI_LINE]
        for key, title in (
            ('stop_words', 'Стоп-слова'),
            ('blocked_types', 'Запрещённые типы'),
            ('allow_domains', 'Разрешённые домены'),
            ('block_domains', 'Заблокированные домены'),
        ):
            values = filters.get(key, [])
            if not isinstance(values, list):
                logger.warning("Некорректный список %s в чате %s", key, msg.chat.id)
                return await msg.answer("❌ Не удалось прочитать настройки фильтров.")
            shown = ', '.join(html.escape(str(value), quote=False) for value in values) or 'нет'
            lines.append(f"\n<b>{title}:</b> {shown}")
        lines.extend((
            "\n\n<code>!фильтр слово add|remove текст</code>",
            "<code>!фильтр тип voice|video|video_note|sticker|forward|audio|document|photo on|off</code>",
            "<code>!фильтр домен allow|block|remove example.com</code>",
        ))
        return await send_chunked_text(msg, '\n'.join(lines))

    category = parts[0].casefold()
    if category == 'слово':
        if len(parts) < 3 or parts[1].casefold() not in {'add', 'remove'}:
            return await msg.answer("❌ Формат: <code>!фильтр слово add|remove текст</code>")
        word = parts[2].strip()
        if not word or len(word) > 64:
            return await msg.answer("❌ Стоп-слово должно содержать от 1 до 64 символов.")
        values = filters.get('stop_words', [])
        if not isinstance(values, list):
            return await msg.answer("❌ Список стоп-слов повреждён; обратитесь к владельцу бота.")
        values = [value for value in values if isinstance(value, str)]
        if parts[1].casefold() == 'add':
            if not await require_bot_right(msg, 'can_delete_messages', 'удаления сообщений со стоп-словами'):
                return
            if word.casefold() in {value.casefold() for value in values}:
                return await msg.answer("ℹ️ Это стоп-слово уже добавлено.")
            if len(values) >= FILTER_LIST_LIMIT:
                return await msg.answer(f"❌ Можно настроить не больше {FILTER_LIST_LIMIT} стоп-слов.")
            values.append(word)
            result = "✅ Стоп-слово добавлено."
        else:
            remaining = [value for value in values if value.casefold() != word.casefold()]
            if len(remaining) == len(values):
                return await msg.answer("ℹ️ Такого стоп-слова нет в списке.")
            values = remaining
            result = "✅ Стоп-слово удалено."
        filters['stop_words'] = values
    elif category == 'тип':
        if len(parts) != 3:
            return await msg.answer("❌ Формат: <code>!фильтр тип voice|video|video_note|sticker|forward|audio|document|photo on|off</code>")
        content_type = parts[1].casefold()
        enabled = parts[2].casefold()
        allowed_types = {'voice', 'video', 'video_note', 'sticker', 'forward', 'audio', 'document', 'photo'}
        if content_type not in allowed_types or enabled not in {'on', 'off'}:
            return await msg.answer("❌ Укажите поддерживаемый тип и состояние <code>on</code> или <code>off</code>.")
        values = filters.get('blocked_types', [])
        if not isinstance(values, list):
            return await msg.answer("❌ Список типов сообщений повреждён; обратитесь к владельцу бота.")
        values = [value for value in values if isinstance(value, str) and value in allowed_types]
        if enabled == 'on':
            if not await require_bot_right(msg, 'can_delete_messages', 'удаления сообщений запрещённого типа'):
                return
            if content_type not in values:
                values.append(content_type)
            result = f"✅ Запрет типа <code>{content_type}</code> включён."
        else:
            values = [value for value in values if value != content_type]
            result = f"✅ Запрет типа <code>{content_type}</code> выключен."
        filters['blocked_types'] = values
    elif category == 'домен':
        if len(parts) != 3 or parts[1].casefold() not in {'allow', 'block', 'remove'}:
            return await msg.answer("❌ Формат: <code>!фильтр домен allow|block|remove example.com</code>")
        domain = normalize_filter_domain(parts[2])
        if not domain:
            return await msg.answer("❌ Укажите корректный домен без пути, например <code>example.com</code>.")
        allow = filters.get('allow_domains', [])
        block = filters.get('block_domains', [])
        if not isinstance(allow, list) or not isinstance(block, list):
            return await msg.answer("❌ Список доменов повреждён; обратитесь к владельцу бота.")
        allow = [value for value in allow if isinstance(value, str)]
        block = [value for value in block if isinstance(value, str)]
        action = parts[1].casefold()
        if action == 'remove':
            allow = [value for value in allow if value != domain]
            block = [value for value in block if value != domain]
            result = f"✅ Домен <code>{html.escape(domain, quote=False)}</code> удалён из списков."
        elif action == 'allow':
            if domain not in allow and len(allow) >= FILTER_LIST_LIMIT:
                return await msg.answer(f"❌ Можно настроить не больше {FILTER_LIST_LIMIT} разрешённых доменов.")
            if domain not in allow:
                allow.append(domain)
            result = f"✅ Домен <code>{html.escape(domain, quote=False)}</code> разрешён."
        else:
            if not await require_bot_right(msg, 'can_delete_messages', 'удаления сообщений с запрещёнными доменами'):
                return
            if domain not in block and len(block) >= FILTER_LIST_LIMIT:
                return await msg.answer(f"❌ Можно настроить не больше {FILTER_LIST_LIMIT} заблокированных доменов.")
            if domain not in block:
                block.append(domain)
            result = f"✅ Домен <code>{html.escape(domain, quote=False)}</code> заблокирован."
        filters['allow_domains'] = allow
        filters['block_domains'] = block
    else:
        return await msg.answer("❌ Разделы фильтров: <code>слово</code>, <code>тип</code>, <code>домен</code>.")

    settings['content_filters'] = filters
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    await msg.answer(result, disable_web_page_preview=True)


async def cmd_captcha(msg: Message, args: str = '', cmd_name: str = 'капча'):
    if not await require_chat_configuration_access(msg, cmd_name, '!капча on'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    settings = storage.get_chat_settings(msg.chat.id)
    mode = args.strip().casefold()
    if not mode:
        enabled = settings.get('captcha_enabled', False)
        raid = settings.get('raid_mode', False)
        return await msg.answer(
            f"🧩 Капча: <b>{'включена' if enabled else 'выключена'}</b>; "
            f"режим рейда: <b>{'включён' if raid else 'выключен'}</b>."
        )
    if mode not in {'on', 'off'}:
        return await msg.answer("❌ Используйте <code>!капча on</code> или <code>!капча off</code>.")
    if mode == 'on' and not await require_bot_right(msg, 'can_restrict_members', 'карантина новичков'):
        return
    settings['captcha_enabled'] = mode == 'on'
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"✅ Капча для новых участников {'включена' if mode == 'on' else 'выключена'}.")


async def cmd_raid_mode(msg: Message, args: str = '', cmd_name: str = 'рейд'):
    if not await require_chat_configuration_access(msg, cmd_name, '!рейд on'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    settings = storage.get_chat_settings(msg.chat.id)
    mode = args.strip().casefold()
    if not mode:
        enabled = settings.get('raid_mode', False)
        return await msg.answer(
            f"🚨 Режим рейда <b>{'включён' if enabled else 'выключен'}</b>. "
            "В режиме рейда для новых участников действует капча."
        )
    if mode not in {'on', 'off'}:
        return await msg.answer("❌ Используйте <code>!рейд on</code> или <code>!рейд off</code>.")
    if mode == 'on' and not await require_bot_right(msg, 'can_restrict_members', 'карантина новичков'):
        return
    settings['raid_mode'] = mode == 'on'
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    await msg.answer(
        f"✅ Режим рейда {'включён' if mode == 'on' else 'выключен'}. "
        "При включении новые участники должны пройти капчу."
    )


async def cmd_channel_autohide(msg: Message, args: str = '', cmd_name: str = 'каналы'):
    if not await require_chat_configuration_access(msg, cmd_name, '!каналы on'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    settings = storage.get_chat_settings(msg.chat.id)
    mode = args.strip().casefold()
    if not mode:
        enabled = settings.get('hide_channel_messages', False)
        return await msg.answer(
            f"📢 Автоудаление сообщений от каналов: <b>{'включено' if enabled else 'выключено'}</b>."
        )
    if mode not in {'on', 'off'}:
        return await msg.answer("❌ Используйте <code>!каналы on</code> или <code>!каналы off</code>.")
    if mode == 'on' and not await require_bot_right(msg, 'can_delete_messages', 'удаления сообщений от каналов'):
        return
    settings['hide_channel_messages'] = mode == 'on'
    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    await msg.answer(
        f"✅ Автоудаление сообщений от каналов {'включено' if mode == 'on' else 'выключено'}."
    )


async def cmd_freeze_chat(msg: Message, args: str = '', cmd_name: str = 'закрыть'):
    if not await require_chat_configuration_access(msg, cmd_name, '!закрыть 10м'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    raw_duration = args.strip()
    if not raw_duration:
        return await msg.answer("❌ Укажите срок заморозки, например <code>!закрыть 10м</code>.")
    duration_minutes = parse_time(raw_duration)
    if not 1 <= duration_minutes <= MAX_CHAT_FREEZE_SECONDS // 60:
        return await msg.answer("❌ Укажите срок заморозки от 1 минуты до 24 часов, например <code>!закрыть 10м</code>.")
    if not await require_bot_right(msg, 'can_restrict_members', 'заморозки чата'):
        return
    if not await freeze_chat(msg.chat.id, duration_minutes * 60):
        return await msg.answer(
            "❌ Не удалось заморозить чат. Проверьте права бота и доступность исходных разрешений."
        )
    await msg.answer(
        f"🔒 Чат заморожен на {html.escape(format_mute_duration(duration_minutes), quote=False)}. "
        "Исходные разрешения будут восстановлены автоматически."
    )


async def cmd_unfreeze_chat(msg: Message, cmd_name: str = 'открыть'):
    if not await require_chat_configuration_access(msg, cmd_name, '!открыть'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    settings = storage.get_chat_settings(msg.chat.id)
    if not isinstance(settings.get('chat_freeze'), dict):
        return await msg.answer("ℹ️ Чат сейчас не заморожен.")
    if not await require_bot_right(msg, 'can_restrict_members', 'восстановления разрешений чата'):
        return
    if not await restore_chat_freeze(msg.chat.id):
        return await msg.answer("❌ Не удалось восстановить разрешения чата; бот повторит попытку автоматически.")
    await msg.answer("🔓 Чат открыт; исходные разрешения восстановлены.")


async def cmd_moderation_history(msg: Message, cmd_name: str = 'история'):
    if not await require_access(
        msg, cmd_name, 1, title='Недостаточно прав',
        message='История модерации доступна модераторам и выше.',
        example='!история @user'
    ):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    parts = (msg.text or '').split(maxsplit=1)
    target_arg = parts[1] if len(parts) > 1 else None
    target_id = None
    if target_arg and has_explicit_target(msg, target_arg):
        target_id = await get_target(msg, target_arg)
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        target_id = msg.reply_to_message.from_user.id
    if not target_id:
        return await msg.answer(
            ui_error(
                "Не указан пользователь",
                "Укажите пользователя или ответьте на его сообщение.",
                "!история @user"
            ),
            disable_web_page_preview=True,
        )

    logs = storage.data.get('moderation_log', {})
    if not isinstance(logs, dict):
        logger.error("Некорректное хранилище журнала модерации")
        return await msg.answer("❌ Не удалось прочитать журнал модерации.")
    entries = logs.get(str(msg.chat.id), [])
    if not isinstance(entries, list):
        logger.warning("Некорректный журнал модерации в чате %s", msg.chat.id)
        return await msg.answer("❌ Не удалось прочитать журнал модерации.")
    entries = [
        entry for entry in entries
        if isinstance(entry, dict) and entry.get('target') == target_id
    ]
    await send_moderation_history(
        msg, entries, title=f"🧾 История модерации {mention(msg.chat.id, target_id)}"
    )


async def send_moderation_history(msg: Message, entries: Any, title: str):
    if not isinstance(entries, list):
        logger.warning("Некорректный журнал модерации в чате %s", msg.chat.id)
        return await msg.answer("❌ Не удалось прочитать журнал модерации.")
    cutoff = time.time() - 90 * 86400
    recent = [
        entry for entry in entries
        if isinstance(entry, dict)
        and isinstance(entry.get('ts'), (int, float))
        and entry['ts'] > cutoff
    ]
    recent.sort(key=lambda entry: entry['ts'], reverse=True)
    recent = recent[:20]
    if not recent:
        return await msg.answer(f"{title}\n\nЗа последние 90 дней записей нет.")

    action_names = {
        'mute': 'мут',
        'unmute': 'размут',
        'ban': 'бан',
        'unban': 'разбан',
        'kick': 'кик',
        'kick_failed': 'неполный кик',
        'ban_channel': 'бан канала',
        'unban_channel': 'разбан канала',
        'warn': 'предупреждение',
        'unwarn': 'снятие предупреждения',
        'auto_mute': 'автоматический мут',
        'auto_ban': 'автоматический бан',
    }
    lines = [title, UI_LINE]
    for entry in recent:
        ts = datetime.fromtimestamp(entry['ts']).strftime('%d.%m.%Y %H:%M')
        actor_id = entry.get('actor')
        actor_text = mention(msg.chat.id, actor_id) if isinstance(actor_id, int) else 'автоматическая система'
        target_id = entry.get('target')
        target_label = entry.get('target_label')
        target_text = (
            html.escape(str(target_label), quote=False)
            if target_label
            else mention(msg.chat.id, target_id) if isinstance(target_id, int)
            else html.escape(str(target_id), quote=False)
        )
        action = html.escape(
            action_names.get(str(entry.get('action')), str(entry.get('action') or 'действие')),
            quote=False,
        )
        reason = html.escape(str(entry.get('reason') or 'Без причины')[:200], quote=False)
        duration = entry.get('duration')
        duration_text = ''
        if isinstance(duration, (int, float)) and duration > 0:
            duration_text = f" — {html.escape(format_mute_duration(max(1, round(duration / 60))), quote=False)}"
        lines.append(
            f"\n<b>{ts}</b> · {action}: {target_text}{duration_text}\n"
            f"Кто: {actor_text} · Причина: {reason}"
        )
    await send_chunked_text(msg, '\n'.join(lines))

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
    if not await require_bot_right(msg, 'can_restrict_members', 'выдачи мута'):
        return

    text = msg.text.strip()
    parts = text.split(maxsplit=2)

    tid = None
    dur_text = ""
    reason = "Без причины"
    permanent = False

    target_arg = parts[1] if len(parts) > 1 else None
    target_mention = get_target_mention_span(msg, target_arg) if target_arg else None
    duration_in_reply = (
        msg.reply_to_message and msg.reply_to_message.from_user
        and target_arg and target_arg.isdigit()
        and int(target_arg) <= MAX_MUTE_MINUTES
    )
    if has_explicit_target(msg, target_arg) and not duration_in_reply:
        target_mention = get_target_mention_span(msg, target_arg)
        tid = await get_target(msg, target_arg)

        if not tid:
            return await msg.answer(
                ui_error(
                    "Пользователь не найден",
                    f"Не могу определить пользователя <code>{html.escape(str(target_arg), quote=False)}</code>. "
                    "Используйте @username, ID в формате id:123456, кликабельное упоминание Telegram или ответ на сообщение.",
                    "!мут @user 30м флуд"
                ),
                disable_web_page_preview=True,
            )

        if target_mention:
            rest = msg.text[target_mention[2]:].strip()
        else:
            rest = ' '.join(parts[2:]).strip()
        if rest:
            permanent, dur_text, reason = parse_mute_duration_and_reason(rest)
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        rest = text[len(parts[0]):].strip()
        if rest:
            permanent, dur_text, reason = parse_mute_duration_and_reason(rest)

    else:
        return await msg.answer(
            ui_error(
                "Не указаны аргументы",
                "Укажите пользователя или ответьте на его сообщение. Срок и причина необязательны.",
                "!мут @user 2ч флуд"
            )
        )

    if not tid:
        return await msg.answer(ui_error("Не удалось определить пользователя", "Не удалось понять, кого именно вы хотите замутить. Ответьте на сообщение пользователя или укажите @user.", "!мут @user 30м флуд"), disable_web_page_preview=True)

    if tid == msg.from_user.id:
        return await msg.answer(ui_error("Нельзя замутить себя", "Вы не можете ограничить доступ сами себе.", "!мут @user 30м флуд"), disable_web_page_preview=True)

    if not await require_target_not_telegram_admin(msg, tid):
        return

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
        else:
            mutes[:] = [mute for mute in mutes if mute.get('user_id') != tid]
        mutes.append({
            'user_id': tid,
            'expire_time': expire_time,
            'permanent': permanent,
            'issued_at': time.time(),
            'duration_minutes': dur if not permanent else None,
            'muted_by': msg.from_user.id,
            'reason': reason
        })
        log_moderation(
            msg.chat.id,
            msg.from_user.id,
            tid,
            'mute',
            reason,
            dur * 60 if not permanent else None,
        )

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
        except Exception:
            pass

        # Сообщение в чат
        await send_moderation_notice(
            msg,
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
    if not await require_bot_right(msg, 'can_restrict_members', 'снятия мута'):
        return

    text = msg.text.strip()
    parts = text.split(maxsplit=1)

    tid = None

    target_arg = parts[1] if len(parts) > 1 else None
    if has_explicit_target(msg, target_arg):
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
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

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

        await restore_chat_default_permissions(msg.chat.id, tid)
        log_moderation(
            msg.chat.id,
            msg.from_user.id,
            tid,
            'unmute',
            str(mute_info.get('reason') or '') if mute_info else '',
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
        await send_moderation_notice(
            msg,
            f"🔊 {mention(msg.chat.id, tid)} размучен{reason_text}",
            disable_web_page_preview=True,
        )

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"🔊 <b>Мут снят!</b>\n\n👮 Снял: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except Exception:
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
    if not await require_bot_right(msg, 'can_restrict_members', 'бана'):
        return

    text = msg.text.strip()
    parts = text.split(maxsplit=2)

    target_arg = parts[1] if len(parts) > 1 else None
    duration_in_reply = (
        msg.reply_to_message and msg.reply_to_message.from_user
        and target_arg and target_arg.isdigit()
        and int(target_arg) <= MAX_MUTE_MINUTES
    )
    sender_chat = (
        msg.reply_to_message.sender_chat
        if msg.reply_to_message and not has_explicit_target(msg, target_arg) and not duration_in_reply else None
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
            log_moderation(
                msg.chat.id,
                msg.from_user.id,
                sender_chat.id,
                'ban_channel',
                reason,
                target_label=sender_chat.title or sender_chat.username or str(sender_chat.id),
            )
            storage.mark_dirty()
            await storage.save()

            channel_name = html.escape(sender_chat.title or sender_chat.username or str(sender_chat.id), quote=False)
            await send_moderation_notice(
                msg,
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

    target_arg = parts[1] if len(parts) > 1 else None
    target_mention = get_target_mention_span(msg, target_arg) if target_arg else None
    if has_explicit_target(msg, target_arg) and not duration_in_reply:
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
            reason = ' '.join(parts[2:]).strip() or "Без причины"
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        reason = text[len(parts[0]):].strip() or "Без причины"

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

    permanent, duration_text, parsed_reason = parse_mute_duration_and_reason(reason)
    duration_minutes = parse_time(duration_text) if duration_text else 0
    if duration_text and duration_minutes < 1:
        return await msg.answer(
            "❌ Не удалось распознать срок временного бана. "
            "Пример: <code>!бан @user 2ч причина</code>."
        )
    if duration_text and duration_minutes > MAX_MUTE_MINUTES:
        return await msg.answer("❌ Срок временного бана должен быть не больше 1 года.")
    if permanent or duration_minutes > 0:
        reason = parsed_reason

    if tid == msg.from_user.id:
        return await msg.answer(ui_error("Нельзя забанить себя", "Вы не можете забанить самого себя.", "!бан @user реклама"), disable_web_page_preview=True)

    if not await require_target_not_telegram_admin(msg, tid):
        return

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer(ui_error("Анти-модерация", "Нельзя банить пользователя с равным или более высоким уровнем доступа.", "!бан @user реклама"), disable_web_page_preview=True)

    try:
        expires_at = (
            datetime.now() + timedelta(minutes=duration_minutes)
            if duration_minutes else None
        )
        ban_kwargs = {'revoke_messages': True}
        if expires_at:
            ban_kwargs['until_date'] = int(expires_at.timestamp())
        await bot.ban_chat_member(msg.chat.id, tid, **ban_kwargs)

        # Сохраняем в банлист
        chat_id_str = str(msg.chat.id)
        if 'banned_users' not in storage.data:
            storage.data['banned_users'] = {}
        if chat_id_str not in storage.data['banned_users']:
            storage.data['banned_users'][chat_id_str] = []
        banned_users = storage.data['banned_users'][chat_id_str]
        banned_users[:] = [
            ban for ban in banned_users
            if not isinstance(ban, dict) or ban.get('user_id') != tid
        ]
        banned_users.append({
            'user_id': tid,
            'banned_by': msg.from_user.id,
            'reason': reason,
            'date': time.time(),
            'expire_time': expires_at.timestamp() if expires_at else None,
            'permanent': expires_at is None,
            'duration_minutes': duration_minutes if duration_minutes else None,
        })

        log_moderation(
            msg.chat.id,
            msg.from_user.id,
            tid,
            'ban',
            reason,
            duration_minutes * 60 if duration_minutes else None,
        )
        storage.mark_dirty()
        await storage.save()

        # Сообщение в чат
        expiration_text = (
            f"\n⏱ Срок: {html.escape(format_mute_duration(duration_minutes), quote=False)}"
            if duration_minutes else ""
        )
        expiration_dm_text = (
            f"⏱ Срок: {html.escape(format_mute_duration(duration_minutes), quote=False)}\n"
            if duration_minutes else ""
        )
        await send_moderation_notice(
            msg,
            "🚫 <b>Бан выдан</b>\n"
            f"{UI_LINE}\n"
            f"👤 Пользователь: {mention(msg.chat.id, tid)}\n"
            f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
            f"{expiration_text}\n"
            f"👮 Забанил: {mention(msg.chat.id, msg.from_user.id)}",
            disable_web_page_preview=True
        )

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"🚫 <b>Вы были забанены!</b>\n\n"
                f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
                f"{expiration_dm_text}"
                f"👮 Забанил: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except Exception:
            pass

    except Exception as e:
        logger.exception("Не удалось забанить пользователя %s", tid)
        await msg.answer(f"❌ Не удалось забанить: {html.escape(str(e)[:250], quote=False)}")


async def cmd_kick(msg: Message, cmd_name: str = 'кик'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not await require_telegram_admin(msg):
        return
    if not await require_access(
        msg, cmd_name, 3, title='Недостаточно прав',
        message='Для кика нужен ранг 3+.',
        example='!кик @user флуд'
    ):
        return
    if not await require_bot_right(msg, 'can_restrict_members', 'кика'):
        return

    text = (msg.text or '').strip()
    parts = text.split(maxsplit=2)
    target_arg = parts[1] if len(parts) > 1 else None
    target_mention = get_target_mention_span(msg, target_arg) if target_arg else None
    if has_explicit_target(msg, target_arg):
        target_id = await get_target(msg, target_arg)
        if not target_id:
            return await msg.answer("❌ Не удалось найти пользователя для кика.")
        if target_mention:
            reason = text[target_mention[2]:].strip() or 'Без причины'
        else:
            reason = ' '.join(parts[2:]).strip() or 'Без причины'
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        target_id = msg.reply_to_message.from_user.id
        reason = text[len(parts[0]):].strip() or 'Без причины'
    else:
        return await msg.answer(
            ui_error("Не указан пользователь", "Укажите пользователя или ответьте на его сообщение.", "!кик @user причина"),
            disable_web_page_preview=True,
        )

    if target_id == msg.from_user.id:
        return await msg.answer("❌ Нельзя кикнуть себя.")
    if not await require_target_not_telegram_admin(msg, target_id):
        return
    if not check_anti_moderation(msg.from_user.id, target_id, msg.chat.id):
        return await msg.answer("❌ Нельзя кикнуть пользователя с равным или более высоким рангом.")

    try:
        target_member = await bot.get_chat_member(msg.chat.id, target_id)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning("Не удалось проверить участника %s перед киком в чате %s: %s", target_id, msg.chat.id, exc)
        return await msg.answer("❌ Не удалось проверить, состоит ли пользователь в чате. Попробуйте позже.")
    if target_member.status in ('left', 'kicked'):
        return await msg.answer("❌ Пользователь уже не состоит в чате.")

    try:
        await bot.ban_chat_member(msg.chat.id, target_id, revoke_messages=False)
    except Exception as exc:
        logger.exception("Не удалось начать кик пользователя %s", target_id)
        return await msg.answer(f"❌ Не удалось кикнуть пользователя: {html.escape(str(exc)[:250], quote=False)}")

    try:
        await bot.unban_chat_member(msg.chat.id, target_id, only_if_banned=True)
    except Exception as exc:
        logger.exception("Кик пользователя %s не завершён снятием временного бана", target_id)
        bans_by_chat = storage.data.setdefault('banned_users', {}).setdefault(str(msg.chat.id), [])
        bans_by_chat[:] = [
            ban for ban in bans_by_chat
            if not isinstance(ban, dict) or ban.get('user_id') != target_id
        ]
        bans_by_chat.append({
            'user_id': target_id,
            'banned_by': msg.from_user.id,
            'reason': f"Кик не завершен: {reason}",
            'date': time.time(),
            'permanent': True,
        })
        storage.mark_dirty()
        log_moderation(
            msg.chat.id, msg.from_user.id, target_id, 'kick_failed',
            f"{reason}; не удалось завершить снятием бана",
        )
        await storage.save()
        return await msg.answer(
            "⚠️ Пользователь заблокирован, но бот не смог снять блокировку после кика. "
            f"Снимите её вручную: {html.escape(str(exc)[:180], quote=False)}"
        )

    log_moderation(msg.chat.id, msg.from_user.id, target_id, 'kick', reason)
    await storage.save()
    await send_moderation_notice(
        msg,
        f"👢 {mention(msg.chat.id, target_id)} кикнут из чата.\n"
        f"📝 Причина: {html.escape(reason, quote=False)}",
        disable_web_page_preview=True,
    )


async def cmd_unban(msg: Message, cmd_name: str = 'разбан'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 3, title='Недостаточно прав', message='Для этой команды нужен ранг 3+.', example='!разбан @user'):
        return
    if not await require_bot_right(msg, 'can_restrict_members', 'снятия бана'):
        return

    text = msg.text.strip()
    parts = text.split(maxsplit=1)

    target_arg = parts[1] if len(parts) > 1 else None
    sender_chat = (
        msg.reply_to_message.sender_chat
        if msg.reply_to_message and not has_explicit_target(msg, target_arg) else None
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
            log_moderation(
                msg.chat.id,
                msg.from_user.id,
                sender_chat.id,
                'unban_channel',
                str(ban_info.get('reason') or '') if ban_info else '',
                target_label=sender_chat.title or sender_chat.username or str(sender_chat.id),
            )
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

    target_arg = parts[1] if len(parts) > 1 else None
    if has_explicit_target(msg, target_arg):
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
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

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
        log_moderation(
            msg.chat.id,
            msg.from_user.id,
            tid,
            'unban',
            str(ban_info.get('reason') or '') if ban_info else '',
        )

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
        await send_moderation_notice(
            msg,
            f"✅ {mention(msg.chat.id, tid)} разбанен{reason_text}",
            disable_web_page_preview=True,
        )

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"✅ <b>Бан снят!</b>\n\n{reason_text}\n👮 Снял: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except Exception:
            pass


    except Exception as e:
        logger.exception("Не удалось разбанить пользователя %s", tid)
        await msg.answer(f"❌ Не удалось разбанить пользователя: {html.escape(str(e)[:250], quote=False)}")


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
    configured_templates = storage.get_chat_settings(msg.chat.id).get('reason_templates', [])
    reason_templates = (
        configured_templates
        if isinstance(configured_templates, list)
        and all(isinstance(item, str) for item in configured_templates)
        else []
    )

    target_arg = parts[1] if len(parts) > 1 else None
    target_mention = get_target_mention_span(msg, target_arg) if target_arg else None
    if has_explicit_target(msg, target_arg):
        tid = await get_target(msg, target_arg)
        if not tid:
            return await msg.answer("❌ Пользователь не найден")
        if target_mention:
            trailing_args = msg.text[target_mention[2]:].strip().split(maxsplit=1)
        else:
            trailing_args = parts[2:]
        if trailing_args:
            template_index = (
                int(trailing_args[0])
                if len(trailing_args) == 1 and trailing_args[0].isdigit() and len(trailing_args[0]) <= 2
                else 0
            )
            if 1 <= template_index <= len(reason_templates):
                reason = reason_templates[template_index - 1]
            else:
                try:
                    days = int(trailing_args[0])
                    reason = ' '.join(trailing_args[1:]) or 'Без причины'
                except ValueError:
                    reason = ' '.join(trailing_args) or 'Без причины'
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            template_index = (
                int(parts[1])
                if len(parts) == 2 and parts[1].isdigit() and len(parts[1]) <= 2
                else 0
            )
            if 1 <= template_index <= len(reason_templates):
                reason = reason_templates[template_index - 1]
            else:
                try:
                    days = int(parts[1])
                    reason = ' '.join(parts[2:]) or 'Без причины'
                except ValueError:
                    reason = ' '.join(parts[1:]) or 'Без причины'
    else:
        return await msg.answer(
            ui_error(
                "Не указаны аргументы",
                "Укажи пользователя или ответь на его сообщение; срок и причина необязательны.",
                "!пред @user 7 флуд"
            )
        )

    if not tid:
        return await msg.answer("❌ Пользователь не найден")

    if not await require_target_not_telegram_admin(msg, tid):
        return

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
    log_moderation(
        msg.chat.id,
        msg.from_user.id,
        tid,
        'warn',
        reason,
        days * 86400 if days > 0 else None,
    )
    
    # Получаем активные предупреждения
    active = [w for w in u['warnings'] if isinstance(w, dict) and warning_is_active(w)]
    warn_actions = storage.get_chat_settings(msg.chat.id).get('warn_actions', [])
    action_rule = next(
        (
            rule for rule in warn_actions
            if isinstance(rule, dict) and rule.get('count') == len(active)
        ),
        None,
    ) if isinstance(warn_actions, list) else None
    action_name = action_rule.get('action') if action_rule else None
    
    storage.mark_dirty()
    await storage.save()
    
    logger.info(f"Предупреждение: {msg.from_user.id} дал {tid}, активных: {len(active)}/{MAX_WARNINGS}")

    # Формируем информативное сообщение
    time_str = f"{days} дн" if days > 0 else "навсегда"
    action_notice = ""

    if action_name == 'mute':
        duration = action_rule.get('duration')
        if not isinstance(duration, int) or not 1 <= duration <= MAX_MUTE_MINUTES:
            logger.warning("Некорректная длительность действия варнов в чате %s: %r", msg.chat.id, duration)
            action_notice = "⚠️ Автоматический мут не выдан: неверная длительность в настройках."
        else:
            restrict_right = await bot_can(msg.chat.id, 'can_restrict_members')
            if restrict_right is None:
                action_notice = "⚠️ Не удалось проверить права бота для автоматического мута."
            elif not restrict_right:
                action_notice = "⚠️ Автоматический мут не выдан: у бота нет права ограничивать участников."
            else:
                try:
                    until = datetime.now() + timedelta(minutes=duration)
                    await bot.restrict_chat_member(
                        msg.chat.id,
                        tid,
                        ChatPermissions(can_send_messages=False),
                        until_date=int(until.timestamp()),
                    )
                    mutes = storage.get_chat(msg.chat.id, 'mutes')
                    if not isinstance(mutes, list):
                        mutes = []
                        storage.data['mutes'][str(msg.chat.id)] = mutes
                    else:
                        mutes[:] = [mute for mute in mutes if mute.get('user_id') != tid]
                    mutes.append({
                        'user_id': tid,
                        'expire_time': until.timestamp(),
                        'permanent': False,
                        'issued_at': time.time(),
                        'duration_minutes': duration,
                        'muted_by': 'auto',
                        'auto_mute': True,
                        'mute_source': 'warn_action',
                        'reason': f'Автоматическое действие: {len(active)} предупреждения',
                    })
                    log_moderation(
                        msg.chat.id,
                        None,
                        tid,
                        'auto_mute',
                        f'Автоматическое действие: {len(active)} предупреждения',
                        duration * 60,
                    )
                    storage.mark_dirty()
                    await storage.save()
                    action_notice = f"🔇 Автоматически выдан мут на {format_mute_duration(duration)}."
                except Exception:
                    logger.exception("Не удалось применить автоматический мут по предупреждениям в чате %s", msg.chat.id)
                    action_notice = "⚠️ Не удалось применить автоматический мут; подробности записаны в журнал."

    if action_name == 'kick':
        restrict_right = await bot_can(msg.chat.id, 'can_restrict_members')
        if restrict_right is not True:
            action_notice = (
                "⚠️ Не удалось проверить права бота для автоматического кика."
                if restrict_right is None
                else "⚠️ Автокик не выполнен: у бота нет права блокировать участников."
            )
        else:
            try:
                await bot.ban_chat_member(msg.chat.id, tid, revoke_messages=False)
                try:
                    await bot.unban_chat_member(msg.chat.id, tid, only_if_banned=True)
                except Exception as unban_exc:
                    bans_by_chat = storage.data.setdefault('banned_users', {}).setdefault(str(msg.chat.id), [])
                    bans_by_chat[:] = [
                        ban for ban in bans_by_chat
                        if not isinstance(ban, dict) or ban.get('user_id') != tid
                    ]
                    bans_by_chat.append({
                        'user_id': tid,
                        'banned_by': 'auto',
                        'reason': f"Автокик по предупреждениям: {reason}",
                        'date': time.time(),
                        'permanent': True,
                    })
                    log_moderation(
                        msg.chat.id, None, tid, 'auto_kick_failed',
                        f"{reason}; не удалось завершить снятием бана",
                    )
                    storage.mark_dirty()
                    await storage.save()
                    action_notice = (
                        "⚠️ Автокик не завершён: участник остался заблокирован. "
                        f"Снимите бан вручную ({html.escape(str(unban_exc)[:120], quote=False)})."
                    )
                else:
                    log_moderation(
                        msg.chat.id, None, tid, 'auto_kick',
                        f"Автоматическое действие: {len(active)} предупреждения; {reason}",
                    )
                    action_notice = "👢 Пользователь автоматически кикнут по действиям за предупреждения."
                storage.mark_dirty()
                await storage.save()
            except Exception:
                logger.exception("Не удалось применить автоматический кик по предупреждениям в чате %s", msg.chat.id)
                action_notice = "⚠️ Не удалось выполнить автоматический кик; подробности записаны в журнал."

    should_ban = action_name == 'ban' or (
        action_rule is None and len(active) >= MAX_WARNINGS
    )
    if should_ban:
        restrict_right = await bot_can(msg.chat.id, 'can_restrict_members')
        if restrict_right is None:
            action_notice = "⚠️ Не удалось проверить права бота для автобана."
            should_ban = False
        elif not restrict_right:
            action_notice = "⚠️ Автобан не выполнен: у бота нет права блокировать участников."
            should_ban = False
    if should_ban:
        try:
            await bot.ban_chat_member(msg.chat.id, tid, revoke_messages=True)

            chat_id_str = str(msg.chat.id)
            if 'banned_users' not in storage.data:
                storage.data['banned_users'] = {}
            if chat_id_str not in storage.data['banned_users']:
                storage.data['banned_users'][chat_id_str] = []
            banned_users = storage.data['banned_users'][chat_id_str]
            banned_users[:] = [
                ban for ban in banned_users
                if not isinstance(ban, dict) or ban.get('user_id') != tid
            ]
            banned_users.append({
                'user_id': tid,
                'banned_by': msg.from_user.id,
                'reason': f"Достигнут лимит предупреждений ({MAX_WARNINGS})",
                'date': time.time(),
                'permanent': True,
            })

            log_moderation(
                msg.chat.id,
                None,
                tid,
                'auto_ban',
                f"Достигнут лимит предупреждений ({MAX_WARNINGS})",
            )
            storage.mark_dirty()
            await storage.save()

            await send_moderation_notice(
                msg,
                f"🚫 {mention(msg.chat.id, tid)} забанен по действию за предупреждения\n"
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
            except Exception:
                pass
            return

        except Exception as e:
            logger.warning(f"Не удалось забанить пользователя {tid} после предупреждений: {e}")

    # Уведомление в чат
    await send_moderation_notice(
        msg,
        "⚠️ <b>Предупреждение выдано</b>\n"
        f"{UI_LINE}\n"
        f"👤 Пользователь: {mention(msg.chat.id, tid)}\n"
        f"📝 Причина: {html.escape(str(reason), quote=False)}\n"
        f"⏱ Срок: {html.escape(str(time_str), quote=False)}\n"
        f"📊 Активных: {len(active)}/{MAX_WARNINGS}\n"
        f"{action_notice + chr(10) if action_notice else ''}"
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
            "📌 Последствия предупреждений зависят от настроек чата."
        )
        await bot.send_message(tid, user_msg, disable_web_page_preview=True)
    except Exception as e:
        logger.debug(f"Не удалось отправить ДМ о варне: {e}")


async def cmd_warn_actions(msg: Message, cmd_name: str = 'варннастройка'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(
        msg,
        cmd_name,
        2,
        title='Недостаточно прав',
        message='Настраивать действия за предупреждения могут модераторы 2+.',
        example='!варннастройка 3 мут 60',
    ):
        return

    raw = strip_command_prefix(msg.text or '', msg.chat.id).strip()
    for alias in ('варннастройка', 'настройка варнов'):
        if raw.casefold() == alias or raw.casefold().startswith(alias + ' '):
            raw = raw[len(alias):].strip()
            break
    parts = raw.split()
    settings = storage.get_chat_settings(msg.chat.id)
    rules = settings.get('warn_actions', [])
    if not isinstance(rules, list):
        logger.warning("Некорректные warn_actions в чате %s; заменяю пустым списком", msg.chat.id)
        rules = []

    if not parts:
        formatted_rules = []
        for rule in sorted(
            (item for item in rules if isinstance(item, dict)),
            key=lambda item: item.get('count', 0)
            if isinstance(item.get('count', 0), int) else 0,
        ):
            count = rule.get('count')
            action = rule.get('action')
            if not isinstance(count, int) or action not in {'mute', 'ban', 'kick', 'none'}:
                continue
            if action == 'mute':
                duration = rule.get('duration')
                action_text = (
                    f"мут на {format_mute_duration(duration)}"
                    if isinstance(duration, int) and duration > 0 else 'мут (неверный срок)'
                )
            else:
                action_text = (
                    'бан' if action == 'ban'
                    else 'кик' if action == 'kick'
                    else 'без автоматического действия'
                )
            formatted_rules.append(f"• {count} предупреждений — {action_text}")
        rules_text = '\n'.join(formatted_rules) or '• Действия не настроены'
        return await msg.answer(
            "⚠️ <b>Действия за предупреждения</b>\n"
            f"{UI_LINE}\n"
            f"{rules_text}\n\n"
            "Настройка (ранг 2+):\n"
            "<code>!варннастройка ЧИСЛО мут МИНУТЫ</code>\n"
            "<code>!варннастройка ЧИСЛО бан</code>\n"
            "<code>!варннастройка ЧИСЛО кик</code>\n"
            "<code>!варннастройка ЧИСЛО выкл</code>\n"
            "<code>!варннастройка сбросить</code> — вернуть значения по умолчанию"
        )

    if len(parts) == 1 and parts[0].casefold() == 'сбросить':
        settings['warn_actions'] = [
            {'count': 3, 'action': 'mute', 'duration': 60},
            {'count': 5, 'action': 'mute', 'duration': 1440},
            {'count': MAX_WARNINGS, 'action': 'ban', 'duration': 0},
        ]
    else:
        try:
            count = int(parts[0])
        except ValueError:
            return await msg.answer(
                "❌ Укажите число предупреждений от 1 до "
                f"{MAX_WARNINGS} или команду <code>сбросить</code>."
            )
        if not 1 <= count <= MAX_WARNINGS:
            return await msg.answer(f"❌ Число предупреждений должно быть от 1 до {MAX_WARNINGS}.")
        if len(parts) < 2:
            return await msg.answer(
                "❌ Укажите действие: <code>мут МИНУТЫ</code>, <code>бан</code> или <code>выкл</code>."
            )

        action = parts[1].casefold()
        updated_rules = [
            rule for rule in rules
            if (
                isinstance(rule, dict)
                and isinstance(rule.get('count'), int)
                and rule.get('action') in {'mute', 'ban', 'kick', 'none'}
                and rule['count'] != count
            )
        ]
        if action in {'выкл', 'off', 'удалить'}:
            if len(parts) != 2:
                return await msg.answer("❌ Для отключения укажите только число предупреждений.")
            updated_rules.append({'count': count, 'action': 'none', 'duration': 0})
            settings['warn_actions'] = sorted(updated_rules, key=lambda item: item['count'])
        elif action == 'бан':
            if len(parts) != 2:
                return await msg.answer("❌ Для действия «бан» не указывайте длительность.")
            updated_rules.append({'count': count, 'action': 'ban', 'duration': 0})
            settings['warn_actions'] = sorted(updated_rules, key=lambda item: item['count'])
        elif action == 'кик':
            if len(parts) != 2:
                return await msg.answer("❌ Для действия «кик» не указывайте длительность.")
            updated_rules.append({'count': count, 'action': 'kick', 'duration': 0})
            settings['warn_actions'] = sorted(updated_rules, key=lambda item: item['count'])
        elif action == 'мут':
            if len(parts) != 3:
                return await msg.answer("❌ Укажите длительность мута в минутах.")
            try:
                duration = int(parts[2])
            except ValueError:
                return await msg.answer("❌ Длительность мута должна быть числом минут.")
            if not 1 <= duration <= MAX_MUTE_MINUTES:
                return await msg.answer(f"❌ Длительность должна быть от 1 до {MAX_MUTE_MINUTES} минут.")
            updated_rules.append({'count': count, 'action': 'mute', 'duration': duration})
            settings['warn_actions'] = sorted(updated_rules, key=lambda item: item['count'])
        else:
            return await msg.answer(
                "❌ Действие должно быть «мут», «кик», «бан» или «выкл»."
            )

    storage.invalidate_chat_settings_cache(msg.chat.id)
    storage.mark_dirty()
    await storage.save()
    await msg.answer("✅ Действия за предупреждения обновлены.")


async def show_warnings(msg: Message, cmd_name: str = 'преды'):
    if not await require_access(msg, cmd_name, 0, title='Нет доступа', message='Эта команда доступна всем участникам.', example='!преды'):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    parts = strip_command_prefix(msg.text, msg.chat.id).split()

    tid = msg.from_user.id
    target_arg = parts[1] if len(parts) > 1 else None
    if has_explicit_target(msg, target_arg):
        target = await get_target(msg, target_arg)
        if not target:
            return await msg.answer("❌ Пользователь не найден")
        tid = target
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

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
        except Exception:
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

    await send_chunked_text(msg, txt)


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


class _HTMLChunkTokenizer(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.tokens = []

    def handle_starttag(self, tag, attrs):
        self.tokens.append(('start', self.get_starttag_text(), tag))

    def handle_startendtag(self, tag, attrs):
        self.tokens.append(('atomic', self.get_starttag_text(), tag))

    def handle_endtag(self, tag):
        self.tokens.append(('end', f'</{tag}>', tag))

    def handle_data(self, data):
        self.tokens.append(('text', data, None))

    def handle_entityref(self, name):
        self.tokens.append(('atomic', f'&{name};', None))

    def handle_charref(self, name):
        self.tokens.append(('atomic', f'&#{name};', None))

    def handle_comment(self, data):
        self.tokens.append(('atomic', f'<!--{data}-->', None))

    def handle_decl(self, decl):
        self.tokens.append(('atomic', f'<!{decl}>', None))

    def handle_pi(self, data):
        self.tokens.append(('atomic', f'<?{data}>', None))

    def unknown_decl(self, data):
        self.tokens.append(('atomic', f'<![{data}]>', None))


def _split_html_message(text: str, limit: int) -> List[str]:
    if limit <= 0:
        raise ValueError("Лимит частей сообщения должен быть положительным")

    tokenizer = _HTMLChunkTokenizer()
    tokenizer.feed(text)
    tokenizer.close()
    chunks = []
    open_tags = []
    current = ''
    content_length = 0

    def open_markup(tags):
        return ''.join(opening for _, opening in tags)

    def close_markup(tags):
        return ''.join(f'</{tag}>' for tag, _ in reversed(tags))

    def flush():
        nonlocal current, content_length
        if content_length:
            chunks.append(current + close_markup(open_tags))
        current = open_markup(open_tags)
        content_length = 0

    for token_type, token, tag in tokenizer.tokens:
        if token_type == 'text':
            position = 0
            while position < len(token):
                available = limit - len(current) - len(close_markup(open_tags))
                if available <= 0:
                    if not content_length:
                        raise ValueError("HTML-разметка не помещается в лимит части сообщения")
                    flush()
                    available = limit - len(current) - len(close_markup(open_tags))
                part = token[position:position + available]
                current += part
                content_length += len(part)
                position += len(part)
                if position < len(token):
                    flush()
            continue

        updated_tags = open_tags
        if token_type == 'start':
            updated_tags = open_tags + [(tag, token)]
        elif token_type == 'end':
            matching_tag = next(
                (index for index in range(len(open_tags) - 1, -1, -1) if open_tags[index][0] == tag),
                None,
            )
            if matching_tag is not None:
                updated_tags = open_tags[:matching_tag]

        if len(current) + len(token) + len(close_markup(updated_tags)) > limit:
            if not content_length:
                raise ValueError("HTML-тег не помещается в лимит части сообщения")
            flush()
            if len(current) + len(token) + len(close_markup(updated_tags)) > limit:
                raise ValueError("HTML-тег не помещается в лимит части сообщения")

        current += token
        content_length += len(token)
        open_tags = updated_tags

    if content_length:
        chunks.append(current + close_markup(open_tags))
    return chunks


async def send_chunked_text(msg: Message, text: str, limit: int = 3800):
    chunks = _split_html_message(text, limit)
    for chunk in chunks:
        await msg.answer(chunk, disable_web_page_preview=True)


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
            expire_time = ban.get('expire_time')
            expiration_text = (
                f"; до {datetime.fromtimestamp(expire_time).strftime('%d.%m.%Y %H:%M')}"
                if isinstance(expire_time, (int, float))
                else "; бессрочно"
            )
            entries.append(
                f"• {mention(msg.chat.id, ban['user_id'])} — с {date_text}{expiration_text}; {reason}; "
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
    storage.load_chat_users(msg.chat.id)
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
    target_arg = parts[1] if len(parts) > 1 else None
    index_in_reply = (
        msg.reply_to_message and msg.reply_to_message.from_user
        and target_arg and target_arg.isdigit() and len(parts) == 2
    )
    explicit_target = has_explicit_target(msg, target_arg) and not index_in_reply
    if explicit_target:
        tid = await get_target(msg, target_arg)
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

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
        except Exception:
            pass
        return

    num_idx = 2 if explicit_target or not msg.reply_to_message else 1
    if len(parts) > num_idx and parts[num_idx].isdigit():
        idx = int(parts[num_idx]) - 1
        if 0 <= idx < len(active):
            removed_warning = u['warnings'][active[idx][0]]
            del u['warnings'][active[idx][0]]

            log_moderation(
                msg.chat.id,
                msg.from_user.id,
                tid,
                'unwarn',
                str(removed_warning.get('reason') or ''),
            )
            storage.mark_dirty()
            await storage.save()

            logger.info(f"Снято предупреждение #{idx + 1} у {tid}")

            await send_moderation_notice(
                msg,
                f"✅ Снято предупреждение #{idx + 1} у {mention(msg.chat.id, tid)}\n"
                f"📝 Причина была: {html.escape(str(removed_warning.get('reason') or 'Без причины'), quote=False)}",
                disable_web_page_preview=True,
            )
            return
        else:
            return await msg.answer(ui_error("Предупреждение не найдено", f"У пользователя {mention(msg.chat.id, tid)} нет предупреждения под номером {idx + 1}.", "!снятьпред @user 1"), disable_web_page_preview=True)

    before_count = len(active)
    removed_reasons = [
        str(warning.get('reason') or '')
        for _, warning in active
    ]
    for idx, _ in sorted(active, key=lambda x: x[0], reverse=True):
        del u['warnings'][idx]

    log_moderation(
        msg.chat.id,
        msg.from_user.id,
        tid,
        'unwarn',
        '; '.join(reason for reason in removed_reasons if reason)[:500],
    )
    storage.mark_dirty()
    await storage.save()

    logger.info(f"Снято {before_count} предупреждений у {tid}")

    await send_moderation_notice(
        msg,
        f"✅ Снято <b>{before_count}</b> предупреждений у {mention(msg.chat.id, tid)}",
        disable_web_page_preview=True,
    )


async def cmd_del(msg: Message, cmd_name: str = '-смс'):
    if not await require_telegram_admin(msg):
        return
    if not await require_access(msg, cmd_name, 1, title='Недостаточно прав', message='Эта команда доступна только модераторам и выше.', example='! -смс'):
        return
    if not await require_bot_right(msg, 'can_delete_messages', 'удаления сообщений'):
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
    if not await require_bot_right(msg, 'can_pin_messages', 'закрепления сообщений'):
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
    if not await require_bot_right(msg, 'can_delete_messages', 'удаления сообщений'):
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
        await telegram_call_with_retry(msg.delete)

        deleted = 0
        rate_limited = False
        current_id = msg.message_id
        target_id = msg.reply_to_message.message_id

        # Удаляем сообщения от текущего ID до целевого
        for message_id in range(current_id - 1, target_id - 1, -1):
            try:
                await telegram_call_with_retry(
                    bot.delete_message,
                    chat_id=msg.chat.id,
                    message_id=message_id,
                )
                deleted += 1
                await asyncio.sleep(0.1)  # Пауза чтобы не превысить лимиты API
            except TelegramRetryAfter as error:
                rate_limited = True
                logger.warning(
                    "Очистка чата %s остановлена из-за лимита Telegram после удаления %s сообщений "
                    "(повтор через %s сек.)",
                    msg.chat.id, deleted, error.retry_after,
                )
                break
            except Exception as e:
                # Пропускаем сообщения, которые нельзя удалить
                # (слишком старые, уже удалённые, или нет прав)
                continue

        # Отправляем результат и удаляем его через 3 секунды
        result_text = (
            f"⚠️ Очистка остановлена из-за лимита Telegram. Удалено {deleted} сообщений."
            if rate_limited else f"✅ Удалено {deleted} сообщений"
        )
        result_msg = await telegram_call_with_retry(
            msg.answer, result_text
        )
        await asyncio.sleep(3)
        await telegram_call_with_retry(result_msg.delete)

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

    parts = text.split(None, 1)
    target_arg = parts[0] if parts else None
    target_mention = get_target_mention_span(msg, target_arg) if target_arg else None
    explicit_target = bool(
        target_arg
        and has_explicit_target(msg, target_arg)
        and (
            len(parts) > 1
            or target_arg.startswith(('@', 'id:'))
            or target_mention
        )
    )
    if explicit_target:
        tid = await get_target(msg, target_arg)
        if tid:
            award_name = (
                msg.text[target_mention[2]:].strip()
                if target_mention
                else parts[1] if len(parts) > 1 else None
            )
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        award_name = text
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

    parts = text.split(None, 1)
    target_arg = parts[0] if parts else None
    target_mention = get_target_mention_span(msg, target_arg) if target_arg else None
    explicit_target = bool(
        target_arg
        and has_explicit_target(msg, target_arg)
        and (
            len(parts) > 1
            or target_arg.startswith(('@', 'id:'))
            or target_mention
        )
    )
    if explicit_target:
        tid = await get_target(msg, target_arg)
        if tid:
            award_name = (
                msg.text[target_mention[2]:].strip()
                if target_mention
                else parts[1] if len(parts) > 1 else None
            )
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        award_name = text
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
    text = strip_command_prefix(msg.text.strip(), msg.chat.id)
    if text.lower().startswith('мои награды'):
        text = text[len('мои награды'):].strip()
    if text:
        first_arg = text.split(maxsplit=1)[0]
        target_arg = (
            text if get_target_mention_span(msg, text)
            else first_arg if first_arg.startswith(('@', 'id:'))
            else text
        )
        if has_explicit_target(msg, target_arg):
            target = await get_target(msg, target_arg)
            if not target:
                return await msg.answer("❌ Не удалось найти пользователя.")
            tid = target
        elif msg.reply_to_message and msg.reply_to_message.from_user:
            tid = msg.reply_to_message.from_user.id
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

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

    await send_chunked_text(msg, txt)


async def cmd_top_awards(msg: Message, cmd_name: str = 'топ наград'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    awards_stats = []
    storage.load_chat_users(msg.chat.id)
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
    target_arg = parts[1] if len(parts) > 1 else None
    if has_explicit_target(msg, target_arg):
        tid = await get_target(msg, target_arg)
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id

    if not tid:
        return await msg.answer("❌ Использование:\n<code>брак @user</code> или ответьте на сообщение")

    if tid == msg.from_user.id:
        return await msg.answer("❌ Нельзя жениться на себе!")

    if tid == bot.id:
        return await msg.answer("❌ Я бот, мне нельзя предлагать брак!")

    user = storage.get_user(msg.chat.id, msg.from_user.id)
    target = storage.get_user(msg.chat.id, tid)

    if user.get('pending_marriage') and marriage_proposal_expired(user):
        clear_pending_marriage(msg.chat.id, msg.from_user.id, user)
    if target.get('pending_marriage') and marriage_proposal_expired(target):
        clear_pending_marriage(msg.chat.id, tid, target)

    if user.get('marriage_partner'):
        partner_name = mention(msg.chat.id, user['marriage_partner'])
        return await msg.answer(f"❌ Вы уже в браке с {partner_name}!", disable_web_page_preview=True)

    if target.get('marriage_partner'):
        return await msg.answer(f"❌ {mention(msg.chat.id, tid)} уже в браке!", disable_web_page_preview=True)

    if target.get('pending_marriage') == msg.from_user.id:
        return await msg.answer("❌ Вы уже отправили предложение этому пользователю!")
    if user.get('pending_marriage') or target.get('pending_marriage'):
        return await msg.answer("❌ У вас или этого пользователя уже есть ожидающее предложение брака.")

    target['pending_marriage'] = msg.from_user.id
    target['pending_marriage_at'] = time.time()
    user['pending_marriage'] = tid
    user['pending_marriage_at'] = target['pending_marriage_at']
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

    if (
        target_user.get('pending_marriage') != proposer_id
        or proposer_user.get('pending_marriage') != call.from_user.id
    ):
        await call.answer("❌ Это предложение не для вас!", show_alert=True)
        return

    if marriage_proposal_expired(target_user):
        clear_pending_marriage(call.message.chat.id, call.from_user.id, target_user)
        await storage.save()
        await call.answer("❌ Срок предложения истёк. Попросите отправить его заново.", show_alert=True)
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
        target_user['pending_marriage_at'] = None
        proposer_user['pending_marriage'] = None
        proposer_user['pending_marriage_at'] = None

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
        target_user['pending_marriage_at'] = None
        proposer_user['pending_marriage'] = None
        proposer_user['pending_marriage_at'] = None
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
    if proposer.get('pending_marriage') != msg.from_user.id:
        return await msg.answer("❌ Предложение устарело. Попросите отправить его заново.")
    if marriage_proposal_expired(u):
        clear_pending_marriage(msg.chat.id, msg.from_user.id, u)
        await storage.save()
        return await msg.answer("❌ Срок предложения истёк. Попросите отправить его заново.")

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
    u['pending_marriage_at'] = None
    proposer['pending_marriage'] = None
    proposer['pending_marriage_at'] = None

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
    if proposer.get('pending_marriage') != msg.from_user.id:
        return await msg.answer("❌ Предложение устарело.")
    if marriage_proposal_expired(u):
        clear_pending_marriage(msg.chat.id, msg.from_user.id, u)
        await storage.save()
        return await msg.answer("❌ Срок предложения истёк.")
    u['pending_marriage'] = None
    u['pending_marriage_at'] = None
    proposer['pending_marriage'] = None
    proposer['pending_marriage_at'] = None
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
        u['pending_marriage'] = None
        u['pending_marriage_at'] = None
        partner['marriage_partner'] = None
        partner['marriage_date'] = None
        partner['pending_marriage'] = None
        partner['pending_marriage_at'] = None

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

    await send_chunked_text(msg, txt)


# ==================== Фразы ====================

async def cmd_add_phrase(msg: Message, cmd_name: str = 'добавить фразу'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 1):
        return await msg.answer("❌ Добавлять фразы можно с ранга 1+")

    command_text = strip_command_prefix(msg.text or '', msg.chat.id)
    command_word_count = len(cmd_name.split())
    parts = command_text.split(maxsplit=command_word_count)
    if (
        len(parts) <= command_word_count
        or ' '.join(parts[:command_word_count]).casefold() != cmd_name.casefold()
    ):
        return await msg.answer(
            "❌ <code>добавить фразу [-any] слово ответ</code>\n\nМожно добавлять несколько ответов на одно слово!"
        )

    phrase_arguments = parts[command_word_count]
    argument_parts = phrase_arguments.split(maxsplit=1)
    anywhere = bool(argument_parts and argument_parts[0].casefold() in {'-any', '[-any]'})
    if anywhere:
        phrase_arguments = argument_parts[1] if len(argument_parts) > 1 else ''
    phrase_parts = phrase_arguments.split(maxsplit=1)
    if len(phrase_parts) < 2:
        return await msg.answer(
            "❌ <code>добавить фразу [-any] слово ответ</code>\n\nМожно добавлять несколько ответов на одно слово!")

    trigger, response = phrase_parts[0].casefold(), phrase_parts[1]

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
    invalidate_phrase_match_cache(msg.chat.id)

    # Подсчитываем сколько всего фраз с таким триггером
    count = sum(
        1 for p in phrases
        if isinstance(p, dict)
        and p.get('trigger') == trigger
        and p.get('anywhere', False) == anywhere
    )

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
        safe_trigger = html.escape(str(trigger)[:100], quote=False)
        anywhere_icon = '🌐' if items[0].get('anywhere') else '📌'
        responses_count = len(items)
        # Показываем первый ответ как пример
        preview = items[0]['response'][:30] + "..." if len(items[0]['response']) > 30 else items[0]['response']
        txt += (
            f"{anywhere_icon} <b>{safe_trigger}</b>: "
            f"{responses_count} отв. (напр. {html.escape(str(preview), quote=False)})\n"
        )

        # Опционально: показать все ответы
        if len(items) <= 3:
            for p in items:
                txt += f"   └ {html.escape(str(p.get('response') or '')[:40], quote=False)}\n"

    await send_chunked_text(msg, txt)


async def cmd_phrase_stats(msg: Message):
    phrases = storage.get_chat(msg.chat.id, 'phrases')
    if not isinstance(phrases, list) or not phrases:
        return await msg.answer("📝 Нет фраз")
    sorted_p = sorted(phrases, key=lambda x: x.get('uses', 0), reverse=True)
    txt = "📊 <b>Статистика фраз:</b>\n\n"
    for p in sorted_p[:20]:
        trigger = html.escape(str(p.get('trigger') or '')[:100], quote=False)
        txt += f"• {trigger}: {p.get('uses', 0)} раз\n"
    await send_chunked_text(msg, txt)


async def cmd_del_phrase(msg: Message, cmd_name: str = 'удалить фразу'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 1):
        return await msg.answer("❌ Удалять фразы можно с ранга 1+")

    command_text = strip_command_prefix(msg.text or '', msg.chat.id)
    command_word_count = len(cmd_name.split())
    parts = command_text.split(maxsplit=command_word_count)
    if (
        len(parts) <= command_word_count
        or ' '.join(parts[:command_word_count]).casefold() != cmd_name.casefold()
    ):
        return await msg.answer("❌ <code>удалить фразу слово [текст]</code>\n\n"
                                "• <code>удалить фразу бот</code> - удалить ВСЕ фразы с триггером 'бот'\n"
                                "• <code>удалить фразу бот пошел</code> - удалить конкретную фразу")

    phrase_parts = parts[command_word_count].split(maxsplit=1)
    trigger = phrase_parts[0].casefold()
    response_text = phrase_parts[1] if len(phrase_parts) > 1 else None

    phrases = storage.get_chat(msg.chat.id, 'phrases')
    if not isinstance(phrases, list) or not phrases:
        return await msg.answer("❌ Фраз не найдено")

    before_count = len(phrases)

    if response_text:
        # Удаляем конкретную фразу
        phrases[:] = [p for p in phrases if
                      not (p['trigger'].casefold() == trigger and p['response'].casefold() == response_text.casefold())]
        invalidate_phrase_match_cache(msg.chat.id)
        removed = before_count - len(phrases)
        await msg.answer(
            f"✅ Удалено {removed} фраз с ответом '{html.escape(response_text, quote=False)}'"
        )
    else:
        # Удаляем все фразы с таким триггером
        phrases[:] = [p for p in phrases if p['trigger'].casefold() != trigger]
        invalidate_phrase_match_cache(msg.chat.id)
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
    command_text = strip_command_prefix(msg.text or '', msg.chat.id)
    command_word_count = len(cmd_name.split())
    parts = command_text.split(maxsplit=command_word_count)
    if (
        len(parts) <= command_word_count
        or ' '.join(parts[:command_word_count]).casefold() != cmd_name.casefold()
    ):
        return await msg.answer("❌ <code>показать фразу слово</code>")

    trigger = parts[command_word_count].casefold()
    phrases = storage.get_chat(msg.chat.id, 'phrases')

    if not isinstance(phrases, list):
        return await msg.answer("❌ Фраз не найдено")

    matching = [
        p for p in phrases
        if isinstance(p, dict)
        and isinstance(p.get('trigger'), str)
        and p['trigger'].casefold() == trigger
    ]

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

    await send_chunked_text(msg, txt)


# ==================== Приветствия ====================

async def cmd_welcome(msg: Message, cmd_name: str = 'приветствие'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return
    cid = str(msg.chat.id)
    settings = storage.data['welcome_settings'].setdefault(cid, {})
    command_text = strip_command_prefix(msg.text, msg.chat.id)
    _, _, arguments = command_text.partition(' ')
    arguments = arguments.strip()
    action, _, value = arguments.partition(' ')
    action = action.casefold()
    value = value.strip()

    if action in {'вкл', 'выкл'}:
        settings['enabled'] = action == 'вкл'
        storage.mark_dirty();
        await storage.save()
        await msg.answer(f"✅ Приветствия {'включены' if settings['enabled'] else 'выключены'}")
        return

    if action == 'картинка':
        if not value:
            return await msg.answer("❌ Укажите ссылку после <code>!приветствие картинка</code>")
        settings['image_url'] = value
        storage.mark_dirty();
        await storage.save()
        await msg.answer("✅ Картинка приветствия установлена")
        return

    if action == 'текст':
        settings['text'] = value
        storage.mark_dirty();
        await storage.save()
        await msg.answer("✅ Текст приветствия установлен")
        return

    await msg.answer("❌ Использование: <code>!приветствие вкл/выкл</code> | <code>!приветствие текст ...</code> | <code>!приветствие картинка URL</code>")


async def cmd_farewell(msg: Message, cmd_name: str = 'прощание'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return

    cid = str(msg.chat.id)
    settings = storage.data['welcome_settings'].setdefault(cid, {})
    command_text = strip_command_prefix(msg.text, msg.chat.id)
    _, _, arguments = command_text.partition(' ')
    arguments = arguments.strip()
    action, _, value = arguments.partition(' ')
    action = action.casefold()
    value = value.strip()

    if action in {'вкл', 'выкл'}:
        settings['farewell_enabled'] = action == 'вкл'
        storage.mark_dirty()
        await storage.save()
        await msg.answer(f"✅ Прощание {'включено' if settings['farewell_enabled'] else 'выключено'}")
        return

    if action == 'картинка':
        if not value:
            return await msg.answer("❌ Укажите ссылку после <code>!прощание картинка</code>")
        settings['farewell_image_url'] = value
        storage.mark_dirty();
        await storage.save()
        await msg.answer("✅ Картинка прощания установлена")
        return

    if action == 'текст':
        settings['farewell_text'] = value
        storage.mark_dirty()
        await storage.save()
        await msg.answer("✅ Текст прощания установлен")
        return

    if arguments:
        settings['farewell_text'] = arguments
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
    await send_chunked_text(msg, txt)


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

    await msg.answer(
        get_games_menu_text(msg.chat.id),
        reply_markup=get_games_menu_keyboard(),
    )


def get_games_menu_text(chat_id: int) -> str:
    chat_games = sum(
        1 for game in active_games.values()
        if game.get('chat_id') == chat_id and game.get('status', 'active') == 'active'
    )
    wordle_game = wordle.get_chat_game(chat_id)
    if wordle_game and wordle_game.get('status') == 'active':
        chat_games += 1
    chat_games += sum(
        1 for game in minesweeper_games.values()
        if game.get('chat_id') == chat_id and game.get('status') == 'active'
    )
    return (
        "🎮 <b>ИГРОВОЙ ЦЕНТР</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "Выбирай режим и зови друзей — всё проходит прямо здесь, в чате!\n\n"
        "🪨 <b>КНБ</b> — быстрая партия против бота или дуэль с игроком.\n"
        "⭕ <b>Крестики-нолики</b> — сыграй против бота или брось вызов другу.\n"
        "💣 <b>Сапёр</b> — открывай клетки и ищи мины.\n"
        "🔤 <b>Wordle</b> — угадай слово и проверь свою смекалку.\n\n"
        f"🔥 Активных игр в этом чате: <b>{chat_games}</b>"
    )


def get_games_menu_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🪨 КНБ с ботом", callback_data="game_rps_bot"),
            InlineKeyboardButton(text="⚔️ Дуэль КНБ", callback_data="game_rps_player")
        ],
        [
            InlineKeyboardButton(text="⭕ Крестики-нолики", callback_data="game_ttt_menu"),
            InlineKeyboardButton(text="🔤 Wordle", callback_data="game_wordle")
        ],
        [InlineKeyboardButton(text="💣 Сапёр", callback_data="game_minesweeper")],
        [InlineKeyboardButton(text="🥊 Боевая дуэль", callback_data="game_duel_info")],
        [InlineKeyboardButton(text="✖️ Закрыть меню", callback_data="game_cancel")]
    ])


MINESWEEPER_DIFFICULTIES = {
    'easy': ('Лёгкая', 5, 5, 5),
    'medium': ('Средняя', 7, 7, 15),
    'hard': ('Тяжёлая', 8, 9, 30),
}
minesweeper_games = {}


def get_minesweeper_menu_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🟢 Лёгкая · 5×5", callback_data="mines_difficulty_easy"),
            InlineKeyboardButton(text="🟡 Средняя · 7×7", callback_data="mines_difficulty_medium"),
        ],
        [InlineKeyboardButton(text="🔴 Тяжёлая · 8×9", callback_data="mines_difficulty_hard")],
        [InlineKeyboardButton(text="◀️ Назад", callback_data="game_back_to_menu")],
    ])


def get_minesweeper_menu_text() -> str:
    return (
        "💣 <b>САПЁР</b>\n"
        "Выберите сложность:\n\n"
        "🟢 Лёгкая — поле 5×5, 5 мин\n"
        "🟡 Средняя — поле 7×7, 15 мин\n"
        "🔴 Тяжёлая — поле 8 столбцов × 9 строк, 30 мин\n\n"
        "Сначала выберите режим внизу поля, затем нажимайте клетки."
    )


async def cmd_minesweeper(msg: Message):
    if not check_access(msg.from_user.id, msg.chat.id, 'сапёр', 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'games')
    await msg.answer(
        get_minesweeper_menu_text(),
        reply_markup=get_minesweeper_menu_keyboard(),
    )


async def cmd_duel(msg: Message, args: str = "", cmd_name: str = 'дуэль'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return

    if msg.chat.type not in ('group', 'supergroup'):
        await msg.answer("🥊 Дуэли можно запускать только в группе.")
        return
    save_activity(msg.chat.id, msg.from_user.id, 'games')

    opponent_id = await get_target(msg, args.split(maxsplit=1)[0] if args else None)
    if opponent_id is None:
        await msg.answer(
            "🥊 <b>Вызов на дуэль</b>\n\n"
            "Ответь командой <code>!дуэль</code> на сообщение соперника "
            "или укажи его через <code>!дуэль @username</code>."
        )
        return
    if opponent_id == msg.from_user.id:
        await msg.answer("Нельзя вызвать на дуэль самого себя 🙂")
        return
    if opponent_id == bot.id:
        await msg.answer("Давай лучше выберем соперника среди участников чата 🙂")
        return

    now = time.time()
    stale_challenges = [
        cid for cid, challenge in pending_challenges.items()
        if challenge.get('game_type') == 'duel'
        and now - challenge.get('timestamp', now) > 60
    ]
    for stale_id in stale_challenges:
        pending_challenges.pop(stale_id, None)

    for challenge in pending_challenges.values():
        if (
            challenge.get('game_type') == 'duel'
            and challenge.get('chat_id') == msg.chat.id
            and challenge.get('challenger') == msg.from_user.id
        ):
            await msg.answer("⏳ У тебя уже есть ожидающий вызов на дуэль.")
            return

    challenge_id = f"duel_{msg.from_user.id}_{int(now)}"
    pending_challenges[challenge_id] = {
        'challenger': msg.from_user.id,
        'opponent': opponent_id,
        'game_type': 'duel',
        'chat_id': msg.chat.id,
        'timestamp': now,
    }
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="⚔️ Принять вызов", callback_data=f"game_accept_{challenge_id}"),
            InlineKeyboardButton(text="🙅 Отказаться", callback_data=f"duel_decline_{challenge_id}"),
        ],
    ])
    await msg.answer(
        "🥊 <b>ВЫЗОВ НА ДУЭЛЬ!</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"{mention(msg.chat.id, msg.from_user.id)} вызывает {mention(msg.chat.id, opponent_id)}.\n\n"
        "Соперник, нажми кнопку ниже, чтобы принять. Вызов действует 60 секунд.",
        reply_markup=keyboard,
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
        if wordle.exit_chat_game(msg.chat.id, msg.from_user.id):
            await msg.answer("❌ Вы вышли из игры Wordle.")
        else:
            await msg.answer("❌ В этом чате нет вашей активной игры.")
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
                InlineKeyboardButton(text="⚔️ Дуэль в чате", callback_data="ttt_mode_player")
            ],
            [InlineKeyboardButton(text="◀️ Назад", callback_data="game_back_to_menu")]
        ])
        await call.message.edit_text(
            "⭕ <b>КРЕСТИКИ-НОЛИКИ</b>\n\n"
            "Сыграй быструю партию прямо в чате. Выбирай соперника:",
            reply_markup=kb
        )
    elif action == "game_wordle":
        await call.message.edit_text(
            get_wordle_menu_text(),
            reply_markup=get_wordle_menu_keyboard()
        )
    elif action == "game_minesweeper":
        await call.message.edit_text(
            get_minesweeper_menu_text(),
            reply_markup=get_minesweeper_menu_keyboard(),
        )
    elif action == "game_duel_info":
        await call.message.edit_text(
            "🥊 <b>БОЕВАЯ ДУЭЛЬ</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "Вызови участника чата командой <code>!дуэль @username</code> "
            "или ответом <code>!дуэль</code> на его сообщение.\n\n"
            "После принятия оба бойца выбирают действие кнопками прямо в группе. "
            "Выборы скрыты до конца раунда. У каждого 100 здоровья, бой длится до "
            "5 раундов или пока здоровье одного из игроков не закончится.\n\n"
            "👊 Удар — надёжный урон.\n"
            "💥 Сильный удар — больше урона, но может промахнуться.\n"
            "🛡 Защита — сильно снижает входящий урон.",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="◀️ Назад", callback_data="game_back_to_menu")]
            ]),
        )
    elif action == "game_back_to_menu":
        await call.message.edit_text(
            get_games_menu_text(call.message.chat.id),
            reply_markup=get_games_menu_keyboard(),
        )
    elif action == "game_cancel":
        await call.message.delete()
    elif action.startswith("game_accept_"):
        challenge_id = action.replace("game_accept_", "")
        await accept_challenge(call, challenge_id)
        return
    elif action == "game_cancel_challenge":
        to_remove = [cid for cid, ch in pending_challenges.items()
                     if ch.get('challenger') == call.from_user.id]
        for cid in to_remove:
            pending_challenges.pop(cid, None)
        await call.message.edit_text("❌ Вызов отменён", reply_markup=None)

    await call.answer()


@router.callback_query(lambda c: c.data and c.data.startswith('mines_difficulty_'))
async def minesweeper_difficulty_handler(call: CallbackQuery):
    difficulty = call.data.removeprefix('mines_difficulty_')
    settings = MINESWEEPER_DIFFICULTIES.get(difficulty)
    if not settings:
        await call.answer("❌ Неизвестная сложность", show_alert=True)
        return

    name, width, height, mine_count = settings
    game_id = f"{random.getrandbits(32):08x}"
    while game_id in minesweeper_games:
        game_id = f"{random.getrandbits(32):08x}"
    minesweeper_games[game_id] = {
        'chat_id': call.message.chat.id,
        'player_id': call.from_user.id,
        'difficulty': name,
        'width': width,
        'height': height,
        'mine_count': mine_count,
        'mines': set(random.sample(range(width * height), mine_count)),
        'revealed': set(),
        'flags': set(),
        'mode': 'open',
        'status': 'active',
        'first_open': True,
        'started_at': time.time(),
    }
    save_activity(call.message.chat.id, call.from_user.id, 'games')
    await draw_minesweeper_board(call.message, game_id)
    await call.answer()


def minesweeper_adjacent_cells(index: int, width: int, height: int):
    row, col = divmod(index, width)
    for next_row in range(max(0, row - 1), min(height, row + 2)):
        for next_col in range(max(0, col - 1), min(width, col + 2)):
            neighbor = next_row * width + next_col
            if neighbor != index:
                yield neighbor


def minesweeper_neighbor_count(game: dict, index: int) -> int:
    return sum(
        neighbor in game['mines']
        for neighbor in minesweeper_adjacent_cells(index, game['width'], game['height'])
    )


async def draw_minesweeper_board(message: Message, game_id: str):
    game = minesweeper_games.get(game_id)
    if not game:
        return

    width = game['width']
    height = game['height']
    game_over = game['status'] != 'active'
    keyboard = []
    number_labels = ('▫️', '1️⃣', '2️⃣', '3️⃣', '4️⃣', '5️⃣', '6️⃣', '7️⃣', '8️⃣')
    page_rows = 6 if height > 9 else height
    page_count = (height + page_rows - 1) // page_rows
    page = min(game.get('page', 0), page_count - 1)
    game['page'] = page
    first_row = page * page_rows
    last_row = min(first_row + page_rows, height)
    for row_index in range(first_row, last_row):
        row = []
        for col_index in range(width):
            index = row_index * width + col_index
            if index in game['flags']:
                label = '🚩'
            elif index in game['revealed']:
                label = '💣' if index in game['mines'] else number_labels[
                    minesweeper_neighbor_count(game, index)
                ]
            elif game_over and index in game['mines']:
                label = '💣'
            else:
                label = '⬜'

            callback_data = (
                "mines_noop" if game_over or index in game['revealed']
                else f"mines_cell_{game_id}_{index}"
            )
            row.append(InlineKeyboardButton(text=label, callback_data=callback_data))
        keyboard.append(row)

    if page_count > 1:
        keyboard.append([
            InlineKeyboardButton(
                text="◀️ Предыдущая",
                callback_data=f"mines_page_{game_id}_{page - 1}" if page > 0 else "mines_noop",
            ),
            InlineKeyboardButton(
                text="Следующая ▶️",
                callback_data=f"mines_page_{game_id}_{page + 1}" if page < page_count - 1 else "mines_noop",
            ),
        ])

    if game_over:
        keyboard.append([
            InlineKeyboardButton(text="🔄 Новая игра", callback_data="game_minesweeper"),
            InlineKeyboardButton(text="🎮 Игровое меню", callback_data="game_back_to_menu"),
        ])
        result = "Победа! Все безопасные клетки открыты 🎉" if game['status'] == 'won' else "Бум! Вы нашли мину 💥"
        title = f"💣 <b>Сапёр · {game['difficulty']}</b>\n{result}"
    else:
        mode_text = "Открытие клетки" if game['mode'] == 'open' else "Установка флажка"
        keyboard.append([
            InlineKeyboardButton(
                text=f"{'✅ ' if game['mode'] == 'open' else ''}🔎 Открыть клетку",
                callback_data=f"mines_mode_open_{game_id}",
            ),
            InlineKeyboardButton(
                text=f"{'✅ ' if game['mode'] == 'flag' else ''}🚩 Поставить флажок",
                callback_data=f"mines_mode_flag_{game_id}",
            ),
        ])
        flags_text = f"Флажки: {len(game['flags'])}/{game['mine_count']}\n"
        title = (
            f"💣 <b>Сапёр · {game['difficulty']} ({width}×{height})</b>\n"
            f"{flags_text}Режим: {mode_text}"
            + (f" · Страница {page + 1}/{page_count}" if page_count > 1 else "")
        )
    if game_over and page_count > 1:
        title += f"\nСтраница {page + 1}/{page_count}"

    await message.edit_text(title, reply_markup=InlineKeyboardMarkup(inline_keyboard=keyboard))


@router.callback_query(lambda c: c.data and c.data.startswith('mines_'))
async def minesweeper_action_handler(call: CallbackQuery):
    data = call.data
    if data == 'mines_noop':
        await call.answer()
        return

    if data.startswith('mines_page_'):
        _, _, game_id, page_text = data.split('_', 3)
        game = minesweeper_games.get(game_id)
        if not game:
            await call.answer("❌ Игра уже завершена или не найдена.", show_alert=True)
            return
        if call.from_user.id != game['player_id'] or call.message.chat.id != game['chat_id']:
            await call.answer("❌ Это игра другого игрока.", show_alert=True)
            return
        page = int(page_text)
        page_rows = 6 if game['height'] > 9 else game['height']
        page_count = (game['height'] + page_rows - 1) // page_rows
        if page < 0 or page >= page_count:
            await call.answer("❌ Такой страницы нет.", show_alert=True)
            return
        game['page'] = page
        await draw_minesweeper_board(call.message, game_id)
        await call.answer()
        return

    if data.startswith('mines_mode_'):
        _, _, mode, game_id = data.split('_', 3)
        game = minesweeper_games.get(game_id)
        if not game or game['status'] != 'active':
            await call.answer("❌ Игра уже завершена или не найдена.", show_alert=True)
            return
        if call.from_user.id != game['player_id'] or call.message.chat.id != game['chat_id']:
            await call.answer("❌ Это игра другого игрока.", show_alert=True)
            return
        if mode not in ('open', 'flag'):
            await call.answer("❌ Неизвестный режим.", show_alert=True)
            return
        game['mode'] = mode
        await draw_minesweeper_board(call.message, game_id)
        await call.answer()
        return

    if not data.startswith('mines_cell_'):
        await call.answer()
        return

    _, _, game_id, index_text = data.split('_', 3)
    game = minesweeper_games.get(game_id)
    if not game or game['status'] != 'active':
        await call.answer("❌ Игра уже завершена или не найдена.", show_alert=True)
        return
    if call.from_user.id != game['player_id'] or call.message.chat.id != game['chat_id']:
        await call.answer("❌ Это игра другого игрока.", show_alert=True)
        return

    index = int(index_text)
    if index < 0 or index >= game['width'] * game['height']:
        await call.answer("❌ Некорректная клетка.", show_alert=True)
        return

    if game['mode'] == 'flag':
        if index in game['revealed']:
            await call.answer("Эта клетка уже открыта.")
            return
        if index in game['flags']:
            game['flags'].remove(index)
        else:
            game['flags'].add(index)
    else:
        if index in game['flags']:
            await call.answer("Сначала снимите флажок с клетки.")
            return
        if game['first_open']:
            safe_start = set(minesweeper_adjacent_cells(index, game['width'], game['height']))
            safe_start.add(index)
            available_cells = [
                cell
                for cell in range(game['width'] * game['height'])
                if cell not in safe_start
            ]
            game['mines'] = set(random.sample(available_cells, game['mine_count']))
            game['flags'] = game['flags'] & set(available_cells)
            game['first_open'] = False

        if index in game['mines']:
            game['status'] = 'lost'
            game['revealed'].add(index)
        else:
            pending = [index]
            while pending:
                cell = pending.pop()
                if cell in game['revealed'] or cell in game['flags'] or cell in game['mines']:
                    continue
                game['revealed'].add(cell)
                if minesweeper_neighbor_count(game, cell) == 0:
                    pending.extend(minesweeper_adjacent_cells(cell, game['width'], game['height']))
            if len(game['revealed']) == game['width'] * game['height'] - game['mine_count']:
                game['status'] = 'won'

    await draw_minesweeper_board(call.message, game_id)
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
        f"⚔️ <b>ВЫЗОВ НА КНБ</b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"{mention(call.message.chat.id, call.from_user.id)} зовёт сыграть!\n\n"
        "Кто-нибудь из участников чата может принять вызов. "
        "Выборы делаются прямо здесь и останутся скрытыми до конца раунда.",
        reply_markup=kb
    )


async def accept_challenge(call: CallbackQuery, challenge_id: str):
    """Принятие вызова"""
    challenge = pending_challenges.get(challenge_id)

    if not challenge or time.time() - challenge.get('timestamp', 0) > 60:
        pending_challenges.pop(challenge_id, None)
        await call.answer("❌ Вызов устарел!", show_alert=True)
        return
    if challenge.get('game_type') == 'duel':
        if (
            not call.message
            or call.message.chat.type not in ('group', 'supergroup')
            or call.message.chat.id != challenge.get('chat_id')
        ):
            await call.answer("❌ Этот вызов доступен только в исходной группе.", show_alert=True)
            return
        if call.from_user.id != challenge.get('opponent'):
            await call.answer("❌ Этот вызов адресован другому игроку.", show_alert=True)
            return

    if challenge['challenger'] == call.from_user.id:
        await call.answer("❌ Нельзя принять свой вызов!", show_alert=True)
        return

    challenge['opponent'] = call.from_user.id
    pending_challenges.pop(challenge_id, None)
    if challenge['game_type'] == 'rps':
        await start_rps_duel(call, challenge)
    elif challenge['game_type'] == 'ttt':
        await start_ttt_duel(call, challenge)
    elif challenge['game_type'] == 'duel':
        await start_battle_duel(call, challenge)
    await call.answer("Вызов принят.")


@router.callback_query(lambda c: c.data and c.data.startswith('duel_decline_'))
async def duel_decline_handler(call: CallbackQuery):
    challenge_id = call.data.removeprefix('duel_decline_')
    challenge = pending_challenges.get(challenge_id)
    if not challenge or time.time() - challenge.get('timestamp', 0) > 60:
        pending_challenges.pop(challenge_id, None)
        await call.answer("❌ Вызов уже истёк.", show_alert=True)
        return
    if call.from_user.id != challenge.get('opponent'):
        await call.answer("❌ Только вызванный игрок может отказаться.", show_alert=True)
        return
    if not call.message or call.message.chat.id != challenge.get('chat_id'):
        await call.answer("❌ Вызов доступен только в исходной группе.", show_alert=True)
        return

    pending_challenges.pop(challenge_id, None)
    await call.message.edit_text(
        f"🙅 {mention(challenge['chat_id'], call.from_user.id)} отказался от дуэли.",
        reply_markup=None,
    )
    await call.answer("Вызов отклонён.")


def get_battle_duel_keyboard(game_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="👊 Удар", callback_data=f"duelmove_{game_id}_attack"),
            InlineKeyboardButton(text="💥 Сильный удар", callback_data=f"duelmove_{game_id}_heavy"),
        ],
        [InlineKeyboardButton(text="🛡 Защита", callback_data=f"duelmove_{game_id}_defend")],
    ])


def get_battle_duel_text(game: dict, waiting_for: Optional[int] = None) -> str:
    first, second = game['players']
    text = (
        f"🥊 <b>ДУЭЛЬ · РАУНД {game['round']}/{game['max_rounds']}</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"🔴 {mention(game['chat_id'], first)} — <b>{game['health'][first]} HP</b>\n"
        f"🔵 {mention(game['chat_id'], second)} — <b>{game['health'][second]} HP</b>\n\n"
    )
    if waiting_for is not None:
        text += (
            f"✅ Ход принял {mention(game['chat_id'], waiting_for)}.\n"
            "⏳ Ждём второго бойца. Выборы скрыты до конца раунда."
        )
    else:
        text += (
            "Выберите действие кнопками ниже — оба хода будут раскрыты одновременно.\n"
            "👊 Удар: надёжный · 💥 Сильный: мощнее, но может промахнуться · "
            "🛡 Защита: уменьшает входящий урон"
        )
    return text


async def start_battle_duel(call: CallbackQuery, challenge: dict):
    p1, p2 = challenge['challenger'], challenge['opponent']
    game_id = f"duel_{p1}_{p2}_{int(time.time())}"
    game = {
        'type': 'battle_duel',
        'players': [p1, p2],
        'health': {p1: 100, p2: 100},
        'choices': {},
        'round': 1,
        'max_rounds': 5,
        'choice_lock': asyncio.Lock(),
        'chat_id': challenge['chat_id'],
        'status': 'active',
        'started_at': time.time(),
    }
    active_games[game_id] = game
    await call.message.edit_text(
        get_battle_duel_text(game),
        reply_markup=get_battle_duel_keyboard(game_id),
    )


@router.callback_query(lambda c: c.data and c.data.startswith('duelmove_'))
async def battle_duel_move_handler(call: CallbackQuery):
    payload = call.data.removeprefix('duelmove_')
    game_id, separator, action = payload.rpartition('_')
    if not separator or action not in {'attack', 'heavy', 'defend'}:
        await call.answer("❌ Неизвестный ход.", show_alert=True)
        return

    game = active_games.get(game_id)
    if not game or game.get('type') != 'battle_duel' or game.get('status') != 'active':
        await call.answer("❌ Эта дуэль уже завершена.", show_alert=True)
        return
    if not call.message or call.message.chat.id != game['chat_id']:
        await call.answer("❌ Эта кнопка из другого чата.", show_alert=True)
        return

    async with game['choice_lock']:
        if active_games.get(game_id) is not game or game.get('status') != 'active':
            await call.answer("❌ Эта дуэль уже завершена.", show_alert=True)
            return
        if call.from_user.id not in game['players']:
            await call.answer("❌ Участвовать могут только вызванные игроки.", show_alert=True)
            return
        if call.from_user.id in game['choices']:
            await call.answer("✅ Ты уже выбрал действие. Ждём соперника.", show_alert=True)
            return

        game['choices'][call.from_user.id] = action
        save_activity(game['chat_id'], call.from_user.id, 'games')
        await call.answer("Ход принят. Соперник его пока не видит.")

        if len(game['choices']) < 2:
            await call.message.edit_text(
                get_battle_duel_text(game, waiting_for=call.from_user.id),
                reply_markup=get_battle_duel_keyboard(game_id),
            )
            return

        await resolve_battle_duel(game_id, call.message)


async def resolve_battle_duel(game_id: str, message: Message):
    game = active_games.get(game_id)
    if not game or game.get('status') != 'active':
        return

    first, second = game['players']
    choices = game['choices']
    action_names = {'attack': '👊 Удар', 'heavy': '💥 Сильный удар', 'defend': '🛡 Защита'}
    damage = {}
    descriptions = {}

    for attacker, defender in ((first, second), (second, first)):
        action = choices[attacker]
        if action == 'defend':
            damage[defender] = 0
            descriptions[attacker] = action_names[action]
            continue

        if action == 'heavy':
            hit = random.random() < 0.65
            raw_damage = random.randint(28, 40) if hit else 0
            descriptions[attacker] = f"{action_names[action]} — {'попадание' if hit else 'промах'}"
        else:
            raw_damage = random.randint(16, 24)
            descriptions[attacker] = action_names[action]

        if choices[defender] == 'defend':
            raw_damage = (raw_damage + 3) // 4
        damage[defender] = raw_damage

    for player_id in game['players']:
        game['health'][player_id] = max(0, game['health'][player_id] - damage[player_id])

    game['choices'] = {}
    game['round'] += 1
    first_hp, second_hp = game['health'][first], game['health'][second]
    finished = min(first_hp, second_hp) == 0 or game['round'] > game['max_rounds']

    if finished:
        if first_hp == second_hp:
            winner = None
            result = "🤝 <b>Ничья!</b>"
        else:
            winner = first if first_hp > second_hp else second
            result = f"🏆 Победитель: {mention(game['chat_id'], winner)}!"

        for player_id in game['players']:
            user = storage.get_user(game['chat_id'], player_id)
            user['duel_games'] = user.get('duel_games', 0) + 1
            if player_id == winner:
                user['duel_wins'] = user.get('duel_wins', 0) + 1
        storage.mark_dirty()
        await storage.save()

        game['status'] = 'finished'
        active_games.pop(game_id, None)
        await message.edit_text(
            f"🥊 <b>ДУЭЛЬ ОКОНЧЕНА · РАУНД {game['round'] - 1}</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            f"🔴 {mention(game['chat_id'], first)} — <b>{first_hp} HP</b> · {descriptions[first]}\n"
            f"🔵 {mention(game['chat_id'], second)} — <b>{second_hp} HP</b> · {descriptions[second]}\n\n"
            f"{result}\n\n"
            f"📊 Победы: {storage.get_user(game['chat_id'], first).get('duel_wins', 0)} — "
            f"{storage.get_user(game['chat_id'], second).get('duel_wins', 0)}",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="🎮 К игровому меню", callback_data="game_back_to_menu")]
            ]),
        )
        return

    await message.edit_text(
        f"🥊 <b>ИТОГ РАУНДА {game['round'] - 1}</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"🔴 {mention(game['chat_id'], first)}: {descriptions[first]} · получил −{damage[first]} HP\n"
        f"🔵 {mention(game['chat_id'], second)}: {descriptions[second]} · получил −{damage[second]} HP\n\n"
        f"❤️ {mention(game['chat_id'], first)} — <b>{first_hp} HP</b>\n"
        f"💙 {mention(game['chat_id'], second)} — <b>{second_hp} HP</b>\n\n"
        f"{get_battle_duel_text(game)}",
        reply_markup=get_battle_duel_keyboard(game_id),
    )


async def start_rps_duel(call: CallbackQuery, challenge: dict):
    """Запускает дуэль КНБ с выбором в групповом сообщении."""
    p1, p2 = challenge['challenger'], challenge['opponent']
    game_id = f"rps_{p1}_{p2}_{int(time.time())}"

    active_games[game_id] = {
        'type': 'rps_duel',
        'players': [p1, p2],
        'choices': {},
        'choice_lock': asyncio.Lock(),
        'chat_id': call.message.chat.id,
        'message_id': call.message.message_id,
        'started_at': time.time()
    }

    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🪨 Камень", callback_data=f"rpsduel_{game_id}_rock"),
            InlineKeyboardButton(text="✂️ Ножницы", callback_data=f"rpsduel_{game_id}_scissors"),
            InlineKeyboardButton(text="📄 Бумага", callback_data=f"rpsduel_{game_id}_paper"),
        ],
    ])
    await call.message.edit_text(
        f"⚔️ <b>ДУЭЛЬ КНБ НАЧАЛАСЬ!</b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"{mention(call.message.chat.id, p1)} против {mention(call.message.chat.id, p2)}\n\n"
        "Оба игрока выберите по одному варианту кнопкой ниже. "
        "Выбор соперника не будет показан до завершения раунда.\n\n"
        "🎯 Сделали выбор: <b>0/2</b>",
        reply_markup=keyboard,
    )


@router.callback_query(lambda c: c.data and c.data.startswith('rpsduel_'))
async def rps_duel_choice(call: CallbackQuery):
    """Принимает скрытый выбор игрока из группового сообщения."""
    parts = call.data.split('_')
    choice = parts[-1]
    game_id = '_'.join(parts[1:-1])
    if choice not in {'rock', 'scissors', 'paper'}:
        await call.answer("❌ Неизвестный выбор!", show_alert=True)
        return

    game = active_games.get(game_id)
    if not game:
        await call.answer("❌ Игра не найдена!", show_alert=True)
        return

    async with game['choice_lock']:
        if active_games.get(game_id) is not game:
            await call.answer("❌ Игра уже завершена!", show_alert=True)
            return

        if call.from_user.id not in game['players']:
            await call.answer("❌ Это не ваша игра!", show_alert=True)
            return

        if call.from_user.id in game['choices']:
            await call.answer("✅ Вы уже сделали выбор!", show_alert=True)
            return

        game['choices'][call.from_user.id] = choice
        await call.answer("✅ Выбор принят. Он скрыт до завершения раунда.")

        if len(game['choices']) == 2:
            await resolve_rps_duel(game_id, game['chat_id'], call.message)
            return

        selected_player = mention(game['chat_id'], call.from_user.id)
        await call.message.edit_text(
            f"⚔️ <b>ДУЭЛЬ КНБ</b>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"{mention(game['chat_id'], game['players'][0])} против "
            f"{mention(game['chat_id'], game['players'][1])}\n\n"
            f"✅ Выбор принял: {selected_player}\n"
            "⏳ Ждём второго игрока — его выбор останется скрытым.",
            reply_markup=call.message.reply_markup,
        )


async def resolve_rps_duel(game_id: str, chat_id: int, game_message: Message):
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

    await game_message.edit_text(
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
    except Exception:
        msg = await message.answer(title, reply_markup=kb)
        game['message_id'] = msg.message_id


@router.callback_query(lambda c: c.data and c.data.startswith('ttt_'))
async def ttt_move_handler(call: CallbackQuery):
    """Обработка хода в TTT"""
    if call.data == 'ttt_noop':
        await call.answer("Клетка занята", show_alert=True)
        return
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
        await asyncio.sleep(120)
        now = time.time()
        storage._cleanup_old_games()
        _prune_chat_default_permissions_cache(time.monotonic())

        for store, ttl in (
            (birthday_wizards, BDAY_WIZARD_TTL),
            (meme_sessions, MEME_SESSION_TTL),
            (activity_graph_wizards, ACTIVITY_GRAPH_WIZARD_TTL),
        ):
            expired = [
                key
                for key, value in store.items()
                if not isinstance(value, dict)
                or not isinstance(value.get('created_at'), (int, float))
                or now - value['created_at'] > ttl
            ]
            for key in expired:
                store.pop(key, None)

        expired = [gid for gid, game in active_games.items()
                   if now - game.get('started_at', now) > 3600]
        for gid in expired:
            del active_games[gid]

        expired_ch = [cid for cid, ch in pending_challenges.items()
                      if now - ch.get('timestamp', now) > 60]
        for cid in expired_ch:
            del pending_challenges[cid]
        expired_minesweeper = [
            game_id for game_id, game in minesweeper_games.items()
            if now - game.get('started_at', now) > 3600
        ]
        for game_id in expired_minesweeper:
            del minesweeper_games[game_id]
        expired_wordle = [
            game_id for game_id, game in wordle.games.items()
            if now - game.get('started_at', now) > 3600
        ]
        for game_id in expired_wordle:
            del wordle.games[game_id]


# ==================== ТЕКСТОВЫЕ КОМАНДЫ ====================

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

POLL_DRAFTS: Dict[str, Dict[str, Any]] = {}
POLL_DRAFT_TTL = 60 * 60
POLL_DEADLINE_OPTIONS = (
    (300, '5 мин.'),
    (600, '10 мин.'),
    (3600, '1 час'),
    (86400, '1 день'),
)
POLL_SETTING_LABELS = (
    ('names', 'Имена участников'),
    ('multiple', 'Несколько ответов'),
    ('adding', 'Добавление вариантов'),
    ('revoting', 'Изменение ответа'),
    ('shuffle', 'Случайный порядок'),
)


def _cleanup_poll_drafts():
    now = time.time()
    expired = [
        draft_id for draft_id, draft in POLL_DRAFTS.items()
        if now - draft['created_at'] > POLL_DRAFT_TTL
    ]
    for draft_id in expired:
        POLL_DRAFTS.pop(draft_id, None)


def _poll_settings_keyboard(draft_id: str, draft: Dict[str, Any]) -> InlineKeyboardMarkup:
    settings = draft['settings']
    rows = []
    callback_prefix = f'pollcfg:{draft_id}:'

    for setting, label in POLL_SETTING_LABELS:
        enabled = settings[setting]
        rows.append([
            InlineKeyboardButton(
                text=f'{"✅" if enabled else "▫️"} {label}',
                callback_data=f'{callback_prefix}{setting}',
            )
        ])

    correct_enabled = settings['correct']
    rows.append([
        InlineKeyboardButton(
            text=f'{"✅" if correct_enabled else "▫️"} Правильный ответ',
            callback_data=f'{callback_prefix}correct',
        )
    ])
    if correct_enabled:
        correct_options = set(settings['correct_options'])
        for start in range(0, len(draft['options']), 2):
            option_buttons = []
            for index in range(start, min(start + 2, len(draft['options']))):
                marker = '✅' if index in correct_options else '▫️'
                label = draft['options'][index][:30]
                option_buttons.append(InlineKeyboardButton(
                    text=f'{marker} {index + 1}. {label}',
                    callback_data=f'{callback_prefix}answer{index}',
                ))
            rows.append(option_buttons)

    deadline = settings['deadline']
    rows.append([
        InlineKeyboardButton(
            text=f'{"✅" if deadline else "▫️"} Ограничение срока',
            callback_data=f'{callback_prefix}deadline',
        )
    ])
    if deadline:
        rows.append([
            InlineKeyboardButton(
                text=f'{"🔘" if deadline == seconds else "▫️"} {label}',
                callback_data=f'{callback_prefix}time{seconds}',
            )
            for seconds, label in POLL_DEADLINE_OPTIONS
        ])

    rows.extend([
        [InlineKeyboardButton(text='Подтвердить', callback_data=f'{callback_prefix}confirm')],
        [InlineKeyboardButton(text='Отмена', callback_data=f'{callback_prefix}cancel')],
    ])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _poll_settings_text(draft: Dict[str, Any]) -> str:
    question = html.escape(draft['question'])
    options = '\n'.join(
        f'{index}. {html.escape(option)}'
        for index, option in enumerate(draft['options'], start=1)
    )
    return (
        f'⚙️ <b>Настройки опроса</b>\n\n'
        f'<b>Вопрос:</b> {question}\n'
        f'<b>Варианты:</b>\n{options}\n\n'
        f'Выберите настройки кнопками и нажмите «Подтвердить».'
    )


async def cmd_poll(msg: Message, cmd_name: str = 'опрос'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    command_text = strip_command_prefix(msg.text, msg.chat.id)
    _, separator, text = command_text.partition(' ')
    if not separator and command_text.casefold() in {'опрос', 'poll'}:
        text = ''
    elif not separator:
        text = command_text
    text = text.strip()

    if not text:
        return await msg.answer(
            "❌ <code>!опрос Вопрос?</code> или "
            "<code>!опрос Вопрос? / Вариант 1 / Вариант 2</code>"
        )

    parts = [part.strip() for part in re.split(r'[/\\]', text)]
    question = parts[0]
    if not question:
        return await msg.answer("❌ Укажите вопрос. Например: <code>!опрос Пойдём гулять?</code>")

    if len(parts) == 1:
        options = ['Да', 'Нет']
    else:
        options = [option for option in parts[1:] if option][:10]
        if len(options) < 2:
            return await msg.answer(
                "❌ Добавьте минимум 2 варианта, разделяя их символом <code>/</code> или <code>\\</code>."
            )

    _cleanup_poll_drafts()
    draft_id = uuid.uuid4().hex[:10]
    draft = {
        'owner_id': msg.from_user.id,
        'chat_id': msg.chat.id,
        'source_message_id': msg.message_id,
        'created_at': time.time(),
        'question': question,
        'options': options,
        'settings': {
            'names': True,
            'multiple': True,
            'adding': True,
            'revoting': True,
            'shuffle': True,
            'correct': False,
            'correct_options': [],
            'deadline': None,
        },
    }

    try:
        menu_message = await msg.answer(
            _poll_settings_text(draft),
            reply_markup=_poll_settings_keyboard(draft_id, draft),
        )
    except TelegramAPIError:
        logger.exception("Не удалось открыть настройки опроса")
        raise

    draft['menu_message_id'] = menu_message.message_id
    POLL_DRAFTS[draft_id] = draft


@router.callback_query(F.data.startswith('pollcfg:'))
async def poll_settings_callback(call: CallbackQuery):
    if not call.message or not call.from_user:
        return await call.answer()

    _cleanup_poll_drafts()
    try:
        _, draft_id, action = call.data.split(':', 2)
    except (AttributeError, ValueError):
        return await call.answer("Настройки опроса недоступны.", show_alert=True)

    draft = POLL_DRAFTS.get(draft_id)
    if not draft:
        return await call.answer("Срок настройки истёк. Создайте опрос заново.", show_alert=True)
    if (
        call.from_user.id != draft['owner_id']
        or call.message.chat.id != draft['chat_id']
        or call.message.message_id != draft['menu_message_id']
    ):
        return await call.answer("Эти настройки создал другой пользователь.", show_alert=True)

    settings = draft['settings']
    if action == 'cancel':
        POLL_DRAFTS.pop(draft_id, None)
        await call.message.edit_text("Создание опроса отменено.", reply_markup=None)
        return await call.answer()

    if action == 'confirm':
        if settings['correct'] and not settings['correct_options']:
            return await call.answer(
                "Выберите хотя бы один правильный вариант.",
                show_alert=True,
            )

        poll_kwargs = {
            'question': draft['question'],
            'options': draft['options'],
            'is_anonymous': not settings['names'],
            'type': 'quiz' if settings['correct'] else 'regular',
            'allows_multiple_answers': settings['multiple'],
            'allow_adding_options': settings['adding'],
            'allows_revoting': settings['revoting'],
            'shuffle_options': settings['shuffle'],
        }
        if settings['correct']:
            poll_kwargs['correct_option_ids'] = settings['correct_options']
        if settings['deadline']:
            poll_kwargs['close_date'] = datetime.now(timezone.utc) + timedelta(
                seconds=settings['deadline']
            )

        try:
            await call.message.answer_poll(**poll_kwargs)
        except TelegramAPIError as exc:
            logger.exception("Ошибка создания реального опроса")
            return await call.answer(
                f"Не удалось создать опрос: {str(exc)[:150]}",
                show_alert=True,
            )

        POLL_DRAFTS.pop(draft_id, None)
        try:
            await call.message.edit_text("✅ Опрос создан.", reply_markup=None)
        except TelegramAPIError:
            logger.exception("Не удалось обновить меню после создания опроса")
        try:
            await call.bot.delete_message(
                chat_id=draft['chat_id'],
                message_id=draft['source_message_id'],
            )
        except TelegramAPIError as exc:
            logger.debug("Не удалось удалить сообщение с командой опроса: %s", exc)
        return await call.answer()

    if action in dict(POLL_SETTING_LABELS):
        settings[action] = not settings[action]
    elif action == 'correct':
        settings['correct'] = not settings['correct']
        settings['correct_options'] = []
    elif action.startswith('answer'):
        try:
            option_index = int(action[6:])
        except ValueError:
            return await call.answer("Неизвестный вариант ответа.", show_alert=True)
        if not 0 <= option_index < len(draft['options']):
            return await call.answer("Такого варианта ответа нет.", show_alert=True)
        selected = set(settings['correct_options'])
        if option_index in selected:
            selected.remove(option_index)
        else:
            selected.add(option_index)
        settings['correct_options'] = sorted(selected)
    elif action == 'deadline':
        settings['deadline'] = None if settings['deadline'] else POLL_DEADLINE_OPTIONS[0][0]
    elif action.startswith('time'):
        try:
            seconds = int(action[4:])
        except ValueError:
            return await call.answer("Неизвестный срок опроса.", show_alert=True)
        if seconds not in {value for value, _ in POLL_DEADLINE_OPTIONS}:
            return await call.answer("Неизвестный срок опроса.", show_alert=True)
        settings['deadline'] = seconds
    else:
        return await call.answer("Неизвестная настройка.", show_alert=True)

    try:
        await call.message.edit_text(
            _poll_settings_text(draft),
            reply_markup=_poll_settings_keyboard(draft_id, draft),
        )
    except TelegramBadRequest as exc:
        if 'message is not modified' not in str(exc).casefold():
            logger.exception("Не удалось обновить настройки опроса")
            return await call.answer("Не удалось обновить настройки.", show_alert=True)
    return await call.answer()


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

        current = weather_data.get('current') or {}
        daily = weather_data.get('daily') or {}
        if not isinstance(current, dict) or not isinstance(daily, dict):
            raise ValueError("Некорректная структура ответа погодного API")

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
        wind_dir = current.get('wind_direction_10m') or 0
        directions = ['⬆️ С', '↗️ СВ', '➡️ В', '↘️ ЮВ', '⬇️ Ю', '↙️ ЮЗ', '⬅️ З', '↖️ СЗ']
        wind_dir_text = directions[round(wind_dir / 45) % 8]

        # Давление
        pressure = current.get('pressure_msl') or 0
        precipitation = current.get('precipitation') or 0
        rain = current.get('rain') or 0
        snowfall = current.get('snowfall') or 0
        gusts = current.get('wind_gusts_10m') or 0
        uv_index = current.get('uv_index') or 0
        def format_clock(value: str) -> str:
            return value.split('T')[-1][:5] if value else '--:--'

        def daily_value(key: str, index: int, default: Any = 0):
            values = daily.get(key)
            if not isinstance(values, list) or index >= len(values):
                return default
            return values[index] if values[index] is not None else default

        forecast_lines = []
        forecast_dates = daily.get('time', [])
        if not isinstance(forecast_dates, list):
            forecast_dates = []
        for index, forecast_date in enumerate(forecast_dates):
            forecast_code = daily_value('weather_code', index, 0)
            forecast_emoji, _ = weather_codes.get(forecast_code, ('🌡️', 'Неизвестно'))
            forecast_min = daily_value('temperature_2m_min', index)
            forecast_max = daily_value('temperature_2m_max', index)
            forecast_probability = daily_value('precipitation_probability_max', index)
            forecast_sum = daily_value('precipitation_sum', index)
            day_label = 'сегодня' if index == 0 else 'завтра' if index == 1 else forecast_date[5:]
            forecast_lines.append(
                f"{forecast_emoji} <b>{day_label}</b>: {forecast_min:.0f}...{forecast_max:.0f}°C, "
                f"осадки {forecast_probability}%, {forecast_sum:.1f} мм"
            )

        # Формируем ответ
        text = (
            f"{emoji} <b>Погода — {safe_city_name}{', ' + safe_country if safe_country else ''}</b>\n"
            f"{UI_LINE}\n"
            f"🌡 Температура: <b>{current.get('temperature_2m') or 0}°C</b>\n"
            f"🤔 Ощущается: <b>{current.get('apparent_temperature') or 0}°C</b>\n"
            f"📝 Описание: <b>{description}</b>\n"
            f"💧 Влажность: <b>{current.get('relative_humidity_2m') or 0}%</b>\n"
            f"💨 Ветер: <b>{current.get('wind_speed_10m') or 0} км/ч {wind_dir_text}</b>\n"
            f"💨 Порывы: <b>до {gusts} км/ч</b>\n"
            f"🌧 Осадки сейчас: <b>{precipitation:.1f} мм</b>"
            f"{f' (дождь {rain:.1f} мм)' if rain else ''}"
            f"{f' (снег {snowfall:.1f} мм)' if snowfall else ''}\n"
            f"☀️ UV-индекс: <b>{uv_index:.1f}</b>\n"
            f"🔵 Давление: <b>{pressure:.0f} гПа</b>\n"
            f"🌅 Восход: <b>{format_clock(daily_value('sunrise', 0, ''))}</b>  "
            f"🌇 Закат: <b>{format_clock(daily_value('sunset', 0, ''))}</b>\n\n"
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


CANDY_STEAL_SUCCESS_TEXTS = (
    "🐻 Валера дождался, пока Паша отвлёкся, и стащил {candy_amount}.",
    "🍬 Валера устроил набег на сладости и принёс {candy_amount}.",
    "🧊 Пока Паша заглядывал в холодильник, Валера прихватил {candy_amount}.",
    "🤫 Валера прошмыгнул мимо Паши и спрятал {candy_amount}.",
    "🎉 Валера так ловко отвлёк Пашу, что утащил {candy_amount}.",
    "🍭 Паша отвернулся всего на секунду — Валера уже унёс {candy_amount}.",
    "🥷 Валера включил режим ниндзя и вынес {candy_amount}.",
    "📦 Валера обнаружил сладкий тайник Паши и забрал оттуда {candy_amount}.",
    "😋 Валера уверяет, что конфеты сами прыгнули к нему. Он прихватил {candy_amount}.",
    "🚙 Валера подъехал на воображаемом джипе и увёз {candy_amount}.",
    "🔍 Пока Паша искал пропажу, Валера уже унёс {candy_amount}.",
    "✨ Валера провёл блестящую операцию и прихватил {candy_amount}.",
    "🧸 Валера спрятался за игрушками и незаметно забрал {candy_amount}.",
    "🎬 В новой серии «Познавателя» Валера успешно добыл {candy_amount}.",
    "🧁 Валера отвлёк Пашу разговором о сладостях и прихватил {candy_amount}.",
    "👀 Паша моргнул — и Валера уже уносит {candy_amount}.",
    "🗝️ Валера подобрал ключ к сладкому шкафчику и достал {candy_amount}.",
    "🎒 Валера вернулся из вылазки и принёс {candy_amount}.",
    "🌟 Валера сегодня особенно ловкий: он утащил {candy_amount}, а Паша заметил пропажу.",
    "🏃 Валера быстро смылся и унёс {candy_amount}.",
)

CANDY_STEAL_FAILURE_TEXTS = (
    "🚨 Паша услышал шуршание обёртки и поймал Валеру на месте.",
    "👀 Паша заметил, как Валера потянулся к конфетам, — операция сорвалась.",
    "🧊 Валера открыл холодильник, но Паша уже ждал его у дверцы.",
    "🤫 Валера старался красться тихо, но фантик выдал его с головой.",
    "🐻 Валера почти добрался до сладостей, однако Паша вовремя обернулся.",
    "📦 Валера нашёл тайник, но Паша успел закрыть его раньше.",
    "🎬 Неудачный дубль: Паша поймал Валеру до того, как тот добрался до конфет.",
    "🕵️ Паша раскрыл сладкий заговор Валеры. Добычи сегодня не будет.",
    "😅 Валера споткнулся о собственную хитрость — Паша всё заметил.",
    "🔔 Дверца холодильника тихонько звякнула, и Паша тут же поймал Валеру.",
    "🏃 Валера попытался скрыться, но Паша оказался быстрее.",
    "🧸 Игрушки не помогли Валере спрятаться: Паша его обнаружил.",
    "🍬 Паша пересчитал запасы прямо перед вылазкой. Валера остался ни с чем.",
    "🚫 Паша сказал «не сегодня» и убрал конфеты подальше от Валеры.",
    "🫣 Валера слишком увлёкся выбором конфет и не заметил вернувшегося Пашу.",
    "🔦 Паша включил свет в самый неподходящий момент — Валера попался.",
    "🛑 Сладкая операция отменена: Паша заметил подозрительное движение.",
    "😮 Валера потянулся за конфетой, а Паша уже стоял за спиной.",
    "🧤 Перчатки не спасли: Паша узнал Валеру по характерному шороху фантика.",
    "📹 Камера в комнате всё записала — Паша успел остановить Валеру.",
)

CANDY_STEAL_COOLDOWN_TEXTS = (
    "🐻 Валера затаился после вылазки. Новая попытка через {wait}.",
    "🤫 Паша пока начеку — Валере стоит выждать {wait}.",
    "🍬 Валера устроил перекус и восстановит силы через {wait}.",
    "🧊 Холодильник под наблюдением. Возвращайся через {wait}.",
    "🥷 Валера залёг на дно. До следующей вылазки {wait}.",
    "🔍 Паша пересчитывает сладости — подожди {wait}.",
    "😇 Валера делает вид, что ни при чём. Попробуй снова через {wait}.",
    "📋 Сладкая операция ещё не готова к повтору. Осталось {wait}.",
    "🗺️ Валера прокладывает новый маршрут. Запасись терпением на {wait}.",
    "🍬 Фантики ещё шуршат — пора подождать {wait}.",
    "👀 Паша пока не отвлекается. Новая попытка через {wait}.",
    "🤐 Валера ждёт, когда в комнате станет потише. Осталось {wait}.",
    "🔐 Конфетный тайник пока под присмотром. Возвращайся через {wait}.",
    "🎭 Валера отвлекает Пашу разговором, но повторить вылазку сможет через {wait}.",
    "🚙 Джип Валеры на сладком пит-стопе. До старта {wait}.",
    "📝 План требует паузы — следующая вылазка через {wait}.",
    "🐻 Валера шепчет: «Нужно выждать ещё {wait}».",
    "🕵️ Паша всё ещё рядом с запасами. Попробуй снова через {wait}.",
    "⚡ Сладкая миссия перезаряжается. Осталось {wait}.",
    "😋 Валера копит хитрость для нового захода. Ждать {wait}.",
)


def _candy_steal_reward_range(streak: int) -> Tuple[int, int]:
    return min(1 + streak, 10), min(3 + 2 * streak, 50)


def _format_candy_count(count: int, *, accusative: bool = False) -> str:
    last_two_digits = count % 100
    last_digit = count % 10
    if 11 <= last_two_digits <= 14:
        noun = 'конфет'
    elif last_digit == 1:
        noun = 'конфету' if accusative else 'конфета'
    elif 2 <= last_digit <= 4:
        noun = 'конфеты'
    else:
        noun = 'конфет'
    return f'{count} {noun}'


async def cmd_steal_candy(
    msg: Message,
    args: str = '',
    cmd_name: str = 'украсть',
):
    if args or msg.reply_to_message:
        return await rp_handler(msg)

    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return

    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    user = storage.get_user(msg.chat.id, msg.from_user.id)
    now = time.time()
    candies = user.get('candies', 0)
    if not isinstance(candies, int) or isinstance(candies, bool) or candies < 0:
        candies = 0

    next_at = user.get('candy_steal_next_at', 0)
    if not isinstance(next_at, (int, float)) or isinstance(next_at, bool):
        next_at = 0

    remaining = next_at - now
    if remaining > 0:
        minutes = max(1, int(remaining / 60 + 0.999))
        cooldown_text = random.choice(CANDY_STEAL_COOLDOWN_TEXTS).format(
            wait=f"<b>{format_mute_duration(minutes)}</b>",
        )
        return await msg.answer(
            f"{cooldown_text}\n\n"
            f"🍬 В запасе: <b>{_format_candy_count(candies)}</b>."
        )

    successes = user.get('candy_steal_successes', 0)
    if not isinstance(successes, int) or isinstance(successes, bool) or successes < 0:
        successes = 0
    streak = user.get('candy_steal_streak', 0)
    if not isinstance(streak, int) or isinstance(streak, bool) or streak < 0:
        streak = 0

    if random.random() < 0.15:
        lost = min(candies, (candies + 9) // 10)
        candies -= lost
        user['candies'] = candies
        user['candy_steal_streak'] = 0
        user['candy_steal_next_at'] = now + 3 * 60 * 60
        storage.mark_dirty()
        await storage.save()
        failure_text = random.choice(CANDY_STEAL_FAILURE_TEXTS)
        return await msg.answer(
            f"{failure_text}\n\n"
            f"📉 Потеряно: <b>{_format_candy_count(lost)}</b>.\n"
            f"🍬 В запасе: <b>{_format_candy_count(candies)}</b>.\n"
            f"🔥 Серия успехов сброшена.\n"
            f"⏳ Новая вылазка через <b>3 часа</b>."
        )

    min_candies, max_candies = _candy_steal_reward_range(streak)
    stolen = random.randint(min_candies, max_candies)
    candies += stolen
    streak += 1
    user['candies'] = candies
    user['candy_steal_successes'] = successes + 1
    user['candy_steal_streak'] = streak
    user['candy_steal_next_at'] = now + 24 * 60 * 60
    storage.mark_dirty()
    await storage.save()
    success_text = random.choice(CANDY_STEAL_SUCCESS_TEXTS).format(
        candy_amount=_format_candy_count(stolen, accusative=True),
    )
    next_min_candies, next_max_candies = _candy_steal_reward_range(streak)
    return await msg.answer(
        f"{success_text}\n\n"
        f"🍬 <b>Запас:</b> {_format_candy_count(candies)}\n"
        f"🔥 <b>Серия успехов:</b> {streak}\n"
        f"🎯 <b>Следующая добыча:</b> {next_min_candies}–{next_max_candies} 🍬\n"
        f"⏳ <b>Новая вылазка:</b> через 24 часа."
    )


async def cmd_candy_balance(msg: Message, cmd_name: str = 'баланс'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return

    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    user = storage.get_user(msg.chat.id, msg.from_user.id)
    candies = user.get('candies', 0)
    if not isinstance(candies, int) or isinstance(candies, bool) or candies < 0:
        candies = 0
    streak = user.get('candy_steal_streak', 0)
    if not isinstance(streak, int) or isinstance(streak, bool) or streak < 0:
        streak = 0
    min_candies, max_candies = _candy_steal_reward_range(streak)

    next_at = user.get('candy_steal_next_at', 0)
    if not isinstance(next_at, (int, float)) or isinstance(next_at, bool):
        next_at = 0
    remaining = next_at - time.time()
    if remaining > 0:
        minutes = max(1, int(remaining / 60 + 0.999))
        next_attempt = random.choice(CANDY_STEAL_COOLDOWN_TEXTS).format(
            wait=f"<b>{format_mute_duration(minutes)}</b>",
        )
    else:
        next_attempt = "⏳ Валера уже готов к новой вылазке!"

    await msg.answer(
        f"🍬 <b>Запас Валеры:</b> {_format_candy_count(candies)}\n"
        f"🔥 <b>Серия успехов:</b> {streak}\n"
        f"🎯 <b>Следующая добыча:</b> {min_candies}–{max_candies} 🍬\n"
        f"{next_attempt}"
    )


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

    chat_users = storage.load_chat_users(msg.chat.id)
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
    today = kaliningrad_now().date().isoformat()
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
        result = random.choice(('Орёл', 'Решка'))
        await msg.answer(f'🪙 Выпало: <b>{result}</b>')
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

    target_arg = parts[1] if len(parts) > 1 else None
    rank_in_reply = (
        msg.reply_to_message and msg.reply_to_message.from_user
        and target_arg and target_arg.isdigit()
        and int(target_arg) <= MAX_RANK and len(parts) == 2
    )
    if has_explicit_target(msg, target_arg) and not rank_in_reply:
        target_mention = get_target_mention_span(msg, target_arg)
        tid = await get_target(msg, target_arg)
        if not tid:
            return await msg.answer("❌ Пользователь не найден")
        if target_mention:
            trailing = msg.text[target_mention[2]:].strip().split()
            if trailing:
                rank_arg = trailing[0]
        elif len(parts) > 2:
            rank_arg = parts[2]
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            rank_arg = parts[1]
    else:
        return await msg.answer("❌ <code>повысить @user 3</code> или ответом")

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
    except Exception:
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

    target_arg = parts[1] if len(parts) > 1 else None
    rank_in_reply = (
        msg.reply_to_message and msg.reply_to_message.from_user
        and target_arg and target_arg.isdigit()
        and int(target_arg) <= MAX_RANK and len(parts) == 2
    )
    if has_explicit_target(msg, target_arg) and not rank_in_reply:
        target_mention = get_target_mention_span(msg, target_arg)
        tid = await get_target(msg, target_arg)
        if target_mention:
            trailing = msg.text[target_mention[2]:].strip().split()
            if trailing:
                rank_arg = trailing[0]
        elif len(parts) > 2:
            rank_arg = parts[2]
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            rank_arg = parts[1]
    else:
        return await msg.answer("❌ <code>понизить @user</code> или ответом")

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
    except Exception:
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
    bot_can_edit_tags = (
        bot_member.status == 'creator'
        or (
            bot_member.status == 'administrator'
            and bool(getattr(bot_member, 'can_manage_tags', False))
        )
    )
    return target_is_admin, target_is_admin and bot_can_set_title, bot_can_edit_tags

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
    target_arg = parts[0] if parts else None
    target_mention = get_target_mention_span(msg, target_arg) if target_arg else None
    explicit_target = bool(
        target_arg
        and has_explicit_target(msg, target_arg)
        and (
            len(parts) > 1
            or target_arg.startswith(('@', 'id:'))
            or target_mention
        )
    )

    if explicit_target:
        target_id = await get_target(msg, target_arg)
        is_other_user = target_id != msg.from_user.id if target_id else True
        if is_other_user and storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) < 1:
            return await msg.answer("❌ Сменить тег другому человеку могут только администраторы.")
        if not target_id:
            return await msg.answer("❌ Не удалось найти пользователя.")
        if len(parts) < 2:
            return await msg.answer("❌ Укажите тег после @user. Пример: <code>!погоняло @user Крутой</code>")
        if target_mention:
            target_name = msg.text[target_mention[2]:].strip()
        else:
            target_name = ' '.join(parts[1:]).strip()
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        target_id = msg.reply_to_message.from_user.id
        target_name = args.strip()
        is_other_user = target_id != msg.from_user.id
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
    storage.get_user(msg.chat.id, target_id)['custom_tag'] = text
    storage.invalidate_user_cache(msg.chat.id, target_id)
    mention_cache.invalidate(f"mention_{msg.chat.id}_{target_id}")
    storage.mark_dirty()
    await storage.save()

    tag_errors = []
    target_is_admin, can_set_title, bot_can_manage_tags = await _get_native_tag_permissions(msg.chat.id, target_id)
    native_title_updated = False
    if can_set_title:
        if len(text) <= 16:
            try:
                await bot.set_chat_administrator_custom_title(msg.chat.id, target_id, text)
                native_title_updated = True
            except Exception as e:
                logger.warning(f"set_chat_administrator_custom_title не сработал для {target_id} в {msg.chat.id}: {e}")

    if target_is_admin:
        if len(text) > 16:
            return await msg.answer(
                f"✅ Тег сохранён в профиле бота (до {MAX_TAG_LENGTH} символов).\n"
                "⚠️ Админский тег Telegram не изменён: его длина ограничена 16 символами."
            )
        if native_title_updated:
            return await msg.answer("✅ Тег сохранён и админский заголовок Telegram обновлён.")
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

    safe_text = html.escape(text, quote=False)
    if target_id == msg.from_user.id:
        result_msg = f"✅ Погоняло изменено!\n🏷️ <b>{safe_text}</b>"
    else:
        result_msg = f"✅ Погоняло для {mention(msg.chat.id, target_id)} изменено на <b>{safe_text}</b>"

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
    target_parts = args.split(maxsplit=1)
    target_arg = target_parts[0] if target_parts else None
    target_mention = get_target_mention_span(msg, target_arg) if target_arg else None
    explicit_target = bool(
        target_arg
        and has_explicit_target(msg, target_arg)
        and (
            len(target_parts) > 1
            or target_arg.startswith(('@', 'id:'))
            or target_mention
        )
    )
    if explicit_target:
        target_id = await get_target(msg, target_arg)
        if not target_id:
            return await msg.answer("❌ Не удалось найти пользователя.")
        if target_mention:
            new_name = msg.text[target_mention[2]:].strip()
        else:
            new_name = target_parts[1].strip() if len(target_parts) > 1 else ''
        if not new_name:
            u = storage.get_user(msg.chat.id, target_id)
            custom_name = html.escape(str(u.get('custom_name') or 'не установлен'), quote=False)
            return await msg.answer(
                f"👤 <b>{mention(msg.chat.id, target_id)}</b>\n📝 Ник: {custom_name}",
                disable_web_page_preview=True,
            )
    elif msg.reply_to_message and msg.reply_to_message.from_user:
        target_id = msg.reply_to_message.from_user.id

    if target_id != msg.from_user.id:
        rank = storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0)
        if rank < 1:
            return await msg.answer("❌ Изменять ник другим участникам могут только администраторы.")

    if new_name.lower() == 'сбросить':
        storage.get_user(msg.chat.id, target_id)['custom_name'] = ''
        storage.invalidate_user_cache(msg.chat.id, target_id)
        storage.invalidate_user_identity_cache(msg.chat.id)
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
    storage.invalidate_user_identity_cache(msg.chat.id)

    storage.mark_dirty()
    await storage.save()

    safe_new_name = html.escape(new_name, quote=False)
    if target_id == msg.from_user.id:
        return await msg.answer(f"✅ Ник изменён!\n📝 {old} → <b>{safe_new_name}</b>")
    return await msg.answer(
        f"✅ Ник для {mention(msg.chat.id, target_id)} изменён!\n📝 {old} → <b>{safe_new_name}</b>")


REPORT_LAST: Dict[Tuple[int, int], float] = {}


async def cmd_report(msg: Message, cmd_name: str = 'репорт'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    parts = (msg.text or '').split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        return await msg.answer("❌ Напишите текст жалобы: <code>!репорт описание</code>")

    key = (msg.chat.id, msg.from_user.id)
    now = time.monotonic()
    if now - REPORT_LAST.get(key, 0) < 300:
        return await msg.answer("⏳ Жалобу можно отправлять раз в 5 минут.")
    REPORT_LAST[key] = now
    if len(REPORT_LAST) > 5000:
        cutoff = now - 600
        for cache_key, timestamp in list(REPORT_LAST.items()):
            if timestamp < cutoff:
                del REPORT_LAST[cache_key]
        if len(REPORT_LAST) > 5000:
            oldest = sorted(REPORT_LAST.items(), key=lambda item: item[1])
            for cache_key, _ in oldest[:len(REPORT_LAST) - 5000]:
                REPORT_LAST.pop(cache_key, None)
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

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
            await telegram_call_with_retry(
                bot.send_message,
                admin.id,
                notification,
                disable_web_page_preview=True,
            )
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
        "Также отклоняет частые нажатия кнопок (10+ за 5 секунд). "
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
    'cmd_prefix': 5,
    'cmd_mute': 1, 'cmd_unmute': 1,
    'cmd_ban': 3, 'cmd_unban': 3, 'cmd_kick': 3,
    'cmd_moderation_history': 1, 'cmd_moderation_log': 1,
    'cmd_moderation_stats': 1, 'cmd_reason_templates': 2,
    'cmd_moderation_auto_delete': 5,
    'cmd_join_requests': 5, 'cmd_filters': 5, 'cmd_captcha': 5,
    'cmd_raid_mode': 5, 'cmd_freeze_chat': 5, 'cmd_unfreeze_chat': 5,
    'cmd_channel_autohide': 5,
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
    'cmd_ping': 5,
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
        (['кик'], None),
        (['история', 'лог'], None),
        (['модстат'], None),
        (['причины'], None),
        (['автоудаление'], None),
        (['заявки'], None),
        (['фильтр', 'капча', 'рейд', 'закрыть', 'открыть', 'каналы'], None),
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
        (['дуэль'], None),
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
                if primary_cmd in DK_PROTECTED_COMMANDS:
                    status = "🔒 защищена от настройки через ДК"
                else:
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

                if primary_cmd not in DK_PROTECTED_COMMANDS:
                    p_users = personal.get(primary_cmd, [])
                    extra = f" · 👤 личный доступ: {len(p_users)}" if p_users else ""
                else:
                    extra = ""
                
                # Выводим все вариации команды с защитой от пустых строк
                cmd_list = [str(cmd).strip() for cmd in cmd_variants if cmd]
                if not cmd_list:
                    continue
                    
                cmd_str = " / ".join(
                    f"<code>{html.escape(cmd, quote=False)}</code>" for cmd in cmd_list
                )
                lines.append(f"• {cmd_str} — {status}{extra}")
            except Exception as e:
                logger.error(f"Ошибка обработки команды {primary_cmd}: {e}")
                lines.append(f"• <i>ошибка: {html.escape(str(primary_cmd), quote=False)}</i>")
        
        text = "\n".join(lines)
        if not text or len(text) == 0:
            return "❌ Нет данных"
        return text
        
    except Exception as e:
        logger.error(f"dk_info_section_text ошибка в {section}: {e}", exc_info=True)
        return f"❌ Ошибка загрузки раздела: {html.escape(str(e)[:100], quote=False)}"


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
        return await msg.answer(
            f"❌ Неизвестная команда '{html.escape(str(parts[1]), quote=False)}'\n\n"
            "Укажите команду из доступных"
        )
    if command in DK_PROTECTED_COMMANDS:
        return await msg.answer("❌ Эту команду нельзя настраивать через ДК.")
    if command in BOT_SUPERADMIN_ONLY_COMMANDS:
        return await msg.answer("❌ Доступ к этой команде нельзя настраивать через ДК.")
    if not rest:
        return await msg.answer("❌ Уровень 0-5 или откл")
    level_token = rest[0]
    level = 9 if level_token.casefold() == 'откл' else (int(level_token) if level_token.isdigit() else None)
    if level is None or not (0 <= level <= 5 or level == 9):
        return await msg.answer("❌ Уровень 0-5 или откл")
    command_access = storage.data['command_access'].setdefault(str(msg.chat.id), {})
    for alias in get_command_aliases(command):
        command_access[alias] = level
    storage.mark_dirty();
    await storage.save()
    if level == 9:
        await msg.answer(f"✅ Команда '{html.escape(command, quote=False)}' отключена")
    else:
        await msg.answer(
            f"✅ Доступ к команде '{html.escape(command, quote=False)}' установлен на уровень {level}"
        )


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
        except Exception:
            logger.error("Не удалось отправить алерт об ошибке")


async def cmd_dk_enable(msg: Message, cmd_name: str = '+дк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    command = ' '.join(msg.text.split()[1:]).lower().strip()
    if command not in COMMANDS:
        return await msg.answer(f"❌ Неизвестная команда '{html.escape(command, quote=False)}'")
    if command in DK_PROTECTED_COMMANDS:
        return await msg.answer("❌ Эту команду нельзя настраивать через ДК.")
    if command in BOT_SUPERADMIN_ONLY_COMMANDS:
        return await msg.answer("❌ Доступ к этой команде нельзя настраивать через ДК.")
    command_access = storage.data['command_access'].setdefault(str(msg.chat.id), {})
    for alias in get_command_aliases(command):
        command_access[alias] = 0
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"✅ Команда '{html.escape(command, quote=False)}' включена (доступна всем)")


async def cmd_dk_disable(msg: Message, cmd_name: str = '-дк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    command = ' '.join(msg.text.split()[1:]).lower().strip()
    if command not in COMMANDS:
        return await msg.answer(f"❌ Неизвестная команда '{html.escape(command, quote=False)}'")
    if command in DK_PROTECTED_COMMANDS:
        return await msg.answer("❌ Эту команду нельзя настраивать через ДК.")
    if command in BOT_SUPERADMIN_ONLY_COMMANDS:
        return await msg.answer("❌ Доступ к этой команде нельзя настраивать через ДК.")
    command_access = storage.data['command_access'].setdefault(str(msg.chat.id), {})
    for alias in get_command_aliases(command):
        command_access[alias] = 9
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"❌ Команда '{html.escape(command, quote=False)}' отключена")


async def cmd_ldk_add(msg: Message, cmd_name: str = '+лдк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    parts = msg.text.split()
    if len(parts) < 3:
        return await msg.answer("❌ <code>!+лдк команда @user</code>")
    command, rest = match_dk_command(parts[1:])
    if command is None:
        return await msg.answer(f"❌ Неизвестная команда '{html.escape(str(parts[1]), quote=False)}'")
    if command in DK_PROTECTED_COMMANDS:
        return await msg.answer("❌ Эту команду нельзя настраивать через ДК.")
    if command in BOT_SUPERADMIN_ONLY_COMMANDS:
        return await msg.answer("❌ Доступ к этой команде нельзя настраивать через ДК.")
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
        return await msg.answer(f"❌ Неизвестная команда '{html.escape(str(parts[1]), quote=False)}'")
    if command in DK_PROTECTED_COMMANDS:
        return await msg.answer("❌ Эту команду нельзя настраивать через ДК.")
    if command in BOT_SUPERADMIN_ONLY_COMMANDS:
        return await msg.answer("❌ Доступ к этой команде нельзя настраивать через ДК.")
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

PING_CHECK_LAST: Dict[Tuple[int, int], float] = {}


async def cmd_ping_check(msg: Message):
    """Проверяет задержку Telegram API и состояние локального хранилища."""
    if not msg.from_user:
        return
    if not await require_access(msg, 'пинг', 0, title='Нет доступа', message='Проверка доступна участникам чата.'):
        return
    key = (msg.chat.id, msg.from_user.id)
    now = time.monotonic()
    previous = PING_CHECK_LAST.get(key, 0)
    if now - previous < 30:
        return await msg.answer("⏳ Проверку можно запускать раз в 30 секунд.")
    PING_CHECK_LAST[key] = now
    if len(PING_CHECK_LAST) > 5000:
        cutoff = now - 300
        for cache_key, timestamp in list(PING_CHECK_LAST.items()):
            if timestamp < cutoff:
                del PING_CHECK_LAST[cache_key]

    uptime = max(0, int(time.monotonic() - BOT_START_TIME))
    uptime_days, uptime = divmod(uptime, 86400)
    uptime_hours, uptime = divmod(uptime, 3600)
    uptime_minutes, uptime_seconds = divmod(uptime, 60)
    uptime_parts = []
    if uptime_days:
        uptime_parts.append(f"{uptime_days}д")
    if uptime_hours or uptime_days:
        uptime_parts.append(f"{uptime_hours}ч")
    if uptime_minutes or uptime_hours or uptime_days:
        uptime_parts.append(f"{uptime_minutes}м")
    uptime_parts.append(f"{uptime_seconds}с")

    storage_start = time.monotonic()
    storage.peek_user(msg.chat.id, msg.from_user.id)
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
    bot_info = await bot.get_me()
    bot_info_latency = (time.monotonic() - bot_info_start) * 1000
    bot_name = html.escape(bot_info.full_name, quote=False)
    if bot_info.username:
        bot_name += f" (@{html.escape(bot_info.username, quote=False)})"
    server_name = html.escape(socket.gethostname(), quote=False)
    server_platform = html.escape(platform.system(), quote=False)

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
        f"└ 📂 Чтение данных: <code>{storage_latency:.1f} мс</code>\n\n"
        "🤖 <b>Бот и сервер:</b>\n"
        f"├ 🏷️ Бот: <b>{bot_name}</b>\n"
        f"├ 🖥️ Сервер: <code>{server_name}</code> ({server_platform})\n"
        f"├ ⏱️ Аптайм: <code>{' '.join(uptime_parts)}</code>\n"
        f"└ 📦 aiogram: <code>{html.escape(aiogram.__version__, quote=False)}</code>",
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
    except Exception as exc:
        logger.warning("Не удалось отправить общий сбор в чате %s: %s", msg.chat.id, exc)
        await msg.answer("❌ Не удалось получить список администраторов чата.")


def log_superadmin_action(actor_id: int, action: str, details: str = ''):
    entries = storage.data.setdefault('superadmin_audit', [])
    if not isinstance(entries, list):
        entries = []
        storage.data['superadmin_audit'] = entries
    now = time.time()
    entries.append({
        'ts': now,
        'actor': actor_id,
        'action': action,
        'details': str(details)[:500],
    })
    cutoff = now - 90 * 86400
    storage.data['superadmin_audit'] = [
        entry for entry in entries
        if isinstance(entry, dict) and isinstance(entry.get('ts'), (int, float))
        and entry['ts'] > cutoff
    ][-500:]
    storage.mark_dirty()


async def require_private_admin_chat(msg: Message) -> bool:
    if msg.chat.type == 'private':
        return True
    await msg.answer("❌ Эта команда доступна главным администраторам только в личном чате с ботом.")
    return False


def _format_bytes(size: Optional[int]) -> str:
    if size is None:
        return "н/д"
    value = float(size)
    for unit in ('Б', 'КБ', 'МБ', 'ГБ', 'ТБ'):
        if value < 1024 or unit == 'ТБ':
            return f"{value:.1f} {unit}" if unit != 'Б' else f"{int(value)} Б"
        value /= 1024
    return f"{value:.1f} ТБ"


def _read_log_tail(max_bytes: int = 256 * 1024) -> List[str]:
    path = Path(LOG_FILE)
    with path.open('rb') as log_file:
        log_file.seek(0, os.SEEK_END)
        size = log_file.tell()
        log_file.seek(max(0, size - max_bytes))
        data = log_file.read()
    if size > max_bytes:
        data = data.split(b'\n', 1)[-1]
    return data.decode('utf-8', 'replace').splitlines()


def _get_rss_mb() -> Optional[float]:
    if os.name == 'nt':
        try:
            import ctypes

            class ProcessMemoryCounters(ctypes.Structure):
                _fields_ = [
                    ('cb', ctypes.c_ulong),
                    ('PageFaultCount', ctypes.c_ulong),
                    ('PeakWorkingSetSize', ctypes.c_size_t),
                    ('WorkingSetSize', ctypes.c_size_t),
                    ('QuotaPeakPagedPoolUsage', ctypes.c_size_t),
                    ('QuotaPagedPoolUsage', ctypes.c_size_t),
                    ('QuotaPeakNonPagedPoolUsage', ctypes.c_size_t),
                    ('QuotaNonPagedPoolUsage', ctypes.c_size_t),
                    ('PagefileUsage', ctypes.c_size_t),
                    ('PeakPagefileUsage', ctypes.c_size_t),
                ]

            counters = ProcessMemoryCounters()
            counters.cb = ctypes.sizeof(counters)
            process = ctypes.windll.kernel32.GetCurrentProcess()
            if ctypes.windll.psapi.GetProcessMemoryInfo(
                process, ctypes.byref(counters), counters.cb
            ):
                return counters.WorkingSetSize / (1024 * 1024)
        except (AttributeError, OSError):
            return None
        return None

    try:
        with open('/proc/self/status', encoding='utf-8') as status_file:
            for line in status_file:
                if line.startswith('VmRSS:'):
                    return int(line.split()[1]) / 1024
    except (OSError, ValueError, IndexError):
        return None
    return None


@superadmin_only
async def cmd_backup(msg: Message, args: str = '', cmd_name: str = 'бэкап'):
    if args.strip().casefold() == 'файл':
        if not await require_private_admin_chat(msg):
            return
        created_at = await storage.create_backup()
        backups = await storage.list_backups()
        backup_meta = next(
            (item for item in backups if abs(float(item['ts']) - created_at) < 0.000001),
            None,
        )
        if not backup_meta or not backup_meta.get('path') or not backup_meta.get('exists'):
            return await msg.answer("❌ Не удалось найти файл созданного бэкапа.")
        log_superadmin_action(msg.from_user.id, 'backup_export', f"id={backup_meta['id']}")
        await storage.flush()
        await msg.answer_document(
            FSInputFile(backup_meta['path'], filename=Path(backup_meta['path']).name),
            caption=f"Снимок базы данных #{backup_meta['id']}",
        )
        return

    created_at = await storage.create_backup()
    backups = await storage.list_backups()
    backup_meta = next(
        (item for item in backups if abs(float(item['ts']) - created_at) < 0.000001),
        None,
    )
    log_superadmin_action(
        msg.from_user.id, 'backup_create',
        f"id={backup_meta['id']}" if backup_meta else "snapshot created",
    )
    await storage.flush()
    await msg.answer(
        f"✅ Бэкап сохранён ({datetime.fromtimestamp(created_at).strftime('%Y-%m-%d %H:%M:%S')})."
    )


@superadmin_only
async def cmd_list_bot_chats(msg: Message):

    bot_info = await bot.get_me()
    known_chats = storage.data.setdefault('bot_chats', {})
    chat_ids = storage.get_known_group_chat_ids()
    unverified_chat_ids = []
    changed = False

    for chat_id in chat_ids:
        chat_key = str(chat_id)
        if chat_key in known_chats:
            continue
        try:
            chat = await bot.get_chat(chat_id)
            member = await bot.get_chat_member(chat_id, bot_info.id)
        except TelegramAPIError as exc:
            logger.warning("Не удалось проверить сохранённый чат %s: %s", chat_id, exc)
            unverified_chat_ids.append(chat_id)
            continue

        is_present = (
            member.status in ('member', 'administrator', 'creator')
            or member.status == 'restricted' and member.is_member
        )
        if is_present:
            changed = remember_bot_group_chat(chat) or changed
        else:
            changed = mark_bot_group_chat_left(chat) or changed

    if changed:
        await storage.save()

    known_chats = storage.data.get('bot_chats', {})
    entries = []
    for chat_id in sorted(chat_ids):
        record = known_chats.get(str(chat_id))
        if not isinstance(record, dict) or record.get('status') == 'left':
            continue
        title = html.escape(str(record.get('title') or chat_id), quote=False)
        username = record.get('username')
        username_text = f" (@{html.escape(str(username), quote=False)})" if username else ''
        entries.append(f"• <b>{title}</b>{username_text} — <code>{chat_id}</code>")

    if entries:
        text = f"💬 <b>Группы, где находится бот: {len(entries)}</b>\n\n" + "\n".join(entries)
    else:
        text = "💬 Пока не найдено групп, где находится бот."

    if unverified_chat_ids:
        unresolved = ', '.join(f"<code>{chat_id}</code>" for chat_id in unverified_chat_ids[:10])
        text += (
            f"\n\n⚠️ Не удалось проверить старые записи ({len(unverified_chat_ids)}): {unresolved}"
        )
        if len(unverified_chat_ids) > 10:
            text += f" и ещё {len(unverified_chat_ids) - 10}"

    await send_chunked_text(msg, text)


def _backup_restore_keyboard(owner_id: int, backup: dict) -> InlineKeyboardMarkup:
    ts_token = int(round(float(backup['ts']) * 1_000_000))
    backup_id = int(backup['id'])
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text=f"✅ Да, восстановить #{backup_id}",
            callback_data=f"restore_confirm_{owner_id}_{ts_token}_{backup_id}",
        ),
        InlineKeyboardButton(
            text="❌ Отмена",
            callback_data=f"restore_cancel_{owner_id}_{ts_token}_{backup_id}",
        ),
    ]])


async def _prompt_restore_confirmation(
    msg: Message, backup: dict, owner_id: int, *, edit: bool = False
):
    created = datetime.fromtimestamp(float(backup['ts'])).strftime('%Y-%m-%d %H:%M:%S')
    text = (
        "⚠️ <b>Подтвердите восстановление</b>\n"
        f"Будет выбран бэкап <code>#{backup['id']}</code> от {created}.\n"
        "Текущие данные будут заменены содержимым выбранной копии."
    )
    keyboard = _backup_restore_keyboard(owner_id, backup)
    if edit:
        await msg.edit_text(text, reply_markup=keyboard)
    else:
        await msg.answer(text, reply_markup=keyboard)


@superadmin_only
async def cmd_restore(msg: Message, args: str = '', cmd_name: str = 'восстановить'):
    backup_id = None
    if args.strip():
        try:
            backup_id = int(args.strip())
        except ValueError:
            return await msg.answer("Использование: <code>!восстановить [id]</code>.")
        if backup_id <= 0:
            return await msg.answer("ID бэкапа должен быть положительным числом.")
    backup = await storage.get_backup(backup_id) if backup_id is not None else await storage.get_latest_backup()
    if not backup:
        return await msg.answer("❌ Нет бэкапов")
    if not isinstance(backup, dict) or not isinstance(backup.get('ts'), (int, float)):
        logger.error("Бэкап %s не содержит корректную временную метку", backup_id)
        return await msg.answer("❌ Бэкап повреждён или имеет неподдерживаемый формат.")
    backup_data = backup.get('data')
    if not validate_backup_data(backup_data):
        logger.error("Бэкап %s имеет некорректную структуру", backup.get('id'))
        return await msg.answer("❌ Бэкап повреждён или имеет неподдерживаемый формат.")
    await _prompt_restore_confirmation(msg, backup, msg.from_user.id)


@superadmin_only
async def cmd_backups(msg: Message):
    backups = await storage.list_backups()
    if not backups:
        return await msg.answer("📭 Сохранённых бэкапов пока нет.")

    lines = ["💾 <b>Резервные копии</b>"]
    keyboard_rows = []
    for backup in backups[:10]:
        created = datetime.fromtimestamp(float(backup['ts'])).strftime('%Y-%m-%d %H:%M:%S')
        size = _format_bytes(backup['size'])
        state = "✅" if backup['exists'] else "⚠️ файл отсутствует"
        lines.append(
            f"• <code>#{backup['id']}</code> — {created}, {size} {state}"
        )
        if backup['exists']:
            keyboard_rows.append([InlineKeyboardButton(
                text=f"Восстановить #{backup['id']}",
                callback_data=f"restore_select_{msg.from_user.id}_{backup['id']}",
            )])
    await msg.answer(
        "\n".join(lines),
        reply_markup=InlineKeyboardMarkup(inline_keyboard=keyboard_rows) if keyboard_rows else None,
    )


@superadmin_only
async def cmd_logs(msg: Message, args: str = ''):
    if not await require_private_admin_chat(msg):
        return
    tokens = args.split()
    levels = {'DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL'}
    level = next((token.upper() for token in tokens if token.upper() in levels), None)
    count = 40
    for token in tokens:
        if token.isdigit():
            count = int(token)
            break
    count = max(1, min(count, 300))
    try:
        lines = await asyncio.to_thread(_read_log_tail)
    except OSError as exc:
        return await msg.answer(f"❌ Не удалось прочитать лог: {html.escape(str(exc))}")
    if level:
        lines = [line for line in lines if f" - {level} - " in line]
    lines = lines[-count:]
    if not lines:
        return await msg.answer("📭 Подходящих записей в хвосте лога нет.")
    header = f"📜 <b>Лог: {len(lines)} строк" + (f", уровень {level}" if level else "") + "</b>\n"
    body = "\n".join(lines)
    if len(body) > 3500:
        return await msg.answer_document(
            BufferedInputFile(body.encode('utf-8'), filename='valera_log.txt'),
            caption=header,
        )
    await msg.answer(header + f"<pre>{html.escape(body, quote=False)}</pre>")


@superadmin_only
async def cmd_status(msg: Message):
    database_path = Path(DATABASE_FILE)
    wal_path = Path(str(database_path) + '-wal')
    db_size = database_path.stat().st_size if database_path.exists() else 0
    wal_size = wal_path.stat().st_size if wal_path.exists() else 0
    chat_count, user_count = storage._connection.execute(
        "SELECT COUNT(DISTINCT chat_id), COUNT(*) FROM users"
    ).fetchone()
    active_chats = len(storage.get_known_group_chat_ids())
    rss_mb = _get_rss_mb()
    now = time.time()
    database_mtimes = [
        path.stat().st_mtime for path in (database_path, wal_path) if path.exists()
    ]
    stat_mtime = max(database_mtimes) if database_mtimes else None
    last_save = (
        datetime.fromtimestamp(stat_mtime).strftime('%Y-%m-%d %H:%M:%S')
        if stat_mtime else "неизвестно"
    )
    cache_sizes = (
        f"user {len(user_cache._cache)}, mention {len(mention_cache._cache)}, "
        f"settings {len(chat_settings_cache._cache)}, антиспам {len(anti_spam_admin_cache._cache)}, "
        f"права {len(bot_rights_cache._cache)}, фразы {len(phrase_match_cache._cache)}, "
        f"индексы пользователей {len(storage._chat_user_index)}"
    )
    other_tasks = sum(
        1 for task in asyncio.all_tasks()
        if task is not asyncio.current_task() and not task.done()
    )
    uptime = max(0, int(now - PROCESS_START_TIME))
    lines = [
        "🩺 <b>Состояние бота</b>",
        f"⏱️ Аптайм: {uptime // 86400}д {(uptime % 86400) // 3600}ч {(uptime % 3600) // 60}м",
        f"📦 aiogram: {html.escape(aiogram.__version__)}",
        f"💬 Групп: {active_chats}; чатов с данными в SQLite: {chat_count}; пользователей: {user_count}",
        f"💾 База: {_format_bytes(db_size)}; WAL: {_format_bytes(wal_size)}",
        f"🔄 Версии сохранения: {storage._change_version}/{storage._saved_version}",
        f"🕒 Последняя запись БД: {last_save}",
        f"🧠 RSS: {rss_mb:.1f} МБ" if rss_mb is not None else "🧠 RSS: недоступен",
        f"♻️ Кэши: {cache_sizes}",
        f"⚙️ Незавершённых задач asyncio: {other_tasks}",
    ]
    await msg.answer("\n".join(lines))


PROCESS_START_TIME = time.time()


@superadmin_only
async def cmd_save_now(msg: Message):
    users_written = (
        sum(len(users) for users in storage.data.get('users', {}).values())
        if storage._replace_all_users else len(storage._dirty_users)
    )
    started = time.perf_counter()
    storage.mark_dirty()
    await storage.flush()
    elapsed_ms = (time.perf_counter() - started) * 1000
    await msg.answer(f"✅ Сохранение завершено: {users_written} пользователей, {elapsed_ms:.1f} мс.")


@superadmin_only
async def cmd_bot_rights(msg: Message, args: str):
    try:
        chat_id = int(args.strip())
    except ValueError:
        return await msg.answer("Использование: <code>!права &lt;chat_id&gt;</code>.")
    try:
        member = await bot.get_chat_member(chat_id, bot.id)
    except TelegramAPIError as exc:
        return await msg.answer(f"❌ Не удалось получить права бота: {html.escape(str(exc))}")
    rights = (
        ('Удалять сообщения', 'can_delete_messages'),
        ('Ограничивать участников', 'can_restrict_members'),
        ('Закреплять сообщения', 'can_pin_messages'),
        ('Приглашать участников', 'can_invite_users'),
        ('Управлять чатом', 'can_manage_chat'),
        ('Назначать администраторов', 'can_promote_members'),
    )
    lines = [f"🔐 <b>Права бота в чате <code>{chat_id}</code></b>", f"Статус: {member.status}"]
    for title, field in rights:
        allowed = member.status == 'creator' or (
            member.status == 'administrator' and bool(getattr(member, field, False))
        )
        lines.append(f"{'✅' if allowed else '❌'} {title}")
    await msg.answer("\n".join(lines))


@superadmin_only
async def cmd_reset_caches(msg: Message):
    for cache in (
        user_cache, mention_cache, chat_settings_cache, anti_spam_admin_cache,
        bot_rights_cache, raid_join_cache, phrase_match_cache,
    ):
        cache.clear()
    chat_owner_sync_cache.clear()
    chat_default_permissions_cache.clear()
    storage._chat_user_index.clear()
    await msg.answer("✅ Кэши очищены.")


@superadmin_only
async def cmd_export_user(msg: Message, args: str):
    if not await require_private_admin_chat(msg):
        return
    parts = args.split()
    if len(parts) != 2:
        return await msg.answer("Использование: <code>!юзер &lt;chat_id&gt; &lt;user_id&gt;</code>.")
    try:
        chat_id, user_id = map(int, parts)
    except ValueError:
        return await msg.answer("chat_id и user_id должны быть числами.")
    chat_key, user_key = str(chat_id), str(user_id)
    user_data = storage.data.get('users', {}).get(chat_key, {}).get(user_key)
    if user_data is None:
        row = storage._connection.execute(
            "SELECT value_json FROM users WHERE chat_id = ? AND user_id = ?",
            (chat_key, user_key),
        ).fetchone()
        if row:
            user_data = json.loads(row[0])
    if not isinstance(user_data, dict):
        return await msg.answer("📭 Профиль не найден.")
    payload = json.dumps(user_data, ensure_ascii=False, indent=2, default=str).encode('utf-8')
    await msg.answer_document(
        BufferedInputFile(payload, filename=f"user_{chat_id}_{user_id}.json"),
        caption=f"Профиль {user_id} в чате {chat_id}",
    )


def _inspect_database_sync(database_path: str) -> dict:
    connection = sqlite3.connect(database_path, timeout=30)
    try:
        connection.execute("PRAGMA busy_timeout=30000")
        integrity = connection.execute("PRAGMA integrity_check").fetchone()[0]
        checkpoint = connection.execute("PRAGMA wal_checkpoint(TRUNCATE)").fetchone()
        tables = [
            row[0] for row in connection.execute(
                "SELECT name FROM sqlite_master WHERE type = 'table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
            )
        ]
        counts = {}
        for table in tables:
            escaped = table.replace('"', '""')
            counts[table] = connection.execute(
                f'SELECT COUNT(*) FROM "{escaped}"'
            ).fetchone()[0]
        return {'integrity': integrity, 'checkpoint': checkpoint, 'counts': counts}
    finally:
        connection.close()


@superadmin_only
async def cmd_database_info(msg: Message):
    if not await require_private_admin_chat(msg):
        return
    try:
        result = await asyncio.to_thread(_inspect_database_sync, str(Path(DATABASE_FILE)))
    except sqlite3.Error as exc:
        logger.exception("Не удалось выполнить диагностику SQLite")
        return await msg.answer(f"❌ Ошибка диагностики БД: {html.escape(str(exc))}")
    db_path = Path(DATABASE_FILE)
    wal_path = Path(str(db_path) + '-wal')
    checkpoint = result['checkpoint'] or (0, 0, 0)
    lines = [
        "🗄️ <b>Диагностика SQLite</b>",
        f"База: {_format_bytes(db_path.stat().st_size if db_path.exists() else 0)}",
        f"WAL после checkpoint: {_format_bytes(wal_path.stat().st_size if wal_path.exists() else 0)}",
        f"Integrity check: <code>{html.escape(str(result['integrity']))}</code>",
        f"WAL checkpoint (busy/log/checkpointed): <code>{checkpoint}</code>",
        "Строки: " + ", ".join(
            f"{html.escape(table)}={count}" for table, count in result['counts'].items()
        ),
    ]
    await msg.answer("\n".join(lines))


@superadmin_only
async def cmd_gc(msg: Message):
    before = _get_rss_mb()
    collected = await asyncio.to_thread(gc.collect)
    after = _get_rss_mb()
    before_text = f"{before:.1f} МБ" if before is not None else "н/д"
    after_text = f"{after:.1f} МБ" if after is not None else "н/д"
    await msg.answer(
        f"♻️ GC собрал объектов: {collected}\nRSS: {before_text} → {after_text}"
    )


@superadmin_only
async def cmd_broadcast(msg: Message, args: str):
    if not await require_private_admin_chat(msg):
        return
    text = args.strip()
    if not text:
        return await msg.answer("Использование: <code>!рассылка &lt;текст&gt;</code>.")
    if len(text) > 4000:
        return await msg.answer("❌ Текст рассылки не должен превышать 4000 символов.")
    now = time.time()
    for old_token, old_pending in list(pending_broadcasts.items()):
        if now - old_pending.get('created_at', 0) > 5 * 60:
            pending_broadcasts.pop(old_token, None)
    token = uuid.uuid4().hex[:12]
    pending_broadcasts[token] = {
        'owner': msg.from_user.id,
        'text': text,
        'created_at': now,
    }
    escaped_preview = html.escape(text[:700], quote=False)
    if len(text) > 700:
        escaped_preview += "…"
    keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text="✅ Отправить",
            callback_data=f"broadcast_confirm_{msg.from_user.id}_{token}",
        ),
        InlineKeyboardButton(
            text="❌ Отмена",
            callback_data=f"broadcast_cancel_{msg.from_user.id}_{token}",
        ),
    ]])
    count = len([
        chat_id for chat_id in storage.get_known_group_chat_ids()
        if str(chat_id) not in storage.data.get('blocked_chats', {})
    ])
    await msg.answer(
        f"⚠️ <b>Предпросмотр рассылки</b> для {count} групп:\n\n{escaped_preview}",
        reply_markup=keyboard,
    )


pending_broadcasts: Dict[str, dict] = {}


@superadmin_only
async def cmd_leave_chat(msg: Message, args: str):
    try:
        chat_id = int(args.strip())
    except ValueError:
        return await msg.answer("Использование: <code>!выйти &lt;chat_id&gt;</code>.")
    record = storage.data.get('bot_chats', {}).get(str(chat_id), {})
    title = html.escape(str(record.get('title', chat_id)), quote=False) if isinstance(record, dict) else str(chat_id)
    keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text="✅ Выйти",
            callback_data=f"leave_confirm_{msg.from_user.id}_{chat_id}",
        ),
        InlineKeyboardButton(
            text="❌ Отмена",
            callback_data=f"leave_cancel_{msg.from_user.id}_{chat_id}",
        ),
    ]])
    await msg.answer(
        f"⚠️ Подтвердите выход из чата <b>{title}</b> (<code>{chat_id}</code>).",
        reply_markup=keyboard,
    )


@superadmin_only
async def cmd_block_chat(msg: Message, args: str, unblock: bool = False):
    try:
        chat_id = int(args.strip())
    except ValueError:
        usage = "!разблок чата" if unblock else "!блок чата"
        return await msg.answer(f"Использование: <code>{usage} &lt;chat_id&gt;</code>.")
    action = 'unblock' if unblock else 'block'
    keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text="✅ Подтвердить",
            callback_data=f"chatblock_{action}_{msg.from_user.id}_{chat_id}",
        ),
        InlineKeyboardButton(
            text="❌ Отмена",
            callback_data=f"chatblock_cancel_{msg.from_user.id}_{chat_id}",
        ),
    ]])
    verb = "разблокировать" if unblock else "заблокировать"
    await msg.answer(
        f"⚠️ Подтвердите: {verb} обработку сообщений чата <code>{chat_id}</code>?",
        reply_markup=keyboard,
    )


@superadmin_only
async def cmd_restart(msg: Message):
    keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text="🔄 Перезапустить",
            callback_data=f"restart_confirm_{msg.from_user.id}",
        ),
        InlineKeyboardButton(
            text="❌ Отмена",
            callback_data=f"restart_cancel_{msg.from_user.id}",
        ),
    ]])
    await msg.answer(
        "⚠️ Подтвердите graceful shutdown. Процесс завершится после сохранения данных "
        "и перезапустится только при настроенном супервизоре.",
        reply_markup=keyboard,
    )


@superadmin_only
async def cmd_superadmin_audit(msg: Message):
    entries = storage.data.get('superadmin_audit', [])
    if not isinstance(entries, list) or not entries:
        return await msg.answer("📭 Аудит действий главных администраторов пока пуст.")
    lines = ["📜 <b>Последние действия суперадминов</b>"]
    for entry in entries[-20:][::-1]:
        if not isinstance(entry, dict):
            continue
        stamp = entry.get('ts', 0)
        when = datetime.fromtimestamp(stamp).strftime('%Y-%m-%d %H:%M:%S') if isinstance(stamp, (int, float)) else "?"
        actor = html.escape(str(entry.get('actor', '?')))
        action = html.escape(str(entry.get('action', '?')))
        details = html.escape(str(entry.get('details', ''))[:180], quote=False)
        lines.append(f"• {when} — <code>{actor}</code>: <b>{action}</b> {details}")
    await send_chunked_text(msg, "\n".join(lines))


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

    parts = call.data.split('_')
    if len(parts) == 4 and parts[1] == 'select':
        try:
            owner_id, backup_id = int(parts[2]), int(parts[3])
        except ValueError:
            return await call.answer("❌ Кнопка восстановления недействительна.", show_alert=True)
        if call.from_user.id != owner_id or not is_bot_superadmin(call.from_user.id):
            return await call.answer("❌ Это действие доступно только его инициатору.", show_alert=True)
        try:
            backup = await storage.get_backup(backup_id)
        except (OSError, ValueError, sqlite3.Error) as exc:
            logger.exception("Не удалось прочитать выбранный бэкап %s", backup_id)
            return await call.answer(f"❌ Не удалось прочитать бэкап: {str(exc)[:180]}", show_alert=True)
        if not backup or not validate_backup_data(backup.get('data')):
            return await call.answer("❌ Бэкап отсутствует или повреждён.", show_alert=True)
        await _prompt_restore_confirmation(call.message, backup, owner_id, edit=True)
        return await call.answer()

    if len(parts) != 5 or parts[1] not in {'confirm', 'cancel'}:
        logger.warning("Получены некорректные данные callback восстановления")
        return await call.answer("❌ Кнопка восстановления недействительна.", show_alert=True)
    try:
        owner_id, ts_token, backup_id = int(parts[2]), int(parts[3]), int(parts[4])
    except ValueError:
        return await call.answer("❌ Кнопка восстановления недействительна.", show_alert=True)
    if call.from_user.id != owner_id or not is_bot_superadmin(call.from_user.id):
        return await call.answer("❌ Это действие доступно только его инициатору.", show_alert=True)
    if parts[1] == 'cancel':
        await call.message.edit_text("✅ Восстановление отменено.", reply_markup=None)
        return await call.answer()

    try:
        backup = await storage.get_backup(backup_id)
    except (OSError, ValueError, sqlite3.Error) as exc:
        logger.exception("Не удалось прочитать бэкап %s при подтверждении", backup_id)
        return await call.answer(f"❌ Не удалось прочитать бэкап: {str(exc)[:180]}", show_alert=True)
    if (
        not backup
        or int(round(float(backup['ts']) * 1_000_000)) != ts_token
        or not validate_backup_data(backup.get('data'))
    ):
        return await call.answer("❌ Выбранный бэкап изменился или повреждён.", show_alert=True)

    restored_data = DataStorage._get_default_data()
    restored_data.update(backup['data'])
    restored_data['backups'] = []
    storage.data = restored_data
    storage._loaded_user_chats = set(restored_data['users'])
    storage._replace_all_users = True
    storage._dirty_users.clear()
    storage._deleted_user_keys.clear()
    storage._deleted_user_chats.clear()
    for cache in (
        user_cache, chat_settings_cache, mention_cache, anti_spam_admin_cache,
        bot_rights_cache, raid_join_cache, phrase_match_cache,
    ):
        cache.clear()
    chat_owner_sync_cache.clear()
    chat_default_permissions_cache.clear()
    storage._chat_user_index.clear()
    active_games.clear()
    minesweeper_games.clear()
    wordle.games.clear()
    activity_graph_wizards.clear()
    storage.mark_dirty()
    log_superadmin_action(owner_id, 'backup_restore', f"id={backup_id}")
    await storage.flush()
    await call.message.edit_text(
        f"✅ Данные восстановлены из бэкапа #{backup_id}.",
        reply_markup=None,
    )
    await call.answer()


@router.callback_query(F.data.startswith('broadcast_'))
async def broadcast_callback(call: CallbackQuery):
    if not call.message:
        return await call.answer("Сообщение рассылки недоступно.", show_alert=True)
    try:
        _, action, owner_token, token = call.data.split('_', maxsplit=3)
        owner_id = int(owner_token)
    except (ValueError, AttributeError):
        return await call.answer("Кнопка рассылки недействительна.", show_alert=True)
    if call.from_user.id != owner_id or not is_bot_superadmin(owner_id):
        return await call.answer("Подтвердить рассылку может только её инициатор.", show_alert=True)
    pending = pending_broadcasts.get(token)
    if not pending or pending.get('owner') != owner_id:
        return await call.answer("Предпросмотр устарел. Создайте рассылку заново.", show_alert=True)
    if time.time() - pending.get('created_at', 0) > 5 * 60:
        pending_broadcasts.pop(token, None)
        return await call.answer("Предпросмотр истёк. Создайте рассылку заново.", show_alert=True)
    if action == 'cancel':
        pending_broadcasts.pop(token, None)
        await call.message.edit_text("✅ Рассылка отменена.", reply_markup=None)
        return await call.answer()
    if action != 'confirm':
        return await call.answer("Неизвестное действие.", show_alert=True)

    pending_broadcasts.pop(token, None)
    targets = [
        chat_id for chat_id in storage.get_known_group_chat_ids()
        if str(chat_id) not in storage.data.get('blocked_chats', {})
    ]
    await call.answer("Рассылка запущена.")
    await call.message.edit_text(f"⏳ Отправляю сообщение в {len(targets)} групп…")
    delivered = 0
    errors = 0
    broadcast_text = pending['text']
    for index, chat_id in enumerate(targets):
        try:
            await telegram_call_with_retry(
                bot.send_message,
                chat_id,
                broadcast_text,
                parse_mode=None,
                disable_web_page_preview=True,
            )
            delivered += 1
        except TelegramAPIError as exc:
            errors += 1
            logger.warning("Рассылка не доставлена в чат %s: %s", chat_id, exc)
        if index + 1 < len(targets):
            await asyncio.sleep(1)
    log_superadmin_action(
        owner_id, 'broadcast',
        f"delivered={delivered}, errors={errors}, targets={len(targets)}",
    )
    await storage.flush()
    await call.message.edit_text(
        f"✅ Рассылка завершена.\nДоставлено: {delivered}\nОшибок: {errors}"
    )


@router.callback_query(F.data.startswith('leave_'))
async def leave_chat_callback(call: CallbackQuery):
    if not call.message:
        return await call.answer("Сообщение подтверждения недоступно.", show_alert=True)
    try:
        _, action, owner_token, chat_token = call.data.split('_', maxsplit=3)
        owner_id, chat_id = int(owner_token), int(chat_token)
    except (ValueError, AttributeError):
        return await call.answer("Кнопка выхода недействительна.", show_alert=True)
    if call.from_user.id != owner_id or not is_bot_superadmin(owner_id):
        return await call.answer("Подтвердить действие может только его инициатор.", show_alert=True)
    if action == 'cancel':
        await call.message.edit_text("✅ Выход отменён.", reply_markup=None)
        return await call.answer()
    if action != 'confirm':
        return await call.answer("Неизвестное действие.", show_alert=True)
    try:
        await bot.leave_chat(chat_id)
    except TelegramAPIError as exc:
        logger.warning("Не удалось покинуть чат %s: %s", chat_id, exc)
        await call.message.edit_text(
            f"❌ Не удалось выйти из чата: {html.escape(str(exc)[:250])}",
            reply_markup=None,
        )
        return await call.answer("Ошибка Telegram.", show_alert=True)
    record = storage.data.setdefault('bot_chats', {}).setdefault(str(chat_id), {})
    if not isinstance(record, dict):
        record = {}
        storage.data['bot_chats'][str(chat_id)] = record
    record['status'] = 'left'
    record.setdefault('title', str(chat_id))
    record.setdefault('type', 'supergroup')
    log_superadmin_action(owner_id, 'leave_chat', f"chat_id={chat_id}")
    await storage.flush()
    await call.message.edit_text(f"✅ Бот вышел из чата <code>{chat_id}</code>.", reply_markup=None)
    await call.answer()


@router.callback_query(F.data.startswith('chatblock_'))
async def block_chat_callback(call: CallbackQuery):
    if not call.message:
        return await call.answer("Сообщение подтверждения недоступно.", show_alert=True)
    try:
        _, action, owner_token, chat_token = call.data.split('_', maxsplit=3)
        owner_id, chat_id = int(owner_token), int(chat_token)
    except (ValueError, AttributeError):
        return await call.answer("Кнопка блокировки недействительна.", show_alert=True)
    if call.from_user.id != owner_id or not is_bot_superadmin(owner_id):
        return await call.answer("Подтвердить действие может только его инициатор.", show_alert=True)
    if action == 'cancel':
        await call.message.edit_text("✅ Действие отменено.", reply_markup=None)
        return await call.answer()
    if action not in {'block', 'unblock'}:
        return await call.answer("Неизвестное действие.", show_alert=True)
    blocked = storage.data.setdefault('blocked_chats', {})
    if action == 'block':
        blocked[str(chat_id)] = {'actor': owner_id, 'ts': time.time()}
    else:
        blocked.pop(str(chat_id), None)
    log_superadmin_action(owner_id, f"chat_{action}", f"chat_id={chat_id}")
    await storage.flush()
    result = "заблокирован" if action == 'block' else "разблокирован"
    await call.message.edit_text(
        f"✅ Чат <code>{chat_id}</code> {result} для обработки сообщений.",
        reply_markup=None,
    )
    await call.answer()


@router.callback_query(F.data.startswith('restart_'))
async def restart_callback(call: CallbackQuery):
    if not call.message:
        return await call.answer("Сообщение подтверждения недоступно.", show_alert=True)
    try:
        _, action, owner_token = call.data.split('_', maxsplit=2)
        owner_id = int(owner_token)
    except (ValueError, AttributeError):
        return await call.answer("Кнопка перезапуска недействительна.", show_alert=True)
    if call.from_user.id != owner_id or not is_bot_superadmin(owner_id):
        return await call.answer("Подтвердить перезапуск может только его инициатор.", show_alert=True)
    if action == 'cancel':
        await call.message.edit_text("✅ Перезапуск отменён.", reply_markup=None)
        return await call.answer()
    if action != 'confirm':
        return await call.answer("Неизвестное действие.", show_alert=True)
    if shutdown_event is None:
        return await call.answer("Обработчик завершения ещё не запущен.", show_alert=True)
    log_superadmin_action(owner_id, 'restart', 'graceful shutdown requested')
    await storage.flush()
    await call.message.edit_text(
        "✅ Данные сохранены. Завершаю процесс; перезапуск зависит от настроек супервизора.",
        reply_markup=None,
    )
    await call.answer()
    shutdown_event.set()


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

def _reputation_direction_state(value: object, now: float) -> dict:
    if not isinstance(value, dict):
        return {'count': 0, 'last_at': 0.0}
    last_at = value.get('last_at', 0)
    if (
        not isinstance(last_at, (int, float))
        or isinstance(last_at, bool)
        or last_at <= 0
        or last_at > now
    ):
        last_at = 0.0
    count = value.get('count', 0)
    if not isinstance(count, int) or isinstance(count, bool):
        count = 0
    count = max(0, min(count, 64))
    if last_at and not count:
        count = 1
    return {'count': count, 'last_at': float(last_at)}


def _reputation_cooldown_state(giver: dict, now: float) -> dict:
    stored = giver.get('rep_cooldown_state')
    if (
        not isinstance(stored, dict)
        or stored.get('version') != REPUTATION_COOLDOWN_STATE_VERSION
    ):
        return {
            'version': REPUTATION_COOLDOWN_STATE_VERSION,
            'plus': {'count': 0, 'last_at': 0.0},
            'minus': {'count': 0, 'last_at': 0.0},
            'last_activity_at': 0.0,
        }

    state = {
        'version': REPUTATION_COOLDOWN_STATE_VERSION,
        'plus': _reputation_direction_state(stored.get('plus'), now),
        'minus': _reputation_direction_state(stored.get('minus'), now),
        'last_activity_at': stored.get('last_activity_at', 0.0),
    }
    last_activity = state['last_activity_at']
    if (
        not isinstance(last_activity, (int, float))
        or isinstance(last_activity, bool)
        or last_activity <= 0
        or last_activity > now
    ):
        last_activity = 0.0
    state['last_activity_at'] = max(
        float(last_activity),
        state['plus']['last_at'],
        state['minus']['last_at'],
    )

    if (
        state['last_activity_at']
        and now - state['last_activity_at'] >= REPUTATION_IDLE_RESET
    ):
        return {
            'version': REPUTATION_COOLDOWN_STATE_VERSION,
            'plus': {'count': 0, 'last_at': 0.0},
            'minus': {'count': 0, 'last_at': 0.0},
            'last_activity_at': 0.0,
        }
    return state


def _adaptive_reputation_cooldown(action_count: int, remove: bool = False) -> int:
    configured_base = REPUTATION_REMOVE_COOLDOWN if remove else REPUTATION_COOLDOWN
    base = max(1, min(15 * 60, configured_base))
    cooldown = base
    for _ in range(max(0, action_count - 1)):
        cooldown = min(REPUTATION_MAX_COOLDOWN, cooldown * 2)
        if cooldown == REPUTATION_MAX_COOLDOWN:
            break
    return cooldown


def _format_reputation_wait(seconds: int) -> str:
    hours, remainder = divmod(max(0, seconds), 3600)
    minutes, seconds = divmod(remainder, 60)
    parts = []
    if hours:
        parts.append(f'{hours} ч')
    if minutes or hours:
        parts.append(f'{minutes} мин')
    parts.append(f'{seconds} сек')
    return ' '.join(parts)


async def give_reputation(
    msg: Message,
    remove: bool = False,
    *,
    reply_on_success: bool = True,
    giver_id: Optional[int] = None,
    receiver_id: Optional[int] = None,
) -> Optional[int]:
    """Начисляет или снимает один балл репутации."""
    try:
        giver_id = giver_id if giver_id is not None else (
            msg.from_user.id if msg.from_user else None
        )
        receiver_user = msg.reply_to_message.from_user if msg.reply_to_message else None
        receiver_id = receiver_id if receiver_id is not None else (
            receiver_user.id if receiver_user else None
        )
        if giver_id is None or receiver_id is None:
            await msg.answer("❌ Не удалось определить пользователя, которому меняется репутация.")
            return None

        giver = storage.get_user(msg.chat.id, giver_id, use_cache=False)
        receiver = storage.get_user(msg.chat.id, receiver_id, use_cache=False)

        now = time.time()
        today = kaliningrad_now().strftime('%Y-%m-%d')
        action = 'Снижение репутации' if remove else 'Выдача репутации'
        daily_limit = REPUTATION_REMOVE_DAILY_LIMIT if remove else REPUTATION_DAILY_LIMIT
        daily_actions_key = 'rep_removed_today' if remove else 'rep_given_today'
        reply_to_receiver = "снимали" if remove else "повышали"

        logger.info(f"{action}: {giver_id} -> {receiver_id}")

        cooldown_state = _reputation_cooldown_state(giver, now)
        direction = 'minus' if remove else 'plus'
        direction_state = cooldown_state[direction]
        cooldown = _adaptive_reputation_cooldown(direction_state['count'], remove)
        last_action = direction_state['last_at']
        remaining = (
            int(cooldown - (now - last_action))
            if direction_state['count'] and last_action
            else 0
        )
        if remaining > 0:
            action_label = "-реп (снять 1 балл)" if remove else "+реп (добавить 1 балл)"
            msg_text = (
                f"⏳ <b>Кулдаун на {action_label}</b>\n"
                f"Следующее изменение репутации будет доступно через "
                f"<b>{_format_reputation_wait(remaining)}</b>.\n"
                f"Сейчас пауза — {_format_reputation_wait(cooldown)}; она растёт при частых действиях."
            )
            logger.debug(f"{action}: кулдаун для пары {giver_id} -> {receiver_id}")
            await msg.answer(msg_text, disable_web_page_preview=True)
            return None

        # Проверка дневного лимита
        action_today = giver.get(daily_actions_key, {})
        if not isinstance(action_today, dict):
            action_today = {}
        action_today = {
            key: value
            for key, value in action_today.items()
            if key == today or key == 'targets_by_day'
        }
        today_count = action_today.get(today, 0)
        if today_count >= daily_limit:
            logger.debug(f"{action}: дневной лимит для {giver_id}")
            await msg.answer(f"❌ Дневной лимит исчерпан ({today_count}/{daily_limit})")
            return None

        targets_by_day = action_today.get('targets_by_day', {})
        if not isinstance(targets_by_day, dict):
            targets_by_day = {}
        targets_today = targets_by_day.get(today, {})
        if not isinstance(targets_today, dict):
            targets_today = {}

        # Ограничиваем каждое направление одним изменением на пользователя в день.
        if str(receiver_id) in targets_today:
            logger.debug(f"{action}: {giver_id} уже изменял репутацию {receiver_id} сегодня")
            await msg.answer(f"⭐ Вы уже {reply_to_receiver} репутацию этому пользователю сегодня.")
            return None

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
        direction_state['count'] = min(64, direction_state['count'] + 1)
        direction_state['last_at'] = now
        cooldown_state['last_activity_at'] = now
        giver['rep_cooldown_state'] = cooldown_state

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
        if reply_on_success:
            await msg.answer(
                f"⭐ {'-1' if remove else '+1'} {mention(msg.chat.id, receiver_id)}\n"
                f"📊 Репутация: {total_rep}",
                disable_web_page_preview=True
            )
        return total_rep

    except Exception as e:
        logger.error(f"Ошибка выдачи репутации: {type(e).__name__}: {e}", exc_info=True)
        try:
            await msg.answer(f"❌ Ошибка репутации: {html.escape(str(e)[:80], quote=False)}")
        except Exception:
            pass
        return None


# ==================== Проверка наказаний ====================

async def process_captcha_pending(now: float) -> None:
    pending_all = storage.data.get('captcha_pending', {})
    if not isinstance(pending_all, dict):
        logger.error("Некорректное хранилище ожидающих проверок капчи")
        return
    changed = False
    for chat_id_text, pending_chat in list(pending_all.items()):
        if not isinstance(pending_chat, dict):
            logger.warning("Некорректная очередь капчи в чате %s", chat_id_text)
            pending_all.pop(chat_id_text, None)
            changed = True
            continue
        try:
            chat_id = int(chat_id_text)
        except (TypeError, ValueError):
            logger.warning("Некорректный идентификатор чата в очереди капчи: %r", chat_id_text)
            pending_all.pop(chat_id_text, None)
            changed = True
            continue
        for user_id_text, pending in list(pending_chat.items()):
            if not isinstance(pending, dict):
                pending_chat.pop(user_id_text, None)
                changed = True
                continue
            expires_at = pending.get('expires_at')
            retry_at = pending.get('next_retry_at', 0)
            if not isinstance(expires_at, (int, float)) or not isinstance(retry_at, (int, float)):
                logger.warning("Некорректная запись капчи для %s в чате %s", user_id_text, chat_id)
                pending_chat.pop(user_id_text, None)
                changed = True
                continue
            if now < retry_at or (now < expires_at and not pending.get('verified')):
                continue
            try:
                user_id = int(user_id_text)
                member = await bot.get_chat_member(chat_id, user_id)
                if member.status in ('left', 'kicked', 'administrator', 'creator'):
                    pending_chat.pop(user_id_text, None)
                    changed = True
                    continue
                if pending.get('verified'):
                    await restore_chat_default_permissions(chat_id, user_id)
                else:
                    if await bot_can(chat_id, 'can_restrict_members') is not True:
                        raise RuntimeError("У бота нет права ограничивать участников")
                    await bot.ban_chat_member(chat_id, user_id, revoke_messages=False)
                    await bot.unban_chat_member(chat_id, user_id, only_if_banned=True)
                    log_moderation(chat_id, None, user_id, 'kick', 'Капча не пройдена')
                    try:
                        await bot.send_message(
                            chat_id,
                            f"🚪 Участник с ID <code>{user_id}</code> удалён: капча не пройдена.",
                        )
                    except (TelegramAPIError, asyncio.TimeoutError) as notice_exc:
                        logger.debug("Не удалось уведомить чат %s о кике по капче: %s", chat_id, notice_exc)
                pending_chat.pop(user_id_text, None)
                changed = True
            except (TelegramAPIError, asyncio.TimeoutError, RuntimeError, ValueError) as exc:
                failures = pending.get('failures', 0)
                failures = failures if isinstance(failures, int) and failures >= 0 else 0
                failures += 1
                pending['failures'] = failures
                pending['next_retry_at'] = now + min(86400, MUTE_CHECK_INTERVAL * (2 ** min(failures, 10)))
                changed = True
                logger.warning(
                    "Не удалось завершить капчу для %s в чате %s (попытка %s): %s",
                    user_id_text, chat_id, failures, exc,
                )
        if not pending_chat:
            pending_all.pop(chat_id_text, None)
            changed = True
    if changed:
        storage.mark_dirty()
        await storage.save()


async def process_expired_chat_freezes(now: float) -> None:
    chat_settings = storage.data.get('chat_settings', {})
    if not isinstance(chat_settings, dict):
        return
    for chat_id_text, settings in list(chat_settings.items()):
        if not isinstance(settings, dict):
            continue
        freeze_state = settings.get('chat_freeze')
        if not isinstance(freeze_state, dict):
            continue
        expires_at = freeze_state.get('expires_at')
        retry_at = freeze_state.get('next_retry_at', 0)
        if not isinstance(expires_at, (int, float)) or not isinstance(retry_at, (int, float)):
            logger.error("Некорректная заморозка в чате %s", chat_id_text)
            continue
        if now < expires_at or now < retry_at:
            continue
        try:
            await restore_chat_freeze(int(chat_id_text))
        except (TelegramAPIError, asyncio.TimeoutError, ValueError) as exc:
            logger.warning("Не удалось восстановить разрешения чата %s: %s", chat_id_text, exc)


async def check_punishments():
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
                    and (
                        not isinstance(m.get('next_unmute_retry_at'), (int, float))
                        or now >= m['next_unmute_retry_at']
                    )
                ]
                removed_any = False
                for m in expired:
                    try:
                        await restore_chat_default_permissions(int(cid), m['user_id'])
                    except Exception as e:
                        previous_failures = m.get('unmute_failures', 0)
                        failures = (previous_failures if isinstance(previous_failures, int) else 0) + 1
                        m['unmute_failures'] = failures
                        m['next_unmute_retry_at'] = now + min(
                            86400,
                            MUTE_CHECK_INTERVAL * (2 ** min(failures, 10)),
                        )
                        removed_any = True
                        logger.warning(
                            "Не удалось снять истёкший мут пользователя %s в чате %s "
                            "(попытка %s, следующая через %s сек.): %s",
                            m.get('user_id'), cid, failures,
                            int(m['next_unmute_retry_at'] - now), e
                        )
                    else:
                        mutes.remove(m)
                        removed_any = True
                        try:
                            user_id = int(m['user_id'])
                            issued_at = m.get('issued_at')
                            duration_seconds = (
                                max(0, m['expire_time'] - issued_at)
                                if isinstance(issued_at, (int, float)) else None
                            )
                            log_moderation(
                                int(cid),
                                None,
                                user_id,
                                'unmute',
                                f"Срок мута истёк: {m.get('reason') or 'Без причины'}",
                                duration_seconds,
                            )
                            is_anti_spam_mute = (
                                m.get('mute_source') == 'anti_spam'
                                or str(m.get('reason') or '').startswith('Антиспам:')
                            )
                            is_warn_action_mute = (
                                m.get('mute_source') == 'warn_action'
                                or str(m.get('reason') or '').startswith('Автоматическое действие:')
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
                            if is_anti_spam_mute:
                                issuer_text = 'антиспам-система'
                            elif is_warn_action_mute:
                                issuer_text = 'автоматическое действие за предупреждения'
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
                                issuer_text = 'автоматическая система' if issued_by == 'auto' else 'неизвестно'

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
                            spawn_background_task(
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

            bans_by_chat = storage.data.get('banned_users', {})
            if isinstance(bans_by_chat, dict):
                for cid, bans in list(bans_by_chat.items()):
                    if not isinstance(bans, list):
                        continue
                    changed = False
                    for ban in list(bans):
                        if (
                            not isinstance(ban, dict)
                            or not isinstance(ban.get('user_id'), int)
                            or ban.get('permanent') is True
                            or not isinstance(ban.get('expire_time'), (int, float))
                            or now < ban['expire_time']
                            or (
                                isinstance(ban.get('next_unban_retry_at'), (int, float))
                                and now < ban['next_unban_retry_at']
                            )
                        ):
                            continue
                        try:
                            await bot.unban_chat_member(
                                int(cid), ban['user_id'], only_if_banned=True
                            )
                        except Exception as e:
                            failures = ban.get('unban_failures', 0)
                            failures = (failures if isinstance(failures, int) else 0) + 1
                            ban['unban_failures'] = failures
                            ban['next_unban_retry_at'] = now + min(
                                86400,
                                MUTE_CHECK_INTERVAL * (2 ** min(failures, 10)),
                            )
                            changed = True
                            logger.warning(
                                "Не удалось снять истёкший бан пользователя %s в чате %s "
                                "(попытка %s): %s",
                                ban['user_id'], cid, failures, e
                            )
                        else:
                            bans.remove(ban)
                            log_moderation(
                                int(cid),
                                None,
                                ban['user_id'],
                                'unban',
                                f"Срок временного бана истёк: {ban.get('reason') or 'Без причины'}",
                            )
                            changed = True
                    if changed:
                        storage.mark_dirty()
                        await storage.save()
            await process_captcha_pending(now)
            await process_expired_chat_freezes(now)
        except Exception as e:
            logger.error(f"Ошибка проверки наказаний: {e}")


# ==================== Автосохранение ====================

async def auto_save_task():
    while True:
        await asyncio.sleep(AUTO_SAVE_INTERVAL)
        try:
            if storage._dirty:
                await storage.save()
        except Exception:
            logger.exception("Автоматическое сохранение не удалось; повтор будет в следующем цикле")


# ==================== Команды с префиксом ! ====================

@router.edited_message()
async def handle_edited_message_anti_spam(msg: Message):
    await handle_anti_spam(msg)


@router.chat_join_request()
async def handle_chat_join_request(request):
    chat_id = request.chat.id
    settings = storage.get_chat_settings(chat_id)
    mode = settings.get('join_request_mode', 'off')
    if mode == 'off':
        return
    if mode not in {'on', 'admin'}:
        logger.warning("Неизвестный режим заявок в чате %s: %r", chat_id, mode)
        return
    if (await bot_can(chat_id, 'can_invite_users')) is not True:
        return

    user = request.from_user
    if mode == 'on':
        try:
            await bot.approve_chat_join_request(chat_id, user.id)
        except (TelegramAPIError, asyncio.TimeoutError) as exc:
            logger.warning("Не удалось автоматически одобрить заявку %s в чате %s: %s", user.id, chat_id, exc)
        return

    keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text='✅ Одобрить',
            callback_data=f'joinreq:approve:{chat_id}:{user.id}',
        ),
        InlineKeyboardButton(
            text='❌ Отклонить',
            callback_data=f'joinreq:decline:{chat_id}:{user.id}',
        ),
    ]])
    try:
        await bot.send_message(
            chat_id,
            f"📨 Запрос на вступление от {mention(chat_id, user)} "
            f"(ID <code>{user.id}</code>).",
            reply_markup=keyboard,
            disable_web_page_preview=True,
        )
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning("Не удалось уведомить чат %s о заявке %s: %s", chat_id, user.id, exc)


@router.callback_query(F.data.startswith('joinreq:'))
async def handle_join_request_decision(call: CallbackQuery):
    parts = (call.data or '').split(':')
    if len(parts) != 4 or parts[1] not in {'approve', 'decline'}:
        return await call.answer("Некорректная заявка.", show_alert=True)
    try:
        chat_id = int(parts[2])
        user_id = int(parts[3])
    except ValueError:
        return await call.answer("Некорректная заявка.", show_alert=True)
    if not call.message or call.message.chat.id != chat_id:
        return await call.answer("Заявка не относится к этому чату.", show_alert=True)
    if not await is_telegram_admin(chat_id, call.from_user.id):
        return await call.answer("Решать заявки могут только Telegram-администраторы.", show_alert=True)
    if (await bot_can(chat_id, 'can_invite_users')) is not True:
        return await call.answer("У бота нет права управлять заявками.", show_alert=True)

    action = parts[1]
    try:
        if action == 'approve':
            await bot.approve_chat_join_request(chat_id, user_id)
        else:
            await bot.decline_chat_join_request(chat_id, user_id)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning("Не удалось обработать заявку %s в чате %s: %s", user_id, chat_id, exc)
        return await call.answer("Не удалось обработать заявку; проверьте, не была ли она уже закрыта.", show_alert=True)

    try:
        await call.message.edit_reply_markup(reply_markup=None)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.debug("Не удалось убрать кнопки заявки в чате %s: %s", chat_id, exc)
    status_text = 'Заявка одобрена.' if action == 'approve' else 'Заявка отклонена.'
    await call.answer(status_text)


def captcha_signature(chat_id: int, user_id: int, expires_at: int) -> str:
    payload = f"{chat_id}:{user_id}:{expires_at}".encode('ascii')
    return hmac.new(BOT_TOKEN.encode('utf-8'), payload, hashlib.sha256).hexdigest()[:16]


async def start_member_captcha(chat_id: int, member: User) -> bool:
    if await bot_can(chat_id, 'can_restrict_members') is not True:
        logger.error("Капча не запущена в чате %s: бот не может ограничивать участников", chat_id)
        return False

    expires_at = int(time.time()) + CAPTCHA_TTL_SECONDS
    pending_all = storage.data.setdefault('captcha_pending', {})
    pending_chat = pending_all.setdefault(str(chat_id), {})
    if not isinstance(pending_chat, dict):
        logger.error("Некорректное хранилище капчи для чата %s", chat_id)
        return False
    pending_chat[str(member.id)] = {
        'expires_at': expires_at,
        'verified': False,
        'next_retry_at': 0,
    }
    storage.mark_dirty()
    await storage.save()

    try:
        await bot.restrict_chat_member(
            chat_id,
            member.id,
            ChatPermissions(can_send_messages=False),
            until_date=expires_at,
        )
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        pending_chat.pop(str(member.id), None)
        if not pending_chat:
            pending_all.pop(str(chat_id), None)
        storage.mark_dirty()
        await storage.save()
        logger.warning("Не удалось ограничить нового участника %s в чате %s для капчи: %s", member.id, chat_id, exc)
        return False

    signature = captcha_signature(chat_id, member.id, expires_at)
    keyboard = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(
            text='Я человек',
            callback_data=f'captcha:{member.id}:{expires_at}:{signature}',
        )
    ]])
    try:
        await bot.send_message(
            chat_id,
            f"🧩 {mention(chat_id, member)}, подтвердите, что вы человек, в течение 5 минут.",
            reply_markup=keyboard,
            disable_web_page_preview=True,
        )
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning("Не удалось отправить капчу пользователю %s в чате %s: %s", member.id, chat_id, exc)
        try:
            await restore_chat_default_permissions(chat_id, member.id)
        except (TelegramAPIError, asyncio.TimeoutError, RuntimeError) as restore_exc:
            logger.error("Не удалось снять ограничение капчи с %s в чате %s: %s", member.id, chat_id, restore_exc)
            pending_chat[str(member.id)]['verified'] = True
            storage.mark_dirty()
            await storage.save()
            return False
        pending_chat.pop(str(member.id), None)
        if not pending_chat:
            pending_all.pop(str(chat_id), None)
        storage.mark_dirty()
        await storage.save()
        return False
    return True


@router.callback_query(F.data.startswith('captcha:'))
async def handle_captcha_confirmation(call: CallbackQuery):
    parts = (call.data or '').split(':')
    if len(parts) != 4 or not call.message:
        return await call.answer("Кнопка проверки некорректна.", show_alert=True)
    try:
        user_id, expires_at = int(parts[1]), int(parts[2])
    except ValueError:
        return await call.answer("Кнопка проверки некорректна.", show_alert=True)
    chat_id = call.message.chat.id
    expected_signature = captcha_signature(chat_id, user_id, expires_at)
    if not hmac.compare_digest(parts[3], expected_signature):
        return await call.answer("Подпись проверки недействительна.", show_alert=True)
    if call.from_user.id != user_id:
        return await call.answer("Пройти проверку может только новый участник.", show_alert=True)

    pending_all = storage.data.get('captcha_pending', {})
    pending_chat = pending_all.get(str(chat_id), {}) if isinstance(pending_all, dict) else {}
    pending = pending_chat.get(str(user_id)) if isinstance(pending_chat, dict) else None
    if not isinstance(pending, dict) or pending.get('expires_at') != expires_at:
        return await call.answer("Проверка уже завершена или истекла.", show_alert=True)
    if time.time() >= expires_at:
        return await call.answer("Время проверки истекло.", show_alert=True)
    if pending.get('verified'):
        return await call.answer("Проверка уже пройдена.")

    pending['verified'] = True
    storage.mark_dirty()
    await storage.save()
    try:
        await restore_chat_default_permissions(chat_id, user_id)
    except (TelegramAPIError, asyncio.TimeoutError, RuntimeError) as exc:
        logger.warning("Капча пройдена, но права %s в чате %s не восстановлены: %s", user_id, chat_id, exc)
        return await call.answer("Проверка пройдена; бот повторит восстановление прав.", show_alert=True)

    pending_chat.pop(str(user_id), None)
    if not pending_chat:
        pending_all.pop(str(chat_id), None)
    storage.mark_dirty()
    await storage.save()
    try:
        await call.message.edit_reply_markup(reply_markup=None)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.debug("Не удалось убрать кнопку капчи в чате %s: %s", chat_id, exc)
    await call.answer("Проверка пройдена. Добро пожаловать!")


async def record_automatic_warning(chat_id: int, actor_id: int, target_id: int, reason: str) -> None:
    user_data = storage.get_user(chat_id, target_id)
    warnings = user_data.setdefault('warnings', [])
    if not isinstance(warnings, list):
        logger.error("Некорректный список предупреждений пользователя %s в чате %s", target_id, chat_id)
        return
    warnings.append({
        'reason': reason,
        'date': time.time(),
        'expire_date': (datetime.now() + timedelta(days=DEFAULT_WARN_DAYS)).timestamp(),
        'permanent': False,
        'warned_by': actor_id,
    })
    log_moderation(chat_id, None, target_id, 'auto_warn', reason, DEFAULT_WARN_DAYS * 86400)
    storage.mark_dirty()
    await storage.save()


async def handle_untrusted_bot_addition(msg: Message, new_member: User) -> bool:
    adder = msg.from_user
    if not adder:
        return False
    try:
        adder_status = await bot.get_chat_member(msg.chat.id, adder.id)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning("Не удалось проверить добавившего бота %s в чате %s: %s", adder.id, msg.chat.id, exc)
        return False
    if adder_status.status in ('administrator', 'creator'):
        return False
    if await bot_can(msg.chat.id, 'can_restrict_members') is not True:
        logger.error("Не удалось удалить добавленного бот-аккаунта %s из чата %s: нет прав", new_member.id, msg.chat.id)
        return False
    try:
        await bot.ban_chat_member(msg.chat.id, new_member.id, revoke_messages=False)
        await bot.unban_chat_member(msg.chat.id, new_member.id, only_if_banned=True)
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning("Не удалось удалить добавленного бот-аккаунта %s из чата %s: %s", new_member.id, msg.chat.id, exc)
        return False
    await record_automatic_warning(
        msg.chat.id,
        adder.id,
        adder.id,
        "Добавление бота без прав администратора Telegram",
    )
    log_moderation(
        msg.chat.id,
        None,
        new_member.id,
        'kick',
        f"Бот добавлен пользователем {adder.id} без прав администратора",
        target_label=new_member.username or new_member.first_name,
    )
    storage.mark_dirty()
    await storage.save()
    try:
        await msg.answer(
            f"⚠️ {mention(msg.chat.id, adder)} получил предупреждение за добавление бота без прав администратора."
        )
    except (TelegramAPIError, asyncio.TimeoutError) as exc:
        logger.warning("Не удалось уведомить чат %s о добавлении бота: %s", msg.chat.id, exc)
    return True


async def track_join_and_enable_raid(chat_id: int) -> None:
    now = time.monotonic()
    if len(join_event_times) > 1000:
        stale_chats = [
            cid for cid, timestamps in join_event_times.items()
            if not timestamps or now - timestamps[-1] > RAID_WINDOW_SECONDS
        ]
        for cid in stale_chats:
            join_event_times.pop(cid, None)
    events = join_event_times.setdefault(chat_id, deque())
    while events and now - events[0] > RAID_WINDOW_SECONDS:
        events.popleft()
    events.append(now)
    if len(events) < RAID_JOIN_THRESHOLD:
        return
    settings = storage.get_chat_settings(chat_id)
    if not settings.get('raid_mode'):
        settings['raid_mode'] = True
        storage.invalidate_chat_settings_cache(chat_id)
        storage.mark_dirty()
        await storage.save()
        logger.warning("Автоантирейд включён в чате %s: %s входов за %s секунд", chat_id, len(events), RAID_WINDOW_SECONDS)
    if isinstance(settings.get('chat_freeze'), dict):
        return
    retry_at = settings.get('raid_freeze_retry_at', 0)
    if isinstance(retry_at, (int, float)) and time.time() < retry_at:
        return
    if await freeze_chat(chat_id, RAID_FREEZE_SECONDS):
        settings.pop('raid_freeze_retry_at', None)
    else:
        settings['raid_freeze_retry_at'] = time.time() + MUTE_CHECK_INTERVAL
        storage.mark_dirty()
        await storage.save()
        logger.error("Автоантирейд включён, но заморозить чат %s не удалось", chat_id)


@router.message(F.new_chat_members)
async def new_member_handler(msg: Message):
    """Приветствие новых участников"""
    cid = str(msg.chat.id)
    welcome_settings = storage.data.get('welcome_settings', {}).get(cid, {})
    chat_settings = storage.get_chat_settings(msg.chat.id)

    for new_member in msg.new_chat_members:
        if new_member.is_bot:
            if new_member.id != bot.id and msg.chat.type in ('group', 'supergroup'):
                await handle_untrusted_bot_addition(msg, new_member)
            continue
        if new_member.id == bot.id:
            continue

        if msg.chat.type in ('group', 'supergroup'):
            try:
                await track_join_and_enable_raid(msg.chat.id)
            except (TelegramAPIError, asyncio.TimeoutError) as exc:
                logger.warning("Не удалось включить автоантирейд для чата %s: %s", msg.chat.id, exc)
            chat_settings = storage.get_chat_settings(msg.chat.id, use_cache=False)
            if chat_settings.get('captcha_enabled') or chat_settings.get('raid_mode'):
                await start_member_captcha(msg.chat.id, new_member)

        if not welcome_settings.get('enabled', True):
            continue
        name = mention(msg.chat.id, new_member)
        text = welcome_settings.get('text')
        if text:
            text = text.replace('{name}', name).replace('{имя}', name)
        else:
            text = f"👋 Добро пожаловать, {name}!"

        try:
            image_url = welcome_settings.get('image_url')
            if image_url:
                try:
                    await bot.send_photo(msg.chat.id, photo=image_url, caption=text)
                except Exception:
                    await msg.answer(text)
            else:
                await msg.answer(text)
        except Exception:
            pass

    if welcome_settings.get('enabled', True):
        try:
            await msg.delete()
        except Exception:
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
    except Exception:
        pass

    try:
        await msg.delete()
    except Exception:
        pass


# ==================== Настройка команд бота ====================

async def setup_bot_commands():
    """Регистрирует стандартные команды в меню Telegram."""
    commands = [
        BotCommand(command='start', description='Старт'),
        BotCommand(command='help', description='Помощь'),
        BotCommand(command='prefix', description='Префикс команд'),
        BotCommand(command='weather', description='Погода'),
        BotCommand(command='time', description='Время в регионе'),
        BotCommand(command='graphtheme', description='Тема графика активности'),
        BotCommand(command='game', description='Игры и мини-игры'),
        BotCommand(command='profile', description='Профиль пользователя'),
        BotCommand(command='top', description='Топ игроков'),
        BotCommand(command='ping', description='Проверить бота'),
    ]
    try:
        await bot.set_my_commands(commands)
    except Exception as e:
        logger.warning(f"Не удалось настроить команды бота: {e}")


# ==================== Запуск ====================

async def main():
    global shutdown_event
    logger.info("🐻 Обкуренный Валера v3.0 запускается...")
    if TRACEMALLOC_ENABLED and not tracemalloc.is_tracing():
        tracemalloc.start(10)
    loop = asyncio.get_running_loop()
    loop.set_default_executor(ThreadPoolExecutor(max_workers=4, thread_name_prefix='valerka'))
    shutdown_event = asyncio.Event()

    def request_shutdown(signum, frame):
        loop.call_soon_threadsafe(shutdown_event.set)

    for signum in (signal.SIGTERM, signal.SIGINT):
        signal.signal(signum, request_shutdown)

    await setup_bot_commands()
    service_tasks = [
        spawn_background_task(check_punishments()),
        spawn_background_task(auto_save_task()),
        spawn_background_task(cleanup_games()),
        spawn_background_task(birthday_notifications_task()),
    ]
    allowed_updates = dp.resolve_used_update_types()
    if 'chat_join_request' not in allowed_updates:
        allowed_updates.append('chat_join_request')
    polling_task = spawn_background_task(
        dp.start_polling(
            bot,
            handle_signals=False,
            allowed_updates=allowed_updates,
        )
    )
    shutdown_task = spawn_background_task(shutdown_event.wait())
    try:
        done, _ = await asyncio.wait(
            (polling_task, shutdown_task),
            return_when=asyncio.FIRST_COMPLETED,
        )
        if shutdown_task in done and not polling_task.done():
            try:
                await dp.stop_polling()
            except RuntimeError as error:
                logger.debug("Поллинг ещё не запущен при завершении: %s", error)
                polling_task.cancel()
        if polling_task.cancelled():
            await asyncio.gather(polling_task, return_exceptions=True)
        else:
            await polling_task
    finally:
        shutdown_task.cancel()
        for task in service_tasks:
            task.cancel()
        await asyncio.gather(shutdown_task, *service_tasks, return_exceptions=True)
        try:
            await storage.flush()
        finally:
            await bot.session.close()


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        storage.save_sync()
    except Exception as e:
        print(f"❌ Ошибка: {e}")
        storage.save_sync()
        raise SystemExit(1) from e
