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
from collections import defaultdict
from datetime import datetime, timedelta
from functools import lru_cache
from io import BytesIO
from pathlib import Path
from typing import Dict, List, Optional, Any, Union, Set

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
    InlineKeyboardMarkup, BufferedInputFile, User
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
MAIN_ADMIN_ID = os.getenv('MAIN_ADMIN_ID')
MAIN_GROUP_ID = os.getenv('MAIN_GROUP_ID')

if not BOT_TOKEN:
    print("❌ BOT_TOKEN не найден!")
    sys.exit(1)

if not MAIN_ADMIN_ID:
    print("❌ MAIN_ADMIN_ID не найден!")
    sys.exit(1)

try:
    MAIN_ADMIN_ID = int(MAIN_ADMIN_ID)
except ValueError:
    print(f"❌ MAIN_ADMIN_ID не является числом: {MAIN_ADMIN_ID}")
    sys.exit(1)

if MAIN_GROUP_ID:
    try:
        MAIN_GROUP_ID = int(MAIN_GROUP_ID)
    except ValueError:
        MAIN_GROUP_ID = None

DATA_FILE = os.getenv('DATA_FILE', 'valera_data.json')
LOG_FILE = os.getenv('LOG_FILE', 'valera_bot.log')
BACKUP_DIR = os.getenv('BACKUP_DIR', 'backups')
DEFAULT_MUTE_MINUTES = int(os.getenv('DEFAULT_MUTE_MINUTES', '30'))
DEFAULT_WARN_DAYS = int(os.getenv('DEFAULT_WARN_DAYS', '30'))
MAX_WARNINGS = int(os.getenv('MAX_WARNINGS', '7'))
REPUTATION_COOLDOWN = int(os.getenv('REPUTATION_COOLDOWN', '3600'))
REPUTATION_DAILY_LIMIT = int(os.getenv('REPUTATION_DAILY_LIMIT', '15'))
MUTE_CHECK_INTERVAL = int(os.getenv('MUTE_CHECK_INTERVAL', '60'))
VIP_RP_RANK = int(os.getenv('VIP_RP_RANK', '2'))
AUTO_SAVE_INTERVAL = int(os.getenv('AUTO_SAVE_INTERVAL', '300'))
MAX_TAG_LENGTH = int(os.getenv('MAX_TAG_LENGTH', '32'))
ANTI_SPAM_ENABLED = os.getenv('ANTI_SPAM_ENABLED', 'true').lower() == 'true'

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

print("=" * 60)
print("🐻 Обкуренный Валера v3.0 - Полная версия")
print("=" * 60)
print(f"👑 Главный админ ID: {MAIN_ADMIN_ID}")
print(f"🏠 Основная группа ID: {MAIN_GROUP_ID or 'не указана (статистика везде)'}")
print(f"📁 Данные: {DATA_FILE}")
print(f"💾 Бэкапы: {BACKUP_DIR}/")
print(f"🔄 Автосохранение: каждые {AUTO_SAVE_INTERVAL} сек")
print(f"🛡️ Анти-спам: {'Включен' if ANTI_SPAM_ENABLED else 'Отключен'}")
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
        self.message_times: Dict[int, List[float]] = defaultdict(list)
        self.message_hashes: Dict[int, List[tuple]] = defaultdict(list)
        self.warnings: Dict[int, int] = defaultdict(int)
        self.last_cleanup = time.time()

    def cleanup(self):
        now = time.time()
        if now - self.last_cleanup < 300:
            return
        self.last_cleanup = now
        for uid in list(self.message_times.keys()):
            self.message_times[uid] = [t for t in self.message_times[uid] if now - t < 10]
            self.message_hashes[uid] = [(h, t) for h, t in self.message_hashes[uid] if now - t < 60]
            if not self.message_times[uid] and not self.message_hashes[uid]:
                del self.message_times[uid]
                del self.message_hashes[uid]
        for uid in list(self.warnings.keys()):
            if now - self.warnings[uid] > 3600:
                del self.warnings[uid]

    def check_message(self, msg: Message) -> tuple:
        if msg.from_user.is_bot:
            return False, None
        uid = msg.from_user.id
        now = time.time()
        self.cleanup()
        self.message_times[uid].append(now)
        if len(self.message_times[uid]) > 7:
            self.warnings[uid] = self.warnings.get(uid, 0) + 1
            return True, "Слишком много сообщений"
        if msg.text and len(msg.text) > 10:
            msg_hash = hashlib.md5(msg.text.encode()).hexdigest()
            self.message_hashes[uid].append((msg_hash, now))
            if sum(1 for h, _ in self.message_hashes[uid] if h == msg_hash) >= 4:
                self.warnings[uid] = self.warnings.get(uid, 0) + 1
                return True, "Повторяющиеся сообщения"
        return False, None

    def get_warnings(self, uid: int) -> int:
        return self.warnings.get(uid, 0)

    def reset_warnings(self, uid: int):
        self.warnings.pop(uid, None)


anti_spam = AntiSpamSystem()


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
            'users': {}, 'command_access': {}, 'personal_access': {},
            'mutes': {}, 'closed_topics': {}, 'phrases': {},
            'welcome_settings': {}, 'marriages': {}, 'isolation': {},
            'games': {}, 'backups': [], 'chat_settings': {}, 'rules': {}, 'polls': {},
            'rank_names': {}, 'rank_emoji': {}
        }

    @staticmethod
    def _create_default_user(uid: int) -> dict:
        """Создаёт пользователя с правильными полями."""
        return {
            'id': uid, 'username': '', 'first_name': '', 'rank': 0,
            'reputation': 0, 'last_rep_time': 0, 'rep_given_today': {},
            'rep_given_total': 0, 'warnings': [], 'awards': [], 'marriage_partner': None,
            'marriage_date': None, 'pending_marriage': None, 'messages_count': 0,
            'violations_count': 0, 'last_violation_time': 0, 'isolation': None,
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

                with open(DATA_FILE, 'w', encoding='utf-8') as f:
                    json.dump(self.data, f, ensure_ascii=False, indent=2, default=str)

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
            with open(DATA_FILE, 'w', encoding='utf-8') as f:
                json.dump(save_data, f, ensure_ascii=False, indent=2, default=str)
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
            'warnings': [],
            'awards': [],
            'activity': {},
            'isolation': None,
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
                'anti_moderation': True,
                'anti_spam': {'enabled': ANTI_SPAM_ENABLED, 'max_messages': 5, 'interval': 5, 'action': 'mute',
                              'duration': 5},
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

def parse_time(s: str) -> int:
    if not s:
        return DEFAULT_MUTE_MINUTES
    s = s.lower().strip()
    total_minutes = 0
    # Тысячелетия, века, годы, месяцы, дни, часы, минуты со всеми падежами
    for pattern, multiplier in [
        (r'(\d+)\s*(?:тысячелети(?:й|и|е)?|тыс\.?(?!\w))', 525600000),  # тысячелетия
        (r'(\d+)\s*(?:век(?:а|ов)?|в\.?(?!\w))', 52560000),  # века
        (r'(\d+)\s*(?:год(?:а|ов)?|л(?:ет)?|г(?!\w))', 525600),  # годы, лет, г
        (r'(\d+)\s*(?:месяц(?:а|ев)?|мес\.?(?!\w))', 43800),  # месяцы
        (r'(\d+)\s*(?:дн?(?:и|ей)?|д(?!\w))', 1440),  # дни, день, дня, дней, д
        (r'(\d+)\s*(?:ча?(?:с(?:а|ов)?)?|ч(?!\w))', 60),  # часы, час, часа, часов, ч
        (r'(\d+)\s*(?:минут(?:ы|)?|минута|м(?!\w))', 1)   # минуты, минута, минут, м
    ]:
        matches = re.finditer(pattern, s)
        for match in matches:
            total_minutes += int(match.group(1)) * multiplier
    if total_minutes > 0:
        return total_minutes
    try:
        return int(s)
    except:
        return DEFAULT_MUTE_MINUTES


def mention(chat_id: int, user: Union[User, int, str]) -> str:
    """Возвращает кликабельную ссылку на пользователя"""
    try:
        if isinstance(user, User):
            if user.username:
                return f'<a href="https://t.me/{user.username}">{user.first_name or user.username}</a>'
            else:
                return f'<a href="tg://user?id={user.id}">{user.first_name or "Пользователь"}</a>'
        if isinstance(user, int):
            cache_key = f"mention_{chat_id}_{user}"
            cached = mention_cache.get(cache_key)
            if cached:
                return cached
            u = storage.get_user(chat_id, user)
            username = u.get('username', '')
            base_display = u.get('custom_name') or u.get('first_name') or username or f"ID:{user}"
            tag = (u.get('custom_tag') or '').strip()
            display = f"{base_display} • {tag}" if tag else base_display
            if username:
                result = f'<a href="https://t.me/{username}">{display}</a>'
            else:
                result = f'<a href="tg://user?id={user}">{display}</a>'
            mention_cache.set(cache_key, result)
            return result
        return str(user)
    except:
        return str(user)


def get_display_name(chat_id: int, uid: int) -> str:
    """Возвращает отображаемое имя пользователя (тег + кастомное или реальное имя)"""
    u = storage.get_user(chat_id, uid)
    base = u.get('custom_name') or u.get('first_name') or u.get('username') or f"ID:{uid}"
    tag = (u.get('custom_tag') or '').strip()
    return f"{base} • {tag}" if tag else base


async def get_target(msg: Message, arg: str = None) -> Optional[int]:
    """
    Получить ID цели. Приоритет: ответ на сообщение > аргумент (username, ID, имя).
    Теперь поддерживает @username даже для новых пользователей!
    """
    if msg.reply_to_message and msg.reply_to_message.from_user:
        return msg.reply_to_message.from_user.id

    if not arg:
        return None

    arg = arg.strip()

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


def check_access(uid: int, chat_id: int, cmd: str, min_rank: int = 0) -> bool:
    if uid == MAIN_ADMIN_ID:
        return True
    uid_str, chat_id_str = str(uid), str(chat_id)
    if cmd in storage.data['personal_access'].get(chat_id_str, {}) and uid in \
            storage.data['personal_access'][chat_id_str][cmd]:
        return True
    acc = storage.data['command_access'].get(chat_id_str, {})
    if cmd in acc:
        return False if acc[cmd] == 9 else storage.get_user(chat_id, uid).get('rank', 0) >= acc[cmd]
    return storage.get_user(chat_id, uid).get('rank', 0) >= min_rank if min_rank else True


def check_anti_moderation(initiator_id: int, target_id: int, chat_id: int) -> bool:
    if initiator_id == target_id or target_id == MAIN_ADMIN_ID:
        return target_id != MAIN_ADMIN_ID
    if initiator_id == MAIN_ADMIN_ID:
        return True
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


def save_activity(chat_id: int, uid: int, atype: str = 'messages'):
    """Сохраняет активность только если пользователь в основной группе"""
    atype_map = {'command': 'commands', 'commands': 'commands', 'rep': 'reputation', 'reputation': 'reputation',
                 'game': 'games', 'games': 'games', 'message': 'messages', 'messages': 'messages'}
    atype = atype_map.get(atype, 'messages')
    u = storage.get_user(chat_id, uid)
    today = datetime.now().strftime('%Y-%m-%d')
    if 'activity' not in u:
        u['activity'] = {}
    if today not in u['activity']:
        u['activity'][today] = {'messages': 0, 'reputation': 0, 'commands': 0, 'games': 0}
    if atype not in u['activity'][today]:
        u['activity'][today][atype] = 0
    u['activity'][today][atype] += 1
    dates = sorted(u['activity'].keys())
    if len(dates) > 60:
        for old in dates[:-60]:
            del u['activity'][old]
    storage.mark_dirty()


def create_graph(chat_id: int, uid: int, days: int = 7) -> Optional[BytesIO]:
    if not MATPLOTLIB_AVAILABLE:
        return None
    u = storage.get_user(chat_id, uid)
    act = u.get('activity', {})
    if not act:
        return None
    today = datetime.now().date()
    dates, msgs, reps = [], [], []
    for i in range(days):
        d = today - timedelta(days=days - 1 - i)
        ds = d.strftime('%Y-%m-%d')
        dates.append(d)
        msgs.append(act.get(ds, {}).get('messages', 0))
        reps.append(act.get(ds, {}).get('reputation', 0))
    try:
        plt.style.use('dark_background')
        fig, ax1 = plt.subplots(figsize=(10, 5), facecolor='#1a170d')
        ax1.set_facecolor('#1a170d')
        ax1.plot(dates, msgs, color='#ebaa47', linewidth=2.5, marker='o', markersize=6, label='Сообщения')
        ax1.fill_between(dates, msgs, color='#604e29', alpha=0.4)
        ax1.set_ylabel('Сообщения', color='#ebaa47')
        ax1.tick_params(axis='y', labelcolor='#ebaa47')
        ax1.tick_params(axis='x', colors='#ebaa47', rotation=45)
        ax2 = ax1.twinx()
        ax2.plot(dates, reps, color='#604e29', linewidth=2.5, marker='o', markersize=6, label='Репутация')
        ax2.set_ylabel('Репутация', color='#604e29')
        ax2.tick_params(axis='y', labelcolor='#604e29')
        ax1.set_ylim(bottom=0)
        ax2.set_ylim(bottom=0)
        ax1.grid(True, color='#604e29', alpha=0.2)
        ax1.xaxis.set_major_formatter(mdates.DateFormatter('%d.%m'))
        plt.title(f'Активность: {get_display_name(chat_id, uid)}', color='#ebaa47', fontsize=14)
        plt.tight_layout()
        buf = BytesIO()
        plt.savefig(buf, format='png', dpi=100, bbox_inches='tight', facecolor='#1a170d')
        buf.seek(0)
        plt.close()
        return buf
    except:
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
RP = RP_FRIENDLY
ALL_RP = {**RP, **VIP_RP, **LOVE_RP}


async def rp_handler(msg: Message):
    if not msg.text:
        return
    raw_text = strip_command_prefix(msg.text)
    text = raw_text.lower()

    for act in sorted(ALL_RP.keys(), key=len, reverse=True):
        if text.startswith(act):
            parts = raw_text.split(maxsplit=2)

            tid = None

            # ПРИОРИТЕТ: ответ на сообщение
            if msg.reply_to_message and msg.reply_to_message.from_user:
                tid = msg.reply_to_message.from_user.id
            elif len(parts) > 1:
                # Если есть аргументы, пробуем найти пользователя
                tid = await get_target(msg, parts[1])

            if not tid:
                return

            if act in VIP_RP and storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) < VIP_RP_RANK:
                return await msg.answer(f"❌ Нужен ранг {VIP_RP_RANK}+")
            if act in LOVE_RP and not storage.get_user(msg.chat.id, msg.from_user.id).get('marriage_partner'):
                return await msg.answer("❌ Только в браке")
            if tid == msg.from_user.id and act not in ['извиниться', 'поздравить']:
                return await msg.answer("❌ Нельзя с собой")

            action_text = random.choice(ALL_RP[act][0])
            emoji = ALL_RP[act][1]
            save_activity(msg.chat.id, msg.from_user.id, 'commands')

            await msg.answer(
                f"{emoji} {mention(msg.chat.id, msg.from_user)} {action_text} {mention(msg.chat.id, tid)}",
                disable_web_page_preview=True
            )
            return


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
    '.ид': 'cmd_id',
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
    'снятьпред': 'cmd_unwarn',
    'снятьварн': 'cmd_unwarn',
    '-пред': 'cmd_unwarn',
    '-варн': 'cmd_unwarn',
    'unwarn': 'cmd_unwarn',
    '-смс': 'cmd_del',
    '.пин': 'cmd_pin',
    'очистить': 'cmd_purge',
    'повысить': 'cmd_promote',
    'понизить': 'cmd_demote',
    'закрыть топик': 'cmd_close_topic',
    'открыть топик': 'cmd_open_topic',
    'топики': 'cmd_list_topics',
    '+изоляция': 'cmd_add_iso',
    '-изоляция': 'cmd_rem_iso',
    'изоляция': 'cmd_show_iso',
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
    'шутка': 'cmd_random_joke',
    'опрос': 'cmd_poll',
    'валера': 'cmd_iris',
    'репорт': 'cmd_report',
    'ник': 'cmd_nick',
    'погоняло': 'cmd_pogonialo',
    'антимодерация': 'cmd_anti_moderation',
    'антиспам': 'cmd_anti_spam',
    'пинг': 'cmd_ping_check',
    'ping': 'cmd_ping_check',
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
}


def strip_command_prefix(text: str) -> str:
    """Удаляет префикс команды (!) в начале строки"""
    text = text.strip()
    if text and text[0] == '!':
        return text[1:] if text[1:2] != ' ' else text[1:].lstrip()
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
        "<code>!погода</code> — погода\n\n"
        "Напишите <code>!помощь</code>, чтобы посмотреть всё меню.")


# ==================== Справка (блоки + кнопки) ====================

HELP_SECTIONS = {
    'info': ("📊 Инфо и статистика",
             "📊 <b>Инфо и статистика</b>\n"
             "━━━━━━━━━━━━━━━\n\n"
             "👤 <b>Профиль</b>\n"
             "  <code>!кто я</code> — ваш профиль\n"
             "  <code>!кто ты @user</code> — профиль пользователя\n"
             "  <code>!кто админ</code> — список админов\n\n"
             "🪜 <b>Ранги и активность</b>\n"
             "  <code>!ранг</code> / <code>!ранги</code> — иерархия рангов\n"
             "  <code>!топ</code> — топ активности\n"
             "  <code>!топ день/неделя/месяц/год</code> — за период\n"
             "  <code>!статистика</code> / <code>!статистика чата</code>\n\n"
             "🎲 <b>Разное</b>\n"
             "  <code>!опрос Вопрос? | Да | Нет</code>\n"
             "  <code>!погода</code>, <code>!шутка</code>"),
    'moderation': ("🛡️ Модерация",
             "🛡️ <b>Модерация</b>\n"
             "━━━━━━━━━━━━━━━\n\n"
             "🔇 <b>Ограничения</b>\n"
             "  <code>!мут @user</code> / <code>!-мут @user</code> — ограничить доступ\n"
             "  <code>!бан @user</code> / <code>!-бан @user</code> — заблокировать пользователя\n"
             "  <code>!бан причина</code> или ответом на сообщение\n\n"
             "🏷️ <b>Тег/погоняло</b>\n"
             "  <code>!погоняло Крутой чел</code> — установить свой тег\n"
             "  <code>!погоняло @user Крутой</code> — поставить тег администратору\n"
             "  <code>!погоняло сбросить</code> — убрать тег\n"
             "  <i>Лимит: до {MAX_TAG_LENGTH} символов</i>\n\n"
             "⚠️ <b>Предупреждения</b>\n"
             "  <code>!пред @user причина</code> — выдать предупреждение\n"
             "  <code>!преды @user</code> — посмотреть активные предупреждения\n"
             "  <code>!снятьпред @user</code> — снять предупреждение\n"
             "  <code>!снятьпред @user 1</code> — снять только одно\n\n"
             "🪜 <b>Ранги</b>\n"
             "  <code>!повысить @user [ранг]</code> — выдать уровень\n"
             "  <code>!понизить @user [ранг]</code> — понизить\n\n"
             "🧹 <b>Чистка</b>\n"
             "  <code>!очистить</code> — очистить чат\n"
             "  <code>!-смс</code> — удалить сообщение (ответом)\n\n"
             "💡 При ответе на сообщение многие команды работают без указания @user".format(MAX_TAG_LENGTH=MAX_TAG_LENGTH)),
    'topics': ("📂 Топики и изоляция",
             "📂 <b>Топики и изоляция</b>\n"
             "━━━━━━━━━━━━━━━\n\n"
             "🗂️ <b>Топики</b>\n"
             "  <code>!закрыть топик</code> — закрыть текущий топик\n"
             "  <code>!закрыть топик 5</code> — закрыть для ранга 5+\n"
             "  <code>!открыть топик</code> — открыть топик\n"
             "  <code>!топики</code> — список закрытых топиков\n\n"
             "🔒 <b>Изоляция</b>\n"
             "  <code>!+изоляция @user 60 спам</code> — ограничить на 60 мин\n"
             "  <code>!-изоляция @user</code> — снять изоляцию\n"
             "  <code>!изоляция</code> — список изолированных\n\n"
             "💡 Работает и по ответу на сообщение, и по @username"),
    'awards': ("🏆 Награды и браки",
             "🏆 <b>Награды и браки</b>\n"
             "━━━━━━━━━━━━━━━\n\n"
             "🎖️ <b>Награды</b>\n"
             "  <code>!наградить @user</code>\n"
             "  <code>!снять награду @user</code>\n"
             "  <code>!мои награды</code>\n"
             "  <code>!топ наград</code>\n\n"
             "💍 <b>Браки</b>\n"
             "  <code>!брак @user</code> — предложение\n"
             "  <code>!развод</code> — расторгнуть\n"
             "  <code>!браки</code> — список пар"),
    'games': ("🎮 Игры, РП, репутация",
             "🎮 <b>Игры, РП, репутация</b>\n"
             "━━━━━━━━━━━━━━━\n\n"
             "🕹️ <b>Игры</b>\n"
             "  <code>!игра</code> — меню игр\n"
             "  <code>!кнб</code> — камень-ножницы-бумага\n"
             "  <code>!крестики нолики</code> — игра в крестики\n\n"
             "🎭 <b>РП</b>\n"
             "  <code>!рп</code> — полный список РП-команд\n\n"
             "⭐ <b>Репутация</b>\n"
             "  Ответьте на сообщение символом <code>+</code>\n"
             "  Или напишите <code>спасибо</code>, <code>плюс</code>, <code>респект</code>\n\n"
             "🧩 <b>Прочее</b>\n"
             "  <code>!репорт</code> — сообщить о нарушении\n"
             "  <code>!ник</code> — сменить никнейм"),
    'settings': ("⚙️ Настройки и ДК",
             "⚙️ <b>Настройки и ДК</b>\n"
             "━━━━━━━━━━━━━━━\n\n"
             "🛠️ <b>Общие настройки</b>\n"
             "  <code>!антимодерация</code> — включить/выключить анти-модерацию\n"
             "  <code>!антиспам</code> — включить/выключить анти-спам\n\n"
             "🔐 <b>Доступ к командам (ДК)</b>\n"
             "  <code>!дк команда 0-5/откл</code> — задать уровень команды\n"
             "  <code>!дк инфо</code> — показать текущие настройки\n"
             "  <code>!+дк команда</code> / <code>!-дк команда</code> — включить/отключить\n"
             "  <code>!+лдк команда @user</code> / <code>!-лдк команда @user</code> — персональный доступ\n\n"
             "<i>Примеры: мут, бан, пред, варн, награда, брак, игра, статистика</i>"),
    'admin': ("🛠️ Админ",
             "🛠️ <b>Админ</b>\n"
             "━━━━━━━━━━━━━━━\n\n"
             "💾 <b>Данные</b>\n"
             "  <code>!общий сбор</code> — общий список активности\n"
             "  <code>!бэкап</code> — создать бэкап\n"
             "  <code>!восстановить</code> — восстановить данные\n\n"
             "👑 <b>Управление</b>\n"
             "  <code>!перед @user</code> — переслать сообщение пользователю\n"
             "  <code>!переранг 0-5 Название</code> — переименовать ранг\n\n"
             "⚠️ Команды работают только при наличии нужных прав и ранга"),
}


def help_main_text() -> str:
    total_cmds = len(set(COMMANDS.values()))
    counter_line = f"📦 <b>{total_cmds} команд</b> в {len(HELP_SECTIONS)} разделах\n\n" if total_cmds else ""
    return ("🐻 <b>ОБКУРЕННЫЙ ВАЛЕРА</b>\n\n"
            "<i>Мощный и многофункциональный бот для управления чатом</i>\n\n"
            f"{counter_line}"
            "� <b>Основные категории:</b>\n"
            "• <b>Инфо и статистика</b> — профиль, ранг, топ, статистика\n"
            "• <b>Модерация</b> — мут, бан, предупреждения, чистка\n"
            "• <b>Топики и изоляция</b> — закрытие топиков и изоляция\n"
            "• <b>Награды и браки</b> — награды, браки, любовь\n"
            "• <b>Фразы и приветствия</b> — автоответы и приветствия\n"
            "• <b>Игры и РП</b> — игры, репутация, РП-команды\n"
            "• <b>Настройки и ДК</b> — доступ к командам и права\n\n"
            "👇 <b>Выберите раздел:</b>\n\n"
            "━━━━━━━━━━━━━━━\n"
            "💡 Все команды с префиксом <code>!</code>\n"
            "📌 Примеры: <code>!кто я</code>, <code>!пред @user</code>, <code>!мут @user</code>\n"
            "🧭 <b>Полезно знать:</b>\n"
            "• Ответьте на сообщение и напишите команду\n"
            "• Работают упоминания <code>@username</code>\n"
            "• Поддерживаются разные падежи и сокращения\n"
            "• Для перечня команд выберите нужный раздел ниже")


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


@router.message(Command('помощь', prefix='!'))
@router.message(Command('help', prefix='!'))
@router.message(Command('инфо', prefix='!'))
@router.message(Command('info', prefix='!'))
async def cmd_help(msg: Message):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    await msg.answer(help_main_text(), reply_markup=help_main_kb())


@router.message(Command('рп', prefix='!'))
async def cmd_rp_list(msg: Message):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    
    # Показываем главное меню РП с кнопками
    txt = "🎭 <b>РП-команды</b>\n━━━━━━━━━━━━━━━\n"
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
    txt = f"{title}\n━━━━━━━━━━━━━━━\n{desc}\n\n"
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
    txt = "🎭 <b>РП-команды</b>\n━━━━━━━━━━━━━━━\n"
    txt += f"Всего команд: <b>{len(ALL_RP)}</b>\n\n"
    txt += "Выбери раздел ниже 👇"
    
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"📌 Обычные ({len(RP)})", callback_data="rp_section:normal")],
        [InlineKeyboardButton(text=f"⭐ ВИП ({len(VIP_RP)})", callback_data="rp_section:vip")],
        [InlineKeyboardButton(text=f"💝 Влюблённые ({len(LOVE_RP)})", callback_data="rp_section:love")],
    ])
    
    await query.message.edit_text(txt, reply_markup=kb)
    await query.answer()


@router.message(F.text)
async def main_text_handler(msg: Message):
    if not msg.text or msg.from_user.is_bot:
        return

    # *** ПРОВЕРКА РЕПУТАЦИИ В ПЕРВУЮ ОЧЕРЕДЬ ***
    # Репутация работает БЕЗ обязательного ! на ответы на сообщения
    if msg.reply_to_message and msg.reply_to_message.from_user:
        if not msg.reply_to_message.from_user.is_bot and msg.from_user.id != msg.reply_to_message.from_user.id:
            text = msg.text.strip()
            rep_words = [
                '+', 'плюс', 'спасибо', 'жиза', 'красава', 'респект',
                'уважение', 'лайк', 'like', 'топ', 'красавчик',
                'молодец', 'умница', 'based', 'base', 'огонь',
                'респектую', '👍', '🔥', '💯', '✅'
            ]
            if text.lower() in rep_words or (text.startswith('+') and len(text) <= 3):
                await give_reputation(msg)
                return

    chat_id = msg.chat.id
    user_id = msg.from_user.id
    main_chat = is_main_chat(chat_id, msg.message_thread_id)

    settings = storage.get_chat_settings(chat_id)
    if settings.get('anti_spam', {}).get('enabled', True):
        is_spam, _ = anti_spam.check_message(msg)
        if is_spam:
            try:
                await msg.delete()
            except:
                pass
            return

    user = storage.update_user_from_message(msg)
    if main_chat:
        save_activity(chat_id, user_id, 'messages')
        user = storage.get_user(chat_id, user_id)
        user['messages_count'] = user.get('messages_count', 0) + 1
        storage.mark_dirty()

    text = msg.text.strip()

    if text and text[0] == '!':
        cleaned = strip_command_prefix(text)
        if cleaned:
            cmd_name, args = match_command(cleaned)
            if cmd_name:
                await execute_command(cmd_name, args, msg, main_chat)
                return

    await rp_handler(msg)
    await auto_mod(msg)


async def execute_command(cmd_name: str, args: str, msg: Message, main_chat: bool):
    """Выполняет команду по её имени"""

    # Маппинг команд на функции
    handlers = {
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
        'cmd_unwarn': lambda: cmd_unwarn(msg, cmd_name),
        'cmd_del': lambda: cmd_del(msg, cmd_name),
        'cmd_pin': lambda: cmd_pin(msg, cmd_name),
        'cmd_purge': lambda: cmd_purge(msg, cmd_name),
        'cmd_promote': lambda: cmd_promote(msg, cmd_name),
        'cmd_demote': lambda: cmd_demote(msg, cmd_name),
        'cmd_close_topic': lambda: cmd_close_topic(msg, cmd_name),
        'cmd_open_topic': lambda: cmd_open_topic(msg, cmd_name),
        'cmd_list_topics': lambda: cmd_list_topics(msg, cmd_name),
        'cmd_add_iso': lambda: cmd_add_iso(msg, cmd_name),
        'cmd_rem_iso': lambda: cmd_rem_iso(msg, cmd_name),
        'cmd_show_iso': lambda: cmd_show_iso(msg),
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
        'cmd_weather': lambda: cmd_weather(msg, cmd_name),
        'cmd_random_joke': lambda: cmd_random_joke(msg, cmd_name),
        'cmd_poll': lambda: cmd_poll(msg, cmd_name),
        'cmd_iris': lambda: cmd_iris(msg, cmd_name),
        'cmd_pogonialo': lambda: cmd_pogonialo(msg, cmd_name),
        'cmd_anti_spam': lambda: cmd_anti_spam(msg, cmd_name),
        'cmd_ping_check': lambda: cmd_ping_check(msg),
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
    if func_name and func_name in handlers:
        await handlers[func_name]()


# ==================== Профиль и информация ====================

def build_profile_text(chat_id: int, uid: int, u: dict, show_last_active: bool = False) -> str:
    """Собирает красиво оформленный текст профиля пользователя."""
    username = u.get('username', '')
    custom_name = u.get('custom_name', '')
    original_name = u.get('first_name') or (f"@{username}" if username else f"ID:{uid}")
    display_name = custom_name or original_name

    if username:
        profile_link = f'<a href="https://t.me/{username}">{display_name}</a>'
    else:
        profile_link = f'<a href="tg://user?id={uid}">{display_name}</a>'

    rank = u.get('rank', 0)
    reputation = u.get('reputation', 0)
    rank_emoji = get_rank_emoji(chat_id, rank)
    rank_name = get_rank_name(chat_id, rank)

    activity = u.get('activity', {})
    today = datetime.now().strftime('%Y-%m-%d')
    today_msgs = activity.get(today, {}).get('messages', 0)
    week_msgs = sum(
        activity.get((datetime.now() - timedelta(days=i)).strftime('%Y-%m-%d'), {}).get('messages', 0)
        for i in range(7))
    month_msgs = sum(
        activity.get((datetime.now() - timedelta(days=i)).strftime('%Y-%m-%d'), {}).get('messages', 0)
        for i in range(30))
    total_msgs = u.get('messages_count', 0)

    first_seen = u.get('first_seen', time.time())
    first_seen_date = datetime.fromtimestamp(first_seen)
    days_since = (datetime.now() - first_seen_date).days

    # ── Заголовок ──
    lines = [f"👤 <b>{profile_link}</b>"]
    if custom_name:
        lines.append(f"📝 <i>оригинальное имя: {original_name}</i>")
    lines.append("━━━━━━━━━━━━━━━")

    # ── Ранг и репутация ──
    lines.append(f"{rank_emoji} <b>{rank_name}</b> <i>(степень {rank})</i>")
    lines.append(f"⭐ Репутация: <b>{reputation}</b>")

    wrn = [w for w in u.get('warnings', []) if w.get('expire_date', 0) > time.time()]
    if wrn:
        lines.append(f"⚠️ Предупреждения: <b>{len(wrn)}/{MAX_WARNINGS}</b>")

    if u.get('marriage_partner'):
        partner = u['marriage_partner']
        marriage_date = u.get('marriage_date')
        if marriage_date:
            days_married = int((time.time() - marriage_date) / 86400)
            lines.append(f"💍 В браке с {mention(chat_id, partner)} <i>({days_married} дн)</i>")
        else:
            lines.append(f"💍 В браке с {mention(chat_id, partner)}")

    # ── Активность ──
    lines.append("")
    lines.append("📊 <b>Активность</b>")
    lines.append(f"  Сегодня: {today_msgs} · Неделя: {week_msgs} · Месяц: {month_msgs}")
    lines.append(f"  Всего сообщений: <b>{total_msgs}</b>")

    # ── Прочее ──
    lines.append("")
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

    # ── Награды ──
    awards = u.get('awards', [])
    recent_awards = sorted(awards, key=lambda x: x.get('given_at', 0), reverse=True)[:5]
    if recent_awards:
        lines.append("")
        lines.append("🏆 <b>Последние награды</b>")
        for award in recent_awards:
            lines.append(f"  • {award['name']} <i>(ст. {award.get('degree', 1)})</i>")

    return "\n".join(lines)


async def who_am_i(msg: Message, cmd_name: str = 'кто я'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
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


async def who_are_you(msg: Message, args: str = None, cmd_name: str = 'кто ты'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    tid = None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif args:
        tid = await get_target(msg, args)

    if not tid:
        return await msg.answer("❌ Укажите пользователя:\n<code>кто ты @user</code> или ответьте на сообщение")

    u = storage.get_user(msg.chat.id, tid)
    text = build_profile_text(msg.chat.id, tid, u, show_last_active=False)

    graph = create_graph(msg.chat.id, tid, 30)
    if graph:
        await msg.answer_photo(BufferedInputFile(graph.read(), 'profile_graph.png'), caption=text)
    else:
        await msg.answer(text, disable_web_page_preview=True)


async def who_admin(msg: Message):
    if not check_access(msg.from_user.id, msg.chat.id, 'кто админ', 0):
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

            if username:
                profile_link = f'<a href="https://t.me/{username}">{display_name}</a>'
            else:
                profile_link = f'<a href="tg://user?id={uid}">{display_name}</a>'

            crown = ' 👑' if uid == MAIN_ADMIN_ID else ''
            txt += f"{status} {profile_link}{crown}\n"

        txt += "\n"

    txt += "━━━━━━━━━━━━━━━━\n"
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
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return await msg.answer("❌ Недостаточно прав!")
    parts = args.split(maxsplit=1)
    if len(parts) < 2 or not parts[0].isdigit():
        return await msg.answer(f"❌ <code>!переранг 0-{MAX_RANK} Новое название</code>")
    level = int(parts[0])
    if not (0 <= level <= MAX_RANK):
        return await msg.answer(f"❌ Уровень должен быть 0-{MAX_RANK}")
    new_name = parts[1].strip()
    if not new_name:
        return await msg.answer("❌ Укажите название")
    storage.data['rank_names'].setdefault(str(msg.chat.id), {})[str(level)] = new_name
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"✅ Ранг {level}: теперь называется «{new_name}»")


async def cmd_id(msg: Message, cmd_name: str = '.ид'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    await msg.answer(
        f"🆔 <code>{msg.reply_to_message.from_user.id}</code>" if msg.reply_to_message else f"🆔 Ваш: <code>{msg.from_user.id}</code>\n💬 Чат: <code>{msg.chat.id}</code>")


# ==================== Топы ====================

async def cmd_top(msg: Message, args: str = "", cmd_name: str = 'топ'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
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
    today = datetime.now().strftime('%Y-%m-%d')
    now = datetime.now()

    users_data = []

    for uid, d in storage.data['users'].get(str(msg.chat.id), {}).items():
        activity = d.get('activity', {})
        msg_count = 0

        if period == 'day':
            msg_count = activity.get(today, {}).get('messages', 0)
        elif period == 'week':
            msg_count = sum(
                activity.get((now - timedelta(days=i)).strftime('%Y-%m-%d'), {}).get('messages', 0) for i in range(7))
        elif period == 'month':
            msg_count = sum(
                activity.get((now - timedelta(days=i)).strftime('%Y-%m-%d'), {}).get('messages', 0) for i in range(30))
        elif period == 'year':
            msg_count = sum(
                activity.get((now - timedelta(days=i)).strftime('%Y-%m-%d'), {}).get('messages', 0) for i in range(365))
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

    txt = f"💬 <b>Топ по сообщениям {period_name}</b>\n\n"

    for i, (uid, count, rank) in enumerate(users_data[:20], 1):
        medal = "🥇" if i == 1 else "🥈" if i == 2 else "🥉" if i == 3 else f"{i}."
        txt += f"{medal} {mention(msg.chat.id, uid)}: {count} сообщ.\n"

    await msg.answer(txt, disable_web_page_preview=True)


async def cmd_chat_stats(msg: Message, cmd_name: str = 'статистика чата'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    total_msgs = sum(d.get('messages_count', 0) for d in storage.data['users'].get(str(msg.chat.id), {}).values())
    total_rep = sum(d.get('reputation', 0) for d in storage.data['users'].get(str(msg.chat.id), {}).values())
    moders = sum(1 for d in storage.data['users'].get(str(msg.chat.id), {}).values() if d.get('rank', 0) >= 1)
    marriages = len(storage.get_chat(msg.chat.id, 'marriages'))
    await msg.answer(
        f"📊 <b>Статистика чата</b>\n\n👥 Пользователей: {len(storage.data['users'].get(str(msg.chat.id), {}))}\n👑 Модераторов: {moders}\n💬 Сообщений: {total_msgs}\n⭐ Репутации: {total_rep}\n💍 Браков: {marriages}")


async def cmd_stats(msg: Message, args: str = "", cmd_name: str = 'статистика'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
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

async def cmd_mute(msg: Message, cmd_name: str = 'мут'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 1):
        return await msg.answer("❌ Недостаточно прав!")

    text = msg.text.strip()
    parts = text.split(maxsplit=2)

    tid = None
    dur_text = ""
    reason = "Без причины"

    # ПРИОРИТЕТ 1: Ответ на сообщение
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        if len(parts) > 1:
            # Парсим время и причину - берём весь остаток после команды
            rest = text[len(parts[0]):].strip()  # Берём весь остаток после "!мут"
            # Ищем число + слово времени (с полной поддержкой падежей и сокращений)
            time_match = re.match(r'^(\d+)\s*(тысячелети(?:й|и|е)?|век(?:а|ов)?|год(?:а|ов)?|месяц(?:а|ев)?|дн?(?:и|ей)?|ча?(?:с(?:а|ов)?)?|минут(?:ы|а)?|[дчм])?(?:\s+(.*))?$', rest, re.IGNORECASE)
            if time_match:
                num = time_match.group(1)
                unit = time_match.group(2) or ""
                reason_part = time_match.group(3) or ""
                dur_text = f"{num} {unit}".strip()
                reason = reason_part.strip() or "Без причины"
            else:
                reason = rest or "Без причины"

    # ПРИОРИТЕТ 2: Аргументы в команде
    elif len(parts) >= 2:
        target_arg = parts[1]
        tid = await get_target(msg, target_arg)

        if not tid:
            return await msg.answer(
                f"❌ Пользователь {target_arg} не найден!\n\n"
                f"💡 Попробуйте ответить на сообщение пользователя"
            )

        if len(parts) >= 3:
            rest = parts[2]
            # Ищем число + слово времени (с полной поддержкой падежей и сокращений)
            time_match = re.match(r'^(\d+)\s*(тысячелети(?:й|и|е)?|век(?:а|ов)?|год(?:а|ов)?|месяц(?:а|ев)?|дн?(?:и|ей)?|ча?(?:с(?:а|ов)?)?|минут(?:ы|а)?|[дчм])?(?:\s+(.*))?$', rest, re.IGNORECASE)
            if time_match:
                num = time_match.group(1)
                unit = time_match.group(2) or ""
                reason_part = time_match.group(3) or ""
                dur_text = f"{num} {unit}".strip()
                reason = reason_part.strip() or "Без причины"
            else:
                reason = rest or "Без причины"

    else:
        return await msg.answer(
            "❌ <b>Использование:</b>\n\n"
            "• <code>мут @user 30 причина</code>\n"
            "• <code>мут 30 причина</code> (ответом)\n\n"
            "⏱️ Время: число + д/ч/м (дни/часы/минуты)\n"
            "📌 Пример: <code>мут @ivan 2ч флуд</code>"
        )

    if not tid:
        return await msg.answer("❌ Не удалось определить пользователя")

    if tid == msg.from_user.id:
        return await msg.answer("❌ Нельзя замутить себя!")

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Анти-модерация!")

    dur = parse_time(dur_text) if dur_text else DEFAULT_MUTE_MINUTES

    try:
        until = datetime.now() + timedelta(minutes=dur)
        await bot.restrict_chat_member(msg.chat.id, tid, ChatPermissions(can_send_messages=False), until_date=int(until.timestamp()))

        # Форматируем время
        if dur >= 525600000:  # тысячелетие (1000 * 365 * 1440)
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
            'expire_time': until.timestamp(),
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
                f"⏱️ Длительность: {time_str}\n"
                f"📝 Причина: {reason}\n"
                f"👮 Выдал: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except:
            pass

        # Сообщение в чат
        await msg.answer(
            f"🔇 {mention(msg.chat.id, tid)} заглушен на {time_str}\n📝 {reason}",
            disable_web_page_preview=True
        )


    except Exception as e:
        await msg.answer(f"❌ Ошибка: {e}")


async def cmd_unmute(msg: Message, cmd_name: str = 'размут'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 1):
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
            return await msg.answer(f"❌ Пользователь {target_arg} не найден!\n\n💡 Ответьте на сообщение пользователя")

    else:
        return await msg.answer(
            "❌ <b>Использование:</b>\n\n"
            "• <code>размут @user</code> или <code>-мут @user</code>\n"
            "• Ответьте на сообщение пользователя и напишите <code>размут</code>"
        )

    if not tid:
        return await msg.answer("❌ Не удалось определить пользователя")

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

        reason_text = f"\n📝 Причина мута была: {mute_info['reason']}" if mute_info and mute_info.get('reason') else ""

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
        await msg.answer(f"❌ Ошибка: {e}")


async def cmd_ban(msg: Message, cmd_name: str = 'бан'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 3):
        return await msg.answer("❌ Недостаточно прав! Требуется ранг 3+")

    text = msg.text.strip()
    parts = text.split(maxsplit=2)

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
        tid = await get_target(msg, target_arg)

        if not tid:
            return await msg.answer(f"❌ Пользователь {target_arg} не найден!\n\n💡 Ответьте на сообщение пользователя")

        if len(parts) >= 3:
            reason = parts[2]

    else:
        return await msg.answer(
            "❌ <b>Использование:</b>\n\n"
            "• <code>бан @user причина</code>\n"
            "• <code>бан причина</code> (ответом)\n\n"
            "📌 Пример: <code>бан @ivan реклама</code>"
        )

    if not tid:
        return await msg.answer("❌ Не удалось определить пользователя")

    if tid == msg.from_user.id:
        return await msg.answer("❌ Нельзя забанить себя!")

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Анти-модерация!")

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
            f"🚫 {mention(msg.chat.id, tid)} забанен\n📝 Причина: {reason}",
            disable_web_page_preview=True
        )

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"🚫 <b>Вы были забанены!</b>\n\n📝 Причина: {reason}\n👮 Забанил: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except:
            pass

    except Exception as e:
        await msg.answer(f"❌ Ошибка: {e}")


async def cmd_unban(msg: Message, cmd_name: str = 'разбан'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 3):
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
            return await msg.answer(f"❌ Пользователь {target_arg} не найден!\n\n💡 Ответьте на сообщение пользователя")

    else:
        return await msg.answer(
            "❌ <b>Использование:</b>\n\n"
            "• <code>разбан @user</code> или <code>-бан @user</code>\n"
            "• Ответьте на сообщение пользователя и напишите <code>разбан</code>"
        )

    if not tid:
        return await msg.answer("❌ Не удалось определить пользователя")

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

        reason_text = f"\n📝 Причина бана: {ban_info['reason']}" if ban_info and ban_info.get('reason') else ""

        # Сообщение в чат
        await msg.answer(f"✅ {mention(msg.chat.id, tid)} разбанен{reason_text}",
                        disable_web_page_preview=True)

        # Уведомление в личку
        try:
            await bot.send_message(
                tid,
                f"✅ <b>Бан снят!</b>\n\n👮 Снял: {mention(msg.chat.id, msg.from_user.id)}",
                disable_web_page_preview=True
            )
        except:
            pass


    except Exception as e:
        await msg.answer(f"❌ Ошибка: {e}")


async def cmd_warn(msg: Message, cmd_name: str = 'пред'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 1):
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
                f"❌ <b>Использование:</b>\n\n"
                f"📌 <code>{command_used} @user [дни] причина</code>\n"
                f"📌 Или ответьте на сообщение пользователя\n\n"
                f"💡 Примеры:\n"
                f"• <code>пред @user 7 флуд</code>\n"
                f"• <code>варн @user спам</code>\n"
                f"• <code>warn @user 30 оскорбления</code>"
            )
        tid = await get_target(msg, parts[1])
        if not tid:
            return await msg.answer("❌ Пользователь не найден")
        if len(parts) > 2:
            try:
                days = int(parts[2])
                reason = parts[3] if len(parts) > 3 else 'Без причины'
            except:
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
        'expire_date': (datetime.now() + timedelta(days=days)).timestamp(),
        'warned_by': msg.from_user.id
    }
    
    if 'warnings' not in u:
        u['warnings'] = []
    
    u['warnings'].append(new_warning)
    
    # Получаем активные предупреждения
    active = [w for w in u['warnings'] if w.get('expire_date', 0) > time.time()]
    
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
                f"📝 Причина: {reason}",
                disable_web_page_preview=True
            )

            try:
                await bot.send_message(
                    tid,
                    f"🚫 <b>Вы были забанены!</b>\n\n"
                    f"📊 Достигнут лимит предупреждений: {len(active)}/{MAX_WARNINGS}\n"
                    f"📝 Последняя причина: {reason}",
                    disable_web_page_preview=True
                )
            except:
                pass
            return

        except Exception as e:
            logger.warning(f"Не удалось забанить пользователя {tid} после предупреждений: {e}")

    # Уведомление в чат
    await msg.answer(
        f"⚠️ <b>Предупреждение выдано!</b>\n\n"
        f"👤 {mention(msg.chat.id, tid)}\n"
        f"📝 Причина: {reason}\n"
        f"⏱️ Срок: {time_str}\n"
        f"📊 Активных: {len(active)}/{MAX_WARNINGS}\n"
        f"👮 Выдал: {mention(msg.chat.id, msg.from_user.id)}",
        disable_web_page_preview=True
    )

    # Уведомление в личку пользователю
    try:
        user_msg = (
            f"⚠️ <b>Вы получили предупреждение!</b>\n\n"
            f"📝 Причина: {reason}\n"
            f"⏱️ Срок: {time_str}\n"
            f"📊 Всего активных: {len(active)}/{MAX_WARNINGS}\n\n"
            f"📌 При {MAX_WARNINGS} предупреждениях вы получите бан."
        )
        await bot.send_message(tid, user_msg, disable_web_page_preview=True)
    except Exception as e:
        logger.debug(f"Не удалось отправить ДМ о варне: {e}")


async def show_warnings(msg: Message, cmd_name: str = 'преды'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    parts = msg.text.split()

    tid = msg.from_user.id
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif len(parts) > 1:
        target = await get_target(msg, parts[1])
        if target:
            tid = target

    wrn = [w for w in storage.get_user(msg.chat.id, tid).get('warnings', []) if w.get('expire_date', 0) > time.time()]

    if not wrn:
        msg_to_send = await msg.answer(f"✅ У {mention(msg.chat.id, tid)} нет активных предупреждений",
                                       disable_web_page_preview=True)
        await asyncio.sleep(3)
        try:
            await msg_to_send.delete()
        except:
            pass
        return

    txt = f"⚠️ <b>Предупреждения {mention(msg.chat.id, tid)}:</b> {len(wrn)}/{MAX_WARNINGS}\n\n"
    for i, w in enumerate(wrn, 1):
        expire_date = datetime.fromtimestamp(w['expire_date']).strftime('%d.%m.%Y')
        txt += f"{i}. {w['reason']}\n   └ до {expire_date} | выдал: {mention(msg.chat.id, w['warned_by'])}\n"

    await msg.answer(txt, disable_web_page_preview=True)


async def cmd_unwarn(msg: Message, cmd_name: str = 'снятьпред'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return

    parts = msg.text.split()

    tid = None
    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif len(parts) > 1:
        tid = await get_target(msg, parts[1])

    if not tid:
        return await msg.answer(
            "❌ <b>Использование:</b>\n\n"
            "• <code>снятьпред @user [номер]</code> — снять конкретное\n"
            "• <code>снятьпред @user</code> — снять все активные\n"
            "• <code>снятьварн @user [номер]</code>\n"
            "• <code>unwarn @user [номер]</code>\n"
            "• Или ответьте на сообщение пользователя"
        )

    u = storage.get_user(msg.chat.id, tid)
    active = [(i, w) for i, w in enumerate(u.get('warnings', [])) if w.get('expire_date', 0) > time.time()]

    if not active:
        chat_msg = await msg.answer(
            f"✅ У {mention(msg.chat.id, tid)} нет активных предупреждений",
            disable_web_page_preview=True
        )
        await asyncio.sleep(3)
        try:
            await chat_msg.delete()
        except:
            pass
        return

    # Проверяем если указан номер
    num_idx = 2 if not msg.reply_to_message else 1
    if len(parts) > num_idx and parts[num_idx].isdigit():
        idx = int(parts[num_idx]) - 1
        if 0 <= idx < len(active):
            # Снимаем конкретное предупреждение по его индексу в исходном массиве
            removed_warning = u['warnings'][active[idx][0]]
            del u['warnings'][active[idx][0]]
            
            storage.mark_dirty()
            await storage.save()
            
            logger.info(f"Снято предупреждение #{idx + 1} у {tid}")

            chat_msg = await msg.answer(
                f"✅ Снято предупреждение #{idx + 1} у {mention(msg.chat.id, tid)}\n"
                f"📝 Причина была: {removed_warning['reason']}",
                disable_web_page_preview=True
            )
            await asyncio.sleep(3)
            try:
                await chat_msg.delete()
            except:
                pass
            return
        else:
            return await msg.answer(f"❌ Предупреждение #{idx + 1} не найдено")

    # Если не указан номер, снимаем ВСЕ АКТИВНЫЕ
    before_count = len(active)
    # Удаляем активные предупреждения в обратном порядке (чтобы не сбить индексы)
    for idx, _ in sorted(active, key=lambda x: x[0], reverse=True):
        del u['warnings'][idx]
    
    storage.mark_dirty()
    await storage.save()
    
    logger.info(f"Снято {before_count} предупреждений у {tid}")

    await msg.answer(
        f"✅ Снято <b>{before_count}</b> предупреждений у {mention(msg.chat.id, tid)}",
        disable_web_page_preview=True
    )


async def cmd_del(msg: Message, cmd_name: str = '-смс'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 1):
        return
    if msg.reply_to_message:
        try:
            await msg.reply_to_message.delete()
            await msg.delete()
        except:
            pass


async def cmd_pin(msg: Message, cmd_name: str = '.пин'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return
    if msg.reply_to_message:
        try:
            await msg.reply_to_message.pin()
        except:
            pass


async def cmd_purge(msg: Message, cmd_name: str = 'очистить'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return

    # Обязательно нужно ответить на сообщение
    if not msg.reply_to_message:
        return await msg.answer(
            "❌ <b>Как использовать очистку:</b>\n\n"
            "1. Ответьте на сообщение, с которого хотите начать очистку\n"
            "2. Напишите <code>очистить</code>\n\n"
            "📌 <i>Будут удалены все сообщения от отвеченного и выше</i>"
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
            await msg.answer("❌ Нельзя удалять сообщения старше 48 часов")
        elif "not enough rights" in error_msg.lower():
            await msg.answer("❌ У бота нет прав на удаление сообщений")
        else:
            await msg.answer(f"❌ Ошибка: {error_msg[:100]}")


# ==================== Топики ====================

async def cmd_close_topic(msg: Message, cmd_name: str = 'закрыть топик'):
    """Закрыть топик - теперь поддерживает @упоминания для исключений"""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return

    # Парсим аргументы: может быть ранг ИЛИ @упоминания
    parts = msg.text.split()

    rank = 0
    allowed_users = []

    for part in parts[1:]:  # пропускаем "закрыть" и "топик"
        if part.isdigit():
            rank = int(part)
        elif part.startswith('@'):
            username = part[1:].lower()
            uid = storage.get_user_by_username(msg.chat.id, username)
            if uid is not None:
                allowed_users.append(str(uid))

    # Определяем топик
    topic_id = msg.message_thread_id
    if topic_id is None or topic_id == 1:
        topic_id = 0
        topic_name = "основной чат"
    else:
        topic_name = f"топик {topic_id}"

    # Сохраняем (теперь с поддержкой и ранга, и пользователей)
    if 'closed_topics' not in storage.data:
        storage.data['closed_topics'] = {}
    if str(msg.chat.id) not in storage.data['closed_topics']:
        storage.data['closed_topics'][str(msg.chat.id)] = {}

    storage.data['closed_topics'][str(msg.chat.id)][str(topic_id)] = {
        'required_rank': rank,
        'allowed_users': allowed_users,  # НОВОЕ: список пользователей с доступом
        'closed_by': msg.from_user.id,
        'closed_at': time.time()
    }

    storage.mark_dirty()
    await storage.save()

    # Ответ
    response = f"🔒 <b>Закрыт: {topic_name}</b>\n👮 Закрыл: {mention(msg.chat.id, msg.from_user.id)}\n"

    if rank > 0:
        response += f"🔐 Требуется ранг: {rank}+\n"

    if allowed_users:
        users_list = ', '.join([mention(msg.chat.id, uid) for uid in allowed_users])
        response += f"👤 Исключения: {users_list}\n"

    if rank == 0 and not allowed_users:
        response += f"🔓 Могут писать все\n"
    elif rank > 0 and allowed_users:
        response += f"💡 Доступ: ранг {rank}+ ИЛИ из списка исключений"

    await msg.answer(response, disable_web_page_preview=True)


async def cmd_open_topic(msg: Message, cmd_name: str = 'открыть топик'):
    """Открыть топик (без изменений)"""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 2):
        return

    topic_id = msg.message_thread_id
    if topic_id is None or topic_id == 1:
        topic_id = 0

    chat_topics = storage.data.get('closed_topics', {}).get(str(msg.chat.id), {})

    if str(topic_id) in chat_topics:
        del chat_topics[str(topic_id)]
        storage.mark_dirty()
        await storage.save()

        topic_name = "основной чат" if topic_id == 0 else f"топик {topic_id}"
        await msg.answer(f"🔓 <b>Открыт {topic_name}</b>", disable_web_page_preview=True)
    else:
        await msg.answer("❌ Этот топик не был закрыт")


async def cmd_list_topics(msg: Message, cmd_name: str = 'топики'):
    """Показать список закрытых топиков (обновлено с показом исключений)"""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    chat_topics = storage.data.get('closed_topics', {}).get(str(msg.chat.id), {})

    if not chat_topics:
        return await msg.answer("📂 <b>Нет закрытых топиков</b>\n\n"
                                "💡 <code>закрыть топик 5</code> - по рангу\n"
                                "💡 <code>закрыть топик @user1 @user2</code> - по исключениям\n"
                                "💡 <code>закрыть топик 5 @user1</code> - комбинированный")

    txt = "🔒 <b>Закрытые топики:</b>\n\n"
    for topic_id_str, data in chat_topics.items():
        topic_id = int(topic_id_str)
        topic_name = "основной чат" if topic_id == 0 else f"топик {topic_id}"
        rank = data.get('required_rank', 0)
        allowed = data.get('allowed_users', [])
        closed_by = mention(msg.chat.id, data.get('closed_by'))
        closed_at = datetime.fromtimestamp(data.get('closed_at', time.time())).strftime('%d.%m.%Y %H:%M')

        txt += f"📌 <b>{topic_name}</b>\n"
        txt += f"   👮 Закрыл: {closed_by}\n"
        txt += f"   🕐 {closed_at}\n"

        if rank > 0:
            txt += f"   🔐 Ранг: {rank}+\n"
        if allowed:
            users_preview = ', '.join([mention(msg.chat.id, uid) for uid in allowed[:3]])
            if len(allowed) > 3:
                users_preview += f" +{len(allowed) - 3}"
            txt += f"   👤 Исключения: {users_preview}\n"

        txt += "\n"

    await msg.answer(txt, disable_web_page_preview=True)


# ==================== Изоляция ====================

async def cmd_add_iso(msg: Message, cmd_name: str = '+изоляция'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 3):
        return

    parts = msg.text.split(maxsplit=5)

    tid = None
    arg_start = 1

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
        arg_start = 1
    else:
        if len(parts) < 2:
            return await msg.answer("❌ <code>+изоляция @user главный/ID время причина</code> или ответом")
        tid = await get_target(msg, parts[1])
        if not tid:
            return await msg.answer("❌ Пользователь не найден")
        arg_start = 2

    remaining = parts[arg_start:]
    if len(remaining) < 2:
        return await msg.answer("❌ Не хватает аргументов: <code>+изоляция [@user] тип время причина</code>")

    iso_type = remaining[0]
    duration_text = remaining[1]
    reason = ' '.join(remaining[2:]) if len(remaining) > 2 else 'Без причины'

    if not check_anti_moderation(msg.from_user.id, tid, msg.chat.id):
        return await msg.answer("❌ Анти-модерация!")

    iso = {
        'chat_id': msg.chat.id,
        'type': iso_type,
        'reason': reason,
        'expire_time': (datetime.now() + timedelta(minutes=parse_time(duration_text))).timestamp(),
        'isolated_by': msg.from_user.id
    }
    storage.data['isolation'][str(tid)] = iso
    storage.get_user(msg.chat.id, tid)['isolation'] = iso
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"🔒 {mention(msg.chat.id, tid)} изолирован на {parse_time(duration_text)} мин.\n📝 {reason}",
                     disable_web_page_preview=True)


async def cmd_rem_iso(msg: Message, cmd_name: str = '-изоляция'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 3):
        return

    parts = msg.text.split()
    tid = None

    if msg.reply_to_message and msg.reply_to_message.from_user:
        tid = msg.reply_to_message.from_user.id
    elif len(parts) > 1:
        tid = await get_target(msg, parts[1])

    if tid:
        storage.data['isolation'].pop(str(tid), None)
        storage.get_user(msg.chat.id, tid)['isolation'] = None
        storage.mark_dirty()
        await storage.save()
        await msg.answer(f"🔓 Изоляция снята с {mention(msg.chat.id, tid)}", disable_web_page_preview=True)


async def cmd_show_iso(msg: Message):
    iso = storage.data.get('isolation', {})
    if not iso:
        return await msg.answer("✅ Нет изолированных")
    txt = "🔒 <b>Изолированные:</b>\n\n"
    for uid, data in iso.items():
        txt += f"• {mention(msg.chat.id, int(uid))}: {data['reason']} (до {datetime.fromtimestamp(data['expire_time']).strftime('%d.%m.%Y %H:%M')})\n"
    await msg.answer(txt, disable_web_page_preview=True)


# ==================== Награды ====================

async def cmd_give_award(msg: Message, cmd_name: str = 'наградить'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 4):
        return await msg.answer("❌ Недостаточно прав! Требуется ранг 4+")

    text = msg.text.strip()

    for prefix in ['!']:
        if text.startswith(prefix):
            text = text[1:].strip()
            break

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
        potential_tid = await get_target(msg, parts[0])

        if potential_tid:
            tid = potential_tid
            award_name = parts[1] if len(parts) > 1 else None
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

    await msg.answer(
        f"{medal} <b>Награда вручена!</b>\n\n"
        f"👤 Получатель: {mention(msg.chat.id, tid)}\n"
        f"🏅 Награда: {award_name}\n"
        f"⭐ Степень: {degree}\n"
        f"📊 Всего наград: {total}\n"
        f"👮 Выдал: {mention(msg.chat.id, msg.from_user.id)}",
        disable_web_page_preview=True
    )


async def cmd_rem_award(msg: Message, cmd_name: str = 'снять награду'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 4):
        return await msg.answer("❌ Недостаточно прав! Требуется ранг 4+")

    text = msg.text.strip()

    for prefix in ['!']:
        if text.startswith(prefix):
            text = text[1:].strip()
            break

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
        potential_tid = await get_target(msg, parts[0])

        if potential_tid:
            tid = potential_tid
            award_name = parts[1] if len(parts) > 1 else None
        else:
            return await msg.answer("❌ Пользователь не найден")

    if not tid:
        return await msg.answer("❌ Не удалось определить пользователя")

    if not award_name or len(award_name.strip()) == 0:
        return await msg.answer("❌ Укажите название награды для снятия")

    award_name = award_name.strip()

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

        await msg.answer(
            f"✅ <b>Награда снята</b>\n\n"
            f"👤 Пользователь: {mention(msg.chat.id, tid)}\n"
            f"🏅 Награда: {found_award['name']}\n"
            f"⭐ Степень: {found_award.get('degree', '?')}\n"
            f"📊 Осталось наград: {len(awards)}",
            disable_web_page_preview=True
        )
        return

    similar = [a for a in awards if award_name.lower() in a['name'].lower()]
    if similar:
        similar_list = "\n".join([f"• {a['name']} (ст. {a.get('degree', '?')})" for a in similar[:10]])
        return await msg.answer(f"❌ Награда '{award_name}' не найдена\n\n🔍 <b>Похожие:</b>\n{similar_list}",
                                disable_web_page_preview=True)

    await msg.answer(f"❌ Награда '{award_name}' не найдена у {mention(msg.chat.id, tid)}",
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
        for prefix in ['!']:
            if text.startswith(prefix):
                text = text[1:].strip()
                break
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

        txt += f"{medal} <b>{name}</b> (ст. {degree})\n"

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

    await msg.answer(f"✅ Фраза добавлена: {trigger} → {response}\n📊 Теперь у этого слова {count} вариант(ов) ответа")


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
        txt += f"{anywhere_icon} <b>{trigger}</b>: {responses_count} отв. (напр. {preview})\n"

        # Опционально: показать все ответы
        if len(items) <= 3:
            for p in items:
                txt += f"   └ {p['response'][:40]}\n"

    await msg.answer(txt)


async def cmd_phrase_stats(msg: Message):
    phrases = storage.get_chat(msg.chat.id, 'phrases')
    if not isinstance(phrases, list) or not phrases:
        return await msg.answer("📝 Нет фраз")
    sorted_p = sorted(phrases, key=lambda x: x.get('uses', 0), reverse=True)
    txt = "📊 <b>Статистика фраз:</b>\n\n"
    for p in sorted_p[:20]:
        txt += f"• {p['trigger']}: {p.get('uses', 0)} раз\n"
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
        await msg.answer(f"✅ Удалено {removed} фраз с ответом '{response_text}'")
    else:
        # Удаляем все фразы с таким триггером
        phrases[:] = [p for p in phrases if p['trigger'] != trigger]
        removed = before_count - len(phrases)
        await msg.answer(f"✅ Удалено {removed} фраз с триггером '{trigger}'")

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
        return await msg.answer(f"❌ Нет фраз с триггером '{trigger}'")

    txt = f"📝 <b>Все ответы на '{trigger}':</b>\n\n"
    for i, p in enumerate(matching, 1):
        anywhere = "🌐 (везде)" if p.get('anywhere') else "📌 (точно)"
        uses = p.get('uses', 0)
        txt += f"{i}. {p['response']}\n   └ {anywhere} | использовано: {uses} раз\n\n"

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
        txt += f"{i}. {rule}\n"
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
            InlineKeyboardButton(text="❌ Крестики-Нолики", callback_data="game_ttt_menu")
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


# ==================== ОБРАБОТЧИК ВСЕХ ИГРОВЫХ CALLBACK'ОВ ====================

@router.callback_query(lambda c: c.data and c.data.startswith('game_'))
async def game_menu_handler(call: CallbackQuery):
    """Обработчик кнопок главного меню"""
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
    elif action == "game_back_to_menu":
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [
                InlineKeyboardButton(text="🎮 КНБ (с ботом)", callback_data="game_rps_bot"),
                InlineKeyboardButton(text="🤝 КНБ (с игроком)", callback_data="game_rps_player")
            ],
            [
                InlineKeyboardButton(text="❌ Крестики-Нолики", callback_data="game_ttt_menu")
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
        'message_id': call.message.message_id
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
        'chat_id': call.message.chat.id
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
        'chat_id': call.message.chat.id
    }

    await draw_ttt_board(call.message, game_id,
                         f"🎮 Крестики-Нолики\n{mention(call.message.chat.id, p1)} (❌) vs {mention(call.message.chat.id, p2)} (⭕)\n"
                         f"Ход: {mention(call.message.chat.id, p1)}")


# ==================== ВЫХОД ИЗ TTT ====================

@router.callback_query(lambda c: c.data and c.data.startswith('tttexit_'))
async def ttt_exit_handler(call: CallbackQuery):
    """Выход из игры"""
    game_id = '_'.join(call.data.split('_')[1:])
    game = active_games.pop(game_id, None)

    if game:
        game['status'] = 'finished'

    await call.message.edit_text("❌ Вы вышли из игры", reply_markup=None)
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
    for prefix in ['!']:
        if text.startswith(prefix):
            text = text[1:].strip()
            break

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

async def cmd_weather(msg: Message, cmd_name: str = 'погода'):
    """Погода через Open-Meteo (с редактированием сообщения)"""
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    parts = msg.text.split(maxsplit=1)
    city = parts[1].strip() if len(parts) > 1 else 'Moscow'

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

        async with aiohttp.ClientSession() as session:
            # Поиск города
            async with session.get(geo_url, params=params) as resp:
                if resp.status != 200:
                    await status_msg.edit_text(f"❌ Город '{city}' не найден")
                    return

                geo_data = await resp.json()

            if not geo_data.get('results'):
                await status_msg.edit_text(f"❌ Город '{city}' не найден")
                return

            location = geo_data['results'][0]
            lat = location['latitude']
            lon = location['longitude']
            city_name = location.get('name', city)
            country = location.get('country', '')

            # Обновляем статус
            await status_msg.edit_text(f"🌤️ <i>Получаю погоду для {city_name}...</i>")

            # Получаем погоду
            weather_url = "https://api.open-meteo.com/v1/forecast"
            weather_params = {
                'latitude': lat,
                'longitude': lon,
                'current': 'temperature_2m,relative_humidity_2m,apparent_temperature,weather_code,wind_speed_10m,wind_direction_10m,pressure_msl',
                'timezone': 'auto'
            }

            async with session.get(weather_url, params=weather_params) as resp:
                weather_data = await resp.json()

        current = weather_data['current']

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

        # Формируем ответ
        text = (
            f"{emoji} <b>Погода в {city_name}{', ' + country if country else ''}</b>\n\n"
            f"🌡️ <b>Температура:</b> {current['temperature_2m']}°C\n"
            f"🤔 <b>Ощущается:</b> {current['apparent_temperature']}°C\n"
            f"📝 <b>Описание:</b> {description}\n"
            f"💧 <b>Влажность:</b> {current['relative_humidity_2m']}%\n"
            f"💨 <b>Ветер:</b> {current['wind_speed_10m']} км/ч {wind_dir_text}\n"
            f"🔵 <b>Давление:</b> {pressure:.0f} гПа"
        )

        # Редактируем сообщение
        await status_msg.edit_text(text, disable_web_page_preview=True)

    except ImportError:
        await status_msg.edit_text("❌ Установите aiohttp: <code>pip install aiohttp</code>")
    except asyncio.TimeoutError:
        await status_msg.edit_text("⏳ Таймаут. Попробуйте позже.")
    except Exception as e:
        logger.error(f"Ошибка погоды: {e}")
        await status_msg.edit_text(f"❌ Не удалось получить погоду для '{city}'")


async def cmd_random_joke(msg: Message, cmd_name: str = 'шутка'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
    try:
        import aiohttp
        async with aiohttp.ClientSession() as session:
            try:
                url = f"http://rzhunemogu.ru/RandJSON.aspx?CType=1&{random.randint(1, 100000)}"
                async with session.get(url, timeout=5) as resp:
                    if resp.status == 200:
                        text = await resp.text()
                        match = re.search(r'"content":"([^"]+)"', text)
                        if match:
                            joke = match.group(1).replace('\\n', '\n').replace('\\"', '"')
                            if len(joke) > 5:
                                return await msg.answer(f"😂 <b>Анекдот:</b>\n\n{joke}")
            except:
                pass
            async with session.get('https://v2.jokeapi.dev/joke/Any?type=single') as resp:
                if resp.status == 200:
                    data = await resp.json()
                    joke = data.get('joke', '') or f"{data.get('setup', '')}\n\n{data.get('delivery', '')}"
                    return await msg.answer(f"😂 <b>Шутка:</b>\n\n{joke}")
            return await msg.answer("❌ Не удалось получить шутку")
    except:
        await msg.answer("❌ Ошибка")


async def cmd_iris(msg: Message, cmd_name: str = 'валера'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    query = re.sub(r'^\S+\s*', '', msg.text, count=1).strip().lower()
    responses = {'характер': '🐻 Я обкуренный желейный медведь-помощник!', 'версия': '🐻 Обкуренный Валера v3.0',
                 'помощь': 'Используйте !помощь'}
    for key, resp in responses.items():
        if key in query:
            return await msg.answer(resp)
    await msg.answer("🐻 Спросите: характер, версия, помощь")


async def cmd_report(msg: Message, cmd_name: str = 'репорт'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    parts = msg.text.split(maxsplit=1)
    reason = parts[1] if len(parts) > 1 else 'Не указана'
    text = f"🚨 <b>Репорт</b>\n👤 {mention(msg.chat.id, msg.from_user.id)}\n💬 {msg.chat.title}\n📝 {reason}"

    recipients = {MAIN_ADMIN_ID}
    for uid, d in storage.data['users'].get(str(msg.chat.id), {}).items():
        if d.get('rank', 0) >= 1:
            recipients.add(int(uid))

    sent = 0
    for admin_id in recipients:
        try:
            await bot.send_message(
                admin_id,
                text,
                disable_web_page_preview=True,
                parse_mode=ParseMode.HTML
            )
            sent += 1
        except Exception:
            continue

    if sent == 0:
        return await msg.answer("❌ Ошибка: не удалось отправить репорт ни одному админу")

    storage.get_user(msg.chat.id, msg.from_user.id)['reports_sent'] = storage.get_user(msg.chat.id,
                                                                                       msg.from_user.id).get(
        'reports_sent', 0) + 1
    storage.mark_dirty()
    await storage.save()
    await msg.answer("✅ Отправлено")


# ==================== Ранги ====================

async def cmd_promote(msg: Message, cmd_name: str = 'повысить'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
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
        tid = await get_target(msg, parts[1])
        if not tid:
            return await msg.answer("❌ Пользователь не найден")
        if len(parts) > 2:
            rank_arg = parts[2]

    if not tid:
        return await msg.answer("❌ Пользователь не найден")

    current = storage.get_user(msg.chat.id, tid).get('rank', 0)
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

    storage.get_user(msg.chat.id, tid)['rank'] = new_rank
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"🎉 {mention(msg.chat.id, tid)}: {get_rank_name(msg.chat.id, current)} → {get_rank_name(msg.chat.id, new_rank)}",
                     disable_web_page_preview=True)


async def cmd_demote(msg: Message, cmd_name: str = 'понизить'):
    save_activity(msg.chat.id, msg.from_user.id, 'commands')
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
        tid = await get_target(msg, parts[1])
        if len(parts) > 2:
            rank_arg = parts[2]

    if not tid:
        return await msg.answer("❌ <code>понизить @user</code> или ответом")

    current = storage.get_user(msg.chat.id, tid).get('rank', 0)
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

    storage.get_user(msg.chat.id, tid)['rank'] = new_rank
    storage.mark_dirty()
    await storage.save()
    await msg.answer(f"📉 {mention(msg.chat.id, tid)}: {get_rank_name(msg.chat.id, current)} → {get_rank_name(msg.chat.id, new_rank)}",
                     disable_web_page_preview=True)


# ==================== Погоняло и ник ====================

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
    if raw.startswith('!'):
        raw = raw[1:].strip()

    args = raw[len(cmd_name):].strip() if raw.lower().startswith(cmd_name.lower()) else raw
    if not args:
        user_tag = (storage.get_user(msg.chat.id, msg.from_user.id).get('custom_tag') or '').strip()
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

    if parts and parts[0].startswith('@'):
        if msg.from_user.id != MAIN_ADMIN_ID and storage.get_user(msg.chat.id, msg.from_user.id).get('rank', 0) < 1:
            return await msg.answer("❌ Сменить тег другому человеку могут только администраторы.")
        target_id = await get_target(msg, parts[0])
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

    if target_name.lower() in ('сбросить', 'очистить', 'reset'):
        storage.get_user(msg.chat.id, target_id)['custom_tag'] = ''
        storage.invalidate_user_cache(msg.chat.id, target_id)
        mention_cache.invalidate(f"mention_{msg.chat.id}_{target_id}")
        storage.mark_dirty()
        await storage.save()

        try:
            await bot.set_chat_administrator_custom_title(msg.chat.id, target_id, "")
        except Exception:
            pass

        tag_error = None
        try:
            await bot.set_chat_member_tag(msg.chat.id, target_id, "")
        except Exception as e:
            tag_error = str(e)
            logger.warning(f"set_chat_member_tag (сброс) не сработал для {target_id} в {msg.chat.id}: {e}")

        if tag_error:
            return await msg.answer(f"✅ Тег сброшен.\n⚠️ Видимый тег в Telegram не убран: <code>{html.escape(tag_error)}</code>")
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

    try:
        await bot.set_chat_administrator_custom_title(msg.chat.id, target_id, text)
    except Exception:
        pass

    tag_error = None
    try:
        await bot.set_chat_member_tag(msg.chat.id, target_id, text[:16])
    except Exception as e:
        tag_error = str(e)
        logger.warning(f"set_chat_member_tag не сработал для {target_id} в {msg.chat.id}: {e}")

    if target_id == msg.from_user.id:
        result_msg = f"✅ Погоняло изменено!\n🏷️ <b>{text}</b>"
    else:
        result_msg = f"✅ Погоняло для {mention(msg.chat.id, target_id)} изменено на <b>{text}</b>"

    if tag_error:
        result_msg += f"\n⚠️ Видимый тег в Telegram не установлен: <code>{html.escape(tag_error)}</code>"

    return await msg.answer(result_msg)


async def cmd_nick(msg: Message, cmd_name: str = 'ник'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 0):
        return
    save_activity(msg.chat.id, msg.from_user.id, 'commands')

    text = msg.text.strip()

    # Очищаем от префиксов
    for prefix in ['!']:
        if text.startswith(prefix):
            text = text[1:].strip()
            break

    # Убираем слово "ник"
    if text.lower().startswith('ник'):
        args = text[3:].strip()
    else:
        args = text

    if not args:
        u = storage.get_user(msg.chat.id, msg.from_user.id)
        custom = u.get('custom_name', '')
        return await msg.answer(
            f"👤 <b>Ваше отображаемое имя:</b> {get_display_name(msg.chat.id, msg.from_user.id)}\n"
            f"{'📝 Кастомное: ' + custom if custom else '💡 У вас нет кастомного ника'}\n\n"
            f"<code>ник Новое Имя</code> — установить ник\n"
            f"<code>ник @user</code> — посмотреть чужой ник\n"
            f"<code>ник сбросить</code> — убрать кастомный ник"
        )

    if args.lower() == 'сбросить':
        storage.get_user(msg.chat.id, msg.from_user.id)['custom_name'] = ''
        storage.invalidate_user_cache(msg.chat.id, msg.from_user.id)  # ← Это есть
        mention_cache.invalidate(f"mention_{msg.from_user.id}")  # ← ДОБАВЬТЕ ЭТО
        storage.mark_dirty()
        await storage.save()
        return await msg.answer("✅ Кастомный ник сброшен.")

    # Проверяем, смотрим ли мы чужой ник
    if args.startswith('@'):
        tid = await get_target(msg, args)
        if tid:
            u = storage.get_user(msg.chat.id, tid)
            return await msg.answer(
                f"👤 <b>{mention(msg.chat.id, tid)}</b>\n📝 Ник: {u.get('custom_name') or 'не установлен'}",
                disable_web_page_preview=True)

    # Устанавливаем новый ник
    new_name = args.strip()
    if len(new_name) > 64:
        return await msg.answer("❌ Слишком длинное имя (макс. 64 символа)")

    old = get_display_name(msg.chat.id, msg.from_user.id)
    storage.get_user(msg.chat.id, msg.from_user.id)['custom_name'] = new_name

    # Сбрасываем ВСЕ кеши
    storage.invalidate_user_cache(msg.chat.id, msg.from_user.id)
    mention_cache.invalidate(f"mention_{msg.from_user.id}")  # ← ДОБАВЬТЕ ЭТУ СТРОКУ

    storage.mark_dirty()
    await storage.save()

    return await msg.answer(f"✅ Ник изменён!\n📝 {old} → <b>{new_name}</b>")


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
    await msg.answer(f"🛡️ <b>Анти-спам система</b>\n\nСтатус: {status}")


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
    'cmd_unwarn': 2,
    'cmd_del': 1,
    'cmd_pin': 2,
    'cmd_purge': 2,
    'cmd_close_topic': 2, 'cmd_open_topic': 2,
    'cmd_add_iso': 3, 'cmd_rem_iso': 3,
    'cmd_give_award': 4, 'cmd_rem_award': 4,
    'cmd_add_phrase': 1, 'cmd_del_phrase': 1,
    'cmd_welcome': 2, 'cmd_farewell': 2,
    'cmd_add_rule': 4, 'cmd_clear_rules': 4,
    'cmd_promote': 5, 'cmd_demote': 5,
    'cmd_anti_moderation': 5, 'cmd_anti_spam': 5,
    'cmd_dk_set': 5, 'cmd_dk_enable': 5, 'cmd_dk_disable': 5,
    'cmd_ldk_add': 5, 'cmd_ldk_rem': 5, 'cmd_dk_menu': 5,
    'cmd_ping': 5, 'cmd_backup': 5, 'cmd_restore': 5,
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
        (['.ид'], None),
        (['топ'], None),
        (['статистика чата', 'статистика'], None),
        (['опрос'], None),
        (['погода', 'п'], None),
        (['шутка'], None),
        (['валера'], None),
    ]),
    'moderation': ("🛡️ Модерация", [
        (['мут', 'размут', '-мут'], None),
        (['бан', 'разбан', '-бан'], None),
        (['пред', 'варн', 'warn'], None),
        (['преды', 'варны', 'warns'], None),
        (['снятьпред', 'снятьварн', '-пред', '-варн', 'unwarn'], None),
        (['-смс'], None),
        (['.пин'], None),
        (['очистить'], None),
        (['повысить'], None),
        (['понизить'], None),
        (['репорт'], None),
        (['ник'], None),
    ]),
    'topics': ("📂 Топики и изоляция", [
        (['закрыть топик', 'открыть топик'], None),
        (['топики'], None),
        (['+изоляция', '-изоляция'], None),
        (['изоляция'], None),
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
    ]),
}


def match_dk_command(tokens: List[str]) -> tuple:
    """Ищет команду ДК в начале списка токенов: команды могут состоять
    из 1 или 2 слов ('дк', 'закрыть топик' и т.д.). Возвращает
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
    storage.data['command_access'].setdefault(str(msg.chat.id), {})[command] = level
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
    storage.data['command_access'].setdefault(str(msg.chat.id), {})[command] = 0
    storage.mark_dirty();
    await storage.save()
    await msg.answer(f"✅ Команда '{command}' включена (доступна всем)")


async def cmd_dk_disable(msg: Message, cmd_name: str = '-дк'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    command = ' '.join(msg.text.split()[1:]).lower().strip()
    if command not in COMMANDS:
        return await msg.answer(f"❌ Неизвестная команда '{command}'")
    storage.data['command_access'].setdefault(str(msg.chat.id), {})[command] = 9
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
    access_list = storage.data['personal_access'].setdefault(str(msg.chat.id), {}).setdefault(command, [])
    if tid in access_list:
        return await msg.answer(f"⚠️ У {mention(msg.chat.id, tid)} уже есть личный доступ к команде '{command}'",
                                 disable_web_page_preview=True)
    access_list.append(tid)
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
    acc = storage.data['personal_access'].get(str(msg.chat.id), {}).get(command, [])
    if tid in acc:
        acc.remove(tid)
        storage.mark_dirty();
        await storage.save()
        await msg.answer(f"✅ Доступ к команде '{command}' отозван у {mention(msg.chat.id, tid)}",
                         disable_web_page_preview=True)
    else:
        await msg.answer(f"❌ У {mention(msg.chat.id, tid)} нет личного доступа к команде '{command}'",
                         disable_web_page_preview=True)


# ==================== Админ-команды ====================

async def cmd_ping_check(msg: Message):
    """Простой пинг бота без обращения к базе и админским правам."""
    start = time.perf_counter()
    await msg.answer(f"🏓 Пинг: {0} мс", disable_web_page_preview=True)
    latency = round((time.perf_counter() - start) * 1000, 1)
    await msg.edit_text(f"🏓 Пинг: {latency} мс", disable_web_page_preview=True)


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
    backup = {'ts': time.time(), 'data': json.loads(json.dumps(storage.data))}
    storage.data.setdefault('backups', []).append(backup)
    storage.data['backups'] = storage.data['backups'][-10:]
    filename = f"{BACKUP_DIR}/backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(filename, 'w', encoding='utf-8') as f:
        json.dump(backup, f, ensure_ascii=False, indent=2)
    await storage.save()
    await msg.answer(f"✅ Бэкап: {filename}")


async def cmd_restore(msg: Message, cmd_name: str = 'восстановить'):
    if not check_access(msg.from_user.id, msg.chat.id, cmd_name, 5):
        return
    if not storage.data.get('backups'):
        return await msg.answer("❌ Нет бэкапов")
    storage.data = storage.data['backups'][-1]['data']
    await storage.save()
    await msg.answer("✅ Восстановлено")


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
        await msg.answer(f"❌ Ошибка: {e}")


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

    # Список слов для выдачи репутации (БЕЗ обязательного !)
    rep_words = [
        '+', 'плюс', 'спасибо', 'жиза', 'красава', 'респект',
        'уважение', 'лайк', 'like', 'топ', 'красавчик',
        'молодец', 'умница', 'based', 'base', 'огонь',
        'респектую', '👍', '🔥', '💯', '✅'
    ]

    # Проверяем точное совпадение ИЛИ начинается с +
    if text.lower() in rep_words or (text.startswith('+') and len(text) <= 3):
        logger.debug(f"Репутация: {msg.from_user.id} -> {msg.reply_to_message.from_user.id}, текст='{text}'")
        await give_reputation(msg)
        return


async def give_reputation(msg: Message):
    """Выдача репутации"""
    try:
        giver_id = msg.from_user.id
        receiver_id = msg.reply_to_message.from_user.id
        
        logger.info(f"Выдача репутации: {giver_id} -> {receiver_id}")

        giver = storage.get_user(msg.chat.id, giver_id, use_cache=False)
        receiver = storage.get_user(msg.chat.id, receiver_id, use_cache=False)

        now = time.time()
        today = datetime.now().strftime('%Y-%m-%d')

        # Проверка кулдауна
        last_rep = giver.get('last_rep_time', 0)
        if now - last_rep < REPUTATION_COOLDOWN:
            remaining = int(REPUTATION_COOLDOWN - (now - last_rep))
            minutes = remaining // 60
            seconds = remaining % 60
            msg_text = f"⏳ Кулдаун! Подождите {minutes}м {seconds}с" if minutes > 0 else f"⏳ Кулдаун! Подождите {seconds}с"
            logger.debug(f"Репутация: кулдаун для {giver_id}")
            await msg.reply(msg_text)
            return

        # Проверка дневного лимита
        rep_today = giver.get('rep_given_today', {})
        today_count = rep_today.get(today, 0)
        if today_count >= REPUTATION_DAILY_LIMIT:
            logger.debug(f"Репутация: дневной лимит для {giver_id}")
            await msg.reply(f"❌ Дневной лимит исчерпан ({today_count}/{REPUTATION_DAILY_LIMIT})")
            return

        # Проверка что сегодня ещё не давали этому пользователю
        targets_today = rep_today.get('targets', {})
        if str(receiver_id) in targets_today:
            logger.debug(f"Репутация: {giver_id} уже давал сегодня {receiver_id}")
            # Уже давали сегодня - молча игнорируем
            return

        # ВЫДАЁМ РЕПУТАЦИЮ
        receiver['reputation'] = receiver.get('reputation', 0) + 1
        logger.info(f"✅ Репутация выдана: {giver_id} -> {receiver_id}, всего: {receiver['reputation']}")

        # Обновляем данные дающего
        giver['last_rep_time'] = now

        if today not in rep_today:
            rep_today[today] = 0
        rep_today[today] = today_count + 1

        if 'targets' not in rep_today:
            rep_today['targets'] = {}
        rep_today['targets'][str(receiver_id)] = True

        giver['rep_given_today'] = rep_today
        giver['rep_given_total'] = giver.get('rep_given_total', 0) + 1

        # Сохраняем активность
        save_activity(msg.chat.id, receiver_id, 'reputation')

        # Очищаем кэш
        storage.invalidate_user_cache(msg.chat.id, giver_id)
        storage.invalidate_user_cache(msg.chat.id, receiver_id)
        storage.mark_dirty()
        await storage.save()

        # Отправляем подтверждение
        total_rep = receiver['reputation']
        await msg.reply(
            f"⭐ +1 {mention(msg.chat.id, receiver_id)}\n"
            f"📊 Репутация: {total_rep}",
            disable_web_page_preview=True
        )

    except Exception as e:
        logger.error(f"Ошибка выдачи репутации: {type(e).__name__}: {e}", exc_info=True)
        try:
            await msg.reply(f"❌ Ошибка репутации: {str(e)[:80]}")
        except:
            pass


# ==================== Автомодерация ====================

async def auto_mod(msg: Message):
    if msg.from_user.is_bot:
        return

    uid = msg.from_user.id
    chat_id = msg.chat.id

    # === ПРОВЕРКА ЗАКРЫТЫХ ТОПИКОВ (ОБНОВЛЕНО) ===
    topic_id = msg.message_thread_id
    if topic_id is None or topic_id == 1:
        topic_id = 0

    closed_topics = storage.data.get('closed_topics', {}).get(str(chat_id), {})
    closed_topic = closed_topics.get(str(topic_id))

    if closed_topic:
        required_rank = closed_topic.get('required_rank', 0)
        allowed_users = closed_topic.get('allowed_users', [])
        user_rank = storage.get_user(msg.chat.id, uid).get('rank', 0)

        # НОВАЯ ПРОВЕРКА: ранг ИЛИ в списке исключений
        has_access = (user_rank >= required_rank) or (uid in allowed_users)

        if not has_access:
            try:
                await msg.delete()

                u = storage.get_user(msg.chat.id, uid)
                now = time.time()
                if now - u.get('last_violation_time', 0) > 300:
                    u['violations_count'] = 0
                u['violations_count'] = u.get('violations_count', 0) + 1
                u['last_violation_time'] = now

                location = "основном чате" if topic_id == 0 else f"топике {topic_id}"

                warning_msg = f"🚫 <b>Топик закрыт!</b>\n\n📌 Вы попытались написать в {location}.\n"

                if required_rank > 0:
                    warning_msg += f"🔐 Требуется ранг: {required_rank}+\n"
                if allowed_users:
                    users_list = ', '.join([mention(msg.chat.id, uid) for uid in allowed_users[:3]])
                    if len(allowed_users) > 3:
                        users_list += f" +{len(allowed_users) - 3}"
                    warning_msg += f"👤 Исключения: {users_list}\n"

                warning_msg += f"\n⚠️ Нарушение #{u['violations_count']}/3"

                sent_msg = await msg.answer(warning_msg, disable_web_page_preview=True)

                if u['violations_count'] >= 3:
                    until = datetime.now() + timedelta(minutes=10)
                    await bot.restrict_chat_member(chat_id, uid,
                                                   ChatPermissions(can_send_messages=False), until_date=int(until.timestamp()))

                    mutes = storage.get_chat(chat_id, 'mutes')
                    if not isinstance(mutes, list):
                        mutes = []
                        storage.data['mutes'][str(chat_id)] = mutes
                    mutes.append({
                        'user_id': uid,
                        'expire_time': until.timestamp(),
                        'muted_by': 'auto',
                        'reason': f'3 нарушения в закрытом топике'
                    })

                    await sent_msg.edit_text(
                        f"🔇 <b>Автоматический мут!</b>\n\n"
                        f"⚠️ Вы получили 3 нарушения за попытку писать в закрытом топике.\n"
                        f"⏱️ Вы заглушены на 10 минут.",
                        disable_web_page_preview=True
                    )
                    u['violations_count'] = 0
                    await asyncio.sleep(5)
                    try:
                        await sent_msg.delete()
                    except:
                        pass
                else:
                    await asyncio.sleep(3)
                    try:
                        await sent_msg.delete()
                    except:
                        pass

                storage.mark_dirty()
                await storage.save()

            except Exception as e:
                logger.error(f"Ошибка авто-модерации топика: {e}")
            return

    # === ПРОВЕРКА ИЗОЛЯЦИИ (оставляем как есть) ===
    iso = storage.get_user(msg.chat.id, uid).get('isolation')
    if iso and iso.get('expire_time', 0) > time.time():
        try:
            await msg.delete()

            until_time = datetime.fromtimestamp(iso['expire_time']).strftime('%H:%M:%S')
            iso_msg = (
                f"🔒 <b>Вы в изоляции!</b>\n\n"
                f"📝 Причина: {iso.get('reason', 'Не указана')}\n"
                f"⏱️ Действует до: {until_time}\n\n"
                f"⚠️ Ваше сообщение удалено."
            )
            sent_msg = await msg.answer(iso_msg, disable_web_page_preview=True)
            await asyncio.sleep(3)
            try:
                await sent_msg.delete()
            except:
                pass

            # Наказание за нарушение изоляции
            mutes = storage.get_chat(msg.chat.id, 'mutes')
            if not isinstance(mutes, list):
                mutes = []
                storage.data['mutes'][str(chat_id)] = mutes

            cnt = len([m for m in mutes if m.get('user_id') == uid])
            mute_durations = [30, 60, 120, 240, 480, 1440]
            duration = mute_durations[min(cnt, 5)]

            until = datetime.now() + timedelta(minutes=duration)
            await bot.restrict_chat_member(
                chat_id, uid,
                ChatPermissions(can_send_messages=False),
                until_date=int(until.timestamp())
            )

            mutes.append({
                'user_id': uid,
                'expire_time': until.timestamp(),
                'muted_by': 'auto',
                'reason': f'Нарушение изоляции: {iso.get("reason", "Неизвестно")}'
            })

            storage.mark_dirty()
            await storage.save()

        except Exception as e:
            logger.error(f"Ошибка авто-модерации изоляции: {e}")
        return

    # === ФРАЗЫ ОТКЛЮЧЕНЫ ===
    # Автоответы по триггерам больше не обрабатываются.
    # Команды управления фразами остаются, но бот не реагирует на них автоматически.


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
                expired = [m for m in mutes if now >= m.get('expire_time', 0)]
                for m in expired:
                    try:
                        await bot.restrict_chat_member(int(cid), m['user_id'], ChatPermissions(
                            can_send_messages=True,
                            can_send_media_messages=True,
                            can_send_other_messages=True,
                            can_add_web_page_previews=True
                        ))
                        # Убираем отсюда увеличение счётчика, так как он уже увеличен при выдаче мута
                    except Exception as e:
                        logger.error(f"Ошибка размута: {e}")
                    mutes.remove(m)
                if expired:
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


# ==================== Запуск ====================

async def main():
    logger.info("🐻 Обкуренный Валера v3.0 запускается...")
    signal.signal(signal.SIGTERM, signal_handler)
    signal.signal(signal.SIGINT, signal_handler)
    asyncio.create_task(check_mutes())
    asyncio.create_task(auto_save_task())
    await dp.start_polling(bot)


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        storage.save_sync()
    except Exception as e:
        print(f"❌ Ошибка: {e}")
        storage.save_sync()
