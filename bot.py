#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import asyncio
import contextlib


import dataclasses
import datetime as dt
import ipaddress
import json
import os
import hashlib
import base64

import re
import shutil
import signal
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Optional, Set, Tuple
from jinja2 import Environment, FileSystemLoader, select_autoescape

from aiogram import Bot, Dispatcher, F
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import StatesGroup, State
from aiogram.types import (
    Message,
    CallbackQuery,
    ReplyKeyboardMarkup,
    KeyboardButton,
    InlineKeyboardMarkup,
    InlineKeyboardButton,
    FSInputFile,
)

BOT_TOKEN = os.getenv("BOT_TOKEN")
ADMINS = set()


@dataclasses.dataclass(frozen=True)
class DomainGroup:
    key: str
    title: str
    path: Path
    acl_name: str
    description: str = ""
    builtin: bool = False

    def to_payload(self) -> Dict[str, object]:
        return {
            "key": self.key,
            "title": self.title,
            "path": str(self.path),
            "acl_name": self.acl_name,
            "description": self.description,
            "builtin": self.builtin,
        }

    @staticmethod
    def from_payload(data: Dict[str, object]) -> "DomainGroup":
        key = str(data.get("key", "")).strip()
        title = str(data.get("title", key)).strip() or key
        path_value = str(data.get("path", f"{key}"))
        acl_name = str(data.get("acl_name", key.upper())).strip() or key.upper()
        description = str(data.get("description", ""))
        builtin = bool(data.get("builtin", False))
        return DomainGroup(key, title, Path(path_value), acl_name, description, builtin)

BUILTIN_GROUP_DEFINITIONS = [
    DomainGroup("deny_betting", "Betting sites", Path("deny_betting"), "DENY_BETTING", "Betting block", True),
    DomainGroup("deny_whatsapp", "WhatsApp", Path("deny_whatsapp"), "DENY_WHATSAPP", "WhatsApp category", True),
    DomainGroup("deny_social", "Social networks", Path("deny_social"), "DENY_SOCIAL", "Social networks and messengers", True),
    DomainGroup("deny_common", "Common restrictions", Path("deny_common"), "DENY_COMMON", "Basic corporate list", True),
]

DENY_GROUP_DEFINITIONS = list(BUILTIN_GROUP_DEFINITIONS)
DENY_GROUPS = {g.key: g for g in DENY_GROUP_DEFINITIONS}
DENY_GROUP_ORDER = [g.key for g in DENY_GROUP_DEFINITIONS]
DEFAULT_DENY_GROUP = "deny_common"

POLICY_ALLOW_ALL_EXCEPT = "allow_all_except"
POLICY_DENY_ALL_EXCEPT = "deny_all_except"
POLICY_CHOICES = {
    POLICY_ALLOW_ALL_EXCEPT: "Разрешено всё, кроме выбранных групп",
    POLICY_DENY_ALL_EXCEPT: "Запрещено всё, кроме выбранных групп",
}
DEFAULT_POLICY = POLICY_ALLOW_ALL_EXCEPT

DENY_FILE = DENY_GROUPS[DEFAULT_DENY_GROUP].path
WHITE_FILE = Path("whitelist_ip")
SQUID_CONF = Path("squid.conf")
ACCESS_LOG = Path("access.log")
CACHE_LOG = Path("cache.log")

SQUID_BIN = shutil.which("squid") or "squid"
SYSTEMCTL_BIN = shutil.which("systemctl") or "systemctl"

BLOCK_ERROR_TEMPLATE = Path("ERR_ACCESS_DENIED")

PERIODIC_REPORT_INTERVAL = 3600
TAIL_STATE_DIR = Path("state")
TAIL_STATE_DIR.mkdir(parents=True, exist_ok=True)
TAIL_STATE_FILE = TAIL_STATE_DIR / "access.log.offset"
CONFIG_FILE = TAIL_STATE_DIR / "bot_config.json"

TEMPLATES_DIR = Path("templates")
TEMPLATES_DIR.mkdir(parents=True, exist_ok=True)
REPORTS_DIR = Path("reports")
REPORTS_DIR.mkdir(parents=True, exist_ok=True)

GROUPS_FILE = TAIL_STATE_DIR / "groups.json"


def set_group_definitions(definitions: Iterable[DomainGroup]) -> None:
    global DENY_GROUP_DEFINITIONS, DENY_GROUPS, DENY_GROUP_ORDER
    DENY_GROUP_DEFINITIONS = list(definitions)
    DENY_GROUPS = {g.key: g for g in DENY_GROUP_DEFINITIONS}
    DENY_GROUP_ORDER = [g.key for g in DENY_GROUP_DEFINITIONS]


def load_group_definitions() -> List[DomainGroup]:
    if GROUPS_FILE.exists():
        try:
            raw = json.loads(GROUPS_FILE.read_text(encoding='utf-8'))
        except Exception:
            raw = None
        if isinstance(raw, list):
            items: List[DomainGroup] = []
            for entry in raw:
                if isinstance(entry, dict):
                    try:
                        items.append(DomainGroup.from_payload(entry))
                    except Exception:
                        continue
            builtin_keys = {g.key for g in BUILTIN_GROUP_DEFINITIONS}
            seen = set()
            result: List[DomainGroup] = []
            for group in items:
                if not group.key or group.key in seen:
                    continue
                seen.add(group.key)
                if group.key in builtin_keys:
                    builtin = next(g for g in BUILTIN_GROUP_DEFINITIONS if g.key == group.key)
                    group = DomainGroup(
                        builtin.key,
                        group.title or builtin.title,
                        group.path or builtin.path,
                        group.acl_name or builtin.acl_name,
                        group.description or builtin.description,
                        True,
                    )
                result.append(group)
            for builtin in BUILTIN_GROUP_DEFINITIONS:
                if builtin.key not in {g.key for g in result}:
                    result.append(builtin)
            return result
    return list(BUILTIN_GROUP_DEFINITIONS)


def save_group_definitions(definitions: Iterable[DomainGroup]) -> None:
    payload = [group.to_payload() for group in definitions]
    GROUPS_FILE.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding='utf-8')


set_group_definitions(load_group_definitions())
if not GROUPS_FILE.exists():
    save_group_definitions(DENY_GROUP_DEFINITIONS)


DEFAULT_DEPARTMENT_SOURCE_DATA: Dict[str, Tuple[str, ...]] = {}

DEPARTMENT_SOURCE_DATA: Dict[str, Tuple[str, ...]] = {}

DEPARTMENT_SRC_DIR = Path("departments")
DEPARTMENT_SRC_DIR.mkdir(parents=True, exist_ok=True)

def _make_department_slug(name: str) -> str:
    base = re.sub(r"[^a-z0-9]+", "_", name.lower()).strip("_")
    if not base:
        base = "dept"
    suffix = hashlib.sha1(name.encode("utf-8")).hexdigest()[:8]
    return f"{base}_{suffix}"

DEPARTMENT_SLUGS: Dict[str, str] = {}
SLUG_TO_DEPARTMENT: Dict[str, str] = {}
IP_TO_DEPARTMENTS: Dict[str, List[str]] = {}
ALL_DEPARTMENT_NAMES: Tuple[str, ...] = tuple()

DEPARTMENTS_FILE = TAIL_STATE_DIR / "departments.json"


def _normalize_department_sources(raw: Dict[str, Iterable[str]]) -> Dict[str, Tuple[str, ...]]:
    normalized: Dict[str, Tuple[str, ...]] = {}
    for name, values in raw.items():
        if not isinstance(name, str):
            continue
        clean_name = name.strip()
        if not clean_name:
            continue
        collected: List[str] = []
        if isinstance(values, (list, tuple, set)):
            iterator = values
        else:
            iterator = [values]
        for value in iterator:
            if isinstance(value, str):
                v = value.strip()
            else:
                v = str(value).strip()
            if v:
                collected.append(v)
        normalized[clean_name] = tuple(dict.fromkeys(collected))
    return normalized


def set_department_source_data(data: Dict[str, Iterable[str]]) -> Dict[str, Tuple[str, ...]]:
    global DEPARTMENT_SOURCE_DATA, DEPARTMENT_SLUGS, SLUG_TO_DEPARTMENT, IP_TO_DEPARTMENTS, ALL_DEPARTMENT_NAMES
    normalized = _normalize_department_sources(data)
    DEPARTMENT_SOURCE_DATA = normalized
    DEPARTMENT_SLUGS = {name: _make_department_slug(name) for name in normalized}
    SLUG_TO_DEPARTMENT = {slug: name for name, slug in DEPARTMENT_SLUGS.items()}
    IP_TO_DEPARTMENTS = {}
    for dept_name, ips in normalized.items():
        for ip in ips:
            IP_TO_DEPARTMENTS.setdefault(ip, []).append(dept_name)
    ALL_DEPARTMENT_NAMES = tuple(normalized.keys())
    return normalized


def load_department_source_data() -> Dict[str, Tuple[str, ...]]:
    if DEPARTMENTS_FILE.exists():
        try:
            raw = json.loads(DEPARTMENTS_FILE.read_text(encoding='utf-8'))
        except Exception:
            raw = None
        if isinstance(raw, dict):
            mapped: Dict[str, Iterable[str]] = {}
            for name, values in raw.items():
                mapped[name] = values
            return _normalize_department_sources(mapped)
    return _normalize_department_sources(DEFAULT_DEPARTMENT_SOURCE_DATA)


def save_department_source_data(data: Dict[str, Tuple[str, ...]]) -> None:
    payload = {name: list(ips) for name, ips in data.items()}
    DEPARTMENTS_FILE.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding='utf-8')

set_department_source_data(load_department_source_data())



def add_department_ip(department: str, ip: str) -> Tuple[bool, str]:
    dept = department.strip()
    value = ip.strip()
    if not dept:
        return False, "Empty department name"
    if dept not in DEPARTMENT_SOURCE_DATA:
        return False, "Department not found"
    if not value:
        return False, "Empty IP"
    if not (is_ip_or_cidr(value) or re.match(r"^[0-9a-fA-F:.]+$", value)):
        return False, "Invalid IP format"
    current = list(DEPARTMENT_SOURCE_DATA.get(dept, ()))
    if value in current:
        return False, "IP already exists"
    updated = {name: list(ips) for name, ips in DEPARTMENT_SOURCE_DATA.items()}
    updated.setdefault(dept, []).append(value)
    normalized = set_department_source_data(updated)
    save_department_source_data(normalized)
    ensure_department_sources()
    return True, value


def remove_department_ip(department: str, ip: str) -> Tuple[bool, str]:
    dept = department.strip()
    value = ip.strip()
    if not dept or dept not in DEPARTMENT_SOURCE_DATA:
        return False, "Department not found"
    if not value:
        return False, "Empty IP"
    current = list(DEPARTMENT_SOURCE_DATA.get(dept, ()))
    if value not in current:
        return False, "IP not found"
    updated = {name: [x for x in ips if x != value] for name, ips in DEPARTMENT_SOURCE_DATA.items()}
    normalized = set_department_source_data(updated)
    save_department_source_data(normalized)
    ensure_department_sources()
    return True, value


MAX_LINES_PER_PAGE = 25
MAX_TEXT_CHARS = 3800

RE_DOMAIN = re.compile(r"^(?=.{1,253}$)(?!-)([a-z0-9-]{1,63}\.)+[a-z]{2,}$", re.IGNORECASE)
RE_PROTOCOL_HOST = re.compile(r"^[a-zA-Z]+://([^/:]+)")


def is_admin(uid: int) -> bool:
    return uid in ADMINS

def now_str() -> str:
    return dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def normalize_domain(text: str) -> str:
    t = text.strip().lower()
    t = t.removeprefix("https://").removeprefix("http://")
    t = t.strip("/")
    return t

def is_domain_like(text: str) -> bool:
    t = normalize_domain(text)
    return bool(RE_DOMAIN.match(t)) or "." in t

def is_ip_or_cidr(text: str) -> bool:
    try:
        ipaddress.ip_network(text.strip(), strict=False)
        return True
    except ValueError:
        return False

def read_lines(path: Path) -> List[str]:
    if not path.exists():
        return []
    out = []
    with path.open("r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            s = line.strip()
            if s and not s.startswith("#"):
                out.append(s)
    return out

def atomic_write_lines(path: Path, lines: Iterable[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_fd, tmp_name = tempfile.mkstemp(prefix=path.name + ".", dir=str(path.parent))
    try:
        with os.fdopen(tmp_fd, "w", encoding="utf-8", newline="\n") as f:
            for line in lines:
                line = line.rstrip("\r\n")
                if line:
                    f.write(line + "\n")
        os.replace(tmp_name, path)
    finally:
        with contextlib.suppress(FileNotFoundError):
            os.unlink(tmp_name)

def unique_sorted(seq: Iterable[str]) -> List[str]:
    return sorted(set(s.strip() for s in seq if s.strip()))

def sanitize_groups(values: Iterable[str]) -> Set[str]:
    return {str(v) for v in values if str(v) in DENY_GROUPS}

@dataclasses.dataclass
class BotConfig:
    policy: str
    deny_groups: Set[str]
    allow_groups: Set[str]

    def normalized(self) -> "BotConfig":
        policy = self.policy if self.policy in POLICY_CHOICES else DEFAULT_POLICY
        deny_groups = sanitize_groups(self.deny_groups)
        if not deny_groups:
            deny_groups = set(DENY_GROUP_ORDER)
        allow_groups = sanitize_groups(self.allow_groups)
        allow_groups -= deny_groups
        if policy != POLICY_DENY_ALL_EXCEPT:
            allow_groups = set()
        return BotConfig(policy, deny_groups, allow_groups)

    def as_dict(self, *, normalized: bool = True) -> Dict[str, object]:
        cfg = self.normalized() if normalized else self
        return {
            "policy": cfg.policy,
            "deny_groups": sorted(cfg.deny_groups),
            "allow_groups": sorted(cfg.allow_groups),
        }

def default_bot_config() -> BotConfig:
    return BotConfig(DEFAULT_POLICY, set(DENY_GROUP_ORDER), set())

APP_CONFIG_VERSION = 2


@dataclasses.dataclass
class ProfileOverride:
    policy: Optional[str] = None
    deny_groups: Optional[Set[str]] = None
    allow_groups: Optional[Set[str]] = None

    def clone(self) -> "ProfileOverride":
        return ProfileOverride(
            policy=self.policy,
            deny_groups=set(self.deny_groups) if self.deny_groups is not None else None,
            allow_groups=set(self.allow_groups) if self.allow_groups is not None else None,
        )

    def normalized(self) -> "ProfileOverride":
        policy = self.policy if self.policy in POLICY_CHOICES else None

        def _norm(values: Optional[Iterable[str]]) -> Optional[Set[str]]:
            if values is None:
                return None
            normalized = sanitize_groups(values)
            return set(normalized)

        deny = _norm(self.deny_groups)
        allow = _norm(self.allow_groups)
        if policy != POLICY_DENY_ALL_EXCEPT:
            allow = None
        return ProfileOverride(policy, deny, allow)

    def is_empty(self) -> bool:
        return self.policy is None and self.deny_groups is None and self.allow_groups is None

    def to_payload(self) -> Dict[str, object]:
        payload: Dict[str, object] = {}
        if self.policy is not None:
            payload["policy"] = self.policy
        if self.deny_groups is not None:
            payload["deny_groups"] = sorted(self.deny_groups)
        if self.allow_groups is not None:
            payload["allow_groups"] = sorted(self.allow_groups)
        return payload

    @staticmethod
    def from_payload(data: Optional[Dict[str, object]]) -> "ProfileOverride":
        if not isinstance(data, dict):
            return ProfileOverride()
        policy = data.get("policy")
        deny = data.get("deny_groups")
        allow = data.get("allow_groups")

        def _to_set(value: Optional[Iterable[str]]) -> Optional[Set[str]]:
            if value is None:
                return None
            return {str(v) for v in value}

        return ProfileOverride(
            policy=str(policy) if isinstance(policy, str) else None,
            deny_groups=_to_set(deny),
            allow_groups=_to_set(allow),
        ).normalized()


@dataclasses.dataclass
class AppConfig:
    global_profile: BotConfig
    departments: Dict[str, ProfileOverride]
    ip_overrides: Dict[str, ProfileOverride]

    def normalized(self) -> "AppConfig":
        global_profile = self.global_profile.normalized()
        departments: Dict[str, ProfileOverride] = {}
        for name, override in self.departments.items():
            normalized = override.normalized()
            if not normalized.is_empty():
                departments[name] = normalized
        ip_overrides: Dict[str, ProfileOverride] = {}
        for ip, override in self.ip_overrides.items():
            if not is_ip_or_cidr(ip):
                continue
            normalized = override.normalized()
            if not normalized.is_empty():
                ip_overrides[ip] = normalized
        return AppConfig(global_profile, departments, ip_overrides)


def default_app_config() -> AppConfig:
    return AppConfig(default_bot_config(), {}, {})


def app_config_to_payload(cfg: AppConfig) -> Dict[str, object]:
    payload: Dict[str, object] = {
        "version": APP_CONFIG_VERSION,
        "global": cfg.global_profile.as_dict(),
    }
    departments_payload: Dict[str, object] = {}
    for name, override in cfg.departments.items():
        data = override.to_payload()
        if data:
            departments_payload[name] = data
    if departments_payload:
        payload["departments"] = departments_payload
    ip_payload: Dict[str, object] = {}
    for ip, override in cfg.ip_overrides.items():
        data = override.to_payload()
        if data and is_ip_or_cidr(ip):
            ip_payload[ip] = data
    if ip_payload:
        payload["ip_overrides"] = ip_payload
    return payload


def app_config_from_payload(payload: Dict[str, object]) -> AppConfig:
    global_payload = payload.get("global", payload)
    global_profile = BotConfig(
        policy=str(global_payload.get("policy", DEFAULT_POLICY)),
        deny_groups=set(global_payload.get("deny_groups", DENY_GROUP_ORDER)),
        allow_groups=set(global_payload.get("allow_groups", [])),
    )
    departments: Dict[str, ProfileOverride] = {}
    for name, data in payload.get("departments", {}).items():
        departments[name] = ProfileOverride.from_payload(data)
    ip_overrides: Dict[str, ProfileOverride] = {}
    for ip, data in payload.get("ip_overrides", {}).items():
        if not is_ip_or_cidr(ip):
            continue
        ip_overrides[ip] = ProfileOverride.from_payload(data)
    return AppConfig(global_profile, departments, ip_overrides).normalized()


def load_app_config() -> AppConfig:
    if CONFIG_FILE.exists():
        try:
            raw_text = CONFIG_FILE.read_text(encoding='utf-8')
            payload = json.loads(raw_text)
        except Exception:
            return default_app_config()
        if isinstance(payload, dict):
            if payload.get('version') == APP_CONFIG_VERSION:
                return app_config_from_payload(payload)
            try:
                payload_with_version = dict(payload)
                payload_with_version['version'] = APP_CONFIG_VERSION
                if 'global' not in payload_with_version:
                    payload_with_version['global'] = dict(payload)
                return app_config_from_payload(payload_with_version)
            except Exception:
                return default_app_config()
    return default_app_config()


def save_app_config(config: AppConfig) -> AppConfig:
    cfg = config.normalized()
    payload = app_config_to_payload(cfg)
    CONFIG_FILE.parent.mkdir(parents=True, exist_ok=True)
    CONFIG_FILE.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding='utf-8')
    return cfg


def update_app_config(mutator: Callable[[AppConfig], AppConfig]) -> AppConfig:
    current = load_app_config()
    updated = mutator(current).normalized()
    return save_app_config(updated)


def load_bot_config() -> BotConfig:
    return load_app_config().global_profile


def save_bot_config(config: BotConfig) -> BotConfig:
    normalized = config.normalized()
    def mut(app_cfg: AppConfig) -> AppConfig:
        return AppConfig(normalized, app_cfg.departments, app_cfg.ip_overrides)
    return update_app_config(mut).global_profile


def update_bot_config(mutator: Callable[[BotConfig], BotConfig]) -> BotConfig:
    def mut(app_cfg: AppConfig) -> AppConfig:
        updated_global = mutator(app_cfg.global_profile).normalized()
        return AppConfig(updated_global, app_cfg.departments, app_cfg.ip_overrides)
    return update_app_config(mut).global_profile


def department_slug(name: str) -> str:
    return DEPARTMENT_SLUGS.get(name, _make_department_slug(name))


def department_src_path(name: str) -> Path:
    return DEPARTMENT_SRC_DIR / f"{department_slug(name)}.src"


def ensure_department_sources() -> Dict[str, Path]:
    DEPARTMENT_SRC_DIR.mkdir(parents=True, exist_ok=True)
    paths: Dict[str, Path] = {}
    for name, ips in DEPARTMENT_SOURCE_DATA.items():
        path = department_src_path(name)
        if ips:
            atomic_write_lines(path, ips)
            paths[name] = path
        else:
            with contextlib.suppress(FileNotFoundError):
                path.unlink()
    return paths


def department_source_paths() -> List[Path]:
    return [department_src_path(name) for name in DEPARTMENT_SOURCE_DATA]


def iter_department_ips(name: str) -> Tuple[str, ...]:
    return DEPARTMENT_SOURCE_DATA.get(name, ())


def encode_token(value: str) -> str:
    raw = value.encode('utf-8')
    return base64.urlsafe_b64encode(raw).decode('ascii').rstrip('=')


def decode_token(token: str) -> str:
    padding = '=' * (-len(token) % 4)
    raw = base64.urlsafe_b64decode((token + padding).encode('ascii'))
    return raw.decode('utf-8')


def ip_token(ip: str) -> str:
    return encode_token(ip)


def ip_from_token(token: str) -> str:
    return decode_token(token)


def resolve_profile(app_cfg: Optional[AppConfig] = None, *, department: Optional[str] = None, ip: Optional[str] = None) -> BotConfig:
    cfg = (app_cfg or load_app_config()).normalized()
    profile = cfg.global_profile.normalized()
    policy = profile.policy
    deny = set(profile.deny_groups)
    allow = set(profile.allow_groups)

    def apply_override(override: Optional[ProfileOverride]):
        nonlocal policy, deny, allow
        if not override:
            return
        normalized = override.normalized()
        if normalized.policy is not None and normalized.policy in POLICY_CHOICES:
            policy = normalized.policy
            if policy != POLICY_DENY_ALL_EXCEPT:
                allow = set()
        if normalized.deny_groups is not None:
            deny = set(normalized.deny_groups)
        if normalized.allow_groups is not None:
            allow = set(normalized.allow_groups)

    if department:
        apply_override(cfg.departments.get(department))
    if ip:
        apply_override(cfg.ip_overrides.get(ip))
    return BotConfig(policy, deny, allow).normalized()


def resolve_department_profile(department: str, *, app_cfg: Optional[AppConfig] = None) -> BotConfig:
    return resolve_profile(app_cfg, department=department)


def resolve_ip_profile(ip: str, *, department: Optional[str] = None, app_cfg: Optional[AppConfig] = None) -> BotConfig:
    return resolve_profile(app_cfg, department=department, ip=ip)


def inherited_department_profile(app_cfg: AppConfig, department: str) -> BotConfig:
    return resolve_profile(AppConfig(app_cfg.global_profile, {k: v for k, v in app_cfg.departments.items() if k != department}, app_cfg.ip_overrides), department=department)


def inherited_ip_profile(app_cfg: AppConfig, department: Optional[str], ip: str) -> BotConfig:
    filtered = {k: v for k, v in app_cfg.ip_overrides.items() if k != ip}
    return resolve_profile(AppConfig(app_cfg.global_profile, app_cfg.departments, filtered), department=department)


def clear_department_override(department: str) -> AppConfig:
    def mut(cfg: AppConfig) -> AppConfig:
        departments = dict(cfg.departments)
        departments.pop(department, None)
        return AppConfig(cfg.global_profile, departments, cfg.ip_overrides).normalized()
    return update_app_config(mut)


def clear_ip_override(ip: str) -> AppConfig:
    def mut(cfg: AppConfig) -> AppConfig:
        overrides = dict(cfg.ip_overrides)
        overrides.pop(ip, None)
        return AppConfig(cfg.global_profile, cfg.departments, overrides).normalized()
    return update_app_config(mut)


def set_department_policy(department: str, new_policy: Optional[str]) -> AppConfig:
    def mut(cfg: AppConfig) -> AppConfig:
        departments = dict(cfg.departments)
        current = departments.get(department, ProfileOverride()).clone()
        base_policy = cfg.global_profile.normalized().policy
        if new_policy in POLICY_CHOICES:
            current.policy = new_policy
        else:
            current.policy = None
        if current.policy == base_policy:
            current.policy = None
        if current.policy != POLICY_DENY_ALL_EXCEPT:
            current.allow_groups = None
        current = current.normalized()
        if current.is_empty():
            departments.pop(department, None)
        else:
            departments[department] = current
        return AppConfig(cfg.global_profile, departments, cfg.ip_overrides).normalized()
    return update_app_config(mut)


def set_ip_policy(ip: str, new_policy: Optional[str]) -> AppConfig:
    def mut(cfg: AppConfig) -> AppConfig:
        overrides = dict(cfg.ip_overrides)
        current = overrides.get(ip, ProfileOverride()).clone()
        if new_policy in POLICY_CHOICES:
            current.policy = new_policy
        else:
            current.policy = None
        if current.policy != POLICY_DENY_ALL_EXCEPT:
            current.allow_groups = None
        current = current.normalized()
        if current.is_empty():
            overrides.pop(ip, None)
        else:
            overrides[ip] = current
        return AppConfig(cfg.global_profile, cfg.departments, overrides).normalized()
    return update_app_config(mut)


def set_department_group(department: str, group_key: str, enabled: bool) -> AppConfig:
    if group_key not in DENY_GROUPS:
        return load_app_config()

    def mut(cfg: AppConfig) -> AppConfig:
        base_cfg = AppConfig(cfg.global_profile, {k: v for k, v in cfg.departments.items() if k != department}, cfg.ip_overrides)
        base_profile = resolve_profile(base_cfg, department=department)
        effective_profile = resolve_profile(cfg, department=department)
        current_override = cfg.departments.get(department, ProfileOverride()).clone()

        if effective_profile.policy == POLICY_ALLOW_ALL_EXCEPT:
            new_deny = set(effective_profile.deny_groups)
            if enabled:
                new_deny.add(group_key)
            else:
                new_deny.discard(group_key)
            new_deny = sanitize_groups(new_deny)
            base_deny = set(base_profile.deny_groups)
            if new_deny == base_deny:
                current_override.deny_groups = None
            else:
                current_override.deny_groups = set(new_deny)
            current_override.allow_groups = None
        else:
            new_allow = set(effective_profile.allow_groups)
            if enabled:
                new_allow.add(group_key)
            else:
                new_allow.discard(group_key)
            new_allow = sanitize_groups(new_allow)
            base_allow = set(base_profile.allow_groups)
            if new_allow == base_allow:
                current_override.allow_groups = None
            else:
                current_override.allow_groups = set(new_allow)
            current_override.deny_groups = None

        current_override = current_override.normalized()
        departments = dict(cfg.departments)
        if current_override.is_empty():
            departments.pop(department, None)
        else:
            departments[department] = current_override
        return AppConfig(cfg.global_profile, departments, cfg.ip_overrides).normalized()

    return update_app_config(mut)


def set_ip_group(ip: str, department: Optional[str], group_key: str, enabled: bool) -> AppConfig:
    if group_key not in DENY_GROUPS:
        return load_app_config()

    def mut(cfg: AppConfig) -> AppConfig:
        base_cfg = AppConfig(cfg.global_profile, cfg.departments, {k: v for k, v in cfg.ip_overrides.items() if k != ip})
        base_profile = resolve_profile(base_cfg, department=department)
        effective_profile = resolve_profile(cfg, department=department, ip=ip)
        current_override = cfg.ip_overrides.get(ip, ProfileOverride()).clone()

        if effective_profile.policy == POLICY_ALLOW_ALL_EXCEPT:
            new_deny = set(effective_profile.deny_groups)
            if enabled:
                new_deny.add(group_key)
            else:
                new_deny.discard(group_key)
            new_deny = sanitize_groups(new_deny)
            base_deny = set(base_profile.deny_groups)
            if new_deny == base_deny:
                current_override.deny_groups = None
            else:
                current_override.deny_groups = set(new_deny)
            current_override.allow_groups = None
        else:
            new_allow = set(effective_profile.allow_groups)
            if enabled:
                new_allow.add(group_key)
            else:
                new_allow.discard(group_key)
            new_allow = sanitize_groups(new_allow)
            base_allow = set(base_profile.allow_groups)
            if new_allow == base_allow:
                current_override.allow_groups = None
            else:
                current_override.allow_groups = set(new_allow)
            current_override.deny_groups = None

        current_override = current_override.normalized()
        overrides = dict(cfg.ip_overrides)
        if current_override.is_empty():
            overrides.pop(ip, None)
        else:
            overrides[ip] = current_override
        return AppConfig(cfg.global_profile, cfg.departments, overrides).normalized()

    return update_app_config(mut)


def render_profile_rules(profile: BotConfig, target_acl: Optional[str] = None) -> List[str]:
    rules: List[str] = []
    if profile.policy == POLICY_ALLOW_ALL_EXCEPT:
        for key in DENY_GROUP_ORDER:
            if key in profile.deny_groups:
                group_acl = DENY_GROUPS[key].acl_name
                if target_acl:
                    rules.append(f"http_access deny {group_acl} {target_acl} !BOT_WHITELIST")
                else:
                    rules.append(f"http_access deny {group_acl} !BOT_WHITELIST")
    else:
        for key in DENY_GROUP_ORDER:
            if key in profile.allow_groups:
                group_acl = DENY_GROUPS[key].acl_name
                if target_acl:
                    rules.append(f"http_access allow {group_acl} {target_acl}")
                else:
                    rules.append(f"http_access allow {group_acl}")
        if target_acl:
            rules.append(f"http_access deny {target_acl}")
    return rules


def group_path(group_key: str) -> Path:
    return DENY_GROUPS[group_key].path

def read_group_items(group_key: str) -> List[str]:
    return unique_sorted(read_lines(group_path(group_key)))

def write_group_items(group_key: str, items: Iterable[str]) -> None:
    atomic_write_lines(group_path(group_key), items)

def ensure_group_files() -> None:
    for group in DENY_GROUPS.values():
        if not group.path.exists():
            atomic_write_lines(group.path, [])

def _generate_group_key(title: str) -> str:
    base = re.sub(r"[^a-z0-9]+", "_", title.lower()).strip("_")
    if not base:
        base = "group"
    if not base.startswith("deny_"):
        base = f"deny_{base}"
    candidate = base
    counter = 1
    existing = set(DENY_GROUPS.keys())
    while candidate in existing:
        candidate = f"{base}_{counter}"
        counter += 1
    return candidate


def _generate_acl_name(key: str) -> str:
    raw = re.sub(r"[^a-z0-9]+", "_", key.lower()).strip("_")
    return f"DENY_{raw.upper()}"[:48]


def create_domain_group(title: str, description: str = "") -> DomainGroup:
    clean_title = title.strip() or "Новая группа"
    key = _generate_group_key(clean_title)
    acl_name = _generate_acl_name(key)
    path = Path(f"/etc/squid/{key}")
    group = DomainGroup(key, clean_title, path, acl_name, description.strip(), False)
    definitions = list(DENY_GROUP_DEFINITIONS) + [group]
    set_group_definitions(definitions)
    save_group_definitions(definitions)
    ensure_group_files()
    save_app_config(load_app_config())
    return group


def delete_domain_group(group_key: str) -> Tuple[bool, str]:
    group = DENY_GROUPS.get(group_key)
    if not group:
        return False, "Группа не найдена"
    if group.builtin:
        return False, "Группу встроенного типа удалить нельзя"
    definitions = [g for g in DENY_GROUP_DEFINITIONS if g.key != group_key]
    set_group_definitions(definitions)
    save_group_definitions(definitions)
    try:
        if group.path.exists():
            backup = group.path.with_suffix(group.path.suffix + ".bak")
            shutil.move(str(group.path), str(backup))
    except Exception:
        pass
    ensure_group_files()
    save_app_config(load_app_config())
    return True, group.title


def group_counts() -> Dict[str, int]:
    return {key: len(read_group_items(key)) for key in DENY_GROUP_ORDER}

def total_denied_entries() -> int:
    return sum(group_counts().values())
def managed_group_paths() -> List[Path]:
    seen: Set[Path] = set()
    result: List[Path] = []
    for group in DENY_GROUP_DEFINITIONS:
        if group.path not in seen:
            result.append(group.path)
            seen.add(group.path)
    return result

def managed_files() -> List[Path]:
    paths = managed_group_paths()
    for path in department_source_paths():
        if path not in paths:
            paths.append(path)
    for extra in (WHITE_FILE, CONFIG_FILE):
        if extra not in paths:
            paths.append(extra)
    return paths

def backup_managed_files(suffix: str = ".bak") -> List[Path]:
    saved: List[Path] = []
    for path in managed_files():
        if path.exists():
            backup = path.with_name(path.name + suffix)
            shutil.copy2(path, backup)
            saved.append(backup)
    return saved

def restore_managed_files(suffix: str = ".bak") -> List[Path]:
    restored: List[Path] = []
    for path in managed_files():
        backup = path.with_name(path.name + suffix)
        if backup.exists():
            shutil.copy2(backup, path)
            restored.append(path)
    return restored


def group_enabled(config: BotConfig, group_key: str) -> bool:
    cfg = config.normalized()
    if cfg.policy == POLICY_ALLOW_ALL_EXCEPT:
        return group_key in cfg.deny_groups
    return group_key in cfg.allow_groups

def set_group_enabled(group_key: str, enabled: bool) -> BotConfig:
    def mutator(cfg: BotConfig) -> BotConfig:
        cfg = cfg.normalized()
        deny = set(cfg.deny_groups)
        allow = set(cfg.allow_groups)
        if cfg.policy == POLICY_ALLOW_ALL_EXCEPT:
            if enabled:
                deny.add(group_key)
            else:
                deny.discard(group_key)
        else:
            if enabled:
                allow.add(group_key)
            else:
                allow.discard(group_key)
        return BotConfig(cfg.policy, deny, allow)
    return update_bot_config(mutator)

def toggle_group_enabled(group_key: str) -> BotConfig:
    current = load_bot_config()
    return set_group_enabled(group_key, not group_enabled(current, group_key))

def set_policy(new_policy: str) -> BotConfig:
    if new_policy not in POLICY_CHOICES:
        raise ValueError(f"Недопустимая политика: {new_policy}")
    def mutator(cfg: BotConfig) -> BotConfig:
        cfg = cfg.normalized()
        deny = set(cfg.deny_groups)
        allow = set(cfg.allow_groups)
        if new_policy == POLICY_ALLOW_ALL_EXCEPT:
            allow = set()
        return BotConfig(new_policy, deny, allow)
    return update_bot_config(mutator)

def apply_config_and_reload(app_config: Optional[AppConfig] = None) -> Tuple[bool, List[str]]:
    """
    Обновляет squid.conf и перезагружает Squid.
    Возвращает (ok, messages) где:
        ok — успешно ли всё прошло,
        messages — список строк для отображения пользователю.
    """
    cfg = (app_config or load_app_config()).normalized()
    messages: List[str] = []

    changed, summary = patch_squid_conf(SQUID_CONF, cfg)
    if changed:
        messages.append("⚙️ Конфигурация обновлена")
    else:
        messages.append("ℹ️ Конфигурация не изменилась")

    ok, reload_msg = squid_reload()
    if ok:
        messages.append("🔄 Squid перезагружен")
    else:
        messages.append(f"❌ Ошибка перезагрузки: {reload_msg}")

    return ok, messages

def run_cmd(cmd: List[str], timeout: int = 20) -> Tuple[int, str, str]:
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout)
        return p.returncode, p.stdout.strip(), p.stderr.strip()
    except Exception as e:
        return 99, "", f"{e}"

def chunked_send_text() -> callable:
    async def _sender(bot: Bot, chat_id: int, text: str):
        if not text:
            text = "(пусто)"
        for i in range(0, len(text), MAX_TEXT_CHARS):
            await bot.send_message(chat_id, text[i:i+MAX_TEXT_CHARS])
    return _sender

send_text = chunked_send_text()

def extract_host_from_url(url: str) -> Optional[str]:
    m = RE_PROTOCOL_HOST.match(url)
    if m:
        return m.group(1).lower()
    return None


MANAGED_BEGIN = "# === squid-bot managed block start ==="
MANAGED_END = "# === squid-bot managed block end ==="
MANAGED_CONFIG_PREFIX = "# squid-bot:config "

@dataclasses.dataclass
class ConfCheck:
    has_managed_block: bool
    global_policy: Optional[str]
    global_deny_groups: Set[str]
    global_allow_groups: Set[str]
    warnings: List[str]
    metadata: Optional[Dict[str, object]] = None
def _group_order_and_acl(keys: Iterable[str]) -> List[Tuple[str, str]]:
    out: List[Tuple[str, str]] = []
    keys = set(keys)
    for k in DENY_GROUP_ORDER:
        if k in keys:
            out.append((k, DENY_GROUPS[k].acl_name))
    return out

def render_allow_exceptions(base_profile: BotConfig, eff_profile: BotConfig, target_acl: Optional[str]) -> List[str]:
    """
    Прицельные allow/deny, чтобы узкий уровень (IP/отдел) мог перебить более широкий.
    Работает для обеих политик.
    """
    lines: List[str] = []
    if getattr(eff_profile, "policy", None) == POLICY_ALLOW_ALL_EXCEPT:
        base_deny = set(getattr(base_profile, "deny_groups", []) or [])
        eff_deny  = set(getattr(eff_profile,  "deny_groups", []) or [])
        to_allow  = [k for k in DENY_GROUP_ORDER if k in base_deny and k not in eff_deny]
        for key in to_allow:
            acl = DENY_GROUPS[key].acl_name
            scope = f" {target_acl}" if target_acl else ""
            lines.append(f"http_access allow {acl}{scope} !BOT_WHITELIST")
    else:
        base_allow = set(getattr(base_profile, "allow_groups", []) or [])
        eff_allow  = set(getattr(eff_profile,  "allow_groups", []) or [])
        to_deny    = [k for k in DENY_GROUP_ORDER if k in base_allow and k not in eff_allow]
        for key in to_deny:
            acl = DENY_GROUPS[key].acl_name
            scope = f" {target_acl}" if target_acl else ""
            lines.append(f"http_access deny {acl}{scope} !BOT_WHITELIST")
    return lines

def _group_order_and_acl(keys: Iterable[str]) -> List[Tuple[str, str]]:
    """
    Возвращает пары (key, ACL_NAME) в правильном порядке для переданного подмножества групп.
    Берёт порядок из DENY_GROUP_ORDER, ACL — из DENY_GROUPS[key].acl_name.
    """
    out: List[Tuple[str, str]] = []
    keyset = set(keys or [])
    for k in DENY_GROUP_ORDER:
        if k in keyset:
            out.append((k, DENY_GROUPS[k].acl_name))
    return out


def render_allow_exceptions(base_profile, eff_profile, target_acl: Optional[str]) -> List[str]:
    """
    Прицельные allow/deny-исключения, чтобы узкий уровень (IP/отдел) перебивал более широкий.
    Работает для обеих политик.
    - allow_all_except: что было запрещено на базовом уровне, но не запрещено на узком — явно разрешаем.
    - deny_all_except:  что было разрешено на базовом уровне, но не разрешено на узком — явно запрещаем.
    """
    lines: List[str] = []
    policy = getattr(eff_profile, "policy", None)

    if policy == "allow_all_except":
        base_deny = set(getattr(base_profile, "deny_groups", []) or [])
        eff_deny  = set(getattr(eff_profile,  "deny_groups", []) or [])
        to_allow  = [acl for _, acl in _group_order_and_acl(base_deny - eff_deny)]
        for acl in to_allow:
            scope = f" {target_acl}" if target_acl else ""
            lines.append(f"http_access allow {acl}{scope} !BOT_WHITELIST")
    elif policy == "deny_all_except":
        base_allow = set(getattr(base_profile, "allow_groups", []) or [])
        eff_allow  = set(getattr(eff_profile,  "allow_groups", []) or [])
        to_deny    = [acl for _, acl in _group_order_and_acl(base_allow - eff_allow)]
        for acl in to_deny:
            scope = f" {target_acl}" if target_acl else ""
            lines.append(f"http_access deny {acl}{scope} !BOT_WHITELIST")

    return lines


def render_managed_block(app_config: AppConfig) -> str:
    """
    Полный рендер управляемого блока для squid.conf.
    Включает:
        - ACL whitelist + доменные группы
        - ACL отделов (src) и IP (src)
        - Правила в порядке: whitelist → IP overrides (allow-exc → профиль) → Dept overrides (allow-exc → профиль)
                             → Глобальные → allow localhost/localnet → deny all
    """
    cfg = app_config.normalized()
    metadata = app_config_to_payload(cfg)

    lines: List[str] = [
        MANAGED_BEGIN,
        f"{MANAGED_CONFIG_PREFIX}{json.dumps(metadata, ensure_ascii=False)}",
        f'acl BOT_WHITELIST src "{WHITE_FILE}"'
    ]

    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        lines.append(f'acl {group.acl_name} dstdomain "{group.path}"')
    lines.append("")

    dept_paths = ensure_department_sources()
    dept_acl_map: Dict[str, str] = {}
    for name in sorted(dept_paths.keys()):
        path = dept_paths[name]
        acl_name = f"SRC_DEPT_{department_slug(name).upper()}"
        dept_acl_map[name] = acl_name
        lines.append(f'acl {acl_name} src "{path}"')

    ip_acl_map: Dict[str, str] = {}
    for ip in sorted(cfg.ip_overrides.keys()):
        token = ip_token(ip)
        acl_name = f"SRC_IP_{token.upper()}"
        ip_acl_map[ip] = acl_name
        lines.append(f"acl {acl_name} src {ip}")

    lines.append("")

    rules: List[str] = []
    rules.append("http_access allow BOT_WHITELIST")

    for ip in sorted(cfg.ip_overrides.keys()):
        acl_name = ip_acl_map[ip]
        departments = IP_TO_DEPARTMENTS.get(ip, [])
        department = departments[0] if departments else None

        base_cfg = AppConfig(cfg.global_profile, cfg.departments, {k: v for k, v in cfg.ip_overrides.items() if k != ip})
        base_profile = resolve_profile(base_cfg, department=department)
        eff_profile  = resolve_profile(cfg,       department=department, ip=ip)

        rules.extend(render_allow_exceptions(base_profile, eff_profile, target_acl=acl_name))
        rules.extend(render_profile_rules(eff_profile, target_acl=acl_name))

    for name in sorted(cfg.departments.keys()):
        acl_name = dept_acl_map.get(name)
        if not acl_name:
            continue

        base_cfg = AppConfig(cfg.global_profile, {k: v for k, v in cfg.departments.items() if k != name}, cfg.ip_overrides)
        base_profile = resolve_profile(base_cfg, department=name)
        eff_profile  = resolve_profile(cfg,       department=name)

        if (
            eff_profile.policy == base_profile.policy
            and eff_profile.deny_groups == base_profile.deny_groups
            and eff_profile.allow_groups == base_profile.allow_groups
        ):
            pass
        else:
            rules.extend(render_allow_exceptions(base_profile, eff_profile, target_acl=acl_name))
            rules.extend(render_profile_rules(eff_profile, target_acl=acl_name))

    rules.extend(render_profile_rules(cfg.global_profile.normalized()))

    rules.append("http_access allow localhost")
    rules.append("http_access allow localnet")
    rules.append("http_access deny all")

    lines.extend(rules)
    lines.append(MANAGED_END)
    return "\n".join(lines) + "\n"

def build_squid_conf(cfg):
    lines = []
    rules = []

    for ip in sorted(cfg.ip_overrides.keys()):
        acl_name = ip_acl_map[ip]
        department = None
        departments = IP_TO_DEPARTMENTS.get(ip, [])
        if departments:
            department = departments[0]

        base_cfg = AppConfig(
            cfg.global_profile,
            cfg.departments,
            {k: v for k, v in cfg.ip_overrides.items() if k != ip},
        )
        base_profile = resolve_profile(base_cfg, department=department)
        effective_profile = resolve_profile(cfg, department=department, ip=ip)

        rules.extend(render_allow_exceptions(base_profile, effective_profile, target_acl=acl_name))
        rules.extend(render_profile_rules(effective_profile, target_acl=acl_name))

    for name in sorted(cfg.departments.keys()):
        acl_name = dept_acl_map.get(name)
        if not acl_name:
            continue

        base_cfg = AppConfig(
            cfg.global_profile,
            {k: v for k, v in cfg.departments.items() if k != name},
            cfg.ip_overrides,
        )
        base_profile = resolve_profile(base_cfg, department=name)
        effective_profile = resolve_profile(cfg, department=name)

        if (
            effective_profile.policy == base_profile.policy
            and effective_profile.deny_groups == base_profile.deny_groups
            and effective_profile.allow_groups == base_profile.allow_groups
        ):
            continue

        rules.extend(render_allow_exceptions(base_profile, effective_profile, target_acl=acl_name))
        rules.extend(render_profile_rules(effective_profile, target_acl=acl_name))

    rules.extend(render_profile_rules(cfg.global_profile.normalized()))
    rules.append("http_access allow localhost")
    rules.append("http_access allow localnet")
    rules.append("http_access deny all")

    lines.extend(rules)
    lines.append(MANAGED_END)
    return "\n".join(lines) + "\n"

def scan_squid_conf(conf: Path) -> ConfCheck:
    warnings: List[str] = []
    if not conf.exists():
        warnings.append("Файл конфигурации отсутствует.")
        return ConfCheck(False, None, set(), set(), warnings)

    original_lines = conf.read_text(encoding="utf-8", errors="ignore").splitlines()
    begin = end_idx = None
    for idx, line in enumerate(original_lines):
        if line.strip() == MANAGED_BEGIN and begin is None:
            begin = idx
        elif line.strip() == MANAGED_END:
            end_idx = idx
            break

    if begin is None or end_idx is None or begin >= end_idx:
        warnings.append("Управляемый блок squid-bot не найден.")
        return ConfCheck(False, None, set(), set(), warnings)

    block = original_lines[begin:end_idx + 1]
    metadata: Optional[Dict[str, object]] = None
    policy: Optional[str] = None
    deny: Set[str] = set()
    allow: Set[str] = set()

    config_line = next((line for line in block if line.startswith(MANAGED_CONFIG_PREFIX)), None)
    if config_line:
        raw_payload = config_line[len(MANAGED_CONFIG_PREFIX):].strip()
        try:
            payload = json.loads(raw_payload)
            if isinstance(payload, dict):
                metadata = payload
                app_cfg = app_config_from_payload(payload)
                global_profile = app_cfg.global_profile.normalized()
                policy = global_profile.policy
                deny = set(global_profile.deny_groups)
                allow = set(global_profile.allow_groups)
        except Exception:
            warnings.append("Не удалось разобрать строку с параметрами блока.")
    else:
        warnings.append("Не найдена строка с параметрами блока.")

    return ConfCheck(True, policy, deny, allow, warnings, metadata)


def describe_group_titles(keys: Iterable[str]) -> str:
    titles = [DENY_GROUPS[key].title for key in DENY_GROUP_ORDER if key in keys]
    return ', '.join(titles) if titles else 'нет'


def confcheck_summary_lines(res: ConfCheck) -> List[str]:
    lines = [
        '⚙️ Проверка конфигурации Squid:',
        f"Управляемый блок: {'✅' if res.has_managed_block else '❌'}",
    ]
    if res.global_policy:
        policy_label = POLICY_CHOICES.get(res.global_policy, res.global_policy)
        lines.append(f'Глобальная политика: {policy_label}')
        if res.global_policy == POLICY_ALLOW_ALL_EXCEPT:
            lines.append(f'Блокируемые группы: {describe_group_titles(res.global_deny_groups)}')
        elif res.global_policy == POLICY_DENY_ALL_EXCEPT:
            lines.append(f'Разрешённые группы: {describe_group_titles(res.global_allow_groups)}')
    else:
        lines.append('Глобальная политика: не найдена')
    if res.metadata and isinstance(res.metadata, dict):
        departments = res.metadata.get('departments')
        ip_overrides = res.metadata.get('ip_overrides')
        dept_count = len(departments) if isinstance(departments, dict) else 0
        ip_count = len(ip_overrides) if isinstance(ip_overrides, dict) else 0
        if dept_count or ip_count:
            lines.append(f'Переопределения: отделы — {dept_count}, IP — {ip_count}')
    if res.warnings:
        lines.append('')
        lines.append('👉 Предупреждения:')
        lines.extend(f'- {warning}' for warning in res.warnings)
    return lines




def policy_label(policy: Optional[str]) -> str:
    if not policy:
        return "не установлена"
    return POLICY_CHOICES.get(policy, policy)


def department_by_slug(slug: str) -> Optional[str]:
    return SLUG_TO_DEPARTMENT.get(slug)


def profile_group_state(profile: BotConfig, group_key: str) -> Tuple[bool, str, str]:
    if profile.policy == POLICY_ALLOW_ALL_EXCEPT:
        active = group_key in profile.deny_groups
        icon = "⛔️" if active else "✅"
        description = "блокируется" if active else "разрешён"
    else:
        active = group_key in profile.allow_groups
        icon = "✅" if active else "⛔️"
        description = "разрешён" if active else "блокируется"
    return active, icon, description


def format_profile_groups(profile: BotConfig) -> str:
    if profile.policy == POLICY_ALLOW_ALL_EXCEPT:
        keys = profile.deny_groups
        label = "Блокируемые группы"
    else:
        keys = profile.allow_groups
        label = "Разрешённые группы"
    titles = describe_group_titles(keys)
    return f"{label}: {titles}"


def build_departments_overview(app_cfg: Optional[AppConfig] = None) -> Tuple[str, InlineKeyboardMarkup, AppConfig]:
    cfg = (app_cfg or load_app_config()).normalized()
    global_profile = cfg.global_profile.normalized()
    lines = [
        "🏢 Управление отделами",
        f"Глобальная политика: {policy_label(global_profile.policy)}",
        format_profile_groups(global_profile),
        f"Переопределения отделов: {len(cfg.departments)}",
        f"IP переопределения: {len(cfg.ip_overrides)}",
        "",
        "Выберите отдел для настройки.",
    ]
    rows: List[List[InlineKeyboardButton]] = []
    row: List[InlineKeyboardButton] = []
    for name in ALL_DEPARTMENT_NAMES:
        slug = department_slug(name)
        row.append(InlineKeyboardButton(text=name, callback_data=f"dept:{slug}:menu"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([InlineKeyboardButton(text="🌐 IP переопределения", callback_data="ip:all")])
    rows.append([InlineKeyboardButton(text="🔄 Обновить", callback_data="dept:list")])
    rows.append([InlineKeyboardButton(text="🏠 Главное меню", callback_data="main")])
    return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=rows), cfg


def department_detail_text(app_cfg: AppConfig, department: str) -> str:
    cfg = app_cfg.normalized()
    effective = resolve_department_profile(department, app_cfg=cfg)
    base = inherited_department_profile(cfg, department)
    ip_count = len(iter_department_ips(department))
    override_ips = [ip for ip, ov in cfg.ip_overrides.items() if department in IP_TO_DEPARTMENTS.get(ip, [])]
    lines = [
        f"🏢 {department}",
        f"Политика: {policy_label(effective.policy)}",
        format_profile_groups(effective),
    ]
    if department in cfg.departments:
        lines.append("Переопределение отдела: ✅")
    else:
        lines.append("Переопределение отдела: ♻️ использует глобальные правила")
    if effective.policy != base.policy:
        lines.append(f"Унаследованная политика: {policy_label(base.policy)}")
    if effective.policy == POLICY_ALLOW_ALL_EXCEPT and effective.deny_groups != base.deny_groups:
        lines.append(f"Унаследованные блокировки: {describe_group_titles(base.deny_groups)}")
    if effective.policy == POLICY_DENY_ALL_EXCEPT and effective.allow_groups != base.allow_groups:
        lines.append(f"Унаследованные разрешения: {describe_group_titles(base.allow_groups)}")
    lines.append("")
    lines.append("Группы:")
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        active, icon, description = profile_group_state(effective, key)
        base_active, _, _ = profile_group_state(base, key)
        marker = " • переопределено" if active != base_active or effective.policy != base.policy else ""
        lines.append(f"{icon} {group.title} — {description}{marker}")
    lines.append("")
    lines.append(f"Закреплённых IP: {ip_count}")
    if override_ips:
        lines.append(f"IP с переопределениями: {len(override_ips)}")
    return "\n".join(lines)


def department_menu_keyboard(department: str) -> InlineKeyboardMarkup:
    slug = department_slug(department)
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⚙️ Политика", callback_data=f"dept:{slug}:policy")],
        [InlineKeyboardButton(text="📚 Группы", callback_data=f"dept:{slug}:groups")],
        [InlineKeyboardButton(text="🌐 IP адреса", callback_data=f"dept:{slug}:ips")],
        [InlineKeyboardButton(text="♻️ Сбросить переопределение", callback_data=f"dept:{slug}:reset")],
        [InlineKeyboardButton(text="⬅️ К списку отделов", callback_data="dept:list")],
    ])


def department_groups_text(app_cfg: AppConfig, department: str) -> str:
    cfg = app_cfg.normalized()
    effective = resolve_department_profile(department, app_cfg=cfg)
    base = inherited_department_profile(cfg, department)
    lines = [
        f"📚 Группы отдела {department}",
        format_profile_groups(effective),
        "",
    ]
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        active, icon, description = profile_group_state(effective, key)
        base_active, _, _ = profile_group_state(base, key)
        marker = " • переопределено" if active != base_active or effective.policy != base.policy else ""
        lines.append(f"{icon} {group.title} — {description}{marker}")
    lines.append("")
    lines.append("Нажмите на группу, чтобы переключить состояние.")
    return "\n".join(lines)


def department_groups_keyboard(department: str, app_cfg: AppConfig) -> InlineKeyboardMarkup:
    cfg = app_cfg.normalized()
    effective = resolve_department_profile(department, app_cfg=cfg)
    slug = department_slug(department)
    rows: List[List[InlineKeyboardButton]] = []
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        active, icon, _ = profile_group_state(effective, key)
        rows.append([InlineKeyboardButton(text=f"{icon} {group.title}", callback_data=f"dept:{slug}:group:{key}")])
    rows.append([InlineKeyboardButton(text="⬅️ Назад", callback_data=f"dept:{slug}:menu")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def department_ips_view(app_cfg: AppConfig, department: str, page: int = 1, per_page: int = 10) -> Tuple[str, InlineKeyboardMarkup]:
    cfg = app_cfg.normalized()
    slug = department_slug(department)
    ips = sorted(set(iter_department_ips(department)))
    manage_row = [
        InlineKeyboardButton(text="➕ Добавить IP", callback_data=f"dept:{slug}:ipadd:{page}"),
        InlineKeyboardButton(text="➖ Удалить IP", callback_data=f"dept:{slug}:ipdel:{page}")
    ]
    if not ips:
        text = "У этого отдела пока нет закреплённых IP адресов."
        kb = InlineKeyboardMarkup(inline_keyboard=[
            manage_row,
            [InlineKeyboardButton(text="⬅️ Назад", callback_data=f"dept:{slug}:menu")],
        ])
        return text, kb
    subset, total_pages = slice_page(ips, page, per_page)
    lines = [
        f"🌐 IP адреса отдела {department}",
        f"Страница {page}/{total_pages}",
        "",
    ]
    rows: List[List[InlineKeyboardButton]] = [manage_row]
    for ip in subset:
        profile = resolve_ip_profile(ip, department=department, app_cfg=cfg)
        icon = "🛠️" if ip in cfg.ip_overrides else "💻"
        lines.append(f"{icon} {ip} — {policy_label(profile.policy)}")
        token = ip_token(ip)
        rows.append([InlineKeyboardButton(text=f"{icon} {ip}", callback_data=f"dept:{slug}:ip:{token}:menu")])
    nav: List[InlineKeyboardButton] = []
    if page > 1:
        nav.append(InlineKeyboardButton(text="⬅️", callback_data=f"dept:{slug}:ips:page:{page-1}"))
    if page < total_pages:
        nav.append(InlineKeyboardButton(text="➡️", callback_data=f"dept:{slug}:ips:page:{page+1}"))
    if nav:
        rows.append(nav)
    rows.append([InlineKeyboardButton(text="⬅️ К отделу", callback_data=f"dept:{slug}:menu")])
    kb = InlineKeyboardMarkup(inline_keyboard=rows)
    lines.append("")
    lines.append("Чтобы управлять IP выберите его в списке.")
    return "\n".join(lines), kb



def ip_detail_text(app_cfg: AppConfig, ip: str, department: Optional[str]) -> str:
    cfg = app_cfg.normalized()
    effective = resolve_ip_profile(ip, department=department, app_cfg=cfg)
    base = inherited_ip_profile(cfg, department, ip)
    attached = IP_TO_DEPARTMENTS.get(ip, [])
    lines = [
        f"💻 IP {ip}",
        f"Политика: {policy_label(effective.policy)}",
        format_profile_groups(effective),
    ]
    if ip in cfg.ip_overrides:
        lines.append("Переопределение IP: ✅")
    else:
        lines.append("Переопределение IP: ♻️ наследует правила")
    if effective.policy != base.policy:
        lines.append(f"Унаследованная политика: {policy_label(base.policy)}")
    if effective.policy == POLICY_ALLOW_ALL_EXCEPT and effective.deny_groups != base.deny_groups:
        lines.append(f"Унаследованные блокировки: {describe_group_titles(base.deny_groups)}")
    if effective.policy == POLICY_DENY_ALL_EXCEPT and effective.allow_groups != base.allow_groups:
        lines.append(f"Унаследованные разрешения: {describe_group_titles(base.allow_groups)}")
    if attached:
        lines.append(f"Связанные отделы: {', '.join(attached)}")
    elif department:
        lines.append(f"Контекст отдела: {department}")
    else:
        lines.append("Связанные отделы: нет")
    lines.append("")
    lines.append("Группы:")
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        active, icon, description = profile_group_state(effective, key)
        base_active, _, _ = profile_group_state(base, key)
        marker = " • переопределено" if active != base_active or effective.policy != base.policy else ""
        lines.append(f"{icon} {group.title} — {description}{marker}")
    return "\n".join(lines)


def ip_menu_keyboard(ip: str, department: Optional[str]) -> InlineKeyboardMarkup:
    token = ip_token(ip)
    dept_part = department_slug(department) if department else "-"
    rows: List[List[InlineKeyboardButton]] = []
    if department and ip in iter_department_ips(department):
        rows.append([InlineKeyboardButton(text="🗑️ Удалить из отдела", callback_data=f"dept:{department_slug(department)}:ipremove:{token}")])
    rows.append([InlineKeyboardButton(text="⚙️ Политика", callback_data=f"ip:view:{dept_part}:{token}:policy")])
    rows.append([InlineKeyboardButton(text="📚 Группы", callback_data=f"ip:view:{dept_part}:{token}:groups")])
    rows.append([InlineKeyboardButton(text="♻️ Сбросить переопределение", callback_data=f"ip:view:{dept_part}:{token}:reset")])
    if department:
        rows.append([InlineKeyboardButton(text="⬅️ К списку IP отдела", callback_data=f"dept:{department_slug(department)}:ips")])
        rows.append([InlineKeyboardButton(text="⬅️ К отделу", callback_data=f"dept:{department_slug(department)}:menu")])
    else:
        rows.append([InlineKeyboardButton(text="⬅️ К списку IP", callback_data="ip:all")])
        rows.append([InlineKeyboardButton(text="⬅️ К отделам", callback_data="dept:list")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def ip_groups_text(app_cfg: AppConfig, ip: str, department: Optional[str]) -> str:
    cfg = app_cfg.normalized()
    effective = resolve_ip_profile(ip, department=department, app_cfg=cfg)
    lines = [
        f"📚 Группы для IP {ip}",
        format_profile_groups(effective),
        "",
    ]
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        active, icon, description = profile_group_state(effective, key)
        lines.append(f"{icon} {group.title} — {description}")
    lines.append("")
    lines.append("Нажмите на группу, чтобы переключить состояние.")
    return "\n".join(lines)


def ip_groups_keyboard(ip: str, department: Optional[str], app_cfg: AppConfig) -> InlineKeyboardMarkup:
    cfg = app_cfg.normalized()
    effective = resolve_ip_profile(ip, department=department, app_cfg=cfg)
    token = ip_token(ip)
    dept_part = department_slug(department) if department else "-"
    rows: List[List[InlineKeyboardButton]] = []
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        active, icon, _ = profile_group_state(effective, key)
        rows.append([InlineKeyboardButton(text=f"{icon} {group.title}", callback_data=f"ip:view:{dept_part}:{token}:group:{key}")])
    rows.append([InlineKeyboardButton(text="⬅️ Назад", callback_data=f"ip:view:{dept_part}:{token}:menu")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def ip_policy_text(ip: str, department: Optional[str]) -> str:
    if department:
        return (
            f"⚙️ Политика для IP {ip}\n\n"
            "Выберите режим доступа для этого адреса. Изменение затронет только данный IP в рамках выбранного отдела."
        )
    return (
        f"⚙️ Политика для IP {ip}\n\n"
        "Выберите режим доступа для этого адреса. Изменение действует глобально для IP."
    )


def ip_policy_keyboard(ip: str, department: Optional[str]) -> InlineKeyboardMarkup:
    token = ip_token(ip)
    dept_part = department_slug(department) if department else "-"
    rows = [
        [InlineKeyboardButton(text="Разрешено всё, кроме выбранных", callback_data=f"ip:view:{dept_part}:{token}:policy:set:allow")],
        [InlineKeyboardButton(text="Запрещено всё, кроме выбранных", callback_data=f"ip:view:{dept_part}:{token}:policy:set:deny")],
        [InlineKeyboardButton(text="♻️ Наследовать", callback_data=f"ip:view:{dept_part}:{token}:policy:set:inherit")],
        [InlineKeyboardButton(text="⬅️ Назад", callback_data=f"ip:view:{dept_part}:{token}:menu")],
    ]
    return InlineKeyboardMarkup(inline_keyboard=rows)


def build_ip_overrides_overview(app_cfg: Optional[AppConfig] = None, page: int = 1, per_page: int = 10) -> Tuple[str, InlineKeyboardMarkup, AppConfig]:
    cfg = (app_cfg or load_app_config()).normalized()
    ips = sorted(cfg.ip_overrides.keys())
    if not ips:
        text = "🌐 Переопределения для IP отсутствуют."
        kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="⬅️ К отделам", callback_data="dept:list")]])
        return text, kb, cfg
    subset, total_pages = slice_page(ips, page, per_page)
    lines = [
        "🌐 Переопределения IP",
        f"Страница {page}/{total_pages}",
        "",
    ]
    rows: List[List[InlineKeyboardButton]] = []
    for ip in subset:
        profile = resolve_ip_profile(ip, department=None, app_cfg=cfg)
        attached = IP_TO_DEPARTMENTS.get(ip, [])
        extra = f" ({', '.join(attached)})" if attached else ""
        lines.append(f"🛠️ {ip}{extra} — {policy_label(profile.policy)}")
        token = ip_token(ip)
        rows.append([InlineKeyboardButton(text=f"🛠️ {ip}", callback_data=f"ip:view:-:{token}:menu")])
    nav: List[InlineKeyboardButton] = []
    if page > 1:
        nav.append(InlineKeyboardButton(text="⬅️", callback_data=f"ip:all:page:{page-1}"))
    if page < total_pages:
        nav.append(InlineKeyboardButton(text="➡️", callback_data=f"ip:all:page:{page+1}"))
    if nav:
        rows.append(nav)
    rows.append([InlineKeyboardButton(text="⬅️ К отделам", callback_data="dept:list")])
    kb = InlineKeyboardMarkup(inline_keyboard=rows)
    return "\n".join(lines), kb, cfg
def patch_squid_conf(conf: Path, app_config: Optional[AppConfig] = None) -> Tuple[bool, str]:
    cfg = (app_config or load_app_config()).normalized()
    managed_block = render_managed_block(cfg).rstrip("\n").splitlines()

    original_lines = conf.read_text(encoding="utf-8", errors="ignore").splitlines() if conf.exists() else []
    lines = list(original_lines)

    begin = end_idx = None
    for idx, line in enumerate(lines):
        if line.strip() == MANAGED_BEGIN and begin is None:
            begin = idx
        elif line.strip() == MANAGED_END:
            end_idx = idx
            break

    if begin is None or end_idx is None or begin >= end_idx:
        legacy = ("acl BLOCKED", "acl WHITELIST", "http_access deny BLOCKED", "deny_info ERR_ACCESS_DENIED BLOCKED")
        lines = [ln for ln in lines if not any(x in ln for x in legacy)]
        begin = end_idx = None

    if begin is not None and end_idx is not None and begin <= end_idx:
        new_lines = lines[:begin] + managed_block + lines[end_idx + 1:]
    else:
        insert_at = None
        for i, ln in enumerate(lines):
            s = ln.strip().lower()
            if s.startswith("http_access allow localnet") or s.startswith("http_access allow localhost") or s == "http_access deny all":
                insert_at = i
                break
        if insert_at is None:
            for i in range(len(lines) - 1, -1, -1):
                if lines[i].strip().startswith("http_access"):
                    insert_at = i
                    break
        if insert_at is None:
            if lines and lines[-1].strip():
                lines.append("")
            new_lines = lines + managed_block
        else:
            before, after = lines[:insert_at], lines[insert_at:]
            if before and before[-1].strip():
                before.append("")
            if after and after[0].strip():
                after.insert(0, "")
            new_lines = before + managed_block + after

    changed = new_lines != original_lines
    conf.parent.mkdir(parents=True, exist_ok=True)
    conf.write_text("\n".join(new_lines) + "\n", encoding="utf-8")
    return changed, f"Управляемый блок обновлён и поставлен до широких правил (политика: {cfg.global_profile.policy})."

def squid_parse_ok() -> Tuple[bool, str]:
    code, out, err = run_cmd([SQUID_BIN, "-k", "parse"])
    return (code == 0), (out or err)

def squid_reload() -> Tuple[bool, str]:
    ok, msg = squid_parse_ok()
    if not ok:
        return False, f"❌ squid -k parse: {msg}"
    if SYSTEMCTL_BIN and (Path("/usr/lib/systemd/system/squid.service").exists() or Path("/lib/systemd/system/squid.service").exists()):
        code, out, err = run_cmd([SYSTEMCTL_BIN, "reload", "squid"])
        if code == 0:
            return True, "✅ Squid перезагружен (systemctl reload)."
    code, out, err = run_cmd([SQUID_BIN, "-k", "reconfigure"])
    if code == 0:
        return True, "✅ Squid перезагружен (squid -k reconfigure)."
    return False, f"❌ Не удалось перезагрузить Squid:\n{out}\n{err}"


@dataclasses.dataclass
class LogStats:
    total: int
    methods: Counter
    codes: Counter
    domains: Counter
    users: Counter
    denied: int
    denied_domains: Counter
    denied_by_ip: Counter

def parse_access_lines(lines: Iterable[str]) -> LogStats:
    methods = Counter()
    codes = Counter()
    domains = Counter()
    users = Counter()
    denied = 0
    denied_domains = Counter()
    denied_by_ip = Counter()
    total = 0

    for line in lines:
        parts = line.split()
        if len(parts) < 7:
            continue
        total += 1
        client_ip = parts[2] if len(parts) > 2 else "-"
        code = parts[3] if len(parts) > 3 else "-"
        method = parts[5] if len(parts) > 5 else "-"
        url = parts[6] if len(parts) > 6 else "-"
        user = parts[7] if len(parts) > 7 else "-"

        codes[code] += 1
        methods[method] += 1
        users[user] += 1

        if method == "CONNECT":
            host = url.split(":")[0].lower() if ":" in url else url.lower()
        else:
            host = extract_host_from_url(url) or "-"
        domains[host] += 1

        if code.startswith("TCP_DENIED"):
            denied += 1
            denied_domains[host] += 1
            denied_by_ip[client_ip] += 1

    return LogStats(total, methods, codes, domains, users, denied, denied_domains, denied_by_ip)

def tail_new_lines(log_path: Path, state_file: Path) -> List[str]:
    if not log_path.exists():
        return []
    last = 0
    try:
        with state_file.open("r") as s:
            last = int((s.read() or "0").strip())
    except FileNotFoundError:
        last = 0
    except Exception:
        last = 0

    lines = []
    size = log_path.stat().st_size
    with log_path.open("r", encoding="utf-8", errors="ignore") as f:
        if last <= size:
            f.seek(last)
        else:
            f.seek(0)
        for ln in f:
            lines.append(ln.rstrip("\n"))
        new_pos = f.tell()
    with state_file.open("w") as s:
        s.write(str(new_pos))
    return lines

def fmt_stats(stats: LogStats, top_n: int = 10) -> str:
    out = []
    out.append(f"📈 Детальная статистика трафика")
    out.append(f"🕐 Время: {now_str()}")
    out.append(f"📊 Всего запросов: {stats.total}")
    
    if stats.total > 0:
        blocked_percent = (stats.denied / stats.total) * 100
        out.append(f"🚫 Заблокировано: {stats.denied} ({blocked_percent:.1f}%)")
        allowed_percent = ((stats.total - stats.denied) / stats.total) * 100
        out.append(f"✅ Разрешено: {stats.total - stats.denied} ({allowed_percent:.1f}%)")
    
    if stats.methods:
        out.append("\n🌐 HTTP методы:")
        for method, count in stats.methods.most_common(5):
            out.append(f"  • {method}: {count}")
    
    if stats.codes:
        out.append("\n📋 Коды ответов:")
        for code, count in stats.codes.most_common(5):
            out.append(f"  • {code}: {count}")
    
    if stats.domains:
        out.append(f"\n🌍 Топ-{min(top_n, 5)} популярных сайтов:")
        for domain, count in stats.domains.most_common(5):
            out.append(f"  • {domain}: {count}")
    
    if stats.denied_domains:
        out.append(f"\n🚫 Топ-{min(top_n, 5)} блокируемых сайтов:")
        for domain, count in stats.denied_domains.most_common(5):
            out.append(f"  • {domain}: {count}")
    
    if stats.denied_by_ip:
        out.append(f"\n🔒 Топ-{min(top_n, 5)} IP с блокировками:")
        for ip, count in stats.denied_by_ip.most_common(5):
            out.append(f"  • {ip}: {count}")
    
    return "\n".join(out)

def create_html_report(stats: LogStats, blacklist_count: int, whitelist_count: int) -> str:
    """Создает красивый HTML-отчет в стиле SARG"""
    
    template_file = TEMPLATES_DIR / "sarg_report.html"
    if not template_file.exists():
        template_content = """
<!DOCTYPE html>
<html lang="ru">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Squid Proxy Report - {{ report_time }}</title>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }
        
        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            min-height: 100vh;
            padding: 20px;
        }
        
        .container {
            max-width: 1200px;
            margin: 0 auto;
            background: rgba(255, 255, 255, 0.95);
            border-radius: 20px;
            box-shadow: 0 20px 40px rgba(0, 0, 0, 0.1);
            overflow: hidden;
        }
        
        .header {
            background: linear-gradient(135deg, #2c3e50 0%, #34495e 100%);
            color: white;
            padding: 30px;
            text-align: center;
        }
        
        .header h1 {
            font-size: 2.5em;
            margin-bottom: 10px;
            text-shadow: 2px 2px 4px rgba(0, 0, 0, 0.3);
        }
        
        .header .subtitle {
            font-size: 1.2em;
            opacity: 0.9;
        }
        
        .stats-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
            gap: 20px;
            padding: 30px;
        }
        
        .stat-card {
            background: white;
            border-radius: 15px;
            padding: 25px;
            box-shadow: 0 10px 20px rgba(0, 0, 0, 0.1);
            border-left: 5px solid #3498db;
            transition: transform 0.3s ease;
        }
        
        .stat-card:hover {
            transform: translateY(-5px);
        }
        
        .stat-card.blocked {
            border-left-color: #e74c3c;
        }
        
        .stat-card.allowed {
            border-left-color: #27ae60;
        }
        
        .stat-card.sites {
            border-left-color: #f39c12;
        }
        
        .stat-card.ip {
            border-left-color: #9b59b6;
        }
        
        .stat-title {
            font-size: 1.1em;
            font-weight: 600;
            color: #2c3e50;
            margin-bottom: 10px;
            display: flex;
            align-items: center;
        }
        
        .stat-title i {
            margin-right: 10px;
            font-size: 1.3em;
        }
        
        .stat-value {
            font-size: 2.5em;
            font-weight: bold;
            color: #34495e;
            margin-bottom: 5px;
        }
        
        .stat-subtitle {
            color: #7f8c8d;
            font-size: 0.9em;
        }
        
        .charts-section {
            padding: 30px;
            background: #f8f9fa;
        }
        
        .section-title {
            font-size: 1.8em;
            color: #2c3e50;
            margin-bottom: 25px;
            text-align: center;
            position: relative;
        }
        
        .section-title::after {
            content: '';
            position: absolute;
            bottom: -10px;
            left: 50%;
            transform: translateX(-50%);
            width: 100px;
            height: 3px;
            background: linear-gradient(90deg, #3498db, #e74c3c);
            border-radius: 2px;
        }
        
        .charts-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
            gap: 25px;
        }
        
        .chart-card {
            background: white;
            border-radius: 15px;
            padding: 25px;
            box-shadow: 0 10px 20px rgba(0, 0, 0, 0.1);
        }
        
        .chart-title {
            font-size: 1.3em;
            font-weight: 600;
            color: #2c3e50;
            margin-bottom: 20px;
            text-align: center;
        }
        
        .chart-item {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 12px 0;
            border-bottom: 1px solid #ecf0f1;
        }
        
        .chart-item:last-child {
            border-bottom: none;
        }
        
        .chart-label {
            font-weight: 500;
            color: #34495e;
            flex: 1;
        }
        
        .chart-value {
            font-weight: bold;
            color: #e74c3c;
            background: #fdf2f2;
            padding: 4px 12px;
            border-radius: 20px;
            font-size: 0.9em;
        }
        
        .chart-value.allowed {
            color: #27ae60;
            background: #f2fdf2;
        }
        
        .footer {
            background: #2c3e50;
            color: white;
            padding: 20px;
            text-align: center;
            font-size: 0.9em;
        }
        
        .progress-bar {
            width: 100%;
            height: 8px;
            background: #ecf0f1;
            border-radius: 4px;
            overflow: hidden;
            margin: 10px 0;
        }
        
        .progress-fill {
            height: 100%;
            background: linear-gradient(90deg, #3498db, #2ecc71);
            border-radius: 4px;
            transition: width 0.3s ease;
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>🦑 Squid Proxy Report</h1>
            <div class="subtitle">Отчет о работе прокси-сервера за период {{ report_time }}</div>
        </div>
        
        <div class="stats-grid">
            <div class="stat-card">
                <div class="stat-title">📊 Всего запросов</div>
                <div class="stat-value">{{ stats.total }}</div>
                <div class="stat-subtitle">за анализируемый период</div>
            </div>
            
            <div class="stat-card blocked">
                <div class="stat-title">🚫 Заблокировано</div>
                <div class="stat-value">{{ stats.denied }}</div>
                <div class="stat-subtitle">{{ "%.1f"|format((stats.denied / stats.total * 100) if stats.total > 0 else 0) }}% от общего трафика</div>
                <div class="progress-bar">
                    <div class="progress-fill" style="width: {{ (stats.denied / stats.total * 100) if stats.total > 0 else 0 }}%"></div>
                </div>
            </div>
            
            <div class="stat-card allowed">
                <div class="stat-title">✅ Разрешено</div>
                <div class="stat-value">{{ stats.total - stats.denied }}</div>
                <div class="stat-subtitle">{{ "%.1f"|format(((stats.total - stats.denied) / stats.total * 100) if stats.total > 0 else 0) }}% от общего трафика</div>
                <div class="progress-bar">
                    <div class="progress-fill" style="width: {{ ((stats.total - stats.denied) / stats.total * 100) if stats.total > 0 else 0 }}%"></div>
                </div>
            </div>
            
            <div class="stat-card sites">
                <div class="stat-title">🚫 Заблокированных сайтов</div>
                <div class="stat-value">{{ blacklist_count }}</div>
                <div class="stat-subtitle">в черном списке</div>
            </div>
            
            <div class="stat-card ip">
                <div class="stat-title">✅ Разрешенных IP</div>
                <div class="stat-value">{{ whitelist_count }}</div>
                <div class="stat-subtitle">в белом списке</div>
            </div>
        </div>
        
        <div class="charts-section">
            <h2 class="section-title">📈 Детальная статистика</h2>
            
            <div class="charts-grid">
                {% if stats.methods %}
                <div class="chart-card">
                    <div class="chart-title">🌐 HTTP методы</div>
                    {% for method, count in stats.methods.most_common(10) %}
                    <div class="chart-item">
                        <span class="chart-label">{{ method }}</span>
                        <span class="chart-value">{{ count }}</span>
                    </div>
                    {% endfor %}
                </div>
                {% endif %}
                
                {% if stats.codes %}
                <div class="chart-card">
                    <div class="chart-title">📋 Коды ответов</div>
                    {% for code, count in stats.codes.most_common(10) %}
                    <div class="chart-item">
                        <span class="chart-label">{{ code }}</span>
                        <span class="chart-value">{{ count }}</span>
                    </div>
                    {% endfor %}
                </div>
                {% endif %}
                
                {% if stats.domains %}
                <div class="chart-card">
                    <div class="chart-title">🌍 Популярные сайты</div>
                    {% for domain, count in stats.domains.most_common(10) %}
                    <div class="chart-item">
                        <span class="chart-label">{{ domain }}</span>
                        <span class="chart-value allowed">{{ count }}</span>
                    </div>
                    {% endfor %}
                </div>
                {% endif %}
                
                {% if stats.denied_domains %}
                <div class="chart-card">
                    <div class="chart-title">🚫 Заблокированные сайты</div>
                    {% for domain, count in stats.denied_domains.most_common(10) %}
                    <div class="chart-item">
                        <span class="chart-label">{{ domain }}</span>
                        <span class="chart-value">{{ count }}</span>
                    </div>
                    {% endfor %}
                </div>
                {% endif %}
                
                {% if stats.denied_by_ip %}
                <div class="chart-card">
                    <div class="chart-title">🔒 IP с блокировками</div>
                    {% for ip, count in stats.denied_by_ip.most_common(10) %}
                    <div class="chart-item">
                        <span class="chart-label">{{ ip }}</span>
                        <span class="chart-value">{{ count }}</span>
                    </div>
                    {% endfor %}
                </div>
                {% endif %}
            </div>
        </div>
        
        <div class="footer">
            <p>Отчет сгенерирован Squid Control Bot | {{ report_time }}</p>
            <p>Для получения актуальной статистики используйте команду /stats в Telegram боте</p>
        </div>
    </div>
</body>
</html>
        """
        template_file.write_text(template_content, encoding='utf-8')
    
    env = Environment(
        loader=FileSystemLoader(str(TEMPLATES_DIR)),
        autoescape=select_autoescape(['html', 'xml'])
    )
    
    template = env.get_template('sarg_report.html')
    
    html_content = template.render(
        stats=stats,
        blacklist_count=blacklist_count,
        whitelist_count=whitelist_count,
        report_time=now_str()
    )
    
    return html_content

def save_html_report(stats: LogStats, blacklist_count: int, whitelist_count: int) -> str:
    """Создает и сохраняет HTML-отчет"""
    html_content = create_html_report(stats, blacklist_count, whitelist_count)
    
    timestamp = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = f"squid_report_{timestamp}.html"
    filepath = REPORTS_DIR / filename
    
    filepath.write_text(html_content, encoding='utf-8')
    
    return str(filepath)


main_kb = ReplyKeyboardMarkup(
    keyboard=[
        [KeyboardButton(text="🚫 Сайты"), KeyboardButton(text="✅ IP адреса")],
        [KeyboardButton(text="🏢 Отделы"), KeyboardButton(text="📊 Статистика")],
        [KeyboardButton(text="⚙️ Настройки"), KeyboardButton(text="💾 Бэкап")],
        [KeyboardButton(text="🔄 Восстановить")],
    ],
    resize_keyboard=True
)

def paginated_kb(prefix: str, page: int, total_pages: int) -> InlineKeyboardMarkup:
    rows = []
    nav = []
    if page > 1:
        nav.append(InlineKeyboardButton(text="⬅️", callback_data=f"{prefix}:p:{page-1}"))
    if page < total_pages:
        nav.append(InlineKeyboardButton(text="➡️", callback_data=f"{prefix}:p:{page+1}"))
    if nav:
        rows.append(nav)
    rows.append([InlineKeyboardButton(text="🔄 Обновить", callback_data=f"{prefix}:refresh")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def slice_page(items: List[str], page: int, per_page: int = MAX_LINES_PER_PAGE) -> Tuple[List[str], int]:
    total_pages = max(1, (len(items) + per_page - 1) // per_page)
    page = max(1, min(page, total_pages))
    start = (page - 1) * per_page
    end = start + per_page
    return items[start:end], total_pages

def list_with_delete_buttons(prefix: str, items: List[str], page: int) -> InlineKeyboardMarkup:
    subset, total_pages = slice_page(items, page)
    rows: List[List[InlineKeyboardButton]] = []
    for val in subset:
        rows.append([InlineKeyboardButton(text=f"❌ {val}", callback_data=f"{prefix}:del:{val}")])
    nav = []
    if page > 1:
        nav.append(InlineKeyboardButton(text="⬅️", callback_data=f"{prefix}:p:{page-1}"))
    if page < total_pages:
        nav.append(InlineKeyboardButton(text="➡️", callback_data=f"{prefix}:p:{page+1}"))
    if nav:
        rows.append(nav)
    rows.append([InlineKeyboardButton(text="🔄 Обновить", callback_data=f"{prefix}:refresh")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def whitelist_management_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Добавить", callback_data="white:add"), InlineKeyboardButton(text="➖ Удалить", callback_data="white:del")],
        [InlineKeyboardButton(text="📋 Показать список", callback_data="white:edit")],
        [InlineKeyboardButton(text="🏠 Главное меню", callback_data="main")],
    ])



class Form(StatesGroup):
    WAIT_GROUP_VALUE = State()
    WAIT_NEW_GROUP_TITLE = State()
    WAIT_NEW_GROUP_DESCRIPTION = State()
    WAIT_WHITE_ADD = State()
    WAIT_WHITE_DEL = State()
    WAIT_DEPT_IP_ADD = State()
    WAIT_DEPT_IP_REMOVE = State()
    WAIT_SEARCH = State()


bot = Bot(BOT_TOKEN)
async def update_groups_overview_message(chat_id: int, message_id: int, status_lines: Optional[List[str]] = None) -> None:
    text, kb, _ = build_groups_overview()
    if status_lines:
        status_text = "\n".join(status_lines)
        text = f"{text}\n\n{status_text}"
    with contextlib.suppress(Exception):
        await bot.edit_message_text(text, chat_id, message_id, reply_markup=kb)


async def update_department_ips_message(chat_id: int, message_id: int, department: str, page: int = 1, status_lines: Optional[List[str]] = None) -> None:
    app_cfg = load_app_config()
    text, kb = department_ips_view(app_cfg, department, page=page)
    if status_lines:
        status_text = "\n".join(status_lines)
        text = f"{text}\n\n{status_text}"
    with contextlib.suppress(Exception):
        await bot.edit_message_text(text, chat_id, message_id, reply_markup=kb)


dp = Dispatcher()


@dp.message(CommandStart())
async def cmd_start(m: Message):
    if not is_admin(m.from_user.id):
        return await m.answer("⛔ Доступ запрещён")
    await m.answer(
        "🦑 Добро пожаловать в Squid Control Bot!\n"
        "Выберите действие из меню ниже.\n"
        "Доступные команды: /help /id /status /check_config /patch_config /report",
        reply_markup=main_kb
    )

@dp.message(Command("help"))
async def cmd_help(m: Message):
    if not is_admin(m.from_user.id):
        return
    await send_text(bot, m.chat.id,
        "📘 Функции бота:\n"
        "• 🚫 Заблокированные сайты — управление черным списком доменов\n"
        "• ✅ Разрешенные IP — управление белым списком IP адресов\n"
        "• 📈 Статистика — анализ логов и статистика трафика\n"
        "• ⚙️ Настройки Squid — проверка и автоматическое исправление конфигурации\n"
        "• /backup — создание резервных копий списков\n"
        "• /restore — восстановление из резервных копий\n"
        "• /report — создание красивого HTML-отчета в стиле SARG\n"
        "• Автоматические отчеты о новых событиях каждый час"
    )

@dp.message(Command("id"))
async def cmd_id(m: Message):
    await m.answer(f"🪪 Ваш ID: `{m.from_user.id}`", parse_mode="Markdown")

@dp.message(Command("status"))
async def cmd_status(m: Message):
    if not is_admin(m.from_user.id):
        return
    code, out, err = run_cmd([SYSTEMCTL_BIN, "status", "squid"]) if SYSTEMCTL_BIN else (1, "", "systemctl not found")
    text = out or err or "(пусто)"
    await send_text(bot, m.chat.id, f"🧩 systemctl status squid:\n{text}")

@dp.message(Command("check_config"))
async def cmd_check_config(m: Message):
    if not is_admin(m.from_user.id):
        return
    res = scan_squid_conf(SQUID_CONF)
    lines = confcheck_summary_lines(res)
    await send_text(bot, m.chat.id, "\n".join(lines))

@dp.message(Command("patch_config"))
async def cmd_patch_config(m: Message):
    if not is_admin(m.from_user.id):
        return
    changed, message = patch_squid_conf(SQUID_CONF)
    await m.answer(f"✍️ {message}")
    if changed:
        ok, r = squid_reload()
        await m.answer(r)

@dp.message(Command("backup"))
async def cmd_backup(m: Message):
    if not is_admin(m.from_user.id):
        return
    try:
        if DENY_FILE.exists():
            shutil.copy2(DENY_FILE, DENY_FILE.with_suffix(".bak"))
        if WHITE_FILE.exists():
            shutil.copy2(WHITE_FILE, WHITE_FILE.with_suffix(".bak"))
        await m.answer("💾 Резервные копии созданы (.bak).")
    except Exception as e:
        await m.answer(f"❌ Ошибка бэкапа: {e}")

@dp.message(Command("report"))
async def cmd_report(m: Message):
    if not is_admin(m.from_user.id):
        return
    try:
        await m.answer("🔄 Создание HTML-отчета...")

        if not ACCESS_LOG.exists():
            return await m.answer("⚠️ Файл логов access.log не найден.")

        with ACCESS_LOG.open("r", encoding="utf-8", errors="ignore") as f:
            tail = f.readlines()[-5000:]
        stats = parse_access_lines(tail)

        blacklist_count = len(read_lines(DENY_FILE))
        whitelist_count = len(read_lines(WHITE_FILE))

        report_path = Path(save_html_report(stats, blacklist_count, whitelist_count))
        caption_lines = [
            "📑 HTML-отчёт Squid",
            f"Файл сохранён: {report_path}",
            "",
            f"Всего запросов: {stats.total}",
            f"Заблокировано: {stats.denied}",
            f"Блокируемых сайтов: {blacklist_count}",
            f"Разрешённых IP: {whitelist_count}",
        ]
        document = FSInputFile(str(report_path), filename=report_path.name)
        await m.answer_document(document=document, caption="\n".join(caption_lines))
    except Exception as e:
        await m.answer(f"❌ Ошибка создания отчёта: {e}")

@dp.message(Command("restore"))
async def cmd_restore(m: Message):
    if not is_admin(m.from_user.id):
        return
    try:
        changed = False
        if DENY_FILE.with_suffix(".bak").exists():
            shutil.copy2(DENY_FILE.with_suffix(".bak"), DENY_FILE)
            changed = True
        if WHITE_FILE.with_suffix(".bak").exists():
            shutil.copy2(WHITE_FILE.with_suffix(".bak"), WHITE_FILE)
            changed = True
        if changed:
            ok, r = squid_reload()
            await m.answer(f"♻️ Восстановлено из .bak\n{r}")
        else:
            await m.answer("ℹ️ .bak файлов не найдено.")
    except Exception as e:
        await m.answer(f"❌ Ошибка восстановления: {e}")


@dp.message(F.text == "🏢 Отделы")
async def departments_menu(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state is not None:
        await m.answer("⚠️ Завершите текущую операцию ввода или нажмите кнопку «Отмена».")
        return
    await state.clear()
    text, kb, _ = build_departments_overview()
    await m.answer(text, reply_markup=kb)


@dp.callback_query(F.data == "dept:list")
async def cb_departments_list(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    text, kb, _ = build_departments_overview()
    with contextlib.suppress(Exception):
        await c.message.edit_text(text, reply_markup=kb)
    await c.answer()


@dp.callback_query(F.data.startswith("dept:"))
async def cb_department_action(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Отдел не найден", show_alert=True)
    parts = c.data.split(":")
    if len(parts) < 3:
        return await c.answer()
    _, slug, action = parts[:3]
    department = department_by_slug(slug)
    if not department:
        return await c.answer("????? ?? ??????", show_alert=True)
    app_cfg = load_app_config()

    def with_status(text: str, messages: List[str]) -> str:
        if not messages:
            return text
        status_text = "\n".join(messages)
        return f"{text}\n\n{status_text}"


    if action == "menu":
        text = department_detail_text(app_cfg, department)
        kb = department_menu_keyboard(department)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()

    if action == "policy":
        if len(parts) >= 5 and parts[3] == "set":
            mode = parts[4]
            if mode == "allow":
                new_cfg = set_department_policy(department, POLICY_ALLOW_ALL_EXCEPT)
            elif mode == "deny":
                new_cfg = set_department_policy(department, POLICY_DENY_ALL_EXCEPT)
            else:
                new_cfg = clear_department_override(department)
            ok, messages = apply_config_and_reload(new_cfg)
            updated = load_app_config()
            text = with_status(department_detail_text(updated, department), messages)
            kb = department_menu_keyboard(department)
            with contextlib.suppress(Exception):
                await c.message.edit_text(text, reply_markup=kb)
            return await c.answer("??????" if ok else "??????", show_alert=not ok)

        profile = resolve_department_profile(department, app_cfg=app_cfg)
        lines = [
            f"⚙️ Политика отдела {department}",
            "",
            f"Текущий режим: {policy_label(profile.policy)}",
            format_profile_groups(profile),
            "",
            "Выберите тип политики для этого отдела."
        ]
        text = "\n".join(lines)
        slug_cb = department_slug(department)
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Разрешено всё, кроме выбранных", callback_data=f"dept:{slug_cb}:policy:set:allow")],
            [InlineKeyboardButton(text="Запрещено всё, кроме выбранных", callback_data=f"dept:{slug_cb}:policy:set:deny")],
            [InlineKeyboardButton(text="♻️ Наследовать глобальные настройки", callback_data=f"dept:{slug_cb}:policy:set:inherit")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data=f"dept:{slug_cb}:menu")],
        ])
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()

    if action == "groups":
        text = department_groups_text(app_cfg, department)
        kb = department_groups_keyboard(department, app_cfg)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()

    if action == "group" and len(parts) >= 4:
        group_key = parts[3]
        profile = resolve_department_profile(department, app_cfg=app_cfg)
        current_active, _, _ = profile_group_state(profile, group_key)
        new_cfg = set_department_group(department, group_key, not current_active)
        ok, messages = apply_config_and_reload(new_cfg)
        updated = load_app_config()
        text = with_status(department_groups_text(updated, department), messages)
        kb = department_groups_keyboard(department, updated)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

    if action == "reset":
        new_cfg = clear_department_override(department)
        ok, messages = apply_config_and_reload(new_cfg)
        updated = load_app_config()
        text = with_status(department_detail_text(updated, department), messages)
        kb = department_menu_keyboard(department)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

    if action == "ips":
        page = 1
        if len(parts) >= 5 and parts[3] == "page":
            try:
                page = int(parts[4])
            except ValueError:
                page = 1
        text, kb = department_ips_view(app_cfg, department, page=page)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()

    if action == "ipadd":
        page = 1
        if len(parts) >= 4:
            try:
                page = int(parts[3])
            except ValueError:
                page = 1
        await state.set_state(Form.WAIT_DEPT_IP_ADD)
        await state.update_data(
            department=department,
            origin_chat_id=c.message.chat.id,
            origin_message_id=c.message.message_id,
            origin_page=page,
        )
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="❌ Отмена", callback_data=f"dept:{slug}:cancel")]
        ])
        prompt = f"?❌ Отмена? IP ????? ??❌ Отмена?? ??❌ Отмена {department}:"
        with contextlib.suppress(Exception):
            await c.message.edit_text(prompt, reply_markup=kb)
        return await c.answer()

    if action == "ipdel":
        page = 1
        if len(parts) >= 4:
            try:
                page = int(parts[3])
            except ValueError:
                page = 1
        await state.set_state(Form.WAIT_DEPT_IP_REMOVE)
        await state.update_data(
            department=department,
            origin_chat_id=c.message.chat.id,
            origin_message_id=c.message.message_id,
            origin_page=page,
        )
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="❌ Отмена", callback_data=f"dept:{slug}:cancel")]
        ])
        prompt = f"?❌ Отмена? IP ?????, Готово➕ Новая группа??? ??❌ Отмена {department}:"
        with contextlib.suppress(Exception):
            await c.message.edit_text(prompt, reply_markup=kb)
        return await c.answer()

    if action == "cancel":
        data = await state.get_data()
        page = data.get("origin_page", 1)
        await state.clear()
        text, kb = department_ips_view(app_cfg, department, page=page)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer("Отменено")

    if action == "ipremove" and len(parts) >= 4:
        token = parts[3]
        try:
            ip = ip_from_token(token)
        except Exception:
            return await c.answer("Некорректный IP", show_alert=True)
        success, value = remove_department_ip(department, ip)
        if not success:
            return await c.answer(value, show_alert=True)
        ok, messages = apply_config_and_reload()
        status = [f"IP {value} удалён из отдела."] + messages
        await update_department_ips_message(c.message.chat.id, c.message.message_id, department, status_lines=status)
        return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

    if action == "ip" and len(parts) >= 5:
        token = parts[3]
        ip_action = parts[4]
        try:
            ip = ip_from_token(token)
        except Exception:
            return await c.answer("ГотовоГотово IP", show_alert=True)
        department_name = department

        if ip_action == "menu":
            text = ip_detail_text(app_cfg, ip, department_name)
            kb = ip_menu_keyboard(ip, department_name)
            with contextlib.suppress(Exception):
                await c.message.edit_text(text, reply_markup=kb)
            return await c.answer()

        if ip_action == "policy":
            if len(parts) >= 7 and parts[5] == "set":
                mode = parts[6]
                if mode == "allow":
                    new_cfg = set_ip_policy(ip, POLICY_ALLOW_ALL_EXCEPT)
                elif mode == "deny":
                    new_cfg = set_ip_policy(ip, POLICY_DENY_ALL_EXCEPT)
                else:
                    new_cfg = clear_ip_override(ip)
                ok, messages = apply_config_and_reload(new_cfg)
                updated = load_app_config()
                text = with_status(ip_detail_text(updated, ip, department_name), messages)
                kb = ip_menu_keyboard(ip, department_name)
                with contextlib.suppress(Exception):
                    await c.message.edit_text(text, reply_markup=kb)
                    return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

            text = ip_policy_text(ip, department_name)
            kb = ip_policy_keyboard(ip, department_name)
            with contextlib.suppress(Exception):
                await c.message.edit_text(text, reply_markup=kb)
            return await c.answer()

        if ip_action == "groups":
            text = ip_groups_text(app_cfg, ip, department_name)
            kb = ip_groups_keyboard(ip, department_name, app_cfg)
            with contextlib.suppress(Exception):
                await c.message.edit_text(text, reply_markup=kb)
            return await c.answer()

        if ip_action == "reset":
            new_cfg = clear_ip_override(ip)
            ok, messages = apply_config_and_reload(new_cfg)
            updated = load_app_config()
            text = with_status(ip_detail_text(updated, ip, department_name), messages)
            kb = ip_menu_keyboard(ip, department_name)
            with contextlib.suppress(Exception):
                await c.message.edit_text(text, reply_markup=kb)
            return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

        if ip_action == "group" and len(parts) >= 6:
            group_key = parts[5]
            profile = resolve_ip_profile(ip, department=department_name, app_cfg=app_cfg)
            current_active, _, _ = profile_group_state(profile, group_key)
            new_cfg = set_ip_group(ip, department_name, group_key, not current_active)
            ok, messages = apply_config_and_reload(new_cfg)
            updated = load_app_config()
            text = with_status(ip_groups_text(updated, ip, department_name), messages)
            kb = ip_groups_keyboard(ip, department_name, updated)
            with contextlib.suppress(Exception):
                await c.message.edit_text(text, reply_markup=kb)
            return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

        return await c.answer()

    return await c.answer()



@dp.callback_query(F.data == "ip:all")
async def cb_ip_overrides(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    text, kb, _ = build_ip_overrides_overview()
    with contextlib.suppress(Exception):
        await c.message.edit_text(text, reply_markup=kb)
    await c.answer()


@dp.callback_query(F.data.startswith("ip:all:"))
async def cb_ip_overrides_page(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    parts = c.data.split(":")
    page = 1
    if len(parts) >= 3 and parts[2] == "page" and len(parts) >= 4:
        try:
            page = int(parts[3])
        except ValueError:
            page = 1
    text, kb, _ = build_ip_overrides_overview(page=page)
    with contextlib.suppress(Exception):
        await c.message.edit_text(text, reply_markup=kb)
    await c.answer()


@dp.callback_query(F.data.startswith("ip:view:"))
async def cb_ip_detail(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("??❌ Отмена?", show_alert=True)
    parts = c.data.split(":")
    if len(parts) < 5:
        return await c.answer()
    _, _, dept_slug, token, action = parts[:5]
    department = department_by_slug(dept_slug) if dept_slug not in {"", "-"} else None
    try:
        ip = ip_from_token(token)
    except Exception:
        return await c.answer("ГотовоГотово IP", show_alert=True)
    app_cfg = load_app_config()

    def with_status(text: str, messages: List[str]) -> str:
        if not messages:
            return text
        status_text = "\n".join(messages)
        return f"{text}\n\n{status_text}"


    if action == "menu":
        text = ip_detail_text(app_cfg, ip, department)
        kb = ip_menu_keyboard(ip, department)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()

    if action == "policy":
        if len(parts) >= 7 and parts[5] == "set":
            mode = parts[6]
            if mode == "allow":
                new_cfg = set_ip_policy(ip, POLICY_ALLOW_ALL_EXCEPT)
            elif mode == "deny":
                new_cfg = set_ip_policy(ip, POLICY_DENY_ALL_EXCEPT)
            else:
                new_cfg = clear_ip_override(ip)
            ok, messages = apply_config_and_reload(new_cfg)
            updated = load_app_config()
            text = with_status(ip_detail_text(updated, ip, department), messages)
            kb = ip_menu_keyboard(ip, department)
            with contextlib.suppress(Exception):
                await c.message.edit_text(text, reply_markup=kb)
            return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

        text = ip_policy_text(ip, department)
        kb = ip_policy_keyboard(ip, department)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()

    if action == "groups":
        text = ip_groups_text(app_cfg, ip, department)
        kb = ip_groups_keyboard(ip, department, app_cfg)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()

    if action == "reset":
        new_cfg = clear_ip_override(ip)
        ok, messages = apply_config_and_reload(new_cfg)
        updated = load_app_config()
        text = with_status(ip_detail_text(updated, ip, department), messages)
        kb = ip_menu_keyboard(ip, department)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

    if action == "group" and len(parts) >= 6:
        group_key = parts[5]
        profile = resolve_ip_profile(ip, department=department, app_cfg=app_cfg)
        current_active, _, _ = profile_group_state(profile, group_key)
        new_cfg = set_ip_group(ip, department, group_key, not current_active)
        ok, messages = apply_config_and_reload(new_cfg)
        updated = load_app_config()
        text = with_status(ip_groups_text(updated, ip, department), messages)
        kb = ip_groups_keyboard(ip, department, updated)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer("Готово" if ok else "Готово", show_alert=not ok)

    return await c.answer()
def blacklist_management_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Добавить", callback_data="black:add"), InlineKeyboardButton(text="➖ Удалить", callback_data="black:del")],
        [InlineKeyboardButton(text="📋 Показать список", callback_data="black:edit")],
        [InlineKeyboardButton(text="🏠 Главное меню", callback_data="main")],
    ])


def groups_overview_text(config: BotConfig, counts: Dict[str, int]) -> str:
    cfg = config.normalized()
    lines = [
        "🗃️ Управление группами доменов",
        f"Текущая политика: {POLICY_CHOICES.get(cfg.policy, cfg.policy)}",
        "",
    ]
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        enabled = group_enabled(cfg, key)
        count = counts.get(key, 0)
        if cfg.policy == POLICY_ALLOW_ALL_EXCEPT:
            status = "блокируется" if enabled else "разрешён"
            icon = "⛔️" if enabled else "✅"
        else:
            status = "разрешён" if enabled else "блокируется"
            icon = "✅" if enabled else "⛔️"
        lines.append(f"{icon} {group.title} — {status} ({count} записей)")
    lines.append("")
    lines.append("Выберите группу для управления или измените политику доступа.")
    return "\n".join(lines)


def groups_overview_keyboard(config: BotConfig, counts: Dict[str, int]) -> InlineKeyboardMarkup:
    rows: List[List[InlineKeyboardButton]] = []
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        text = f"{group.title} ({counts.get(key, 0)})"
        rows.append([InlineKeyboardButton(text=text, callback_data=f"group:{key}:menu")])
    rows.append([InlineKeyboardButton(text="➕ Новая группа", callback_data="groups:new")])
    if any(not DENY_GROUPS[key].builtin for key in DENY_GROUP_ORDER):
        rows.append([InlineKeyboardButton(text="🗑️ Удалить группу", callback_data="groups:delete")])
    rows.append([InlineKeyboardButton(text="⚙️ Изменить политику", callback_data="groups:policy")])
    rows.append([InlineKeyboardButton(text="🔄 Обновить", callback_data="groups:refresh")])
    rows.append([InlineKeyboardButton(text="🏠 Главное меню", callback_data="main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)



def build_groups_overview(config: Optional[BotConfig] = None) -> Tuple[str, InlineKeyboardMarkup, BotConfig]:
    cfg = (config or load_bot_config()).normalized()
    counts = group_counts()
    text = groups_overview_text(cfg, counts)
    kb = groups_overview_keyboard(cfg, counts)
    return text, kb, cfg


def group_detail_text(config: BotConfig, group_key: str) -> str:
    cfg = config.normalized()
    group = DENY_GROUPS[group_key]
    items = read_group_items(group_key)
    enabled = group_enabled(cfg, group_key)
    if cfg.policy == POLICY_ALLOW_ALL_EXCEPT:
        status = "блокируется" if enabled else "разрешён"
    else:
        status = "разрешён" if enabled else "блокируется"
    lines = [
        f"🗃️ {group.title}",
        f"Политика: {POLICY_CHOICES.get(cfg.policy, cfg.policy)}",
        f"Статус: {status}",
        f"Записей: {len(items)}",
        "",
        "Используйте кнопки ниже для работы с этой группой.",
    ]
    return "\n".join(lines)


def group_menu_keyboard(config: BotConfig, group_key: str) -> InlineKeyboardMarkup:
    cfg = config.normalized()
    enabled = group_enabled(cfg, group_key)
    if cfg.policy == POLICY_ALLOW_ALL_EXCEPT:
        toggle_text = "🔄 Разрешить группу" if enabled else "🛑 Блокировать группу"
    else:
        toggle_text = "🔄 Удалить из разрешённых" if enabled else "🔓 Разрешить группу"
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📄 Показать список", callback_data=f"group:{group_key}:list:1")],
        [InlineKeyboardButton(text="➕ Добавить запись", callback_data=f"group:{group_key}:add")],
        [InlineKeyboardButton(text="➖ Удалить запись", callback_data=f"group:{group_key}:remove")],
        [InlineKeyboardButton(text=toggle_text, callback_data=f"group:{group_key}:toggle")],
        [InlineKeyboardButton(text="⬅️ К списку групп", callback_data="groups:back")],
    ])


@dp.message(F.text == "🚫 Сайты")
async def groups_menu(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state is not None:
        await m.answer("⚠️ Завершите текущую операцию ввода или нажмите кнопку «Отмена».")
        return
    await state.clear()
    text, kb, _ = build_groups_overview()
    await m.answer(text, reply_markup=kb)


@dp.callback_query(F.data.in_({"groups:refresh", "groups:back"}))
async def cb_groups_refresh(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    text, kb, _ = build_groups_overview()
    with contextlib.suppress(Exception):
        await c.message.edit_text(text, reply_markup=kb)
    await c.answer()


@dp.callback_query(F.data == "groups:new")
async def cb_groups_new(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    await state.set_state(Form.WAIT_NEW_GROUP_TITLE)
    await state.update_data(
        origin_chat_id=c.message.chat.id,
        origin_message_id=c.message.message_id,
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Подтвердить", callback_data="groups:new:skipdesc")],
        [InlineKeyboardButton(text="❌ Отмена", callback_data="groups:cancel")]
    ])
    prompt = "✍️ Введите название новой группы и нажмите «Подтвердить»:"

    with contextlib.suppress(Exception):
        await c.message.edit_text(prompt, reply_markup=kb)
    await c.answer()


@dp.callback_query(F.data == "groups:cancel")
async def cb_groups_cancel(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    data = await state.get_data()
    origin_chat = data.get("origin_chat_id", c.message.chat.id)
    origin_message = data.get("origin_message_id", c.message.message_id)
    await state.clear()
    await update_groups_overview_message(origin_chat, origin_message)
    await c.answer("Отменено")


@dp.callback_query(F.data == "groups:new:skipdesc")
async def cb_groups_skip_description(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)

    data = await state.get_data()
    title = str(data.get("new_group_title", "")).strip()
    if not title:
        return await c.answer("Сначала введите название.", show_alert=True)

    origin_chat = data.get("origin_chat_id", c.message.chat.id)
    origin_message = data.get("origin_message_id")

    try:
        group = create_domain_group(title, "")
        ok, messages = apply_config_and_reload()
        status = [f"✅ Группа «{group.title}» создана."] + messages
        await update_groups_overview_message(origin_chat, origin_message, status_lines=status)
        await state.clear()
        return await c.answer("Группа создана", show_alert=not ok)
    except Exception as e:
        await state.clear()
        return await c.answer(f"❌ Ошибка: {e}", show_alert=True)



@dp.callback_query(F.data == "groups:delete")
async def cb_groups_delete(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    await state.clear()
    removable = [g for g in DENY_GROUP_DEFINITIONS if not g.builtin]
    if not removable:
        return await c.answer("Пользовательских групп нет", show_alert=True)
    rows = [[InlineKeyboardButton(text=g.title, callback_data=f"group-remove:{g.key}:ask")] for g in removable]
    rows.append([InlineKeyboardButton(text="⬅️ Назад", callback_data="groups:back")])
    kb = InlineKeyboardMarkup(inline_keyboard=rows)
    with contextlib.suppress(Exception):
        await c.message.edit_text("Выберите группу для удаления:", reply_markup=kb)
    await c.answer()


@dp.callback_query(F.data.startswith("group-remove:"))
async def cb_group_remove(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    parts = c.data.split(":")
    if len(parts) < 3:
        return await c.answer()
    _, group_key, action = parts[:3]
    group = DENY_GROUPS.get(group_key)
    if not group:
        return await c.answer("Группа не найдена", show_alert=True)
    if action == "ask":
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="✅ Удалить", callback_data=f"group-remove:{group_key}:confirm")],
            [InlineKeyboardButton(text="⬅️ Назад", callback_data="groups:delete")],
        ])
        prompt = f"Удалить группу «{group.title}»?"
        with contextlib.suppress(Exception):
            await c.message.edit_text(prompt, reply_markup=kb)
        return await c.answer()
    if action == "confirm":
        success, title = delete_domain_group(group_key)
        if not success:
            return await c.answer(title, show_alert=True)
        ok, messages = apply_config_and_reload()
        status = [f"Группа «{title}» удалена."] + messages
        await update_groups_overview_message(c.message.chat.id, c.message.message_id, status_lines=status)
        return await c.answer("Готово" if ok else "Ошибка", show_alert=not ok)
    return await c.answer()


@dp.callback_query(F.data == "groups:policy")
async def cb_groups_policy(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    text = (
        "⚙️ Выберите новую политику доступа:\n\n"
        "• Разрешено всё, кроме выбранных групп — сайты из активных групп блокируются.\n"
        "• Запрещено всё, кроме выбранных групп — доступ открыт только к отмеченным группам."
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Разрешено всё, кроме выбранных", callback_data="policy:set:allow")],
        [InlineKeyboardButton(text="Запрещено всё, кроме выбранных", callback_data="policy:set:deny")],
        [InlineKeyboardButton(text="⬅️ К списку групп", callback_data="groups:back")],
    ])
    with contextlib.suppress(Exception):
        await c.message.edit_text(text, reply_markup=kb)
    await c.answer()


@dp.callback_query(F.data.startswith("policy:set:"))
async def cb_policy_set(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    _, _, value = c.data.split(":", 2)
    new_policy = POLICY_ALLOW_ALL_EXCEPT if value == "allow" else POLICY_DENY_ALL_EXCEPT
    try:
        config = set_policy(new_policy)
    except ValueError as e:
        await c.answer(str(e), show_alert=True)
        return
    ok, messages = apply_config_and_reload()
    text, kb, _ = build_groups_overview(config)
    if messages:
        status_text = "\n".join(messages)
        text = f"{text}\n\n{status_text}"
    with contextlib.suppress(Exception):
        await c.message.edit_text(text, reply_markup=kb)
    await c.answer("Готово" if ok else "Ошибка", show_alert=not ok)


@dp.callback_query(F.data.startswith("group:"))
async def cb_group_action(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    parts = c.data.split(":")
    if len(parts) < 3:
        return await c.answer()
    _, group_key, action = parts[:3]
    if group_key not in DENY_GROUPS:
        return await c.answer("Неизвестная группа", show_alert=True)
    if action == "menu":
        config = load_bot_config()
        text = group_detail_text(config, group_key)
        kb = group_menu_keyboard(config, group_key)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()
    if action == "toggle":
        config = toggle_group_enabled(group_key)
        ok, messages = apply_config_and_reload()
        text = group_detail_text(config, group_key)
        if messages:
            status_text = "\n".join(messages)
            text = f"{text}\n\n{status_text}"
        kb = group_menu_keyboard(config, group_key)
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer("Готово" if ok else "Ошибка", show_alert=not ok)
    if action in {"add", "remove"}:
        await state.set_state(Form.WAIT_GROUP_VALUE)
        await state.update_data(
            group=group_key,
            action=action,
            origin_chat_id=c.message.chat.id,
            origin_message_id=c.message.message_id,
        )
        group_title = DENY_GROUPS[group_key].title
        if action == "add":
            prompt = f"✍️ Введите домен или шаблон для добавления в группу «{group_title}»:"
        else:
            prompt = f"✍️ Введите домен для удаления из группы «{group_title}»:"
        await c.message.answer(prompt)

        return await c.answer()
    if action == "list":
        page = 1
        if len(parts) >= 4:
            with contextlib.suppress(ValueError):
                page = int(parts[3])
        await show_group_list(c, group_key, page)
        return
    return await c.answer()



async def show_group_list(c: CallbackQuery, group_key: str, page: int = 1):
    items = read_group_items(group_key)
    if not items:
        text = "📄 Список пуст."
        kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="⬅️ Назад", callback_data=f"group:{group_key}:menu")]])
        with contextlib.suppress(Exception):
            await c.message.edit_text(text, reply_markup=kb)
        return await c.answer()
    subset, total_pages = slice_page(items, page)
    lines = [
        f"📄 {DENY_GROUPS[group_key].title}",
        f"Страница {page}/{total_pages}",
        "",
    ]
    lines.extend(subset)
    text = "\n".join(lines)
    kb = list_with_delete_buttons(f"grpdel:{group_key}", items, page)
    kb.inline_keyboard.append([InlineKeyboardButton(text="⬅️ Назад", callback_data=f"group:{group_key}:menu")])
    with contextlib.suppress(Exception):
        await c.message.edit_text(text, reply_markup=kb)
    await c.answer()


@dp.callback_query(F.data.startswith("grpdel:"))
async def cb_group_delete(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    parts = c.data.split(":")
    if len(parts) < 3:
        return await c.answer()
    _, group_key, action = parts[:3]
    if group_key not in DENY_GROUPS:
        return await c.answer("Неизвестная группа", show_alert=True)
    if action == "del":
        value = ":".join(parts[3:])
        items = read_group_items(group_key)
        if value in items:
            items.remove(value)
            write_group_items(group_key, unique_sorted(items))
            ok, msg = squid_reload()
            await c.message.answer(msg if ok else f"⚠️ Ошибка перезагрузки: {msg}")
        else:
            return await c.answer("Нет в списке", show_alert=True)
        await show_group_list(c, group_key, page=1)
        return
    if action == "p":
        try:
            page = int(parts[3])
        except (ValueError, IndexError):
            page = 1
        await show_group_list(c, group_key, page)
        return
    if action == "refresh":
        await show_group_list(c, group_key, page=1)
        return
    await c.answer()


@dp.message(Form.WAIT_GROUP_VALUE)
async def handle_group_value(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    data = await state.get_data()
    group_key = data.get("group")
    action = data.get("action")
    origin_chat_id = data.get("origin_chat_id")
    origin_message_id = data.get("origin_message_id")
    if group_key not in DENY_GROUPS or action not in {"add", "remove"}:
        await state.clear()
        return await m.answer("⚠️ Нет активной операции.")
    raw_value = m.text.strip()
    if not raw_value:
        return await m.answer("⚠️ Введите непустое значение.")
    entry = normalize_domain(raw_value)
    if not entry:
        return await m.answer("⚠️ Не удалось распознать значение.")
    if action == "add":
        items = read_group_items(group_key)
        if entry.lower() in {x.lower() for x in items}:
            await m.answer("⚠️ Такая запись уже существует.")
        else:
            items.append(entry)
            write_group_items(group_key, unique_sorted(items))
            ok, msg = squid_reload()
            await m.answer(f"✅ Добавлено: `{entry}`", parse_mode="Markdown")
            if not ok:
                await m.answer(msg)
    else:
        items = read_group_items(group_key)
        lower_map = {x.lower(): x for x in items}
        target = lower_map.get(entry.lower())
        if not target:
            await m.answer("⚠️ Запись не найдена.")
        else:
            items.remove(target)
            write_group_items(group_key, unique_sorted(items))
            ok, msg = squid_reload()
            await m.answer(f"✅ Удалено: `{target}`", parse_mode="Markdown")
            if not ok:
                await m.answer(msg)
    await state.clear()
    if origin_chat_id and origin_message_id:
        config = load_bot_config()
        text = group_detail_text(config, group_key)
        kb = group_menu_keyboard(config, group_key)
        with contextlib.suppress(Exception):
            await bot.edit_message_text(text, origin_chat_id, origin_message_id, reply_markup=kb)

@dp.message(Form.WAIT_NEW_GROUP_TITLE)
async def handle_new_group_title(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    title = (m.text or "").strip()
    if not title:
        await m.answer("Введите корректное название группы.")
        return
    await state.update_data(new_group_title=title)
    data = await state.get_data()
    origin_chat = data.get("origin_chat_id", m.chat.id)
    origin_message = data.get("origin_message_id")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Сохранить без описания", callback_data="groups:new:skipdesc")],
        [InlineKeyboardButton(text="❌ Отмена", callback_data="groups:cancel")],
    ])
    prompt = "Введите описание группы (или '-' чтобы пропустить):"
    if origin_chat and origin_message:
        with contextlib.suppress(Exception):
            await bot.edit_message_text(prompt, origin_chat, origin_message, reply_markup=kb)
    else:
        await m.answer(prompt, reply_markup=kb)
    await state.set_state(Form.WAIT_NEW_GROUP_DESCRIPTION)


@dp.message(Form.WAIT_NEW_GROUP_DESCRIPTION)
async def handle_new_group_description(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return

    data = await state.get_data()
    title = str(data.get("new_group_title", "")).strip()
    if not title:
        await state.clear()
        return await m.answer("⚠️ Название группы не найдено.")

    description = (m.text or "").strip()
    if description in {"-", "—"}:
        description = ""

    origin_chat = data.get("origin_chat_id", m.chat.id)
    origin_message = data.get("origin_message_id")

    try:
        group = create_domain_group(title, description)
        ok, messages = apply_config_and_reload()
        status = [f"✅ Группа «{group.title}» создана."] + messages
        if origin_chat and origin_message:
            await update_groups_overview_message(origin_chat, origin_message, status_lines=status)
        else:
            overview_text, kb, _ = build_groups_overview()
            status_text = "\n".join(status)
            await m.answer(f"{overview_text}\n\n{status_text}", reply_markup=kb)
        await state.clear()
    except Exception as e:
        await state.clear()
        await m.answer(f"❌ Ошибка при создании группы: {e}")


@dp.message(Form.WAIT_DEPT_IP_ADD)
async def handle_department_ip_add(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    data = await state.get_data()
    department = data.get("department")
    if not department:
        await state.clear()
        await m.answer("?? ?❌ Отмена ?????.")
        return
    ip_value = (m.text or "").strip()
    success, message = add_department_ip(department, ip_value)
    if not success:
        await m.answer(f"?? {message}")
        return
    ok, reload_messages = apply_config_and_reload()
    status = [f"? IP {message} Готово?? ? ?????."] + reload_messages
    origin_chat = data.get("origin_chat_id", m.chat.id)
    origin_message = data.get("origin_message_id")
    page = data.get("origin_page", 1)
    if origin_chat and origin_message:
        await update_department_ips_message(origin_chat, origin_message, department, page=page, status_lines=status)
    else:
        app_cfg = load_app_config()
        base_text, kb = department_ips_view(app_cfg, department, page=page)
        status_text = "\n".join(status)
        await m.answer(f"{base_text}\n\n{status_text}", reply_markup=kb)
    await state.clear()


@dp.message(Form.WAIT_DEPT_IP_REMOVE)
async def handle_department_ip_remove(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    data = await state.get_data()
    department = data.get("department")
    if not department:
        await state.clear()
        await m.answer("?? ?❌ Отмена ?????.")
        return
    ip_value = (m.text or "").strip()
    success, message = remove_department_ip(department, ip_value)
    if not success:
        await m.answer(f"?? {message}")
        return
    ok, reload_messages = apply_config_and_reload()
    status = [f"??? IP {message} Готово ?❌ Отмена."] + reload_messages
    origin_chat = data.get("origin_chat_id", m.chat.id)
    origin_message = data.get("origin_message_id")
    page = data.get("origin_page", 1)
    if origin_chat and origin_message:
        await update_department_ips_message(origin_chat, origin_message, department, page=page, status_lines=status)
    else:
        app_cfg = load_app_config()
        base_text, kb = department_ips_view(app_cfg, department, page=page)
        status_text = "\n".join(status)
        await m.answer(f"{base_text}\n\n{status_text}", reply_markup=kb)
    await state.clear()

@dp.message(F.text == "✅ IP адреса")
async def whitelist_menu(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state is not None:
        await m.answer("⚠️ Завершите текущую операцию ввода или нажмите кнопку «Отмена».")
        return
    await state.clear()
    items = unique_sorted(read_lines(WHITE_FILE))
    summary = [
        "✅ Управление разрешёнными IP",
        f"Всего записей: {len(items)}",
        "",
        "Выберите действие:",
    ]
    await m.answer("\n".join(summary), reply_markup=whitelist_management_kb())

@dp.message(Form.WAIT_WHITE_ADD)
async def do_white_add(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    ip = m.text.strip()
    if not is_ip_or_cidr(ip):
        await m.answer("⚠️ Неверный формат IP адреса. Введите корректный IP или CIDR диапазон.")
        return
    items = unique_sorted(read_lines(WHITE_FILE))
    if ip in items:
        await m.answer("⚠️ IP адрес уже разрешен.")
    else:
        items.append(ip)
        atomic_write_lines(WHITE_FILE, items)
        ok, r = squid_reload()
        await m.answer(f"✅ IP адрес разрешен: `{ip}`", parse_mode="Markdown")
        if not ok:
            await m.answer(f"⚠️ Ошибка перезагрузки Squid: {r}")
    await state.clear()
    await m.answer("Операция завершена.", reply_markup=main_kb)


@dp.message(Form.WAIT_WHITE_DEL)
async def do_white_del(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    ip = m.text.strip()
    items = unique_sorted(read_lines(WHITE_FILE))
    if ip not in items:
        await m.answer("⚠️ IP адрес не разрешен.")
    else:
        items.remove(ip)
        atomic_write_lines(WHITE_FILE, items)
        ok, r = squid_reload()
        await m.answer(f"✅ IP адрес запрещен: `{ip}`", parse_mode="Markdown")
        if not ok:
            await m.answer(f"⚠️ Ошибка перезагрузки Squid: {r}")
    await state.clear()
    await m.answer("Операция завершена.", reply_markup=main_kb)


@dp.message(F.text == "📊 Статистика")
async def logs_menu(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state is not None:
        await m.answer("⚠️ Завершите текущую операцию ввода или нажмите кнопку «Отмена».")
        return
    if not ACCESS_LOG.exists():
        await m.answer("⚠️ Файл логов access.log не найден.")
        return
    try:
        with ACCESS_LOG.open("r", encoding="utf-8", errors="ignore") as f:
            tail = f.readlines()[-1000:]
        stats = parse_access_lines(tail)
    except Exception as e:
        await m.answer(f"⚠️ Ошибка чтения логов: {e}")
        return
    whitelist_count = len(read_lines(WHITE_FILE))
    counts = group_counts()
    overview = [
        "📊 Общая статистика системы",
        f"Всего запросов: {stats.total}",
        f"Заблокировано запросов: {stats.denied}",
        f"Всего записей в блокирующих группах: {sum(counts.values())}",
        f"Разрешённых IP: {whitelist_count}",
        "",
        "Группы доменов:",
    ]
    for key in DENY_GROUP_ORDER:
        group = DENY_GROUPS[key]
        overview.append(f"  • {group.title}: {counts.get(key, 0)}")
    overview.append("")
    overview.append("Выберите действие:")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔍 Поиск в логах", callback_data="log:search")],
        [InlineKeyboardButton(text="🔁 Обновить", callback_data="log:refresh")],
        [InlineKeyboardButton(text="📊 Детальная статистика", callback_data="log:full")],
        [InlineKeyboardButton(text="📄 Создать HTML-отчёт", callback_data="log:html")],
        [InlineKeyboardButton(text="🏠 Главное меню", callback_data="main")],
    ])
    await state.clear()
    await m.answer("\n".join(overview), reply_markup=kb)

@dp.callback_query(F.data == "log:refresh")
async def cb_log_refresh(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    with ACCESS_LOG.open("r", encoding="utf-8", errors="ignore") as f:
        tail = f.readlines()[-400:]
    stats = parse_access_lines(tail)
    text = fmt_stats(stats, top_n=10)
    await send_text(bot, c.message.chat.id, text)
    await c.answer("Обновлено")

@dp.callback_query(F.data == "log:search")
async def cb_log_search(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    await state.set_state(Form.WAIT_SEARCH)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Отмена", callback_data="cancel")]
    ])
    await c.message.answer("✍️ Введите ключевое слово для поиска в логах (домен, IP, пользователь и т.д.):", reply_markup=kb)
    await c.answer()

@dp.message(Form.WAIT_SEARCH)
async def do_log_search(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state != Form.WAIT_SEARCH:
        return
    q = m.text.strip().lower()
    if not ACCESS_LOG.exists():
        await state.clear()
        return await m.answer("⚠️ Файл логов access.log не найден.")
    res = []
    with ACCESS_LOG.open("r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            if q in line.lower():
                res.append(line.rstrip("\n"))
            if len(res) >= 300:
                break
    if not res:
        await m.answer("Ничего не найдено.")
    else:
        await send_text(bot, m.chat.id, "🔎 Найдено:\n" + "\n".join(res[:300]))
    await state.clear()
    await m.answer("Операция завершена.", reply_markup=main_kb)


@dp.message(F.text == "⚙️ Настройки")
async def conf_menu(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state is not None:
        await m.answer("⚠️ Завершите текущую операцию ввода или нажмите кнопку «Отмена».")
        return
    res = scan_squid_conf(SQUID_CONF)
    lines = confcheck_summary_lines(res)
    await send_text(bot, m.chat.id, "\n".join(lines))
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✍️ Автопатч", callback_data="conf:patch")],
        [InlineKeyboardButton(text="🔁 Перезагрузить Squid", callback_data="conf:reload")],
        [InlineKeyboardButton(text="📄 Проверить шаблон ERR_ACCESS_DENIED", callback_data="conf:tpl")],
    ])
    await m.answer("Доступные действия:", reply_markup=kb)

@dp.callback_query(F.data == "conf:patch")
async def cb_conf_patch(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    changed, message = patch_squid_conf(SQUID_CONF)
    await c.message.answer(f"✍️ {message}")
    if changed:
        ok, r = squid_reload()
        await c.message.answer(r)
    await c.answer("Ок")

@dp.callback_query(F.data == "conf:reload")
async def cb_conf_reload(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    ok, r = squid_reload()
    await c.message.answer(r)
    await c.answer("Ок")

@dp.callback_query(F.data == "conf:tpl")
async def cb_conf_tpl(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    if BLOCK_ERROR_TEMPLATE.exists():
        await c.message.answer(f"✅ Шаблон найден: {BLOCK_ERROR_TEMPLATE}")
    else:
        await c.message.answer(
            "⚠️ Шаблон не найден. Создайте файл:\n"
            f"{BLOCK_ERROR_TEMPLATE}\n\n"
            "Пример простого HTML:\n"
            "<html><head><meta charset='utf-8'><title>Доступ запрещён</title></head>"
            "<body style='font-family:Arial;background:#20232a;color:#61dafb;padding:40px;'>"
            "<h1 style='color:#ff4c4c'>🚫 Доступ запрещён</h1>"
            "<p>Сайт в корпоративном черном списке. Обратитесь в IT.</p>"
            "</body></html>"
        )
    await c.answer("Ок")

@dp.callback_query(F.data == "cancel")
async def cb_cancel(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    await state.clear()
    await c.message.edit_text("❌ Операция отменена.")
    await c.message.answer("Выберите действие из меню:", reply_markup=main_kb)
    await c.answer()

@dp.callback_query(F.data == "main")
async def cb_main_menu(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    await state.clear()
    await c.message.edit_text("🏠 Главное меню")
    await c.message.answer("Выберите действие:", reply_markup=main_kb)
    await c.answer()

@dp.callback_query(F.data == "white:add")
async def cb_white_add(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    await state.set_state(Form.WAIT_WHITE_ADD)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Отмена", callback_data="cancel")]
    ])
    await c.message.edit_text("✍️ Введите IP адрес или диапазон CIDR (например: 192.168.1.100 или 192.168.1.0/24):", reply_markup=kb)
    await c.answer()

@dp.callback_query(F.data == "white:del")
async def cb_white_del(c: CallbackQuery, state: FSMContext):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    await state.set_state(Form.WAIT_WHITE_DEL)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Отмена", callback_data="cancel")]
    ])
    await c.message.edit_text("✍️ Введите IP адрес для запрета:", reply_markup=kb)
    await c.answer()

@dp.callback_query(F.data == "black:edit")
async def cb_black_edit(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    items = unique_sorted(read_lines(DENY_FILE))
    if not items:
        await c.message.edit_text("🚫 Список заблокированных сайтов пуст.", reply_markup=blacklist_management_kb())
        return await c.answer()
    page = 1
    subset, total_pages = slice_page(items, page)
    text = f"🚫 Страница {page}/{total_pages} - Заблокированные сайты\n\n" + "\n".join(f"{i+1}. {item}" for i, item in enumerate(subset))
    kb = list_with_delete_buttons("blk", items, page)
    await c.message.edit_text(text, reply_markup=kb)
    await c.answer()

@dp.callback_query(F.data == "white:edit")
async def cb_white_edit(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    items = unique_sorted(read_lines(WHITE_FILE))
    if not items:
        await c.message.edit_text("✅ Список разрешенных IP пуст.", reply_markup=whitelist_management_kb())
        return await c.answer()
    page = 1
    subset, total_pages = slice_page(items, page)
    text = f"✅ Страница {page}/{total_pages} - Разрешенные IP\n\n" + "\n".join(f"{i+1}. {item}" for i, item in enumerate(subset))
    kb = list_with_delete_buttons("wht", items, page)
    await c.message.edit_text(text, reply_markup=kb)
    await c.answer()

@dp.callback_query(F.data == "log:full")
async def cb_log_full(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)
    
    if not ACCESS_LOG.exists():
        await c.message.edit_text("⚠️ Файл логов access.log не найден.")
        return await c.answer()
    
    try:
        with ACCESS_LOG.open("r", encoding="utf-8", errors="ignore") as f:
            tail = f.readlines()[-5000:]
        stats = parse_access_lines(tail)
        
        text = fmt_stats(stats, top_n=10)
        await send_text(bot, c.message.chat.id, text)
        
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔁 Обновить", callback_data="log:full")],
            [InlineKeyboardButton(text="🏠 Главное меню", callback_data="main")],
        ])
        await c.message.answer("Доступные действия:", reply_markup=kb)
    except Exception as e:
        await c.message.answer(f"❌ Ошибка чтения логов: {e}")
    await c.answer()

@dp.callback_query(F.data == "log:html")
async def cb_log_html(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет доступа", show_alert=True)

    try:
        await c.message.edit_text("🔄 Создание HTML-отчета...")

        if not ACCESS_LOG.exists():
            await c.message.edit_text("⚠️ Файл логов access.log не найден.")
            return await c.answer()

        with ACCESS_LOG.open("r", encoding="utf-8", errors="ignore") as f:
            tail = f.readlines()[-5000:]
        stats = parse_access_lines(tail)

        blacklist_count = len(read_lines(DENY_FILE))
        whitelist_count = len(read_lines(WHITE_FILE))

        report_path = Path(save_html_report(stats, blacklist_count, whitelist_count))
        caption_lines = [
            "📑 HTML-отчёт Squid",
            f"Файл сохранён: {report_path}",
            "",
            f"Всего запросов: {stats.total}",
            f"Заблокировано: {stats.denied}",
            f"Заблокированных сайтов: {blacklist_count}",
            f"Разрешённых IP: {whitelist_count}",
        ]
        document = FSInputFile(str(report_path), filename=report_path.name)

        await c.message.edit_text("✅ HTML-отчёт создан и отправлен файлом.")
        await c.message.answer_document(document=document, caption="\n".join(caption_lines))

        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔄 Создать ещё отчёт", callback_data="log:html")],
            [InlineKeyboardButton(text="🏠 Главное меню", callback_data="main")],
        ])
        await c.message.answer("Доступные действия:", reply_markup=kb)

    except Exception as e:
        await c.message.edit_text(f"❌ Ошибка создания отчёта: {e}")

    await c.answer()

@dp.message(F.text == "💾 Бэкап")
async def cmd_backup_new(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state is not None:
        await m.answer("⚠️ Завершите текущую операцию ввода или нажмите кнопку «Отмена».")
        return
    try:
        if DENY_FILE.exists():
            shutil.copy2(DENY_FILE, DENY_FILE.with_suffix(".bak"))
        if WHITE_FILE.exists():
            shutil.copy2(WHITE_FILE, WHITE_FILE.with_suffix(".bak"))
        await m.answer("💾 Резервные копии созданы (.bak).")
    except Exception as e:
        await m.answer(f"❌ Ошибка бэкапа: {e}")

@dp.message(F.text == "🔄 Восстановить")
async def cmd_restore_new(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state is not None:
        await m.answer("⚠️ Завершите текущую операцию ввода или нажмите кнопку «Отмена».")
        return
    try:
        changed = False
        if DENY_FILE.with_suffix(".bak").exists():
            shutil.copy2(DENY_FILE.with_suffix(".bak"), DENY_FILE)
            changed = True
        if WHITE_FILE.with_suffix(".bak").exists():
            shutil.copy2(WHITE_FILE.with_suffix(".bak"), WHITE_FILE)
            changed = True
        if changed:
            ok, r = squid_reload()
            await m.answer(f"♻️ Восстановлено из .bak\n{r}")
        else:
            await m.answer("ℹ️ .bak файлов не найдено.")
    except Exception as e:
        await m.answer(f"❌ Ошибка восстановления: {e}")


@dp.message(F.text.func(lambda t: isinstance(t, str) and len(t) <= 200 and not t.startswith("/")) & ~F.text.in_({
        "🚫 Сайты","✅ IP адреса","📊 Статистика","⚙️ Настройки",
        "💾 Бэкап","🔄 Восстановить"
    }))
async def maybe_search_black(m: Message, state: FSMContext):
    if not is_admin(m.from_user.id):
        return
    current_state = await state.get_state()
    if current_state is not None:
        return
    
    text = m.text.strip()
    if is_ip_or_cidr(text):
        await m.answer(f"💡 Обнаружен IP адрес: `{text}`\n\nИспользуйте раздел «✅ IP адреса» для управления.", parse_mode="Markdown")
        return
    elif is_domain_like(text):
        await m.answer(f"💡 Обнаружен домен: `{text}`\n\nИспользуйте раздел «🚫 Сайты» для управления.", parse_mode="Markdown")
        return
        
    q = text.lower()
    black = [x for x in read_lines(DENY_FILE) if q in x.lower()]
    white = [x for x in read_lines(WHITE_FILE) if q in x.lower()]
    if black:
        await send_text(bot, m.chat.id, "🔎 Найдено в заблокированных сайтах:\n" + "\n".join(black[:200]))
    if white:
        await send_text(bot, m.chat.id, "🔎 Найдено в разрешенных IP:\n" + "\n".join(white[:200]))
    if not black and not white:
        await m.answer("Ничего не найдено.")


async def periodic_report_task():
    await asyncio.sleep(5)
    while True:
        try:
            new_lines = tail_new_lines(ACCESS_LOG, TAIL_STATE_FILE)
            if new_lines:
                stats = parse_access_lines(new_lines)
                if stats.total > 0:
                    text = fmt_stats(stats, top_n=10)
                    for admin in ADMINS:
                        with contextlib.suppress(Exception):
                            await send_text(bot, admin, f"⏰ {now_str()} — новые события\n\n{text}")
        except Exception as e:
            for admin in ADMINS:
                with contextlib.suppress(Exception):
                    await bot.send_message(admin, f"⚠️ Ошибка фонового отчёта: {e}")
        await asyncio.sleep(PERIODIC_REPORT_INTERVAL)


async def on_startup():
    ensure_group_files()
    ensure_department_sources()
    if not WHITE_FILE.exists():
        atomic_write_lines(WHITE_FILE, [])
    save_app_config(load_app_config())

async def main():
    loop = asyncio.get_running_loop()
    for s in (signal.SIGINT, signal.SIGTERM):
        with contextlib.suppress(NotImplementedError):
            loop.add_signal_handler(s, loop.stop)

    asyncio.create_task(periodic_report_task())
    await on_startup()
    await dp.start_polling(bot)

if __name__ == "__main__":
    if not BOT_TOKEN or "PASTE_TELEGRAM_BOT_TOKEN_HERE" in BOT_TOKEN:
        print("✋ Необходимо указать BOT_TOKEN в начале файла.")
        sys.exit(1)
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        print("👋 Бот остановлен.")


