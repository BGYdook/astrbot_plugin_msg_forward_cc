import asyncio
import hashlib
import json
import os
import re
import secrets
import shutil
import ssl
import string
import tempfile
import time
from collections.abc import Awaitable, Callable
from pathlib import Path
from typing import TYPE_CHECKING
from urllib.parse import urlparse

import astrbot.api.star as star
from astrbot.api.event import filter, AstrMessageEvent
from astrbot.api.star import Context, Star
from astrbot.api import logger
from astrbot.api import AstrBotConfig

from astrbot.core.message.components import At, Plain, Image, Record, Video, File, Face
from astrbot.core.message.message_event_result import MessageEventResult

if TYPE_CHECKING:
    import discord

    from astrbot.core.platform.sources.discord.discord_platform_adapter import (
        DiscordPlatformAdapter,
    )
    from astrbot.core.platform.sources.discord.discord_platform_event import (
        DiscordPlatformEvent,
    )


# ------------------------
# 工具与数据路径
# ------------------------


# 远程媒体 Content-Type → 落盘后缀映射（自定义下载器据此确定临时文件后缀）
_MIME_EXT_MAP = {
    "image/jpeg": ".jpg",
    "image/png": ".png",
    "image/gif": ".gif",
    "image/webp": ".webp",
    "image/bmp": ".bmp",
    "image/svg+xml": ".svg",
    "audio/amr": ".amr",
    "audio/mpeg": ".mp3",
    "audio/mp3": ".mp3",
    "audio/wav": ".wav",
    "audio/x-wav": ".wav",
    "audio/silk": ".silk",
    "audio/ogg": ".ogg",
    "audio/flac": ".flac",
    "audio/mp4": ".m4a",
    "video/mp4": ".mp4",
    "video/mpeg": ".mpg",
    "video/quicktime": ".mov",
    "application/pdf": ".pdf",
    "application/zip": ".zip",
}

# 兜底：按组件类型确定后缀
_DEFAULT_MEDIA_EXT = {
    Image: ".jpg",
    Record: ".amr",
    Video: ".mp4",
    File: ".bin",
}

_VALID_URL_EXT = {
    ".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".svg",
    ".amr", ".mp3", ".wav", ".silk", ".ogg", ".flac", ".m4a",
    ".mp4", ".mov", ".mpg", ".mpeg", ".pdf", ".zip", ".bin",
}


def _comp_type_name(comp) -> str:
    """返回组件的可读类型名，用于日志与占位文本。"""
    return getattr(getattr(comp, "type", None), "value", None) or type(comp).__name__


# ------------------------
# 内容类型筛选（v0.5.0）
# ------------------------

# 全部可选内容类型（键 = 配置/命令中使用的标识，显示名用于日志与命令提示）
CONTENT_TYPES = {
    "plain": "文字",
    "image": "图片",
    "face": "表情",
    "record": "语音",
    "video": "视频",
    "file": "文件",
    "at": "@提及",
    "other": "其他",
}

# 别名 → 标准键（/mf content 命令解析与配置值兼容用）。
# 中文别名与 WebUI labels 显示名一致：配置里直接填中文（如 ["文字","表情"]）也能正确解析
_CONTENT_TYPE_ALIASES = {
    "plain": "plain", "text": "plain", "文字": "plain",
    "image": "image", "img": "image", "图片": "image",
    "face": "face", "sticker": "face", "emoji": "face", "表情": "face",
    "record": "record", "voice": "record", "语音": "record",
    "video": "video", "视频": "video",
    "file": "file", "文件": "file",
    "at": "at", "mention": "at", "@提及": "at", "艾特": "at",
    "other": "other", "其他": "other",
}


def _comp_content_type(comp) -> str:
    """返回单个消息组件对应的内容类型键（CONTENT_TYPES 之一）。

    用于内容类型筛选：判断该组件是否属于规则选中的转发类型。
    AtAll 继承自 At，一并归入 at。其余未显式分类的组件归入 other。
    注意：「表情」仅指 QQ 内置表情（Face 组件）；收藏的表情/表情包以图片形式
    到达，归入「图片」类型（不同协议端上报形态不一致，无法稳定区分，不重分类）。"""
    if isinstance(comp, Plain):
        return "plain"
    if isinstance(comp, Image):
        return "image"
    if isinstance(comp, Face):
        return "face"
    if isinstance(comp, Record):
        return "record"
    if isinstance(comp, Video):
        return "video"
    if isinstance(comp, File):
        return "file"
    if isinstance(comp, At):
        return "at"
    return "other"


def _content_types_for(rule: dict, config) -> set:
    """解析某条规则生效的内容类型集合。

    规则级 content_types 非空时用它；为空/缺失时继承全局 default_content_types。
    全局默认全选（与旧版行为一致）。返回 set（去重、忽略非法键）。"""
    allowed = rule.get("content_types")
    if not allowed:
        allowed = config.get("default_content_types")
    if not allowed:
        return set(CONTENT_TYPES.keys())
    if isinstance(allowed, str):
        allowed = [x.strip() for x in allowed.split(",") if x.strip()]
    result = set()
    for item in allowed:
        key = _CONTENT_TYPE_ALIASES.get(str(item).strip().lower())
        if key:
            result.add(key)
    return result or set(CONTENT_TYPES.keys())


def _filter_chain_by_types(chain, allowed: set) -> list:
    """按内容类型集合过滤消息链，仅保留类型命中的组件。

    返回新链；若全部组件都被过滤则返回空列表（调用方据此跳过转发）。"""
    if not chain:
        return chain
    return [comp for comp in chain if _comp_content_type(comp) in allowed]


def _should_attach_header(rule: dict, allowed: set) -> bool:
    """判断是否前置文字形式的来源信息头。

    规则 hide_header 为 true 时不前置；否则仅当「文字」在选中类型中才前置——
    只转发图片/视频等纯媒体时，消息里不含任何文字，来源头也不附带。"""
    if rule.get("hide_header", False):
        return False
    return "plain" in allowed


def _extract_remote_url(comp) -> str | None:
    """返回组件引用的远程 http(s) URL；本地文件 / base64 / data URI 返回 None。

    注意：File 组件的 `.file` 是 property，在异步上下文访问会触发同步下载并报
    警告，因此对 File 只检查 `.url` 与 `.file_`。
    """
    url = getattr(comp, "url", None)
    if isinstance(url, str) and url.startswith(("http://", "https://")):
        return url
    if isinstance(comp, File):
        file_ref = getattr(comp, "file_", None)
    else:
        file_ref = getattr(comp, "file", None)
    if isinstance(file_ref, str) and file_ref.startswith(("http://", "https://")):
        return file_ref
    return None


def _guess_media_ext(comp, url: str, content_type: str) -> str:
    """根据 Content-Type / URL 后缀 / 组件类型确定临时文件后缀。"""
    mime = (content_type or "").split(";")[0].strip().lower()
    ext = _MIME_EXT_MAP.get(mime)
    if ext:
        return ext
    url_ext = Path(urlparse(url).path).suffix.lower()
    if url_ext in _VALID_URL_EXT:
        return url_ext
    for comp_type, default in _DEFAULT_MEDIA_EXT.items():
        if isinstance(comp, comp_type):
            return default
    return ".bin"


async def _download_url_to_local(comp, url: str, use_proxy: bool = False, proxy_url: str | None = None) -> str:
    """把远程媒体下载到本地临时目录，返回本地路径。

    先用正常网络（aiohttp 默认 AF_UNSPEC / happy eyeballs）尝试，失败后改用强制
    IPv4（AF_INET）重试，规避宿主机 IPv6 无默认路由 / DNS no-data 时 aiohttp 报
    `Cannot connect ... ssl:default [None]`（aio-libs/aiohttp#9447）的问题。
    代理三态：use_proxy=False 直连；use_proxy=True 且 proxy_url 空走系统代理（环境变量）；
    use_proxy=True 且 proxy_url 非空走该代理地址。两次都失败则抛异常，由调用方降级为占位文本。
    """
    try:
        import aiohttp
    except ImportError as e:
        raise RuntimeError("aiohttp 不可用，无法本地化媒体") from e

    try:
        import certifi
        ssl_context = ssl.create_default_context(cafile=certifi.where())
    except Exception:
        ssl_context = ssl.create_default_context()

    import socket

    # 代理三态：关→直连；开且无地址→系统代理（读环境变量）；开且有地址→指定代理
    if not use_proxy:
        trust_env, proxy = False, None
    elif proxy_url:
        trust_env, proxy = False, proxy_url
    else:
        trust_env, proxy = True, None

    async def _fetch(connector):
        async with aiohttp.ClientSession(trust_env=trust_env, connector=connector) as session:
            async with session.get(url, proxy=proxy, timeout=120) as resp:
                resp.raise_for_status()
                content_type = resp.headers.get("Content-Type", "")
                return await resp.read(), content_type

    # 先正常网络（默认 AF_UNSPEC），失败再强制 IPv4
    try:
        data, content_type = await _fetch(aiohttp.TCPConnector(ssl=ssl_context))
    except Exception as e:
        logger.warning(f"⚠️ 正常网络下载媒体失败（{e}），改用强制 IPv4 重试")
        data, content_type = await _fetch(
            aiohttp.TCPConnector(ssl=ssl_context, family=socket.AF_INET)
        )

    suffix = _guess_media_ext(comp, url, content_type)
    tmp_dir = _get_media_cache_dir()
    tmp_dir.mkdir(parents=True, exist_ok=True)
    fd, path = tempfile.mkstemp(suffix=suffix, dir=str(tmp_dir))
    with os.fdopen(fd, "wb") as f:
        f.write(data)
    return path


def _rebuild_from_local_path(comp, local_path: str, keep_local: bool = False):
    """按本地文件路径重建组件（fromFileSystem）。

    注意：File/Video 重建时优先使用原始 URL（NapCat 通过 URL 下载），而非本地路径
    （NapCat 读不到本地路径会报 retcode=1200 '路径不存在'）。
    本地文件仅作为下载缓存保留在磁盘上。
    队列场景（keep_local=True）：保留本地路径（fromFileSystem / file=本地路径），
    由发送前的 _prepare_chain_for_media_urls 注册 AstrBot 文件服务 token，
    生成短时稳定 URL（跨容器可下载、发送时实时注册不过期）。"""
    if isinstance(comp, Image):
        return Image.fromFileSystem(local_path)
    if isinstance(comp, Record):
        return Record.fromFileSystem(local_path)
    if isinstance(comp, Video):
        # 清空 cover：源端封面通常是源平台临时路径，跨进程不可达
        if keep_local:
            # 保留本地路径（path 字段），发送前注册文件服务 URL
            return Video.fromFileSystem(local_path)
        # 优先保留原始 URL，让目标端（NapCat）通过 URL 下载
        url = getattr(comp, "url", None) or ""
        if url:
            return Video(file=url, url=url)
        return Video.fromFileSystem(local_path)
    if isinstance(comp, File):
        # File 组件优先使用 URL（NapCat 通过 URL 下载），
        # 无 URL 时降级为本地路径（从 local_path 缓存重建）
        name = getattr(comp, "name", None) or ""
        if keep_local:
            # 保留本地路径（file_ 字段），发送前注册文件服务 URL
            return File(name=name, file=local_path)
        url = getattr(comp, "url", None) or ""
        if url:
            return File(name=name, url=url)
        return File(name=name, file=local_path)
    return comp


async def _rebuild_media_component(comp, use_proxy: bool = False, proxy_url: str | None = None):
    """把媒体组件重新下载到本进程临时目录并以 fromFileSystem 重建。

    解决跨会话转发时，组件内嵌的 file/cover 是源端临时路径、目标端不可达，导致 ENOENT / FileNotFoundError 的问题。
    注意：File 组件没有 convert_to_file_path()/fromFileSystem()，等价方法是 get_file() 与构造函数 File(name=..., file=...)。
    如果本地文件不可用（如群文件未下载到本地），尝试从远程 URL 下载。
    全部失败时退化为 Plain 占位文本，绝不向上抛异常影响整条转发。"""
    comp_type = _comp_type_name(comp)
    # 1) 先尝试获取本地文件路径（Image/Record/Video 用 convert_to_file_path；File 用 get_file）
    try:
        if isinstance(comp, File):
            # File 组件没有 convert_to_file_path()，等价方法是 get_file()（异步下载并返回本地路径）
            local_path = await comp.get_file()
        else:
            local_path = await comp.convert_to_file_path()
        if local_path:
            try:
                return _rebuild_from_local_path(comp, local_path)
            except Exception as e:
                logger.warning(f"⚠️ 按本地路径重建媒体失败（{comp_type}），尝试远程 URL 下载：{e}")
        else:
            logger.warning(f"⚠️ 获取文件路径返回空（{comp_type}），尝试远程 URL 下载")
    except Exception as e:
        logger.warning(f"⚠️ 获取文件路径失败（{comp_type}），尝试远程 URL 下载：{e}")

    # 2) 本地文件不可用，尝试从远程 URL 下载后重建
    remote_url = _extract_remote_url(comp)
    if remote_url:
        try:
            local_path = await _download_url_to_local(comp, remote_url, use_proxy=use_proxy, proxy_url=proxy_url)
            try:
                return _rebuild_from_local_path(comp, local_path)
            except Exception as e:
                logger.warning(f"⚠️ 按下载路径重建媒体失败（{comp_type}），将以占位文本代替：{e}")
        except Exception as e:
            logger.warning(f"⚠️ 转发时重下载媒体失败（{comp_type}，本地文件与远程下载均失败），将以占位文本代替：{e}")
    else:
        logger.warning(f"⚠️ 转发时重下载媒体失败（{comp_type}，无远程 URL 且本地文件不可用），将以占位文本代替")
    return Plain(text=f"[{comp_type}转发失败：源文件不可达]")


async def _prepare_chain_for_forward(chain, use_proxy: bool = False, proxy_url: str | None = None):
    """转发前对消息链做「本地化」预处理，返回新的可安全跨会话发送的链。"""
    if not chain:
        return chain
    prepared = []
    for comp in chain:
        if isinstance(comp, (Image, Record, Video, File)):
            prepared.append(await _rebuild_media_component(comp, use_proxy=use_proxy, proxy_url=proxy_url))
        else:
            prepared.append(comp)
    return prepared


async def _prepare_chain_fallback(chain, use_proxy: bool = False, proxy_url: str | None = None):
    """把远程 URL 媒体下载到本地（内部先正常网络、失败再 IPv4），作为转发失败后的兜底链。

    仅处理引用远程 http(s) URL 的媒体组件（图片/语音/视频/文件），下载失败降级为
    Plain 占位文本；本地文件/base64 与非媒体组件原样保留。与 _prepare_chain_for_forward
    的区别：后者走 AstrBot 核心 download_file，本函数自带「正常网络 → 强制 IPv4」的
    兜底下载器，用于规避宿主机 IPv6 无默认路由 / DNS no-data 时核心 download_file
    连接远程源报 `Cannot connect ... ssl:default [None]`（aio-libs/aiohttp#9447）的问题。
    代理三态：use_proxy=False 直连；use_proxy=True 且 proxy_url 空走系统代理；非空走该地址。
    """
    if not chain:
        return chain
    prepared = []
    for comp in chain:
        if isinstance(comp, (Image, Record, Video, File)):
            remote_url = _extract_remote_url(comp)
            if remote_url:
                comp_type = _comp_type_name(comp)
                try:
                    local_path = await _download_url_to_local(comp, remote_url, use_proxy=use_proxy, proxy_url=proxy_url)
                    prepared.append(_rebuild_from_local_path(comp, local_path))
                except Exception as e:
                    logger.warning(f"⚠️ 转发失败后本地化媒体失败（{comp_type}），将以占位文本代替：{e}")
                    prepared.append(Plain(text=f"[{comp_type}转发失败：源文件不可达]"))
            else:
                # 无远程 URL，尝试本地文件路径兜底（File 用 get_file，其余用 convert_to_file_path）
                try:
                    if isinstance(comp, File):
                        local_path = await comp.get_file()
                    else:
                        local_path = await comp.convert_to_file_path()
                    if local_path:
                        prepared.append(_rebuild_from_local_path(comp, local_path))
                    else:
                        prepared.append(comp)
                except Exception:
                    prepared.append(comp)
        else:
            prepared.append(comp)
    return prepared


async def _prepare_chain_for_queue(chain, use_proxy: bool = False, proxy_url: str | None = None):
    """将消息链中的所有媒体本地化到插件自有临时目录，防止队列延迟后源端文件被清理。

    优先用 AstrBot 核心 convert_to_file_path() 获取本地缓存路径（适配器层已缓存，
    通常瞬间返回）；失败后回退到远程 URL 下载。所有文件复制到 AstrBot data 目录下的
    msg_forward_cc_media 自有目录（持久化，重启不丢），确保队列延迟后仍可访问。
    """
    if not chain:
        return chain
    prepared = []
    tmp_dir = _get_media_cache_dir()
    tmp_dir.mkdir(parents=True, exist_ok=True)
    for comp in chain:
        if not isinstance(comp, (Image, Record, Video, File)):
            prepared.append(comp)
            continue
        comp_type = _comp_type_name(comp)
        try:
            # 用 AstrBot 核心获取本地路径（适配器层已缓存，通常很快）
            # 注意：File 组件没有 convert_to_file_path()，等价方法是 get_file()
            if isinstance(comp, File):
                local_path = await comp.get_file()
            else:
                local_path = await comp.convert_to_file_path()
            if local_path and os.path.isfile(local_path):
                suffix = Path(local_path).suffix or ""
                fd, dest = tempfile.mkstemp(suffix=suffix, dir=str(tmp_dir))
                os.close(fd)
                shutil.copy2(local_path, dest)
                # keep_local=True：保留本地路径，发送前由 _prepare_chain_for_media_urls
                # 注册 AstrBot 文件服务 token 生成跨容器可下载的 URL
                prepared.append(_rebuild_from_local_path(comp, dest, keep_local=True))
                continue
        except Exception:
            pass  # convert_to_file_path 失败，尝试远程 URL

        # 回退：远程 URL 下载
        remote_url = _extract_remote_url(comp)
        if remote_url:
            try:
                local_path = await _download_url_to_local(comp, remote_url, use_proxy, proxy_url)
                prepared.append(_rebuild_from_local_path(comp, local_path, keep_local=True))
                continue
            except Exception as e:
                logger.warning(f"⚠️ 队列本地化媒体失败（{comp_type}），将以占位文本代替：{e}")
                prepared.append(Plain(text=f"[{comp_type}转发失败：源文件不可达]"))
                continue

        logger.warning(f"⚠️ 队列本地化媒体失败（{comp_type}），无法获取文件，将以占位文本代替")
        prepared.append(Plain(text=f"[{comp_type}转发失败：源文件不可达]"))
    return prepared


# ------------------------
# AstrBot 内置文件服务（跨容器媒体 URL）
# ------------------------

# 队列媒体缓存目录：AstrBot data 目录下持久化子目录（重启/重载不丢文件）
# 实际路径由插件 __init__ 按 data_dir 设置（StarTools.get_data_dir）
_MEDIA_CACHE_DIR: Path | None = None


def _get_media_cache_dir() -> Path:
    """返回队列媒体缓存目录（AstrBot data 目录下，持久化）。"""
    global _MEDIA_CACHE_DIR
    if _MEDIA_CACHE_DIR is not None:
        return _MEDIA_CACHE_DIR
    return Path(tempfile.gettempdir()) / "msg_forward_cc_media"


def _get_file_service_base_url() -> str:
    """读取 AstrBot 全局配置 callback_api_base（外部访问 AstrBot 的地址）。

    供文件服务 URL 拼接：{callback_api_base}/api/file/{token}。
    未配置时返回空串（文件服务不可用）。"""
    try:
        from astrbot.core import astrbot_config
        base = (astrbot_config.get("callback_api_base") or "").strip().rstrip("/")
        return base
    except Exception:
        return ""


def _file_service_available() -> bool:
    """AstrBot 内置文件服务是否可用（需配置 callback_api_base）。"""
    return bool(_get_file_service_base_url())


async def _register_file_with_service(local_path: str, timeout: float = 3600) -> str | None:
    """把本地文件注册到 AstrBot 文件服务，返回可下载的 URL。

    返回 {callback_api_base}/api/file/{token}；token 单次使用、默认 300s 过期，
    因此需在每次发送前重新注册（本实现用较长 timeout + 发送前注册保证有效）。
    未配置 callback_api_base 或注册失败时返回 None。"""
    base = _get_file_service_base_url()
    if not base:
        return None
    try:
        from astrbot.core import file_token_service
        token = await file_token_service.register_file(local_path, timeout=timeout)
        return f"{base}/api/file/{token}"
    except Exception as e:
        logger.warning(f"⚠️ 注册媒体文件服务失败（{local_path}）：{e}")
        return None


def _local_media_path_of(comp) -> str | None:
    """提取媒体组件本地化的文件路径；无本地文件返回 None（序列化时存的是本地路径）。"""
    try:
        if isinstance(comp, Video):
            # keep_local 场景下 file 是 file:// URI 或本地路径
            cand = getattr(comp, "file", "") or ""
        elif isinstance(comp, File):
            cand = getattr(comp, "file_", "") or ""
        elif isinstance(comp, (Image, Record)):
            cand = getattr(comp, "file", "") or ""
        else:
            return None
    except Exception:
        return None
    if not cand:
        return None
    # file:// URI → 本地路径
    if cand.startswith("file://"):
        from urllib.parse import unquote, urlparse
        try:
            p = urlparse(cand)
            return unquote(p.path)
        except Exception:
            return None
    # base64/data URI / http(s) URL 不算本地路径
    if cand.startswith(("base64://", "data:", "http://", "https://")):
        return None
    p = Path(cand)
    if p.is_absolute() and p.is_file():
        return str(p)
    # 兼容相对路径（在媒体缓存目录内查找）
    try:
        rel = _get_media_cache_dir() / cand
        if rel.is_file():
            return str(rel)
    except Exception:
        pass
    return None


async def _prepare_chain_for_media_urls(chain) -> list:
    """发送前把链中媒体组件注册到 AstrBot 文件服务，生成可下载的 URL。

    队列场景下媒体已本地化到 AstrBot data 目录（持久化），但由于 NapCat 在另一容器
    读不到本地路径、源端短效 URL 又会在队列延迟后过期，这里在「发送前」实时注册
    新 token（每次发送、每个目标都重新注册，避免单次 token 与 300s 过期问题）。
    Image/Record 由 aiocqhttp 转 base64 内嵌，无需文件服务；仅处理 Video/File。
    callback_api_base 未配置时返回原链（回退原始 URL 行为）。"""
    if not chain or not _file_service_available():
        return chain
    new_chain = []
    for comp in chain:
        if isinstance(comp, (Video, File)):
            local_path = _local_media_path_of(comp)
            if local_path:
                url = await _register_file_with_service(local_path)
                if url:
                    if isinstance(comp, Video):
                        comp = Video(file=url, url=url)
                    else:
                        comp = File(name=getattr(comp, "name", "") or "", url=url)
        new_chain.append(comp)
    return new_chain


# ------------------------
# 消息链序列化（队列持久化）
# ------------------------

def _serialize_chain(chain) -> list:
    """把消息链组件序列化为可 JSON 存储的 dict 列表（供队列持久化）。

    仅覆盖队列转发涉及的组件类型（Plain/Image/Record/Video/File/At）；
    其余组件类型原样保留（无法序列化时跳过，避免阻塞入队）。"""
    out = []
    for comp in chain:
        try:
            if isinstance(comp, Plain):
                out.append({"t": "plain", "text": comp.text})
            elif isinstance(comp, Image):
                out.append({"t": "image", "file": comp.file, "url": comp.url or ""})
            elif isinstance(comp, Record):
                out.append({"t": "record", "file": comp.file, "url": comp.url or ""})
            elif isinstance(comp, Video):
                out.append({"t": "video", "file": comp.file, "url": comp.url or "", "cover": getattr(comp, "cover", None) or ""})
            elif isinstance(comp, File):
                out.append({"t": "file", "name": comp.name or "", "file_": comp.file_ or "", "url": comp.url or ""})
            elif isinstance(comp, At):
                out.append({"t": "at", "qq": str(comp.qq), "name": comp.name or ""})
            else:
                # 无法序列化的组件类型：跳过（队列持久化不覆盖）
                continue
        except Exception:
            continue
    return out


def _deserialize_chain(data: list) -> list:
    """把序列化的 dict 列表还原为消息链组件列表。"""
    chain = []
    for item in data or []:
        try:
            t = item.get("t")
            if t == "plain":
                chain.append(Plain(text=item.get("text", "")))
            elif t == "image":
                chain.append(Image(file=item.get("file", ""), url=item.get("url", "")))
            elif t == "record":
                chain.append(Record(file=item.get("file", ""), url=item.get("url", "")))
            elif t == "video":
                chain.append(Video(file=item.get("file", ""), url=item.get("url", ""), cover=item.get("cover", "")))
            elif t == "file":
                chain.append(File(name=item.get("name", ""), file=item.get("file_", ""), url=item.get("url", "")))
            elif t == "at":
                chain.append(At(qq=item.get("qq", ""), name=item.get("name", "")))
        except Exception:
            continue
    return chain


def _sanitize_chain_for_forward(chain):
    """转发前清洗 @ 提及组件（事件级无损清洗，不决定转发时的 At 策略）。

    处理顺序（逐组件）：
      1. @全体（qq="all"）与纯数字目标 → 保留 At 组件（供后续按策略透传/反查）；
      2. 非数字但非空的目标（如 openid / uid / "qq_official"）→ 同样保留 At 组件
         与 qq 与 name；
      3. 空目标（qq 为空、None 或 "0"）→ 无任何可解析信息，且透传会让目标平台
         （如 OneBot/NapCat）用空 uid 查询群成员，内核调用超时导致整个转发失败
         （retcode=1200 invoke timeout），故丢弃；有昵称则降级为纯文本 @昵称。

    注意：转发时的 @ 策略（默认文本化 / 高级 @ 透传+反查）由 _textify_at_chain 与
    _sanitize_at_chain_for_target / _resolve_at_mentions 在目标级执行，本函数只做清洗。"""
    if not chain:
        return chain
    cleaned = []
    for comp in chain:
        if not isinstance(comp, At):
            cleaned.append(comp)
            continue
        qq = getattr(comp, "qq", None)
        qq_str = str(qq).strip() if qq is not None else ""
        name = (getattr(comp, "name", "") or "").strip()
        # 纯数字是 OneBot 标准 @ 目标；本项目历史配置中 "0" 表示无效值，一并按空目标处理
        if qq_str == "all" or (qq_str.isdigit() and qq_str != "0"):
            cleaned.append(comp)
            continue
        if qq_str and qq_str != "0":
            # 非数字但非空：保留 qq 与 name 原样透传，由目标协议端按 qq 解析
            if name:
                logger.info(f"ℹ️ 转发时 @ 目标({qq_str!r})非数字，已原样透传（昵称 {name!r} 作为兜底）")
            else:
                logger.info(f"ℹ️ 转发时 @ 目标({qq_str!r})非数字，已原样透传交由目标协议端解析")
            cleaned.append(comp)
            continue
        # 空目标：无语义，原样透传会触发目标平台空 uid 查询超时，丢弃
        if name:
            cleaned.append(Plain(text=f"@{name}"))
            logger.info(f"⚠️ 转发时 @ 目标为空，已降级为文本 @{name}")
        else:
            logger.warning(f"⚠️ 转发时丢弃无效的 @ 目标: {qq_str!r}")
    return cleaned


# 源目标可被目标协议端按 qq 解析的平台（qq 透传白名单的默认值，可由配置追加）
_QQ_TARGET_PLATFORMS = {
    "aiocqhttp", "qq_official", "qq_official_webhook",
    "onebot", "napcat", "llonebot", "lagrange",
}


def _parse_platform_set(raw) -> set:
    """把配置里的平台列表（list 或按行/逗号分隔的字符串）解析为小写集合。"""
    if not raw:
        return set()
    if isinstance(raw, str):
        items = [x for line in raw.splitlines() for x in line.split(",")]
    elif isinstance(raw, (list, tuple, set)):
        items = list(raw)
    else:
        items = [raw]
    return {str(x).strip().lower() for x in items if str(x).strip()}


def _at_passthrough_platforms(config) -> set:
    """返回允许 At 透传（按 qq 解析）的目标平台集合。

    内置 QQ 系平台默认透传；配置 at_passthrough_extra_platforms 可追加
    （如自建适配器平台名）。追加项只增不减，无法用于关闭内置平台。"""
    platforms = set(_QQ_TARGET_PLATFORMS)
    if config:
        platforms |= _parse_platform_set(config.get("at_passthrough_extra_platforms"))
    return platforms


def _sanitize_at_chain_for_target(chain, target: str, passthrough_platforms: set | None = None):
    """高级 @ 模式下的目标级 At 处理：仅在「目标端无法按 qq 解析」时降级为文本 @昵称。

    （仅在 at_nickname_lookup 开启时被调用；默认关闭时 At 一律由 _textify_at_chain 转文本。）
    目标平台属于 QQ 系（见 _QQ_TARGET_PLATFORMS）时，At 原样透传（高级 @ 主路径）：
    qq 数字命中即可精确 @，协议端解析不到时自己按 At.name 降级显示。
    目标平台为跨平台（微信 / Telegram / Discord 等）时，「@ + 源 qq」在该平台
    没有任何可解析含义，透传可能因空/非法目标查询成员而超时或报错，
    故降级为文本 @昵称，保证信息不丢失。

    与旧版（v0.4.7）的区别：旧版对所有目标一律按「非数字即降级」处理，
    本版把非数字目标的判断下沉到目标平台粒度，从而做到「优先 qq 精确匹配」。"""
    if not chain:
        return chain
    platform = ""
    parts = str(target).split(":")
    if len(parts) == 3:
        platform = parts[0].strip().lower()
    allowed = _QQ_TARGET_PLATFORMS if passthrough_platforms is None else passthrough_platforms
    if platform in allowed:
        return chain
    cleaned = []
    for comp in chain:
        if not isinstance(comp, At):
            cleaned.append(comp)
            continue
        qq_str = str(getattr(comp, "qq", "") or "").strip()
        # @全体成员与纯数字目标在各平台均有意义（数字目标交给目标端尽力解析）
        if qq_str == "all" or (qq_str.isdigit() and qq_str != "0"):
            cleaned.append(comp)
            continue
        name = (getattr(comp, "name", "") or "").strip()
        if name:
            cleaned.append(Plain(text=f"@{name}"))
            logger.info(f"ℹ️ 目标平台 {platform or '未知'} 无法解析 @({qq_str!r})，已降级为文本 @{name}")
        else:
            logger.warning(f"⚠️ 目标平台 {platform or '未知'} 无法解析且无昵称的 @ 目标已丢弃: {qq_str!r}")
    return cleaned


def _textify_at_chain(chain):
    """把链中所有 At 组件一律转为纯文本 @昵称（默认 At 转发策略）。

    默认不发送真实 At 组件：彻底规避目标协议端按 qq 解析、查询群成员时的
    内核调用超时（retcod=-1200）与跨平台无法解析问题，信息以 @昵称 文本保留。
      - @全体（qq="all"）→ "@全体成员"（name 非 "all" 时优先用 name）；
      - 普通 At → "@昵称"（name 为空时用 qq 兜底；两者皆无则丢弃）。
    开启高级 @（at_nickname_lookup）后不再走本函数，由
    _sanitize_at_chain_for_target + _resolve_at_mentions 处理真实 At。"""
    if not chain:
        return chain
    cleaned = []
    for comp in chain:
        if not isinstance(comp, At):
            cleaned.append(comp)
            continue
        qq = str(getattr(comp, "qq", "") or "").strip()
        name = (getattr(comp, "name", "") or "").strip()
        if qq == "all":
            label = name if name and name != "all" else "全体成员"
            cleaned.append(Plain(text=f"@{label}"))
            logger.info("ℹ️ @全体成员已按默认策略转为文本 @全体成员")
            continue
        if name:
            cleaned.append(Plain(text=f"@{name}"))
            continue
        if qq and qq != "0":
            cleaned.append(Plain(text=f"@{qq}"))
            continue
        logger.warning(f"⚠️ 丢弃无昵称且无有效目标的 @ 组件（qq={qq!r}）")
    return cleaned


def _sanitize_file_chain_for_forward(chain):
    """清洗 File/Video 组件的本地路径引用，只保留 URL。

    OneBot/NapCat 的 File/Video 组件 `file_`/`file` 常是源端容器内本地路径
    （如 `/app/llbot/data/temp/...`），透传给目标端后 NapCat 读不到该路径，
    报 retcode=1200 'rich media transfer failed'；仅保留 `url` 字段让 NapCat 走 URL 下载。
    无 URL 的本地文件（如 base64/纯路径）原样保留。"""
    if not chain:
        return chain
    cleaned = []
    for comp in chain:
        if isinstance(comp, File):
            url = getattr(comp, "url", None) or ""
            if url and url.startswith(("http://", "https://")):
                name = getattr(comp, "name", None) or ""
                cleaned.append(File(name=name, url=url))
                continue
            if not url:
                name = getattr(comp, "name", None) or ""
                file_ = getattr(comp, "file_", None) or ""
                logger.warning(f"⚠️ 群文件 {name!r} 无远程 URL（file_={file_!r}），尝试 API 获取")
        elif isinstance(comp, Video):
            url = getattr(comp, "url", None) or ""
            if url and url.startswith(("http://", "https://")):
                # 保留 URL，清空本地路径（file 字段设为 url）
                cleaned.append(Video(file=url, url=url))
                continue
            if not url:
                logger.info(f"ℹ️ 视频无远程 URL（file={getattr(comp, 'file', '')!r}），NapCat 将尝试读取本地路径")
        cleaned.append(comp)
    return cleaned


def load_json(path: Path) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        logger.error("❌ 文件不存在！本次创建空 JSON！")
        return {}
    except json.JSONDecodeError as e:
        logger.error(f"❌ 文件 {path} 不是有效 JSON: {e}")
        raise ValueError(f"❌ 文件 {path} 不是有效 JSON: {e}") from e
    except OSError as e:
        logger.error(f"❌ 读取文件 {path} 失败: {e}")
        raise RuntimeError(f"❌ 读取文件 {path} 失败: {e}") from e
    except Exception as e:
        logger.error(f"❌ 发生预期外的 JSON 读取错误: {e}！")
        raise RuntimeError(f"❌ 发生预期外的 JSON 读取错误: {e}！")


def save_json(path: Path, data: dict):
    try:
        tmp = path.with_suffix(".tmp")
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        tmp.replace(path)
    except OSError as e:
        logger.error(f"❌ 写入文件 {path} 失败: {e}")
        raise RuntimeError(f"❌ 写入文件 {path} 失败: {e}") from e
    except TypeError as e:
        logger.error(f"❌ 数据无法序列化为 JSON: {e}")
        raise ValueError(f"❌ 数据无法序列化为 JSON: {e}") from e
    except Exception as e:
        logger.error(f"❌ 发生预期外的 JSON 写入错误: {e}")
        raise RuntimeError(f"❌ 发生预期外的 JSON 写入错误: {e}") from e


def gen_code(n=6):
    # 使用 secrets 模块生成更安全的随机字符串
    alphabet = string.ascii_lowercase + string.digits
    return ''.join(secrets.choice(alphabet) for _ in range(n))


_DISCORD_HOOK_ATTR = "_msg_forward_cc_discord_hook"

# 挂载轮询间隔（秒）：适配器客户端要等平台 run() 才创建，插件加载时通常还不存在；
# 平台重连/重载也会换新客户端，因此用低频轮询持续补齐，开销可忽略
_DISCORD_HOOK_INTERVAL = 15

_DISCORD_HANDLED_IDS_MAX = 500

_DISCORD_HOOK_EVENT_ATTR = "_mf_from_discord_hook"

# 当前活跃插件实例的标记名。挂在 AstrBot 的 Context 上而不是模块全局变量：
# 插件重载会清空 sys.modules 并重新导入本模块，模块全局变量不跨代共享（旧监听读到的
# 仍是旧实例），而 Context 全进程唯一、每代实例都拿到同一个对象
_ACTIVE_ATTR = "_mf_active_instance"


def _mark_active(context: object, instance: object) -> None:
    """登记当前活跃实例（Context 不支持写属性时静默降级，不影响转发）。"""
    try:
        setattr(context, _ACTIVE_ATTR, instance)
    except Exception:
        pass


def _active_of(context: object) -> object | None:
    """取当前活跃实例；未登记返回 None。"""
    return getattr(context, _ACTIVE_ATTR, None)


# 插件自身目录名：用于在核心 star 注册表里定位本插件（判断是否仍装载/启用）
_PLUGIN_DIR = os.path.dirname(os.path.abspath(__file__))
_PLUGIN_DIR_NAME = os.path.basename(_PLUGIN_DIR)


def _plugin_alive(instance: object) -> bool:
    """本插件是否仍可用：目录还在，且在核心 star 注册表里仍处于启用状态。

    补挂的监听挂在 Discord 客户端上，不随插件实例销毁；而核心的 `_terminate_plugin` 存在多个
    提前返回（例如 `activated=False`、`star_cls is None`）——WebUI 卸载/停用插件时不保证会调用
    `terminate()`。因此监听必须自己判断存活，否则「插件已删/已停用」后仍会按内存里的旧配置继续转发。
    取不到注册表时按存活处理，避免误杀正常运行的插件。"""
    try:
        if not os.path.isdir(_PLUGIN_DIR):
            return False  # 插件目录已被删除（WebUI 卸载）
    except OSError:
        pass
    try:
        from astrbot.core.star.star import star_registry
    except Exception:
        return True
    try:
        metas = [
            md for md in list(star_registry)
            if getattr(md, "root_dir_name", None) == _PLUGIN_DIR_NAME
        ]
        total = len(list(star_registry))
    except Exception:
        return True
    if not metas:
        # 注册表非空却找不到本插件 → 已卸载；注册表为空（核心尚未装载完）→ 不误杀
        return total == 0
    return bool(getattr(metas[0], "activated", True))


# ------------------------
# 转发时翻译（百度翻译开放平台「通用文本翻译」）
# ------------------------

_BAIDU_TRANSLATE_URL = "https://fanyi-api.baidu.com/api/trans/vip/translate"

# 单次请求 q 的字节上限（官方 6000 字节），保守取 5000 后按 UTF-8 字节切分
_BAIDU_Q_MAX_BYTES = 5000

# 翻译前需要原样保留的片段：链接、Discord 标记（<:表情:id> / <@id> / <#频道>）、行内代码
# 百度会改写这些符号，先用占位符换出、译完再还原
_TRANSLATE_KEEP_RE = re.compile(r"(https?://\S+|<a?[:#@][^>\s]*>|`[^`\n]+`)")
_TRANSLATE_PLACEHOLDER_RE = re.compile(r"\{+\s*(\d+)\s*\}+")

# 百度标准版 QPS=1：串行调用并按最小间隔节流，避免 54003 频率受限
_TRANSLATE_LOCK = asyncio.Lock()
_TRANSLATE_LAST_CALL = 0.0

# 语言别名 → 百度语言代码（配置与命令里写中文即可）
_LANG_ALIASES = {
    "自动": "auto", "自动检测": "auto", "auto": "auto",
    "中文": "zh", "简体": "zh", "简体中文": "zh", "zh": "zh", "zh-cn": "zh", "zh_hans": "zh",
    "繁体": "cht", "繁体中文": "cht", "cht": "cht", "zh-tw": "cht",
    "英文": "en", "英语": "en", "en": "en",
    "日文": "jp", "日语": "jp", "jp": "jp", "ja": "jp",
    "韩文": "kor", "韩语": "kor", "kor": "kor", "ko": "kor",
    "法文": "fra", "法语": "fra", "fra": "fra", "fr": "fra",
    "德文": "de", "德语": "de", "de": "de",
    "俄文": "ru", "俄语": "ru", "ru": "ru",
    "西班牙语": "spa", "spa": "spa", "es": "spa",
    "葡萄牙语": "pt", "pt": "pt",
    "意大利语": "it", "it": "it",
    "阿拉伯语": "ara", "ara": "ara", "ar": "ara",
    "泰语": "th", "th": "th",
    "越南语": "vie", "vie": "vie", "vi": "vie",
}


def _normalize_lang(raw: str, default: str) -> str:
    """把配置/命令中的语言写法归一化为百度语言代码（支持中文别名）。"""
    key = (raw or "").strip().lower()
    if not key:
        return default
    return _LANG_ALIASES.get(key, key)


def _looks_like_lang(text: str, lang: str) -> bool:
    """粗判文本是否已是目标语言（仅用于跳过无谓的翻译调用）。

    只对中文目标做判断：非空白字符里汉字占比 ≥ 60% 即认为已是中文。"""
    if lang not in ("zh", "cht"):
        return False
    stripped = [c for c in text if not c.isspace()]
    if not stripped:
        return True
    cjk = sum(1 for c in stripped if "\u4e00" <= c <= "\u9fff")
    return cjk / len(stripped) >= 0.6


def _protect_translate_tokens(text: str) -> tuple[str, dict]:
    """把不该被翻译的片段换成 {n} 占位符，返回（保护后的文本, 占位符表）。"""
    mapping: dict = {}

    def _sub(match: "re.Match") -> str:
        token = "{%d}" % len(mapping)
        mapping[token] = match.group(0)
        return token

    return _TRANSLATE_KEEP_RE.sub(_sub, text), mapping


def _restore_translate_tokens(text: str, mapping: dict) -> str | None:
    """还原占位符；有占位符被翻译接口吞掉/改写时返回 None（调用方保留原文）。"""
    if not mapping:
        return text
    seen: set = set()

    def _sub(match: "re.Match") -> str:
        # 接口可能把 {0} 写成 { 0 }，统一按数字还原
        token = "{%s}" % match.group(1)
        value = mapping.get(token)
        if value is None:
            return match.group(0)
        seen.add(token)
        return value

    restored = _TRANSLATE_PLACEHOLDER_RE.sub(_sub, text)
    if len(seen) != len(mapping):
        return None
    return restored


def _split_translate_chunks(text: str, max_bytes: int = _BAIDU_Q_MAX_BYTES) -> list:
    """按 UTF-8 字节数把长文本切成不超过上限的片段（优先在换行处切）。"""
    chunks: list = []
    buf = ""
    for line in text.splitlines(keepends=True):
        if len((buf + line).encode("utf-8")) <= max_bytes:
            buf += line
            continue
        if buf:
            chunks.append(buf)
            buf = ""
        if len(line.encode("utf-8")) <= max_bytes:
            buf = line
            continue
        # 单行本身就超长：按字符累加切分
        piece = ""
        for ch in line:
            if len((piece + ch).encode("utf-8")) > max_bytes:
                chunks.append(piece)
                piece = ch
            else:
                piece += ch
        buf = piece
    if buf:
        chunks.append(buf)
    if not chunks and text:
        chunks.append(text)
    return chunks


async def _baidu_translate(
    text: str,
    appid: str,
    secret: str,
    from_lang: str,
    to_lang: str,
    timeout: float = 10.0,
    interval: float = 1.1,
    use_proxy: bool = False,
    proxy_url: str | None = None,
) -> str:
    """调用百度翻译「通用文本翻译」返回译文（长文本自动分段拼接）。

    签名规则 sign = md5(appid + q + salt + 密钥)；失败抛异常，由调用方降级为原文。
    代理三态与媒体下载一致：关→直连；开且地址为空→系统代理；开且非空→该地址。
    """
    import aiohttp  # 惰性导入：与媒体下载保持一致，缺失时不影响其余功能

    global _TRANSLATE_LAST_CALL
    proxy = proxy_url if (use_proxy and proxy_url) else None
    trust_env = bool(use_proxy and not proxy_url)
    translated: list = []

    async with _TRANSLATE_LOCK:
        for chunk in _split_translate_chunks(text):
            data = {}
            for attempt in range(2):
                wait = interval - (time.monotonic() - _TRANSLATE_LAST_CALL)
                if wait > 0:
                    await asyncio.sleep(wait)
                salt = str(secrets.randbelow(65536) + 32768)
                sign = hashlib.md5(f"{appid}{chunk}{salt}{secret}".encode("utf-8")).hexdigest()
                payload = {
                    "q": chunk, "from": from_lang, "to": to_lang,
                    "appid": appid, "salt": salt, "sign": sign,
                }
                client_timeout = aiohttp.ClientTimeout(total=timeout)
                async with aiohttp.ClientSession(timeout=client_timeout, trust_env=trust_env) as session:
                    async with session.post(_BAIDU_TRANSLATE_URL, data=payload, proxy=proxy) as resp:
                        _TRANSLATE_LAST_CALL = time.monotonic()
                        data = await resp.json(content_type=None)
                code = str(data.get("error_code", "") or "")
                if not code:
                    break
                # 54003 = 访问频率受限：等一个间隔再重试一次
                if code == "54003" and attempt == 0:
                    await asyncio.sleep(max(interval, 1.0))
                    continue
                raise RuntimeError(f"百度翻译错误 {code}: {data.get('error_msg', '')}")
            items = data.get("trans_result") or []
            if not items:
                raise RuntimeError("百度翻译返回结果为空")
            translated.append("\n".join(str(item.get("dst", "")) for item in items))
    return "\n".join(translated)


# ------------------------
# 存储层（无锁简化）
# ------------------------
class MsgForwardStore:
    def __init__(self, pending_file: Path):
        self.pending_file = pending_file
        self._ensure_files()

    def _ensure_files(self):
        if not self.pending_file.exists():
            self.pending_file.write_text("{}", encoding="utf-8")

    # ----- pending -----
    def load_pending(self):
        return load_json(self.pending_file)

    def save_pending(self, data: dict):
        save_json(self.pending_file, data)

    def add_pending(self, code: str, source_umo: str):
        p = self.load_pending()
        p[code] = source_umo
        self.save_pending(p)

    def pop_pending(self, code: str):
        p = self.load_pending()
        if code not in p:
            raise KeyError("绑定码不存在或已使用")
        source_umo = p.pop(code)
        self.save_pending(p)
        return source_umo


# ------------------------
# 插件主体
# ------------------------
class MsgForward(star.Star):
    def __init__(self, context: Context, config: AstrBotConfig = None):
        super().__init__(context)
        self.config = config or {}

        self.data_dir = star.StarTools.get_data_dir("msg_forward_cc")
        self.pending_file = self.data_dir / "pending.json"
        self.queue_file = self.data_dir / "queue.json"

        # 队列媒体缓存目录：AstrBot data 目录下持久化子目录（重启/重载不丢文件）
        global _MEDIA_CACHE_DIR
        _MEDIA_CACHE_DIR = self.data_dir / "media"
        _MEDIA_CACHE_DIR.mkdir(parents=True, exist_ok=True)

        self.store = MsgForwardStore(self.pending_file)

        # 冷却计时器：key = "source_umo|target_umo"，value = 冷却结束时间戳
        self._cooldowns: dict[str, float] = {}
        # 冷却失效提示：队列模式下冷却被跳过，按 rule_key 只告警一次（避免刷屏日志）
        self._cooldown_warned: set = set()

        # 发送队列：按规则（rule_key）分桶的 FIFO 队列，队列间隔 > 0 时消息
        # 不立即转发，而是由后台 worker 按每规则独立间隔依次发送（与「冷却」的
        # 丢弃语义互补）。各规则桶互不阻塞——某规则间隔长不会拖慢其他规则的节拍。
        self._rule_queues: dict[str, asyncio.Queue] = {}
        # 每规则下一次允许发送的单调时钟时间戳（无记录=立即可发）；
        # worker 发送后置为「发送时刻 + 该条间隔」，实现规则级独立限流
        self._rule_next_send: dict[str, float] = {}
        # 唤醒 worker 的事件：新条目入队 / 磁盘恢复入队时 set，
        # 避免 worker 睡在等待中错过到点的条目
        self._queue_wake: asyncio.Event = asyncio.Event()
        # 队列积压按规则归集计数：rule_key → 当前积压条数（入队 +1，worker 取走 -1）
        self._queue_rule_counts: dict[str, int] = {}
        self._queue_worker_task: asyncio.Task | None = None
        self._cleanup_task: asyncio.Task | None = None
        # 队列暂停标志：pause 后 worker 停止消费（积压消息暂不发送），resume 恢复
        self._queue_paused: bool = False

        # Discord 机器人消息接管：AstrBot 的 Discord 适配器会丢弃机器人消息，
        # 插件默认给客户端补挂 on_message 监听补齐
        self._discord_hook_task: asyncio.Task | None = None
        self._discord_hook_logged: bool = False
        self._discord_hook_warned: bool = False
        self._discord_hook_attempts: int = 0
        self._discord_hook_ready_warned: bool = False
        self._discord_empty_skipped: int = 0
        self._discord_handled_ids: set = set()
        # 自检判定插件已停用/卸载后置位：保证只摘一次监听、只打一次日志
        self._self_disabled: bool = False
        # 翻译告警去重：按 key 只告警一次，避免接口报错时每条消息刷屏
        self._translate_warned: set = set()

        # 迁移旧版 list 存储的 UMO 字段 → 每行一条的文本（修复 WebUI 校验失败）
        self._migrate_legacy_umo_lists()

    def _migrate_legacy_umo_lists(self):
        """把旧版 list 类型存储的 source_umo / target_umo 迁移为每行一条的 text。

        旧版 schema 中这两个字段是 list 类型，存量规则里可能是 ["umo1", "umo2"] 数组；
        现 schema 为 text（每行一条），AstrBot 在 WebUI 保存时校验会因 list 值报
        「期望是 string, 得到了 list」导致无法保存。这里在启动时一次性转换并持久化。
        """
        try:
            rules = self.config.get("rules", [])
            if not isinstance(rules, list) or not rules:
                return
            changed = False
            for rule in rules:
                if not isinstance(rule, dict):
                    continue
                for key in ("source_umo", "target_umo"):
                    val = rule.get(key)
                    if isinstance(val, list):
                        rule[key] = "\n".join(str(x).strip() for x in val if str(x).strip())
                        changed = True
            if changed:
                self.config.save_config()
                logger.info("✅ 已将旧版列表格式的 source_umo/target_umo 迁移为每行一条的文本格式")
        except Exception as e:
            logger.warning(f"⚠️ UMO 字段迁移失败（不影响正常运行）：{e}")

    def _format_origin_header(self, event: AstrMessageEvent, umo: str) -> str:
        try:
            _, msg_type, conversation_id = umo.split(":", 2)
        except ValueError:
            msg_type = "Unknown"
            conversation_id = "Unknown"

        source_platform = event.get_platform_name()
        sender_name = event.get_sender_name()
        sender_id = event.get_sender_id()

        # 平台友好名称（全部从配置 platform_names 列表读取）
        # 迁移：旧版 platform_name_map（object 格式）优先转换为 list
        old_map = self.config.get("platform_name_map", {})
        if isinstance(old_map, dict) and old_map:
            platform_names_raw = [f"{k}={v}" for k, v in old_map.items()]
        else:
            platform_names_raw = self.config.get("platform_names", []) or []

        # 解析为 dict
        platform_map = {}
        for item in platform_names_raw:
            if isinstance(item, str) and "=" in item:
                key, _, value = item.partition("=")
                platform_map[key.strip()] = value.strip()

        source_platform_human = platform_map.get(source_platform, source_platform)

        # 消息类型友好名称
        if msg_type == "GroupMessage":
            msg_type_human = "群组"
        elif msg_type == "FriendMessage":
            msg_type_human = "私聊"
        else:
            msg_type_human = "未知类型"

        # 使用配置中的模板
        template = self.config.get("header_template", "").strip()
        if template:
            header = template.format(
                sender_name=sender_name,
                sender_id=sender_id,
                platform=source_platform_human,
                msg_type=msg_type_human,
                conversation_id=conversation_id,
            )
        else:
            header = (
                f"[转发] {sender_name} ({sender_id})\n"
                f"来自 {source_platform_human} 的 {msg_type_human}（ID: {conversation_id}）消息"
            )

        return header

    @staticmethod
    def _umo_list(rule: dict, key: str) -> list:
        """把规则中的 UMO 字段统一归一化为列表。

        兼容三种存储格式：text 按行拆分（每行一条）、list 列表、单字符串。"""
        val = rule.get(key)
        if not val:
            return []
        if isinstance(val, str):
            # 单字符串或多行 text 均按行拆分（单个 UMO 无换行，拆出单项）
            return [x.strip() for x in val.splitlines() if x.strip()]
        if isinstance(val, list):
            return [str(x).strip() for x in val if str(x).strip()]
        return []

    @staticmethod
    def _rule_name(rule: dict) -> str:
        """规则展示名称：优先取自定义备注 remark，留空则回退为 source_umo → target_umo。"""
        remark = (rule.get("remark") or "").strip()
        if remark:
            return remark
        src = ", ".join(MsgForward._umo_list(rule, "source_umo")) or "?"
        dst = ", ".join(MsgForward._umo_list(rule, "target_umo")) or "?"
        return f"{src} → {dst}"

    @staticmethod
    def _rule_key(rule: dict) -> str:
        """规则的稳定标识（供队列积压按规则归集统计）。

        由规则自身的 source_umo 与 target_umo 内容派生，不依赖规则编号，
        因此规则增删、排序后已入队的消息仍能正确归属到对应规则。"""
        srcs = "|".join(MsgForward._umo_list(rule, "source_umo"))
        dsts = "|".join(MsgForward._umo_list(rule, "target_umo"))
        return f"{srcs}=>{dsts}"

    def _add_rule(self, source_umo: str, target_umo: str, hide_header: bool) -> int:
        """新增一条转发规则并持久化，返回新规则的编号（1-based）。

        统一 bind / bindraw 的建规则逻辑：构造带 __template_key 的规则 dict、
        自动生成 remark 编号、追加到 rules 并保存。"""
        rules = list(self.config.get("rules", []))
        rules.append({
            "__template_key": "rule",
            "remark": f"规则 #{len(rules) + 1}",
            "source_umo": source_umo,
            "target_umo": target_umo,
            "hide_header": hide_header,
            "enabled": True,
        })
        self.config["rules"] = rules
        self.config.save_config()
        return len(rules)

    async def initialize(self):
        # 登记为当前活跃实例：补挂监听与转发都以此实例的配置为准
        _mark_active(self.context, self)
        # 恢复上次未发送完的持久化队列（重启/重载不丢消息）
        self._restore_persisted_queue()
        self._queue_worker_task = asyncio.create_task(self._queue_worker())
        # 启动时清理所有队列媒体缓存
        self._cleanup_old_media()
        # 启动定期清理任务
        self._cleanup_task = asyncio.create_task(self._periodic_cleanup())
        # Discord 机器人消息接管（可用 discord_takeover 关掉：关掉后本插件不再改写客户端对象，
        # 卸载/停用即彻底消失，代价是 Discord 适配器丢弃的机器人/Webhook 消息收不到）
        if self.config.get("discord_takeover", True):
            self._discord_hook_task = asyncio.create_task(self._discord_hook_loop())
        else:
            logger.info(
                "[astrbot_plugin_msg_forward_cc] ℹ️ 已关闭 Discord 机器人消息接管（discord_takeover=false），"
                "插件不再改写客户端，机器人/Webhook 消息不会被转发"
            )
            self._unhook_discord_clients()
        # 重复规则提示：同源同目标的两条规则会让「关掉一条仍在转发」看起来像失效
        try:
            for idxs, src, dst in self._duplicate_rule_groups():
                logger.warning(
                    f"[astrbot_plugin_msg_forward_cc] ⚠️ 检测到重复规则 {idxs}（源/目标完全相同）："
                    f"{'、'.join(src)} → {'、'.join(dst)}，建议只保留一条，否则关掉其中一条仍会被另一条转发"
                )
        except Exception as e:
            logger.warning(f"[astrbot_plugin_msg_forward_cc] ⚠️ 重复规则检查失败：{e}")
        logger.info("MsgForward plugin init OK")

    @filter.command_group("mf")
    def mf(self):
        """mf 命令组"""
        pass

    @mf.command("help")
    async def cmd_help(self, event: AstrMessageEvent):
        """显示帮助信息"""
        yield event.plain_result(
            "📋 MsgForward 帮助\n\n"
            "mf\n"
            "├── 🔗 绑定\n"
            "│   ├── add: 创建一则转发绑定请求\n"
            "│   ├── bind (code(str)): 接受一则转发绑定请求\n"
            "│   └── bindraw ([源平台] 源ID [目标平台] 目标ID): 直接创建转发绑定\n"
            "│       平台简写 df/qq/wx/tg/dc，加s为私聊，省略平台=default\n"
            "│       例：/mf bindraw 654321 wx 123456\n"
            "│       例：/mf bindraw dfs 114514 wx 123456s（私聊）\n"
            "├── 📋 规则\n"
            "│   ├── list: 列出当前会话的转发规则（含群号）\n"
            "│   ├── listall: 列出所有转发规则\n"
            "│   ├── del (编号(str)): 删除一条转发规则\n"
            "│   ├── hide (编号(str)): 切换规则来源信息显示/隐藏\n"
            "│   ├── toggle (编号(str)): 启用/停用一条转发规则\n"
            "│   └── remark (编号(str), 备注(str)): 设置规则备注名称，留空清除备注\n"
            "├── ❄ 冷却\n"
            "│   ├── cooldown: 查看当前冷却配置\n"
            "│   ├── cooldown default <秒>: 设置全局默认冷却（0=关闭）\n"
            "│   ├── cooldown <编号> <秒>: 设置某条规则冷却（0=关闭该规则冷却）\n"
            "│   └── cooldown <编号> inherit: 重置为继承全局默认\n"
            "├── 🎯 过滤\n"
            "│   └── filter: 查看当前过滤配置\n"
            "├── 📦 内容类型\n"
            "│   ├── content: 查看内容类型筛选配置\n"
            "│   ├── content list: 查看可选内容类型与别名\n"
            "│   ├── content default <类型...>: 设置全局默认（all=全选）\n"
            "│   ├── content <编号> <类型...>: 设置某条规则转发的内容类型（多选）\n"
            "│   └── content <编号> inherit: 重置为继承全局默认\n"
            "├── 🔔 @ 转发\n"
            "│   ├── at: 查看 @ 转发与昵称反查配置\n"
            "│   ├── at on / at off: 全局开启/关闭 @昵称反查\n"
            "│   ├── at cache <秒>: 群成员列表缓存有效期（0=每次重新拉取）\n"
            "│   ├── at <编号> on|off: 设置某条规则昵称反查（inherit=继承全局）\n"
            "│   └── at test <群号或UMO>: 测试目标群 @昵称反查命中情况\n"
            "├── 🌐 翻译\n"
            "│   ├── translate status: 查看翻译配置与各规则开关\n"
            "│   ├── translate on / off: 全局开启/关闭转发时翻译\n"
            "│   ├── translate to <语言>: 目标语言（zh/中文/en/jp…）\n"
            "│   ├── translate from <语言>: 源语言（auto=自动检测）\n"
            "│   ├── translate interval <毫秒>: 调用接口最小间隔（标准版 QPS=1 建议 1100）\n"
            "│   ├── translate keep on|off: 译文后是否附原文\n"
            "│   ├── translate <编号> on|off|inherit: 规则级翻译开关\n"
            "│   └── translate test <文本>: 实测翻译（验证 APPID/密钥）\n"
            "├── ⏳ 发送队列\n"
            "│   ├── queue status: 查看发送队列状态与配置\n"
            "│   ├── queue on / queue off: 启用/停用发送队列总开关\n"
            "│   ├── queue interval <秒>: 设置全局默认发送队列间隔（0=关闭）\n"
            "│   ├── queue maxsize <条数>: 设置发送队列总上限（0=不限制）\n"
            "│   ├── queue maxsize default <条数>: 同上（与规则编号区分）\n"
            "│   ├── queue maxsize <编号> <条数>: 设置某条规则队列长度上限（0=不限制）\n"
            "│   ├── queue maxsize <编号> inherit: 重置为继承全局上限\n"
            "│   ├── queue retention <小时>: 队列媒体缓存保留时长（0=默认24小时）\n"
            "│   ├── queue set <编号> <秒>: 设置某条规则队列间隔（0=关闭该规则队列）\n"
            "│   ├── queue set <编号> inherit: 重置为继承全局默认\n"
            "│   ├── queue clear: 清空积压队列与媒体缓存\n"
            "│   └── queue pause / queue resume: 暂停/恢复队列消费\n"
            "└── help: 显示此帮助\n\n"
            "冷却：转发一次后在该时间内不会再次转发，避免刷屏。\n"
            "队列：规则设置 queue_interval_seconds > 0 时进入队列，\n"
            "每隔该秒数转发一条；queue_max_size 控制该规则队列长度，\n"
            "达上限后新消息丢弃（总上限同理）。\n"
            "冷却与队列同时开启时冷却失效（队列间隔已在限流），\n"
            "list 中以 ❄失效(队列中) 标记，日志会告警一次。\n"
            "@ 转发：默认 At 一律转为文本 @昵称（不发送真实 At，稳妥）；开启昵称反查\n"
            "（高级 @）后按目标群成员列表把 @昵称 换成真实 qq 再精确 @（默认关闭）。\n"
            "翻译：规则级开关，开启后转发前把文字译为目标语言（百度翻译开放平台）；\n"
            "只翻文字，图片/语音/视频/文件与来源信息头原样转发，接口失败自动保留原文。"
        )

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("add")
    async def cmd_add(self, event: AstrMessageEvent):
        """创建一则消息转发绑定的请求"""
        code = gen_code()
        source_umo = str(event.unified_msg_origin)
        self.store.add_pending(code, source_umo)

        yield event.plain_result(
            f"📌 已创建绑定请求\n"
            f"请在目标会话执行：/mf bind {code}"
        )

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("bind")
    async def cmd_bind(self, event: AstrMessageEvent, code: str):
        """接受一则消息转发绑定的请求"""
        try:
            target_umo = str(event.unified_msg_origin)
            source_umo = self.store.pop_pending(code)
            hide_header = self.config.get("default_hide_header", False)

            idx = self._add_rule(source_umo, target_umo, hide_header)
            yield event.plain_result(f"✅ 已绑定 #{idx}\n{source_umo} → {target_umo}")
        except Exception as e:
            yield event.plain_result(f"❌ 绑定失败：{e}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("bindraw")
    async def cmd_bindraw(self, event: AstrMessageEvent, args: str = ""):
        """直接创建转发绑定（格式：/mf bindraw 平台 群号 平台 群号）"""
        PLATFORM_MAP = {
            "df": "default",
            "qq": "aiocqhttp",
            "wx": "weixin_oc",
            "tg": "telegram",
            "dc": "discord",
        }

        def build_umo(plat: str, uid: str) -> str:
            plat_lower = plat.lower()
            msg_type = "FriendMessage" if plat_lower.endswith("s") else "GroupMessage"
            plat_key = plat_lower[:-1] if plat_lower.endswith("s") else plat_lower
            if not plat_key or plat_key == "default":
                plat_key = "default"
            # 大于 3 个字母的平台名直接作为完整平台标识使用（如 aiocqhttp、weixin_oc）
            if len(plat_key) > 3:
                platform = plat_key
            else:
                platform = PLATFORM_MAP.get(plat_key, plat_key)
            # 兼容在 ID 末尾加 s 表示私聊（如 /mf bindraw 654321 123456s）
            if uid.endswith("s") and msg_type == "GroupMessage" and plat_lower == plat_key:
                msg_type = "FriendMessage"
                uid = uid[:-1]
            return f"{platform}:{msg_type}:{uid}"

        try:
            raw = (event.message_str or "").strip()
            idx = raw.lower().find("bindraw")
            args_str = raw[idx + len("bindraw"):].strip() if idx != -1 else (args or "")
            parts = args_str.split()
            if len(parts) == 2:
                src_plat, dst_plat = "default", "default"
                src_id, dst_id = parts[0], parts[1]
            elif len(parts) == 3:
                if parts[0].isdigit():
                    src_plat = "default"
                    src_id, dst_plat, dst_id = parts
                else:
                    src_plat, src_id, dst_id = parts
                    dst_plat = "default"
            elif len(parts) == 4:
                src_plat, src_id, dst_plat, dst_id = parts
            else:
                yield event.plain_result("❌ 格式错误，用法：/mf bindraw [源平台] 源ID [目标平台] 目标ID\n例：/mf bindraw 654321 wx 123456（省略源平台=default）")
                return
            source_umo = build_umo(src_plat, src_id)
            target_umo = build_umo(dst_plat, dst_id)
            hide_header = self.config.get("default_hide_header", False)

            idx = self._add_rule(source_umo, target_umo, hide_header)
            yield event.plain_result(f"✅ 已绑定 #{idx}\n{source_umo} → {target_umo}")
        except Exception as e:
            yield event.plain_result(f"❌ 直接绑定失败：{e}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("del")
    async def cmd_del(self, event: AstrMessageEvent, rid: str):
        """删除一条转发规则（规则编号从 /mf list 查看）"""
        rules, idx, rule = self._get_rule(rid)
        if rule is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        removed = rules.pop(idx)
        self.config["rules"] = rules
        self.config.save_config()
        yield event.plain_result(
            f"🗑️ 已删除规则 #{rid}（{self._rule_name(removed)}）"
        )

    def _get_rule(self, rid: str):
        """按编号解析规则，返回 (rules, idx, rule)。

        编号非法或越界时返回 (None, None, None)，由调用方统一提示「规则不存在」。
        rules 是可变副本，调用方修改后需自行 self.config["rules"] = rules 并保存。"""
        try:
            idx = int(rid) - 1
        except (TypeError, ValueError):
            return None, None, None
        rules = list(self.config.get("rules", []))
        if idx < 0 or idx >= len(rules):
            return None, None, None
        return rules, idx, rules[idx]

    def _toggle_rule_field(self, rid: str, field: str, on_text: str, off_text: str) -> str | None:
        """切换规则某个布尔字段并持久化，返回成功提示文案；失败返回 None。

        供 /mf hide（hide_header）与 /mf toggle（enabled）复用。"""
        rules, idx, rule = self._get_rule(rid)
        if rule is None:
            return None
        current = bool(rule.get(field, False))
        rule[field] = not current
        self.config["rules"] = rules
        self.config.save_config()
        status = on_text if not current else off_text
        return f"✅ 规则 #{rid}（{self._rule_name(rule)}）{status}"

    def _format_rules(self, items) -> list:
        """把 (规则编号, 规则) 对列表格式化为展示行（启用/隐藏/冷却/队列间隔/队列长度/@反查/内容类型状态）。

        供 /mf list 与 /mf listall 复用，避免两处重复；编号由调用方决定
        （list 传原始编号，listall 传 1..n 递增编号）。"""
        lines = []
        for idx, r in items:
            en_status = "🟢" if r.get("enabled", True) else "⛔"
            hide_status = "🔒" if r.get("hide_header", False) else "🔓"
            cd = self._cooldown_for(r)
            qi = self._queue_interval_for(r)
            qi_str = f"⏳{qi}s" if qi > 0 else ""
            # 队列模式下冷却检查被跳过（队列分支先于冷却检查 continue），标记失效避免误判
            if cd <= 0:
                cd_str = ""
            else:
                cd_str = "❄失效(队列中)" if self._cooldown_ignored(r) else f"❄{cd}s"
            qmax = self._rule_queue_max_size(r)
            qmax_str = f"📮≤{qmax}条" if qmax > 0 else ""
            at_str = "🔔@反查" if self._should_at_lookup(r) else ""
            tr_str = "🌐翻译" if self._should_translate(r) else ""
            # 内容类型覆盖标记：仅当规则显式配置 content_types 时显示
            # （只选 1 类时显示类型名如 📦仅表情，多类显示类数如 📦3类）
            ct_keys = self._rule_content_types_raw(r)
            if ct_keys:
                first = next(k for k in CONTENT_TYPES if k in ct_keys)
                ct_str = f"📦仅{CONTENT_TYPES[first]}" if len(ct_keys) == 1 else f"📦{len(ct_keys)}类"
            else:
                ct_str = ""
            parts = [en_status, f"#{idx}", self._rule_name(r), hide_status, cd_str, qi_str, qmax_str, at_str, ct_str, tr_str]
            lines.append(" ".join(p for p in parts if p))
        return lines

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("list")
    async def cmd_list(self, event: AstrMessageEvent):
        """列出与当前会话相关的所有转发规则"""
        source_umo = str(event.unified_msg_origin)
        rules = self.config.get("rules", [])
        matched = [(idx, r) for idx, r in enumerate(rules, start=1)
                   if source_umo in MsgForward._umo_list(r, "source_umo")]
        if not matched:
            yield event.plain_result(f"📭 当前会话 {source_umo} 没有规则")
            return

        lines = [f"📜 当前会话({source_umo}) 的规则："]
        lines.extend(self._format_rules(matched))
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("hide")
    async def cmd_hide_header(self, event: AstrMessageEvent, rid: str):
        """切换规则的来源信息显示状态（隐藏/显示）"""
        msg = self._toggle_rule_field(rid, "hide_header", "来源信息已隐藏", "来源信息已显示")
        if msg is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        yield event.plain_result(msg)

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("toggle")
    async def cmd_toggle(self, event: AstrMessageEvent, rid: str):
        """切换规则的启用状态（启用/停用）"""
        msg = self._toggle_rule_field(rid, "enabled", "已启用", "已停用")
        if msg is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        yield event.plain_result(msg)

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("remark")
    async def cmd_remark(self, event: AstrMessageEvent, rid: str, remark: str = ""):
        """设置规则的备注名称（留空清除备注，恢复默认显示）"""
        rules, idx, rule = self._get_rule(rid)
        if rule is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        remark = (remark or "").strip()
        if remark:
            rule["remark"] = remark
            self.config["rules"] = rules
            self.config.save_config()
            yield event.plain_result(f"✅ 规则 #{rid} 备注已设为：{remark}")
        else:
            rule.pop("remark", None)
            self.config["rules"] = rules
            self.config.save_config()
            yield event.plain_result(f"✅ 规则 #{rid} 备注已清除（恢复为默认显示）")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("cooldown")
    async def cmd_cooldown(self, event: AstrMessageEvent, args: str = ""):
        """查看/设置转发冷却时间。

        用法：
          /mf cooldown                查看当前冷却配置
          /mf cooldown default <秒>   设置全局默认冷却（0=关闭）
          /mf cooldown <编号> <秒>    设置某条规则冷却（0=关闭，inherit=继承全局）
        """
        args = (args or "").strip()
        # 无参数：查看当前冷却配置
        if not args:
            default_cd = int(self.config.get("default_cooldown_seconds", 0) or 0)
            lines = [f"📋 转发冷却：全局默认 ❄{default_cd}s" if default_cd > 0 else "📋 转发冷却：全局默认 ❄关闭"]
            rules = self.config.get("rules", [])
            has_per_rule = False
            for idx, r in enumerate(rules, start=1):
                cd = r.get("cooldown_seconds")
                if cd is None:
                    continue
                cd = int(cd)
                if not has_per_rule:
                    lines.append("规则级冷却：")
                    has_per_rule = True
                lines.append(f"  #{idx} | {self._rule_name(r)} | ❄{cd}s" if cd > 0 else f"  #{idx} | {self._rule_name(r)} | ❄关闭")
            if not has_per_rule:
                lines.append("（所有规则使用全局默认冷却）")
            lines.append("\n用法：/mf cooldown default <秒> 设全局默认；/mf cooldown <编号> <秒|inherit> 设规则级")
            yield event.plain_result("\n".join(lines))
            return

        parts = args.split()
        # 首参数为 default：设置全局默认冷却
        if parts[0].lower() == "default":
            if len(parts) != 2:
                yield event.plain_result("❌ 用法：/mf cooldown default <秒>（非负整数）")
                return
            try:
                val = int(parts[1])
                if val < 0:
                    raise ValueError
            except ValueError:
                yield event.plain_result("❌ 用法：/mf cooldown default <秒>（非负整数）")
                return
            self.config["default_cooldown_seconds"] = val
            self.config.save_config()
            desc = f"❄{val}s" if val > 0 else "❄关闭"
            yield event.plain_result(f"✅ 全局默认冷却已设为 {desc}")
            return

        # 单参数（纯数字）：兼容旧用法，设置全局默认冷却
        if len(parts) == 1:
            try:
                val = int(parts[0])
                if val < 0:
                    raise ValueError
            except ValueError:
                yield event.plain_result("❌ 用法：/mf cooldown default <秒> 设全局默认；/mf cooldown <编号> <秒|inherit> 设规则级")
                return
            self.config["default_cooldown_seconds"] = val
            self.config.save_config()
            desc = f"❄{val}s" if val > 0 else "❄关闭"
            yield event.plain_result(f"✅ 全局默认冷却已设为 {desc}")
            return

        # 双参数：设置规则级冷却
        rid, arg = parts[0], parts[1].strip().lower()
        rules, idx, rule = self._get_rule(rid)
        if rule is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        if arg == "inherit":
            rule.pop("cooldown_seconds", None)
            self.config["rules"] = rules
            self.config.save_config()
            yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rule)}）冷却已重置为继承全局默认")
            return
        try:
            val = int(arg)
            if val < 0:
                raise ValueError
        except ValueError:
            yield event.plain_result("❌ 用法：/mf cooldown <编号> <秒|inherit>，秒必须是非负整数")
            return
        rule["cooldown_seconds"] = val
        self.config["rules"] = rules
        self.config.save_config()
        desc = f"❄{val}s" if val > 0 else "❄关闭"
        yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rule)}）冷却已设为 {desc}")

    # ----- 内容类型筛选命令（v0.5.0） -----

    @staticmethod
    def _parse_content_type_args(tokens) -> tuple[set | None, str]:
        """解析内容类型参数序列（/mf content 命令用），返回 (类型集合, 错误信息)。

        支持 all（全部类型）与别名（text/img/sticker/emoji/voice/mention 等）；
        含未知类型或为空时返回 (None, 错误提示)，由调用方直接回复给用户。"""
        out = set()
        for tok in tokens:
            t = str(tok).strip().lower()
            if not t:
                continue
            if t == "all":
                out.update(CONTENT_TYPES.keys())
                continue
            key = _CONTENT_TYPE_ALIASES.get(t)
            if not key:
                return None, f"❌ 未知内容类型「{tok}」，用 /mf content list 查看可用类型"
            out.add(key)
        if not out:
            return None, "❌ 未指定任何内容类型，例：/mf content default plain image"
        return out, ""

    @staticmethod
    def _content_types_text(allowed: set) -> str:
        """把内容类型集合格式化为按固定顺序的中文显示名（顿号分隔）。"""
        return "、".join(label for key, label in CONTENT_TYPES.items() if key in allowed)

    @staticmethod
    def _rule_content_types_raw(rule: dict) -> set:
        """读取规则显式配置的 content_types（list 或逗号分隔字符串），返回类型键集合。

        仅解析规则自身的覆盖值，不做全局回退；未配置/为空返回空集合。"""
        ct = rule.get("content_types")
        if isinstance(ct, str):
            ct = [x for x in ct.split(",") if x.strip()]
        if not isinstance(ct, (list, tuple)):
            return set()
        return {_CONTENT_TYPE_ALIASES.get(str(x).strip().lower()) for x in ct} - {None}

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("content")
    async def cmd_content(self, event: AstrMessageEvent, args: str = ""):
        """查看/设置转发的内容类型筛选（多选，未勾选的类型不转发）"""
        args = (args or "").strip()
        # 无参数或 list：查看当前配置与可用类型
        if not args or args.lower() == "list":
            default_types = _content_types_for({}, self.config)
            lines = [
                "📦 内容类型筛选（多选，未勾选的类型不转发）：",
                f"  全局默认：{self._content_types_text(default_types)}",
            ]
            rules = self.config.get("rules", [])
            has_override = False
            for idx, r in enumerate(rules, start=1):
                keys = self._rule_content_types_raw(r)
                if not keys:
                    continue
                if not has_override:
                    lines.append("规则级覆盖：")
                    has_override = True
                lines.append(f"  #{idx} | {self._rule_name(r)} | {self._content_types_text(keys)}")
            if not has_override:
                lines.append("（所有规则继承全局默认）")
            else:
                lines.append("（其余规则继承全局默认）")
            lines.append(
                "类型：plain=文字 image=图片 face=表情 record=语音 video=视频 file=文件 at=@提及 other=其他\n"
                "别名：text=文字 img=图片 sticker/emoji=表情 voice=语音 mention=@提及 all=全部\n"
                "      中文名可直接使用，例：/mf content 2 表情（等价 face）、/mf content 3 图片 文字\n"
                "用法：/mf content default <类型...> 设全局默认（all=全选）；\n"
                "/mf content <编号> <类型...> 设规则级；/mf content <编号> inherit 继承全局"
            )
            yield event.plain_result("\n".join(lines))
            return

        parts = args.split()
        # default 前缀：设置全局默认内容类型
        if parts[0].lower() == "default":
            types, err = self._parse_content_type_args(parts[1:])
            if types is None:
                yield event.plain_result(err)
                return
            self.config["default_content_types"] = [k for k in CONTENT_TYPES if k in types]
            self.config.save_config()
            yield event.plain_result(f"✅ 全局默认内容类型已设为：{self._content_types_text(types)}")
            return

        # 规则级：<编号> <类型...|inherit>
        rid = parts[0]
        rules, idx, rule = self._get_rule(rid)
        if rule is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        if len(parts) == 1:
            yield event.plain_result(
                "❌ 用法：/mf content <编号> <类型...|inherit>\n"
                "例：/mf content 2 表情 或 /mf content 2 face（只转发表情）；\n"
                "/mf content 3 文字 图片 或 /mf content 3 plain image（只转发文字和图片）；\n"
                "/mf content 2 all（全选）；/mf content 2 inherit（继承全局默认）"
            )
            return
        if len(parts) == 2 and parts[1].strip().lower() == "inherit":
            rule.pop("content_types", None)
            self.config["rules"] = rules
            self.config.save_config()
            yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rule)}）内容类型已重置为继承全局默认")
            return
        types, err = self._parse_content_type_args(parts[1:])
        if types is None:
            yield event.plain_result(err)
            return
        rule["content_types"] = [k for k in CONTENT_TYPES if k in types]
        self.config["rules"] = rules
        self.config.save_config()
        yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rule)}）内容类型已设为：{self._content_types_text(types)}")

    @mf.group("at")
    def at(self):
        """at 命令组：@ 转发与昵称反查配置"""
        pass

    @filter.permission_type(filter.PermissionType.ADMIN)
    @at.command("status")
    async def cmd_at_status(self, event: AstrMessageEvent):
        """查看 @ 转发与昵称反查配置（/mf at 等价）"""
        enabled = bool(self.config.get("at_nickname_lookup", False))
        ttl = self._at_lookup_ttl()
        cache_size = len(self._group_member_cache)
        lines = [
            f"🔔 @ 转发：默认 At 转为文本 @昵称；开启高级 @（昵称反查）后按 qq 透传真实 At",
            f"🔍 昵称反查：{'✅ 全局开启' if enabled else '⛔ 全局关闭（默认）'}"
            + (f" | 缓存 {ttl}s" if ttl > 0 else " | 缓存关闭（每次重新拉取）"),
            f"💾 已缓存群成员列表：{cache_size} 个群",
        ]
        rules = self.config.get("rules", [])
        per_rule = [(idx, r) for idx, r in enumerate(rules, start=1) if r.get("at_nickname_lookup") is not None]
        if per_rule:
            lines.append("\n规则级昵称反查：")
            for idx, r in per_rule:
                lines.append(f"  #{idx} | {self._rule_name(r)} | {'🔔开启' if self._should_at_lookup(r) else '关闭'}")
        else:
            lines.append("（所有规则继承全局昵称反查设置）")
        lines.append("\n用法：/mf at on|off 全局开关；/mf at <编号> on|off|inherit 规则级；"
            "/mf at cache <秒> 缓存时长；/mf at test <群号> 测试反查"
        )
        lines.append("说明：默认 At 转为文本 @昵称（不发送真实 At）；开启反查（高级 @）后在目标为 QQ 系群聊时按 qq 透传并反查真实成员，每条消息多一次群成员查询（有缓存）。")
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(filter.PermissionType.ADMIN)
    @at.command("on")
    async def cmd_at_on(self, event: AstrMessageEvent):
        """全局开启 @昵称反查"""
        self.config["at_nickname_lookup"] = True
        self.config.save_config()
        yield event.plain_result("✅ 已全局开启高级 @（昵称反查，规则未单独设置时生效）")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @at.command("off")
    async def cmd_at_off(self, event: AstrMessageEvent):
        """全局关闭 @昵称反查"""
        self.config["at_nickname_lookup"] = False
        self.config.save_config()
        yield event.plain_result("✅ 已全局关闭 @昵称反查（At 将一律转为文本 @昵称）")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @at.command("cache")
    async def cmd_at_cache(self, event: AstrMessageEvent, seconds: str = ""):
        """设置群成员列表缓存有效期（秒，0=每次重新拉取）"""
        arg = (seconds or "").strip()
        try:
            val = int(arg)
            if val < 0:
                raise ValueError
        except ValueError:
            yield event.plain_result("❌ 用法：/mf at cache <秒>（非负整数，0=每次重新拉取）")
            return
        self.config["at_nickname_lookup_cache_ttl"] = val
        self.config.save_config()
        desc = f"{val}s" if val > 0 else "关闭（每次重新拉取）"
        yield event.plain_result(f"✅ 群成员列表缓存已设为 {desc}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @at.command("set")
    async def cmd_at_set(self, event: AstrMessageEvent, rid: str = "", mode: str = ""):
        """设置规则级昵称反查（/mf at <编号> on|off|inherit）"""
        arg = (mode or "").strip().lower()
        if not rid or arg not in ("on", "off", "inherit", "true", "false"):
            yield event.plain_result(
                "❌ 用法：/mf at <编号> on|off|inherit\n"
                "  on=该规则开启反查；off=关闭；inherit=继承全局设置"
            )
            return
        rules, idx, rule = self._get_rule(rid)
        if rule is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        if arg in ("inherit",):
            rule.pop("at_nickname_lookup", None)
            result = "已重置为继承全局"
        else:
            rule["at_nickname_lookup"] = "true" if arg in ("on", "true") else "false"
            result = f"已设为{'🔔开启' if rule['at_nickname_lookup'] == 'true' else '关闭'}"
        self.config["rules"] = rules
        self.config.save_config()
        yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rule)}）昵称反查{result}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @at.command("test")
    async def cmd_at_test(self, event: AstrMessageEvent, args: str = ""):
        """测试目标群 @ 反查：拉取成员列表并显示命中情况"""
        target = (args or "").strip()
        if not target:
            yield event.plain_result("❌ 用法：/mf at test <群号 或 UMO>\n例：/mf at test 123456 或 /mf at test aiocqhttp:GroupMessage:123456")
            return
        parts = target.split(":")
        if len(parts) == 3:
            platform, msg_type, group_id = parts[0].strip().lower(), parts[1], parts[2]
        else:
            platform, msg_type, group_id = "aiocqhttp", "GroupMessage", target
        if platform not in _QQ_TARGET_PLATFORMS or msg_type != "GroupMessage":
            yield event.plain_result(f"❌ 昵称反查仅支持 QQ 系群聊（当前：{platform}:{msg_type}）")
            return
        name_map, id_map = await self._get_group_member_name_map(group_id)
        if not name_map:
            yield event.plain_result(f"❌ 未能拉取群 {group_id} 的成员列表（无 QQ 协议端 / 群号错误 / 无权限），反查将降级为文本 @昵称")
            return
        lines = [f"✅ 群 {group_id} 成员 {len(id_map)} 人已缓存", "样例（昵称 → qq）："]
        for nick, uid in list(name_map.items())[:10]:
            uniq = id_map.get(uid, uid)
            lines.append(f"  {nick} → {uid}" + ("" if uniq == nick else f"（{uniq}）"))
        lines.append("提示：转发时会把 @昵称 中能在上表命中的昵称替换为对应 qq。")
        yield event.plain_result("\n".join(lines))

    @mf.group("translate")
    def translate(self):
        """translate 命令组：转发时翻译（百度翻译开放平台）"""
        pass

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("status")
    async def cmd_translate_status(self, event: AstrMessageEvent):
        """查看翻译配置与各规则开关"""
        settings = self._translate_settings()
        cred = "✅ 已配置" if (settings["appid"] and settings["key"]) else "❌ 未配置（请在 WebUI 填 APPID 与密钥）"
        lines = [
            "🌐 转发时翻译（百度翻译·通用文本翻译）",
            f"总开关：{'✅ 全局开启' if self._global_translate_enabled() else '⛔ 全局关闭（默认）'}",
            f"APPID/密钥：{cred}",
            f"语言：{settings['from']} → {settings['to']}"
            + ("（自动检测源语言）" if settings["from"] == "auto" else ""),
            f"调用间隔：{int(settings['interval'] * 1000)}ms | 超时：{settings['timeout']:.0f}s"
            + (" | 走代理" if settings["use_proxy"] else ""),
            f"已是目标语言则跳过：{'是' if settings['skip_same_lang'] else '否'}"
            f" | 附原文：{'是' if settings['keep_original'] else '否'}",
            "范围：只翻译文字组件，图片/语音/视频/文件等媒体与来源信息头原样转发",
        ]
        rules = self.config.get("rules", [])
        per_rule = [(idx, r) for idx, r in enumerate(rules, start=1) if r.get("translate") is not None]
        if per_rule:
            lines.append("\n规则级翻译：")
            for idx, r in per_rule:
                lines.append(f"  #{idx} | {self._rule_name(r)} | {'🌐开启' if self._should_translate(r) else '关闭'}")
        else:
            lines.append("（所有规则继承全局翻译设置）")
        lines.append(
            "\n用法：/mf translate on|off 全局开关；/mf translate to <语言> 目标语言；"
            "/mf translate from <语言> 源语言；/mf translate interval <毫秒> 调用间隔；"
            "/mf translate keep on|off 是否附原文；/mf translate <编号> on|off|inherit 规则级；"
            "/mf translate test <文本> 实测翻译"
        )
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("on")
    async def cmd_translate_on(self, event: AstrMessageEvent):
        """全局开启转发时翻译"""
        self.config["translate_enabled"] = True
        self.config.save_config()
        missing = "" if (self.config.get("translate_appid") and self.config.get("translate_key")) else \
            "\n⚠️ 还没填百度翻译 APPID / 密钥（WebUI 插件配置里填），填好才会真正翻译"
        yield event.plain_result(f"✅ 已全局开启转发时翻译（规则未单独设置时生效）{missing}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("off")
    async def cmd_translate_off(self, event: AstrMessageEvent):
        """全局关闭转发时翻译"""
        self.config["translate_enabled"] = False
        self.config.save_config()
        yield event.plain_result("✅ 已全局关闭转发时翻译")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("to")
    async def cmd_translate_to(self, event: AstrMessageEvent, lang: str = ""):
        """设置目标语言（如 zh / 中文 / en）"""
        raw = (lang or "").strip()
        if not raw:
            yield event.plain_result("❌ 用法：/mf translate to <语言>（如 zh / 中文 / en / jp，具体代码见百度文档）")
            return
        code = _normalize_lang(raw, "zh")
        if code == "auto":
            yield event.plain_result("❌ 目标语言不能是 auto（自动检测只能用于源语言）")
            return
        self.config["translate_to_lang"] = code
        self.config.save_config()
        yield event.plain_result(f"✅ 翻译目标语言已设为 {code}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("from")
    async def cmd_translate_from(self, event: AstrMessageEvent, lang: str = ""):
        """设置源语言（auto=自动检测）"""
        raw = (lang or "").strip()
        if not raw:
            yield event.plain_result("❌ 用法：/mf translate from <语言>（auto=自动检测，默认）")
            return
        code = _normalize_lang(raw, "auto")
        self.config["translate_from_lang"] = code
        self.config.save_config()
        yield event.plain_result(f"✅ 翻译源语言已设为 {code}" + ("（自动检测）" if code == "auto" else ""))

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("interval")
    async def cmd_translate_interval(self, event: AstrMessageEvent, ms: str = ""):
        """设置两次调用接口的最小间隔（毫秒）"""
        arg = (ms or "").strip()
        try:
            val = int(arg)
            if val < 0:
                raise ValueError
        except ValueError:
            yield event.plain_result(
                "❌ 用法：/mf translate interval <毫秒>（非负整数）\n"
                "  百度标准版 QPS=1 → 建议 1100；高级版可调小（如 150）"
            )
            return
        self.config["translate_interval_ms"] = val
        self.config.save_config()
        yield event.plain_result(f"✅ 翻译调用间隔已设为 {val}ms")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("keep")
    async def cmd_translate_keep(self, event: AstrMessageEvent, mode: str = ""):
        """设置译文后是否附上原文"""
        arg = (mode or "").strip().lower()
        if arg not in ("on", "off", "true", "false"):
            yield event.plain_result("❌ 用法：/mf translate keep on|off（on=译文后附原文）")
            return
        val = arg in ("on", "true")
        self.config["translate_keep_original"] = val
        self.config.save_config()
        yield event.plain_result(f"✅ 转发时{'会' if val else '不会'}附带原文")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("set")
    async def cmd_translate_set(self, event: AstrMessageEvent, rid: str = "", mode: str = ""):
        """设置规则级翻译（/mf translate <编号> on|off|inherit）"""
        arg = (mode or "").strip().lower()
        if not rid or arg not in ("on", "off", "inherit", "true", "false"):
            yield event.plain_result(
                "❌ 用法：/mf translate <编号> on|off|inherit\n"
                "  on=该规则转发时翻译；off=不翻译；inherit=继承全局设置"
            )
            return
        rules, idx, rule = self._get_rule(rid)
        if rule is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        if arg == "inherit":
            rule.pop("translate", None)
            result = "已重置为继承全局"
        else:
            rule["translate"] = "true" if arg in ("on", "true") else "false"
            result = f"已设为{'🌐开启' if rule['translate'] == 'true' else '关闭'}"
        self.config["rules"] = rules
        self.config.save_config()
        yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rule)}）翻译{result}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @translate.command("test")
    async def cmd_translate_test(self, event: AstrMessageEvent, text: str = ""):
        """实测翻译一段文字（用于验证 APPID/密钥是否可用）"""
        raw = (text or "").strip()
        if not raw:
            yield event.plain_result("❌ 用法：/mf translate test <文本>\n例：/mf translate test Hello world")
            return
        settings = self._translate_settings()
        if not settings["appid"] or not settings["key"]:
            yield event.plain_result("❌ 未配置百度翻译 APPID / 密钥，请先在 WebUI 插件配置里填写")
            return
        try:
            result = await self._translate_text(raw, settings)
        except Exception as e:
            yield event.plain_result(
                f"❌ 翻译失败：{e}\n"
                "  常见原因：APPID/密钥错误（54001）、未开通通用文本翻译（54003/54004）、"
                "IP 未在白名单（58000）、调用频率超限（54003）"
            )
            return
        yield event.plain_result(f"✅ 翻译成功（{settings['from']} → {settings['to']}）\n原文：{raw}\n译文：{result}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("listall")
    async def cmd_list_all(self, event: AstrMessageEvent):
        """列出所有转发规则"""
        rules = self.config.get("rules", [])
        if not rules:
            yield event.plain_result("📭 暂无规则")
            return

        lines = ["📜 所有转发规则："]
        lines.extend(self._format_rules(list(enumerate(rules, start=1))))
        lines.extend(self._duplicate_rule_hints())
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(filter.PermissionType.ADMIN)
    @mf.command("filter")
    async def cmd_filter_list(self, event: AstrMessageEvent):
        """查看当前的过滤配置"""
        filter_mode = self.config.get("filter_mode", "off")
        patterns_data = MsgForward._unwrap_patterns(self.config.get("filter_patterns"))

        mode_text = {"off": "关闭", "blacklist": "黑名单", "whitelist": "白名单"}.get(filter_mode, filter_mode)
        lines = [f"📋 全局过滤：{mode_text}" + (f"（共 {len(patterns_data)} 条）" if patterns_data else "")]

        if filter_mode == "off":
            lines.append("      （关闭，未启用过滤）")
        elif not patterns_data:
            lines.append(f"      （已启用但未配置过滤规则）")
        else:
            for i, item in enumerate(patterns_data, start=1):
                tp, val = MsgForward._parse_filter_item(item)
                tag = "[正]" if tp == "regex" else "[关]"
                lines.append(f"      {tag} {i}. {val}")

        # 显示各规则的单独过滤配置
        rules = self.config.get("rules", [])
        has_per_rule = False
        for idx, r in enumerate(rules, start=1):
            rfm = r.get("filter_mode", "inherit")
            rfp = r.get("filter_patterns", [])
            if rfm != "inherit" or (rfp and len(rfp) > 0):
                if not has_per_rule:
                    lines.append(f"\n📋 规则级过滤（共 {len(rules)} 条规则）：")
                    has_per_rule = True
                rm_text = {"off": "关闭", "blacklist": "黑名单", "whitelist": "白名单"}.get(rfm, "继承全局") if rfm != "inherit" else "继承全局"
                lines.append(f"  #{idx} | {self._rule_name(r)} | {rm_text}")
                if rfp:
                    for j, item in enumerate(rfp, start=1):
                        tp, val = MsgForward._parse_filter_item(str(item))
                        tag = "[正]" if tp == "regex" else "[关]"
                        lines.append(f"      {tag} {j}. {val}")

        if not has_per_rule:
            lines.append("（所有规则使用全局过滤配置）")

        # 显示冷却配置
        default_cd = self.config.get("default_cooldown_seconds", 0)
        cd_desc = f"{default_cd}s" if int(default_cd) > 0 else "关闭"
        lines.append(f"\n📋 转发冷却：全局默认 ❄{cd_desc}")
        for idx, r in enumerate(rules, start=1):
            if r.get("cooldown_seconds") is None:
                continue
            try:
                cd_val = max(int(r.get("cooldown_seconds") or 0), 0)
            except (TypeError, ValueError):
                cd_val = 0
            if cd_val > 0:
                tail = "（队列中失效）" if self._cooldown_ignored(r) else ""
                lines.append(f"  #{idx} | {self._rule_name(r)} | ❄{cd_val}s{tail}")
            else:
                lines.append(f"  #{idx} | {self._rule_name(r)} | ❄关闭")

        yield event.plain_result("\n".join(lines))

    @mf.group("queue")
    def queue(self):
        """queue 命令组：发送队列配置"""
        pass

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("status")
    async def cmd_queue_status(self, event: AstrMessageEvent):
        """查看发送队列状态与配置"""
        enabled = bool(self.config.get("queue_enabled", False))
        default_qi = int(self.config.get("default_queue_interval_seconds", 0) or 0)
        max_size = int(self.config.get("queue_max_size", 0) or 0)
        retention = int(self.config.get("queue_media_retention_hours", 0) or 0)
        if retention <= 0:
            retention = 24
        pending = self._queue_total_size()

        lines = [
            "📋 发送队列状态：",
            f"  总开关：{'🟢 已启用' if enabled else '⛔ 已停用'}",
            f"  消费状态：{'⏸️ 已暂停' if self._queue_paused else '▶️ 运行中'}",
            f"  默认间隔：{'⏳' + str(default_qi) + 's' if default_qi > 0 else '关闭'}",
            f"  队列总上限：{'无限制' if max_size <= 0 else str(max_size) + ' 条'}",
            f"  媒体缓存保留：{retention} 小时",
            f"  当前积压：{pending} 条",
        ]
        if not enabled:
            lines.append("  ⚠️ 总开关已停用，即使规则设置了间隔也不会进入队列")
        if self._queue_paused:
            lines.append("  ⚠️ 队列已暂停，积压消息暂不发送（/mf queue resume 恢复）")
        lines.append("\n📋 各规则队列（间隔 / 长度上限 / 当前积压）：")
        lines.extend(self._queue_rule_table_lines())
        lines.append(
            "\n提示：下表规则已进入队列模式，其冷却 ❄ 会被跳过（队列间隔本身已在限流），"
            "/mf list 中以 ❄失效(队列中) 标记"
        )
        lines.append(
            "\n用法：/mf queue maxsize <条数>（或 default <条数>）设总上限；"
            "/mf queue maxsize <编号> <条数|inherit> 设规则级长度上限"
        )
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("on")
    async def cmd_queue_on(self, event: AstrMessageEvent):
        """启用发送队列总开关"""
        self.config["queue_enabled"] = True
        self.config.save_config()
        yield event.plain_result("✅ 发送队列已启用")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("off")
    async def cmd_queue_off(self, event: AstrMessageEvent):
        """停用发送队列总开关"""
        self.config["queue_enabled"] = False
        self.config.save_config()
        yield event.plain_result("✅ 发送队列已停用（规则设置的间隔将不再生效）")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("interval")
    async def cmd_queue_interval(self, event: AstrMessageEvent, seconds: str):
        """设置全局默认发送队列间隔（秒），0=关闭"""
        try:
            val = int(seconds)
            if val < 0:
                raise ValueError
        except ValueError:
            yield event.plain_result("❌ 间隔必须是非负整数（秒），如 /mf queue interval 5")
            return
        self.config["default_queue_interval_seconds"] = val
        self.config.save_config()
        desc = f"⏳{val}s" if val > 0 else "关闭"
        yield event.plain_result(f"✅ 全局默认队列间隔已设为 {desc}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("maxsize")
    async def cmd_queue_maxsize(self, event: AstrMessageEvent, size: str = ""):
        """设置发送队列长度上限。

        用法：
          /mf queue maxsize                      查看总上限与各规则长度上限
          /mf queue maxsize <条数>               设置全局队列总上限（0=不限制）
          /mf queue maxsize default <条数>       同上（与规则编号区分）
          /mf queue maxsize <编号> <条数>        设置某条规则的队列长度上限（0=不限制）
          /mf queue maxsize <编号> inherit       重置为继承全局上限
        """
        args = (size or "").strip()
        # 无参数：查看当前配置
        if not args:
            gmax = self._queue_global_max()
            lines = [
                f"📋 队列总上限：{'无限制' if gmax <= 0 else str(gmax) + ' 条'}",
                "各规则队列长度上限（间隔 / 上限 / 当前积压）：",
            ]
            lines.extend(self._queue_rule_table_lines())
            lines.append(
                "\n用法：/mf queue maxsize <条数>（或 default <条数>）设总上限；"
                "/mf queue maxsize <编号> <条数|inherit> 设规则级长度上限"
            )
            yield event.plain_result("\n".join(lines))
            return

        parts = args.split()
        # default 前缀：设置全局总上限
        if parts[0].lower() == "default":
            if len(parts) != 2:
                yield event.plain_result("❌ 用法：/mf queue maxsize default <条数>（非负整数）")
                return
            try:
                val = int(parts[1])
                if val < 0:
                    raise ValueError
            except ValueError:
                yield event.plain_result("❌ 用法：/mf queue maxsize default <条数>（非负整数）")
                return
            self.config["queue_max_size"] = val
            self.config.save_config()
            desc = "不限制" if val == 0 else f"{val} 条"
            yield event.plain_result(f"✅ 发送队列总上限已设为 {desc}")
            return

        # 单参数（纯数字）：兼容旧用法，设置全局总上限
        if len(parts) == 1:
            try:
                val = int(parts[0])
                if val < 0:
                    raise ValueError
            except ValueError:
                yield event.plain_result(
                    "❌ 用法：/mf queue maxsize <条数>（全局总上限）或 "
                    "/mf queue maxsize <编号> <条数|inherit>（规则级）"
                )
                return
            self.config["queue_max_size"] = val
            self.config.save_config()
            desc = "不限制" if val == 0 else f"{val} 条"
            yield event.plain_result(f"✅ 发送队列总上限已设为 {desc}")
            return

        # 双参数：设置规则级队列长度上限
        rid, arg = parts[0], parts[1].strip().lower()
        rules, idx, rule = self._get_rule(rid)
        if rule is None:
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return
        if arg == "inherit":
            # 删除键 → 恢复为继承全局上限（无独立上限）
            rules[idx].pop("queue_max_size", None)
            self.config["rules"] = rules
            self.config.save_config()
            yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rules[idx])}）队列长度上限已重置为继承全局")
            return
        try:
            val = int(arg)
            if val < 0:
                raise ValueError
        except ValueError:
            yield event.plain_result(
                "❌ 用法：/mf queue maxsize <编号> <条数|inherit>，条数必须是非负整数，如 /mf queue maxsize 2 10"
            )
            return
        rules[idx]["queue_max_size"] = val
        self.config["rules"] = rules
        self.config.save_config()
        desc = "不限制（继承全局总上限）" if val == 0 else f"≤{val} 条"
        yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rules[idx])}）队列长度上限已设为 {desc}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("retention")
    async def cmd_queue_retention(self, event: AstrMessageEvent, hours: str):
        """设置队列媒体缓存保留时长（小时），0=默认24小时"""
        try:
            val = int(hours)
            if val < 0:
                raise ValueError
        except ValueError:
            yield event.plain_result("❌ 保留时长必须是非负整数（小时），如 /mf queue retention 48")
            return
        self.config["queue_media_retention_hours"] = val
        self.config.save_config()
        desc = f"{val} 小时" if val > 0 else "默认 24 小时"
        yield event.plain_result(f"✅ 队列媒体缓存保留时长已设为 {desc}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("set")
    async def cmd_queue_set(self, event: AstrMessageEvent, rid: str, seconds: str):
        """设置某条规则的队列间隔（秒），0=关闭该规则队列，inherit=重置为继承全局"""
        try:
            idx = int(rid) - 1
        except ValueError:
            yield event.plain_result("❌ 用法：/mf queue set <规则编号> <秒|inherit>，如 /mf queue set 2 5 或 /mf queue set 2 inherit")
            return
        rules = list(self.config.get("rules", []))
        if idx < 0 or idx >= len(rules):
            yield event.plain_result(f"❌ 规则 #{rid} 不存在")
            return

        arg = (seconds or "").strip().lower()
        if arg == "inherit":
            # 删除键 → 恢复为继承全局默认间隔
            rules[idx].pop("queue_interval_seconds", None)
            self.config["rules"] = rules
            self.config.save_config()
            yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rules[idx])}）队列间隔已重置为继承全局默认")
            return

        try:
            val = int(arg)
            if val < 0:
                raise ValueError
        except ValueError:
            yield event.plain_result("❌ 用法：/mf queue set <规则编号> <秒|inherit>，秒必须是非负整数，如 /mf queue set 2 5")
            return
        rules[idx]["queue_interval_seconds"] = val
        self.config["rules"] = rules
        self.config.save_config()
        desc = f"⏳{val}s" if val > 0 else "关闭（立即转发）"
        yield event.plain_result(f"✅ 规则 #{rid}（{self._rule_name(rules[idx])}）队列间隔已设为 {desc}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("clear")
    async def cmd_queue_clear(self, event: AstrMessageEvent):
        """清空当前积压的发送队列，并清理队列媒体缓存"""
        n = self._queue_total_size()
        for q in self._rule_queues.values():
            while not q.empty():
                try:
                    q.get_nowait()
                    q.task_done()
                except asyncio.QueueEmpty:
                    break
        self._rule_queues.clear()
        # 队列已空，按规则归集的积压计数与下次发送记录一并清零
        self._queue_rule_counts = {}
        self._rule_next_send.clear()
        # 唤醒 worker 及时重算（它可能正睡在某规则的等待时刻上）
        self._queue_wake.set()
        # 同步清空磁盘持久化队列
        try:
            self._save_persisted_queue([])
        except Exception:
            pass
        cache_deleted = self._clear_media_cache()
        msg = f"🗑️ 已清空发送队列（丢弃 {n} 条积压消息）"
        if cache_deleted is not None:
            msg += f"\n🧹 已清理 {cache_deleted} 个队列媒体缓存文件"
        yield event.plain_result(msg)

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("pause")
    async def cmd_queue_pause(self, event: AstrMessageEvent):
        """暂停发送队列消费：已入队的消息暂不发送，新消息仍可入队"""
        if self._queue_paused:
            yield event.plain_result("⏸️ 发送队列已处于暂停状态")
            return
        self._queue_paused = True
        yield event.plain_result(f"⏸️ 发送队列已暂停（当前积压 {self._queue_total_size()} 条暂不发送）")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @queue.command("resume")
    async def cmd_queue_resume(self, event: AstrMessageEvent):
        """恢复发送队列消费"""
        if not self._queue_paused:
            yield event.plain_result("▶️ 发送队列未处于暂停状态")
            return
        self._queue_paused = False
        # 唤醒 worker：它可能正睡在等待条目的唤醒事件上（见 _queue_worker）
        self._queue_wake.set()
        yield event.plain_result(f"▶️ 发送队列已恢复（继续发送积压的 {self._queue_total_size()} 条消息）")

    def _clear_media_cache(self) -> int | None:
        """清空队列媒体缓存目录（AstrBot data 目录下 media/）下的所有文件。

        返回删除的文件数；目录不存在时返回 None（表示无缓存可清理）。"""
        tmp_dir = _get_media_cache_dir()
        if not tmp_dir.exists():
            return None
        deleted = 0
        for f in tmp_dir.iterdir():
            if f.is_file():
                try:
                    f.unlink()
                    deleted += 1
                except OSError:
                    pass
        return deleted

    async def _resolve_file_urls(self, event: AstrMessageEvent, chain):
        """为链中无 URL 的 File 组件尝试从原始 OneBot 消息获取下载 URL。

        通过 `event.message_obj.raw_message` 获取原始 OneBot 消息段中的 `file_id`，
        调用 `get_group_file_url` API 获取下载 URL，使 File 组件能通过 URL 转发
        （而非本地路径，NapCat 读不到跨进程的容器内本地路径）。"""
        umo = str(event.unified_msg_origin)
        raw_event = getattr(event.message_obj, "raw_message", None)
        if not raw_event or not isinstance(raw_event, dict):
            return chain

        raw_segments = raw_event.get("message")
        if not isinstance(raw_segments, list):
            return chain

        # 从原始消息段中提取 file_path → url 映射
        file_url_map = {}
        for seg in raw_segments:
            if seg.get("type") != "file":
                continue
            data = seg.get("data", {})
            file_path = data.get("file", "")
            url = data.get("url", "")
            if url and url.startswith(("http://", "https://")):
                file_url_map[file_path] = url
            elif data.get("file_id"):
                # 尝试调用 OneBot API 获取下载 URL
                try:
                    from astrbot.core.platform.sources.aiocqhttp.aiocqhttp_platform_adapter import AiocqhttpAdapter
                    parts = umo.split(":")
                    group_id = parts[2] if len(parts) >= 3 and parts[1] == "GroupMessage" else None
                    if not group_id:
                        continue
                    for platform in self.context.platform_manager.get_insts():
                        if isinstance(platform, AiocqhttpAdapter):
                            ret = await platform.bot.call_action(
                                action="get_group_file_url",
                                file_id=data["file_id"],
                                group_id=group_id,
                            )
                            if ret and "url" in ret:
                                file_url_map[file_path] = ret["url"]
                                logger.info(f"ℹ️ 通过 get_group_file_url 获取到文件下载 URL")
                except ImportError:
                    pass
                except Exception as e:
                    logger.warning(f"⚠️ 调用 get_group_file_url 失败: {e}")

        if not file_url_map:
            return chain

        # 替换链中无 URL 的 File 组件（有 URL 的用最新获取的 URL 替换，可能更有效/未过期）
        cleaned = []
        for comp in chain:
            if isinstance(comp, File):
                name = getattr(comp, "name", None) or ""
                file_ = getattr(comp, "file_", None) or ""
                url = getattr(comp, "url", None) or ""
                if url and url.startswith(("http://", "https://")):
                    new_url = file_url_map.get(name) or file_url_map.get(file_)
                    if new_url and new_url != url:
                        cleaned.append(File(name=name, url=new_url))
                        continue
                    cleaned.append(comp)
                    continue
                # 用文件名或 file_ 路径匹配（OneBot 消息段 file 字段可能是文件名或路径）
                matched_url = file_url_map.get(name) or file_url_map.get(file_)
                if matched_url:
                    cleaned.append(File(name=name, url=matched_url))
                    continue
            cleaned.append(comp)
        return cleaned

    # ----- @昵称反查 qq（v0.5.0 可选增强，默认关闭） -----

    # 群成员列表缓存：group_id → (拉取时间戳, {昵称/群名片: user_id}, {user_id: 昵称})
    # 反查 @ 时优先用缓存，避免每条消息都拉一次成员列表
    _group_member_cache: dict = {}
    _GROUP_MEMBER_CACHE_TTL = 300  # 秒
    _GROUP_MEMBER_CACHE_MAX = 32   # 最多缓存的群数，超出按最旧淘汰
    # 同一群的并发拉取合并：group_id → asyncio 任务（避免瞬间多条消息各拉一次）
    _group_member_inflight: dict = {}

    def _should_at_lookup(self, rule: dict) -> bool:
        """判断某条规则是否开启「高级 @（昵称反查）」。

        关闭（默认）：转发时 At 一律转为文本 @昵称，不发送真实 At 组件；
        开启：QQ 系目标按 qq 透传真实 At，并按目标群成员列表反查昵称精确 @。
        规则显式设置为 true/false 时按规则值决定；inherit（或未设置）时继承全局配置。
        兼容旧版 bool 存储（True/False）。"""
        val = rule.get("at_nickname_lookup")
        if isinstance(val, bool):
            return val
        if isinstance(val, str):
            if val == "true":
                return True
            if val == "false":
                return False
            # "inherit" 或其他值 → 继承全局
        return bool(self.config.get("at_nickname_lookup", False))

    def _at_lookup_ttl(self) -> int:
        """群成员列表缓存有效期（秒），0 表示每次都重新拉取；默认 300 秒。"""
        try:
            ttl = int(self.config.get("at_nickname_lookup_cache_ttl", 300) or 0)
        except (TypeError, ValueError):
            ttl = 300
        return max(ttl, 0)

    def _member_cache_get(self, group_id: str):
        """取群成员缓存（未命中或已过期返回 None）；过期项顺手清除。"""
        cached = self._group_member_cache.get(group_id)
        if not cached:
            return None
        ttl = self._at_lookup_ttl()
        if ttl <= 0 or time.time() - cached[0] >= ttl:
            self._group_member_cache.pop(group_id, None)
            return None
        return cached

    def _member_cache_put(self, group_id: str, name_map: dict, id_map: dict):
        """写入群成员缓存，并按上限淘汰最旧的条目。"""
        self._group_member_cache[group_id] = (time.time(), name_map, id_map)
        max_size = self._GROUP_MEMBER_CACHE_MAX
        if max_size > 0 and len(self._group_member_cache) > max_size:
            oldest = sorted(self._group_member_cache.items(), key=lambda kv: kv[1][0])
            for key, _ in oldest[:len(self._group_member_cache) - max_size]:
                self._group_member_cache.pop(key, None)

    async def _fetch_group_member_list(self, group_id: str):
        """调用 get_group_member_list 拉取目标群成员列表（不缓存、不抛异常）。

        逐个已加载平台尝试：按群号数字匹配 AiocqhttpAdapter；匹配不到时回退到
        首个 AiocqhttpAdapter（兼容非 QQ 协议端 / 群号非纯数字的 UMO）。
        全部失败返回 None，由调用方降级为文本 @昵称。"""
        try:
            from astrbot.core.platform.sources.aiocqhttp.aiocqhttp_platform_adapter import AiocqhttpAdapter
        except Exception as e:
            logger.warning(f"⚠️ 无法加载 aiocqhttp 适配器，@ 昵称反查不可用：{e}")
            return None
        try:
            adapters = [p for p in self.context.platform_manager.get_insts()
                        if isinstance(p, AiocqhttpAdapter)]
        except Exception as e:
            logger.warning(f"⚠️ 获取平台实例失败，@ 昵称反查降级为文本：{e}")
            return None
        if not adapters:
            return None
        candidates = []
        if group_id.isdigit():
            for p in adapters:
                try:
                    if str(getattr(p, "self_id", "") or "") == group_id:
                        continue
                    candidates.append(p)
                except Exception:
                    candidates.append(p)
        # 数字群号优先逐个尝试；非数字 UMO 或都未命中时回退首个适配器
        for platform in (candidates or adapters[:1]):
            try:
                ret = await platform.bot.call_action(
                    action="get_group_member_list",
                    group_id=int(group_id),
                )
            except Exception as e:
                logger.warning(f"⚠️ 拉取群成员列表失败（群 {group_id}），@ 昵称反查降级为文本：{e}")
                continue
            if isinstance(ret, dict):
                # 部分协议端把成员列表包在 {"data": [...]} / {"members": [...]} 里
                for key in ("data", "members", "list"):
                    if isinstance(ret.get(key), list):
                        ret = ret[key]
                        break
            if isinstance(ret, list):
                return ret
        return None

    async def _get_group_member_name_map(self, group_id: str):
        """拉取（或取缓存）目标群成员列表，返回 (昵称→user_id, user_id→昵称) 映射。

        群名片（card）优先、昵称（nickname）兜底；同名时后者覆盖前者。
        缓存有效期由 at_nickname_lookup_cache_ttl 控制；同一群的并发拉取会合并。
        失败返回 (None, None)（不抛异常，由调用方降级为文本 @昵称）。"""
        cached = self._member_cache_get(group_id)
        if cached:
            return cached[1], cached[2]
        inflight = self._group_member_inflight.get(group_id)
        if inflight is None:
            inflight = asyncio.ensure_future(self._fetch_group_member_list(group_id))
            self._group_member_inflight[group_id] = inflight
            inflight.add_done_callback(lambda _t, gid=group_id: self._group_member_inflight.pop(gid, None))
        try:
            ret = await asyncio.shield(inflight)
        except Exception as e:
            logger.warning(f"⚠️ 拉取群成员列表失败（群 {group_id}），@ 昵称反查降级为文本：{e}")
            return None, None
        if not ret:
            return None, None
        name_map = {}
        id_map = {}
        for m in ret:
            if not isinstance(m, dict):
                continue
            uid = str(m.get("user_id", "") or "")
            if not uid:
                continue
            card = (m.get("card") or "").strip()
            nickname = (m.get("nickname") or "").strip()
            display = card or nickname
            if display:
                id_map[uid] = display
            # 群名片优先，昵称作为独立的可匹配键（同名时后出现的覆盖）
            if card:
                name_map[card] = uid
            if nickname:
                name_map[nickname] = uid
        self._member_cache_put(group_id, name_map, id_map)
        logger.info(f"ℹ️ 已拉取群 {group_id} 成员列表：{len(id_map)} 人（缓存 {self._at_lookup_ttl()}s）")
        return name_map, id_map

    async def _resolve_at_mentions(self, chain, target: str) -> list:
        """高级 @ 模式：把链中「无法解析的 @ 提及」按昵称反查为目标群真实成员。

        反查顺序（优先 qq 精确匹配，昵称仅作兜底）：
          1. 纯数字 qq / @全体 → 不动，直接透传（协议端可精确解析，无需反查）；
          2. 数字 qq 但目标群中不存在该成员 → 用 At.name 反查目标群成员，命中则替换 qq；
          3. 非数字目标（openid / uid 等）→ 同样按 name 反查替换为数字 qq；
          4. 反查不到 / 目标非 QQ 群 / 拉取失败 → 保留原 At 与 name，后续由
             _sanitize_at_chain_for_target 按目标平台决定透传或降级为文本 @昵称。

        昵称重名（多人同名）时不做替换：随机 @ 错人比降级为文本更糟，仅记录日志。"""
        if not chain:
            return chain
        parts = str(target).split(":")
        if len(parts) != 3 or parts[0].strip().lower() not in _QQ_TARGET_PLATFORMS or parts[1] != "GroupMessage":
            return chain
        group_id = parts[2]
        name_map, id_map = await self._get_group_member_name_map(group_id)
        if not name_map:
            return chain
        # 同名检测：同一昵称被两个及以上成员占用时，该昵称不参与反查
        # （用 id_map 反查：id_map 一个 user_id 对应一个人，计数准确）
        ambiguous = set()
        counts = {}
        for uid, display in id_map.items():
            counts[display] = counts.get(display, 0) + 1
        for nick in name_map:
            if counts.get(nick, 0) > 1:
                ambiguous.add(nick)
        cleaned = []
        for comp in chain:
            if not isinstance(comp, At):
                cleaned.append(comp)
                continue
            qq = str(getattr(comp, "qq", "") or "").strip()
            name = (getattr(comp, "name", "") or "").strip()
            if qq == "all":
                cleaned.append(comp)
                continue
            if qq.isdigit() and qq != "0" and qq in id_map:
                # qq 本身在目标群可精确解析：不改动
                cleaned.append(comp)
                continue
            if not name:
                cleaned.append(comp)
                continue
            if name in ambiguous:
                logger.warning(f"⚠️ 目标群 {group_id} 中存在多个昵称 {name!r}，@ 反查跳过（避免 @ 错人）")
                cleaned.append(comp)
                continue
            found = name_map.get(name)
            if found:
                cleaned.append(At(qq=found, name=name))
                logger.info(f"ℹ️ 已将昵称 {name!r} 反查为目标群成员 {found}（原目标 {qq or '空'}）")
            else:
                cleaned.append(comp)
        return cleaned

    def _should_forward(self, event: AstrMessageEvent, rule: dict = None) -> bool:
        # 确定生效的过滤模式和规则列表
        if rule:
            fm = rule.get("filter_mode", "inherit")
            if fm == "inherit":
                fm = self.config.get("filter_mode", "off")
            rfp = rule.get("filter_patterns")
            if rfp and len(rfp) > 0:
                fp = rfp
            else:
                fp = MsgForward._unwrap_patterns(self.config.get("filter_patterns"))
        else:
            fm = self.config.get("filter_mode", "off")
            fp = MsgForward._unwrap_patterns(self.config.get("filter_patterns"))

        if fm == "off":
            return True

        fp = [x.strip() for x in fp if x.strip()]
        if not fp:
            return True

        msg_text = event.message_str
        msg_lower = msg_text.lower()

        for item in fp:
            item_type, item_val = self._parse_filter_item(item)
            if not item_val:
                continue
            if item_type == "keyword":
                if item_val.lower() in msg_lower:
                    return fm == "whitelist"
            else:
                if re.search(item_val, msg_text):
                    return fm == "whitelist"

        return fm == "blacklist"

    @staticmethod
    def _parse_filter_item(item: str):
        """解析一条过滤规则，返回 (type, value)"""
        s = item.strip()
        if s.startswith("regex:"):
            return "regex", s[6:].strip()
        return "keyword", s

    @staticmethod
    def _unwrap_patterns(patterns):
        """将全局 filter_patterns 统一转为字符串列表（兼容 text 和 template_list 格式）"""
        if not patterns:
            return []
        if isinstance(patterns, str):
            return [x.strip() for x in patterns.splitlines() if x.strip()]
        if isinstance(patterns, list):
            return [item.get("rule", "").strip() for item in patterns
                    if isinstance(item, dict) and item.get("rule", "").strip()]
        return []

    def _should_download_media(self, rule: dict) -> bool:
        """判断某条规则是否需要在发送前先把媒体下载到本地。

        规则显式设置为 true/false 时按规则值决定；inherit（或未设置）时继承全局配置。
        兼容旧版 bool 存储（True/False）。"""
        val = rule.get("download_media_before_send")
        if isinstance(val, bool):
            return val
        if isinstance(val, str):
            if val == "true":
                return True
            if val == "false":
                return False
            # "inherit" 或其他值 → 继承全局
        return bool(self.config.get("download_media_before_send", False))

    def _queue_interval_for(self, rule: dict) -> int:
        """解析某条规则生效的发送队列间隔（秒）。

        规则未设置（键不存在）时继承全局 default_queue_interval_seconds；
        显式设置为 0 时关闭队列（立即转发），语义与冷却字段一致。"""
        val = rule.get("queue_interval_seconds")
        if val is None:
            val = self.config.get("default_queue_interval_seconds", 0)
        try:
            return int(val) if val else 0
        except (TypeError, ValueError):
            return 0

    def _cooldown_for(self, rule: dict) -> int:
        """解析某条规则生效的转发冷却时间（秒）。

        规则未设置（键不存在）时继承全局 default_cooldown_seconds；
        显式设置为 0 时关闭本规则冷却，语义与 queue_interval_seconds 一致。"""
        val = rule.get("cooldown_seconds")
        if val is None:
            val = self.config.get("default_cooldown_seconds", 0)
        try:
            return max(int(val) if val else 0, 0)
        except (TypeError, ValueError):
            return 0

    def _cooldown_ignored(self, rule: dict) -> bool:
        """判断该规则的冷却是否因进入队列模式而被跳过（实际失效）。

        forward_message 中队列分支先于冷却检查 continue，冷却判断与写入都不再执行，
        后台 worker 也不读冷却表——此时只有队列间隔在限流。
        仅当总开关开启且规则实际处于队列模式（间隔 > 0）时成立；总开关关闭时
        队列间隔被强制置 0，冷却仍正常生效。"""
        return self._queue_interval_for(rule) > 0 and bool(self.config.get("queue_enabled", False))

    def _queue_global_max(self) -> int:
        """全局发送队列总上限（所有规则合计积压条数），0=不限制。"""
        try:
            return max(int(self.config.get("queue_max_size", 0) or 0), 0)
        except (TypeError, ValueError):
            return 0

    def _rule_queue_max_size(self, rule: dict) -> int:
        """解析某条规则生效的队列长度上限（条）。

        规则未设置 queue_max_size（键不存在）或为 0 时，该规则没有独立上限，
        仅受全局 queue_max_size 总上限约束；> 0 时该规则最多积压该条数，
        达到后新消息被丢弃（记录错误日志）。语义与 cooldown_seconds 一致。"""
        val = rule.get("queue_max_size")
        try:
            return max(int(val) if val else 0, 0)
        except (TypeError, ValueError):
            return 0

    def _queue_total_size(self) -> int:
        """统计全部规则队列的积压条数总和（各规则桶 qsize 之和）。"""
        return sum(q.qsize() for q in self._rule_queues.values())

    def _rule_queue(self, rule_key: str) -> asyncio.Queue:
        """按 rule_key 取对应规则桶队列，不存在时懒创建（空规则 key 归入共用桶）。"""
        q = self._rule_queues.get(rule_key)
        if q is None:
            q = asyncio.Queue()
            self._rule_queues[rule_key] = q
        return q

    def _queued_count_for_rule(self, rule_key: str) -> int:
        """统计队列中属于某条规则的积压条数（按入队时记录的 rule_key 归集）。

        计数在入队时 +1、worker 取走条目时 -1，不依赖 asyncio.Queue 的内部实现
        （Queue.queue 自 Python 3.11 起废弃、3.13 已移除）。
        同一规则的多目标转发会产生多条队列条目，全部计入该规则。"""
        if not rule_key:
            return 0
        return self._queue_rule_counts.get(rule_key, 0)

    def _dec_queue_count(self, rule_key: str):
        """worker 取走（或清空）一条队列条目后递减该规则的积压计数。"""
        if not rule_key:
            return
        n = self._queue_rule_counts.get(rule_key, 0)
        if n <= 1:
            self._queue_rule_counts.pop(rule_key, None)
        else:
            self._queue_rule_counts[rule_key] = n - 1

    def _rule_queue_max_size_for_key(self, rule_key: str) -> int:
        """按 rule_key 查找对应规则并返回其队列长度上限（0=无独立上限）。

        规则已删除/找不到时返回 0，不再对新消息施加该规则的上限，
        避免残留 key 导致消息被误丢弃。"""
        if not rule_key:
            return 0
        for r in self.config.get("rules", []):
            if isinstance(r, dict) and self._rule_key(r) == rule_key:
                return self._rule_queue_max_size(r)
        return 0

    def _queue_rule_table_lines(self) -> list:
        """生成「各规则队列」状态行：间隔 / 长度上限 / 当前积压。

        仅列出启用了队列间隔或设置了独立长度上限的规则；都没有时返回占位提示。"""
        lines = []
        rules = self.config.get("rules", [])
        has_rule = False
        for idx, r in enumerate(rules, start=1):
            qi = self._queue_interval_for(r)
            qmax = self._rule_queue_max_size(r)
            if qi <= 0 and qmax <= 0:
                continue
            has_rule = True
            qi_txt = f"⏳{qi}s" if qi > 0 else "⏳关闭"
            qmax_txt = f"📮≤{qmax}条" if qmax > 0 else "📮不限"
            cnt = self._queued_count_for_rule(self._rule_key(r))
            lines.append(f"  #{idx} | {self._rule_name(r)} | {qi_txt} {qmax_txt} | 积压 {cnt} 条")
        if not has_rule:
            lines.append("  （无规则启用队列或设置独立长度上限，全部立即转发）")
        return lines

    def _enqueue_send(self, target: str, result: MessageEventResult, interval: int,
                      sanitized_chain, header_text: str, has_media: bool,
                      use_proxy: bool, proxy_url, rule_key: str = "", rule_label: str = ""):
        """把一次转发任务加入发送队列，交由后台 worker 按间隔依次发送。

        同时保存兜底所需的信息，供发送失败时在 worker 内本地化媒体后重试。
        入队前依次检查两级上限，任一达到即拒绝入队并记录错误：
          1. 全局 queue_max_size —— 所有规则合计的队列总上限；
          2. 规则级 queue_max_size —— 本规则在队列中的独立积压上限（按 rule_key 归集）。
        入队后同步持久化到磁盘（queue.json），重启/重载后由 initialize 恢复。"""
        global_max = self._queue_global_max()
        if global_max > 0 and self._queue_total_size() >= global_max:
            logger.error(
                f"❌ 发送队列已满（总上限 {global_max} 条），本条消息被丢弃 → {target}。"
                f"请调大 queue_max_size 或降低发送频率。"
            )
            return
        rule_max = self._rule_queue_max_size_for_key(rule_key)
        if rule_max > 0:
            used = self._queued_count_for_rule(rule_key)
            if used >= rule_max:
                label = f"（{rule_label}）" if rule_label else ""
                logger.error(
                    f"❌ 规则队列已满{label}（上限 {rule_max} 条，已积压 {used} 条），"
                    f"本条消息被丢弃 → {target}。请调大该规则的 queue_max_size 或降低发送频率。"
                )
                return
        uid = secrets.token_hex(8)
        item = {
            "uid": uid,
            "target": target,
            "result": result,
            "interval": max(0, interval),
            "sanitized_chain": sanitized_chain,
            "header_text": header_text,
            "has_media": has_media,
            "use_proxy": use_proxy,
            "proxy_url": proxy_url,
            "rule_key": rule_key,
        }
        # 按规则分桶入队（不同规则的桶互不阻塞，各自按自己的间隔调度）
        self._rule_queue(rule_key).put_nowait(item)
        # 唤醒 worker：可能有规则桶已到可发送时刻（或初始立即可发）
        self._queue_wake.set()
        if rule_key:
            self._queue_rule_counts[rule_key] = self._queue_rule_counts.get(rule_key, 0) + 1
        # 持久化：入队即写盘（序列化链组件），发送成功后由 worker 按 uid 移除
        try:
            persisted = self._load_persisted_queue()
            persisted.append({
                "uid": uid,
                "target": target,
                "interval": max(0, interval),
                "chain": _serialize_chain(sanitized_chain),
                "header_text": header_text,
                "has_media": has_media,
                "use_proxy": use_proxy,
                "proxy_url": proxy_url,
                "rule_key": rule_key,
            })
            self._save_persisted_queue(persisted)
        except Exception as e:
            logger.warning(f"⚠️ 队列持久化失败（不影响本次入队）：{e}")

    def _load_persisted_queue(self) -> list:
        """读取磁盘上未发送完的队列条目（queue.json）。"""
        try:
            if self.queue_file.exists():
                data = load_json(self.queue_file)
                if isinstance(data, list):
                    return data
                if isinstance(data, dict) and isinstance(data.get("items"), list):
                    return data["items"]
            return []
        except Exception as e:
            logger.warning(f"⚠️ 读取持久化队列失败：{e}")
            return []

    def _save_persisted_queue(self, items: list):
        """把未发送完的队列条目写回磁盘（queue.json）。"""
        try:
            save_json(self.queue_file, {"items": items})
        except Exception as e:
            logger.warning(f"⚠️ 写入持久化队列失败：{e}")

    def _remove_persisted_item(self, uid: str):
        """发送成功后从磁盘队列移除对应条目（按 uid）。"""
        if not uid:
            return
        try:
            items = self._load_persisted_queue()
            before = len(items)
            items = [it for it in items if it.get("uid") != uid]
            if len(items) != before:
                self._save_persisted_queue(items)
        except Exception as e:
            logger.warning(f"⚠️ 更新持久化队列失败：{e}")

    def _restore_persisted_queue(self):
        """重启/重载后把磁盘上未发送完的队列条目重新入队。

        媒体组件保持序列化时的 URL/路径；若本地化媒体已随清理被删除，
        仍按原样入队，由 worker 发送失败时走媒体兜底降级。"""
        items = self._load_persisted_queue()
        if not items:
            return
        restored = 0
        for it in items:
            try:
                chain = _deserialize_chain(it.get("chain", []))
                if not chain:
                    continue
                header_text = it.get("header_text", "") or ""
                # sanitized_chain 不含来源头；result 才前置来源头（与入队时一致）
                result_chain = ([Plain(text=header_text)] + chain) if header_text else chain
                result = MessageEventResult(chain=result_chain)
                rk = it.get("rule_key", "") or ""
                self._rule_queue(rk).put_nowait({
                    "uid": it.get("uid", ""),
                    "target": it.get("target", ""),
                    "result": result,
                    "interval": int(it.get("interval", 0) or 0),
                    "sanitized_chain": chain,
                    "header_text": header_text,
                    "has_media": bool(it.get("has_media", False)),
                    "use_proxy": bool(it.get("use_proxy", False)),
                    "proxy_url": it.get("proxy_url", None),
                    "rule_key": rk,
                })
                if rk:
                    self._queue_rule_counts[rk] = self._queue_rule_counts.get(rk, 0) + 1
                restored += 1
            except Exception as e:
                logger.warning(f"⚠️ 恢复队列条目失败：{e}")
        if restored:
            logger.info(f"✅ 已从磁盘恢复 {restored} 条未发送完的队列消息")

    async def _queue_worker(self):
        """后台发送队列消费者：按规则（rule_key）分桶独立调度。

        每条规则一个 FIFO 桶，各自维护「下一次可发送时刻」（_rule_next_send），
        到点才发送该桶的下一条——不同规则的间隔互不拖累：60s 的规则不会因
        300s 的规则刚发过一条而被迫多等（旧版单一全局队列 + 统一 sleep 的
        头阻塞问题，见 __init__ 中 _rule_queues 注释）。

        单条消息发送失败（含异常）只记录日志、不影响后续消息；整体用外层兜底，
        确保 worker 永不因单条消息或意外异常而退出，避免队列永久卡住。"""
        while True:
            try:
                # 暂停时阻塞等待，直到 resume 唤醒；不消费队列中的消息
                while self._queue_paused:
                    await asyncio.sleep(0.5)
                now = time.monotonic()
                # 找一条「已到可发送时刻且有积压」的规则桶（FIFO 依次发送）
                ready_key = None
                for rule_key, q in self._rule_queues.items():
                    if not q.empty() and self._rule_next_send.get(rule_key, 0.0) <= now:
                        ready_key = rule_key
                        break
                if ready_key is not None:
                    q = self._rule_queues[ready_key]
                    item = q.get_nowait()
                    self._dec_queue_count(item.get("rule_key", ""))
                    try:
                        await self._send_queued_item(item)
                    except Exception as e:
                        logger.error(f"❌ 队列发送异常: {e}")
                    finally:
                        q.task_done()
                    # 间隔从发送完成起算（保持旧版语义：发完一条隔 N 秒再发下一条）
                    self._rule_next_send[ready_key] = \
                        time.monotonic() + item.get("interval", 0)
                    # 发送完立即回到循环顶部：其他规则桶可能已到点
                    continue
                # 没有桶到点：睡到最近的到期时刻；期间新条目入队会唤醒提前重算
                next_at = None
                for rule_key, q in self._rule_queues.items():
                    if q.empty():
                        continue
                    nxt = self._rule_next_send.get(rule_key, 0.0)
                    if next_at is None or nxt < next_at:
                        next_at = nxt
                self._queue_wake.clear()
                if next_at is None:
                    # 全部规则桶为空：挂起等待新条目入队
                    await self._queue_wake.wait()
                else:
                    wait = max(0.0, next_at - time.monotonic())
                    try:
                        await asyncio.wait_for(self._queue_wake.wait(), timeout=wait)
                    except asyncio.TimeoutError:
                        pass
            except asyncio.CancelledError:
                # 插件终止（terminate 调用 task.cancel()）时正常退出，其余情况不让 worker 挂掉
                raise
            except Exception as e:
                logger.error(f"❌ 队列 worker 异常，已恢复继续运行: {e!r}")
                await asyncio.sleep(1)

    async def _send_queued_item(self, item: dict):
        """发送队列中的单条消息，失败时先尝试重新本地化媒体再重试。

        第一层降级：用 AstrBot 核心 downloader（convert_to_file_path）重新本地化所有
        媒体组件，覆盖因队列延迟导致源端临时文件路径/短效 URL 过期的问题；
        超时保护（45s）防止 downloader 挂死阻塞队列；
        第二层降级：对远程 URL 媒体用裸 aiohttp 下载（_prepare_chain_fallback）兜底。
        任一成功路径都会从磁盘持久化队列移除该条（uid）。
        发送前会为链中 Video/File 媒体注册 AstrBot 文件服务 token（每次发送实时注册，
        避免单次 token 与 300s 过期问题），使跨容器目标端（NapCat）能通过 URL 下载。"""
        target = item["target"]
        result = item["result"]
        uid = item.get("uid", "")
        try:
            # 发送前：为 Video/File 注册文件服务 URL（Image/Record 由 aiocqhttp 转 base64）
            outgoing = await _prepare_chain_for_media_urls(result.chain)
            await self.context.send_message(target, MessageEventResult(chain=outgoing))
            self._remove_persisted_item(uid)
        except ValueError as e:
            logger.error(f"❌ 不合法的 session 字符串，转发失败: {e}")
        except Exception as e:
            # 第一层降级：AstrBot 核心重新本地化所有媒体（覆盖本地临时路径过期）
            try:
                prepared = await asyncio.wait_for(
                    _prepare_chain_for_forward(item["sanitized_chain"]),
                    timeout=45,
                )
                fb_chain = prepared if not item["header_text"] else \
                    [Plain(text=item["header_text"])] + prepared
                # 重试前同样注册文件服务 URL
                fb_chain = await _prepare_chain_for_media_urls(fb_chain)
                await self.context.send_message(target, MessageEventResult(chain=fb_chain))
                self._remove_persisted_item(uid)
                logger.warning(f"⚠️ 队列转发首次失败（{e}），已重新本地化媒体后重试成功")
            except asyncio.TimeoutError:
                logger.warning(f"⚠️ 队列转发：媒体本地化超时（45s），进入远程 URL 兜底")
                # 第二层降级：远程 URL 媒体
                if item.get("has_media"):
                    try:
                        localized = await _prepare_chain_fallback(
                            item["sanitized_chain"],
                            use_proxy=item["use_proxy"],
                            proxy_url=item["proxy_url"],
                        )
                        fb_chain = localized if not item["header_text"] else \
                            [Plain(text=item["header_text"])] + localized
                        fb_chain = await _prepare_chain_for_media_urls(fb_chain)
                        await self.context.send_message(target, MessageEventResult(chain=fb_chain))
                        self._remove_persisted_item(uid)
                        logger.warning(f"⚠️ 队列转发二次降级，已通过远程 URL 本地化后重试成功")
                    except Exception as e3:
                        logger.error(f"❌ 队列转发失败（本地化重试后仍失败）: {e3}")
                else:
                    logger.error(f"❌ 队列转发失败: 媒体本地化超时且无媒体可兜底")
            except Exception as e2:
                # 第二层降级：原始兜底，仅处理远程 URL 媒体
                if item.get("has_media"):
                    try:
                        localized = await _prepare_chain_fallback(
                            item["sanitized_chain"],
                            use_proxy=item["use_proxy"],
                            proxy_url=item["proxy_url"],
                        )
                        fb_chain = localized if not item["header_text"] else \
                            [Plain(text=item["header_text"])] + localized
                        fb_chain = await _prepare_chain_for_media_urls(fb_chain)
                        await self.context.send_message(target, MessageEventResult(chain=fb_chain))
                        self._remove_persisted_item(uid)
                        logger.warning(f"⚠️ 队列转发二次降级，已通过远程 URL 本地化后重试成功")
                    except Exception as e3:
                        logger.error(f"❌ 队列转发失败（本地化重试后仍失败）: {e3}")
                else:
                    logger.error(f"❌ 队列转发失败: {e2}")

    def _cleanup_old_media(self):
        """清理超过保留时间的媒体缓存文件。"""
        retention_hours = int(self.config.get("queue_media_retention_hours", 0) or 0)
        if retention_hours <= 0:
            retention_hours = 24
        tmp_dir = _get_media_cache_dir()
        if not tmp_dir.exists():
            return
        cutoff = time.time() - retention_hours * 3600
        deleted = 0
        for f in tmp_dir.iterdir():
            if f.is_file() and f.stat().st_mtime < cutoff:
                try:
                    f.unlink()
                    deleted += 1
                except OSError:
                    pass
        if deleted:
            logger.info(f"🧹 已清理 {deleted} 个过期队列媒体缓存文件")

    async def _periodic_cleanup(self):
        """每小时清理一次过期媒体缓存。"""
        while True:
            try:
                await asyncio.sleep(3600)
                self._cleanup_old_media()
            except asyncio.CancelledError:
                raise
            except Exception:
                pass

    # ----- 重复规则检测（同源同目标的规则会让「关掉一条仍在转发」看起来像失效） -----

    def _duplicate_rule_groups(self) -> list:
        """按「源集合 + 目标集合」分组，返回存在多条规则的分组：[(编号列表, 源, 目标), ...]。"""
        groups: dict = {}
        for idx, rule in enumerate(self.config.get("rules", []), start=1):
            if not isinstance(rule, dict):
                continue
            src = tuple(sorted(MsgForward._umo_list(rule, "source_umo")))
            dst = tuple(sorted(MsgForward._umo_list(rule, "target_umo")))
            if not src or not dst:
                continue
            groups.setdefault((src, dst), []).append(idx)
        return [(idxs, key[0], key[1]) for key, idxs in groups.items() if len(idxs) > 1]

    def _duplicate_rule_hints(self) -> list:
        """把重复规则整理成展示行（供 /mf listall 提示）。"""
        lines = []
        for idxs, src, dst in self._duplicate_rule_groups():
            lines.append(
                f"⚠️ 规则 {'、'.join('#' + str(i) for i in idxs)} 的源/目标完全相同（{'、'.join(src)} → {'、'.join(dst)}），"
                f"转发会重复，建议 /mf del 删掉多余的那些"
            )
        return lines

    # ----- 转发时翻译（百度翻译开放平台，仅翻文字） -----
    def _global_translate_enabled(self) -> bool:
        """全局翻译开关（规则未单独设置时生效）。"""
        return bool(self.config.get("translate_enabled", False))

    def _should_translate(self, rule: dict) -> bool:
        """判断某条规则转发时是否翻译：规则显式 true/false 优先，inherit（或未设置）继承全局。

        兼容旧版 bool 存储（True/False）。"""
        val = rule.get("translate")
        if isinstance(val, bool):
            return val
        if isinstance(val, str):
            v = val.strip().lower()
            if v in ("true", "on"):
                return True
            if v in ("false", "off"):
                return False
        return self._global_translate_enabled()

    def _translate_settings(self) -> dict:
        """读取翻译相关全局配置（防御式转换，非法值降级为默认）。"""
        def _int(key: str, default: int, minimum: int = 0) -> int:
            try:
                val = int(self.config.get(key, default) or 0)
            except (TypeError, ValueError):
                return default
            return max(val, minimum)

        return {
            "appid": str(self.config.get("translate_appid", "") or "").strip(),
            "key": str(self.config.get("translate_key", "") or "").strip(),
            "from": _normalize_lang(str(self.config.get("translate_from_lang", "auto") or ""), "auto"),
            "to": _normalize_lang(str(self.config.get("translate_to_lang", "zh") or ""), "zh"),
            "interval": _int("translate_interval_ms", 1100, 0) / 1000.0,
            "timeout": float(_int("translate_timeout", 10, 1)),
            "keep_original": bool(self.config.get("translate_keep_original", False)),
            "skip_same_lang": bool(self.config.get("translate_skip_same_lang", True)),
            "use_proxy": bool(self.config.get("translate_use_proxy", False)),
            "proxy_url": str(self.config.get("translate_proxy_url", "") or "").strip(),
        }

    def _warn_translate_once(self, key: str, message: str) -> None:
        """翻译相关告警按 key 只打一次，避免每条消息刷屏。"""
        if key in self._translate_warned:
            return
        self._translate_warned.add(key)
        logger.warning(f"[astrbot_plugin_msg_forward_cc] ⚠️ {message}")

    async def _translate_text(self, text: str, settings: dict) -> str:
        """翻译一段文字：保护链接/标记 → 调接口 → 还原占位符；异常由调用方降级为原文。"""
        if settings["skip_same_lang"] and _looks_like_lang(text, settings["to"]):
            return text
        protected, mapping = _protect_translate_tokens(text)
        result = await _baidu_translate(
            protected,
            settings["appid"], settings["key"], settings["from"], settings["to"],
            timeout=settings["timeout"], interval=settings["interval"],
            use_proxy=settings["use_proxy"], proxy_url=settings["proxy_url"] or None,
        )
        restored = _restore_translate_tokens(result, mapping)
        if restored is None:
            self._warn_translate_once("placeholder", "翻译结果改动了链接/标记占位符，本条保留原文")
            return text
        restored = restored.strip()
        if not restored or restored == text:
            return text
        if settings["keep_original"]:
            return f"{restored}\n\n—— 原文 ——\n{text}"
        return restored

    async def _translate_chain(self, chain: list) -> list:
        """翻译消息链中的文字组件，图片/语音/视频/文件等媒体原样保留。

        未配置 APPID/密钥、接口报错、占位符被破坏时都保留原文继续转发，绝不影响转发本身。"""
        if not any(isinstance(c, Plain) and (c.text or "").strip() for c in chain):
            return chain
        settings = self._translate_settings()
        if not settings["appid"] or not settings["key"]:
            self._warn_translate_once(
                "cred", "已开启翻译但未配置百度翻译 APPID/密钥（translate_appid / translate_key），本次不翻译"
            )
            return chain
        texts = [c.text for c in chain if isinstance(c, Plain) and (c.text or "").strip()]
        translated: dict = {}
        for text in dict.fromkeys(texts):  # 同一条消息内的重复文本只调一次接口
            try:
                translated[text] = await self._translate_text(text, settings)
            except Exception as e:
                self._warn_translate_once(f"fail:{type(e).__name__}", f"翻译失败，本条保留原文继续转发：{e}")
                translated[text] = text
        out = []
        for comp in chain:
            if isinstance(comp, Plain) and comp.text in translated:
                out.append(Plain(text=translated[comp.text]))
            else:
                out.append(comp)
        return out

    # ----- 平台机器人消息接管（仅 Discord） -----

    @staticmethod
    def _is_discord_platform(platform: object) -> bool:
        """判断平台适配器实例是否为 Discord 适配器。"""
        try:
            meta = platform.meta()
        except Exception:
            return False
        return getattr(meta, "name", "") == "discord"

    async def _discord_hook_loop(self) -> None:
        """低频轮询为 Discord 适配器挂载机器人消息监听。

        适配器客户端（platform.client）要等平台 run() 才创建，插件加载时通常还不存在；
        平台重连/重载也会换新客户端，所以用轮询持续补齐，而不是只在 initialize 挂一次。
        每轮先自检存活：插件被停用/卸载后核心不保证调用 terminate()，此时必须自己摘监听并退出。
        """
        while True:
            if not _plugin_alive(self):
                self._self_disable("插件已停用或卸载")
                return
            try:
                self._hook_discord_clients()
            except asyncio.CancelledError:
                raise
            except Exception as e:
                logger.warning(f"[astrbot_plugin_msg_forward_cc] ⚠️ Discord 机器人消息接管异常：{e}")
            await asyncio.sleep(_DISCORD_HOOK_INTERVAL)

    def _self_disable(self, reason: str) -> None:
        """自检判定插件已不可用：摘掉自己补挂的监听并停掉后台任务。

        不依赖核心是否调用 terminate()（WebUI 卸载/停用可能跳过），保证监听不会带着旧配置继续转发。
        """
        if self._self_disabled:
            return
        self._self_disabled = True
        logger.info(
            f"[astrbot_plugin_msg_forward_cc] ℹ️ 检测到{reason}，已摘除 Discord 机器人消息监听并停止后台任务"
        )
        try:
            self._unhook_discord_clients()
        except Exception as e:
            logger.warning(f"[astrbot_plugin_msg_forward_cc] ⚠️ 摘除 Discord 监听失败：{e}")
        for task in (self._discord_hook_task, self._queue_worker_task, self._cleanup_task):
            if task is not None and task is not asyncio.current_task():
                task.cancel()

    @staticmethod
    def _discord_client_of(platform: object) -> object | None:
        """取 Discord 适配器持有的 py-cord 客户端。

        核心各版本的属性名不一定叫 `client`，因此先按属性名取，取不到再按能力探测
        （带 add_listener 且有 user 的对象即为客户端），避免版本差异导致静默不挂载。
        """
        client = getattr(platform, "client", None)
        if client is not None and hasattr(client, "add_listener"):
            return client
        for value in vars(platform).values():
            if hasattr(value, "add_listener") and hasattr(value, "user"):
                return value
        return None

    def _hook_discord_clients(self) -> None:
        """为所有已就绪的 Discord 客户端补挂机器人消息监听（幂等）。

        只有当前活跃实例才挂载：插件重载后旧实例的任务可能尚未结束，若不拦住，
        新旧实例会来回抢挂监听，旧实例还会按旧配置继续转发。"""
        if not self.config.get("discord_takeover", True):
            return  # 接管开关关闭：绝不改写客户端对象
        active = _active_of(self.context)
        if active is not None and active is not self:
            return
        try:
            from astrbot.core.platform.sources.discord.discord_platform_event import (
                DiscordPlatformEvent,
            )
        except ImportError as e:
            if not self._discord_hook_warned:
                self._discord_hook_warned = True
                logger.warning(f"[astrbot_plugin_msg_forward_cc] ⚠️ 无法导入 Discord 事件类，机器人消息接管不可用：{e}")
            return

        hooked = 0
        found = 0
        pending = ""
        for platform in self.context.platform_manager.get_insts():
            if not MsgForward._is_discord_platform(platform):
                continue
            found += 1
            client = MsgForward._discord_client_of(platform)
            if client is None:
                pending = f"{type(platform).__name__} 尚未持有可用客户端"
                continue
            hook = getattr(client, _DISCORD_HOOK_ATTR, None)
            if hook is not None:
                if hook[0] is self:
                    hooked += 1
                    continue
                # 活跃实例持有的监听不要抢（否则新旧实例来回抢挂）
                if hook[0] is active:
                    continue
                try:
                    client.remove_listener(hook[1])
                except Exception as e:
                    logger.warning(f"[astrbot_plugin_msg_forward_cc] ⚠️ 摘除旧 Discord 机器人消息监听失败：{e}")
            listener = self._build_discord_bot_listener(platform, client, DiscordPlatformEvent)
            try:
                client.add_listener(listener, "on_message")
                setattr(client, _DISCORD_HOOK_ATTR, (self, listener))
            except Exception as e:
                pending = f"挂载 {type(client).__name__} 失败：{e}"
                logger.warning(f"[astrbot_plugin_msg_forward_cc] ⚠️ 挂载 Discord 机器人消息监听失败：{e}")
                try:
                    client.remove_listener(listener)
                except Exception:
                    pass
                continue
            hooked += 1

        if hooked and not self._discord_hook_logged:
            self._discord_hook_logged = True
            logger.info(
                f"[astrbot_plugin_msg_forward_cc] ✅ 已接管 {hooked} 个 Discord 适配器的机器人/Webhook 消息转发"
            )

        if found and not hooked:
            # 有 Discord 适配器却没挂上（客户端还没就绪 / 结构不符）：约 1 分钟后告警一次，避免静默失效
            self._discord_hook_attempts += 1
            if self._discord_hook_attempts >= 4 and not self._discord_hook_ready_warned:
                self._discord_hook_ready_warned = True
                logger.warning(
                    f"[astrbot_plugin_msg_forward_cc] ⚠️ 发现 {found} 个 Discord 适配器，但机器人消息监听尚未挂载：{pending}"
                )

    def _unhook_discord_clients(self) -> None:
        """摘除本实例挂载的 Discord 机器人消息监听（插件重载/卸载时调用）。"""
        for platform in self.context.platform_manager.get_insts():
            if not MsgForward._is_discord_platform(platform):
                continue
            client = MsgForward._discord_client_of(platform)
            if client is None:
                continue
            hook = getattr(client, _DISCORD_HOOK_ATTR, None)
            # 只摘自己的监听：重载期间新旧实例可能并存，误摘会漏掉消息
            if not hook or hook[0] is not self:
                continue
            try:
                client.remove_listener(hook[1])
            except Exception as e:
                logger.warning(f"[astrbot_plugin_msg_forward_cc] ⚠️ 摘除 Discord 机器人消息监听失败：{e}")
            try:
                delattr(client, _DISCORD_HOOK_ATTR)
            except AttributeError:
                pass

    def _build_discord_bot_listener(
        self,
        platform: "DiscordPlatformAdapter",
        client: "discord.Client",
        event_cls: type["DiscordPlatformEvent"],
    ) -> Callable[["discord.Message"], Awaitable[None]]:
        """构造补挂在 Discord 客户端上的 on_message 监听（只接管机器人消息）。

        py-cord 的 dispatch 会同时调用适配器覆写的 on_message 与 add_listener 注册的
        附加监听，所以普通用户消息仍由核心管道投递，这里只补核心丢弃的机器人消息，
        并且不经过核心管道直接调用本插件的转发逻辑（避免顺带把 LLM 唤醒）。
        """

        async def _on_discord_bot_message(message: "discord.Message") -> None:
            try:
                # 始终用当前活跃实例转发：WebUI 保存配置会重载插件（清 sys.modules 重新导入），
                # 旧实例带着旧配置留在客户端上就会「关掉规则仍照转」。优先取 Context 上的活跃
                # 实例，其次取客户端上最后挂载的监听所属实例，都没有才退回自身
                info = getattr(client, _DISCORD_HOOK_ATTR, None)
                plugin = _active_of(self.context) or (info[0] if info else None) or self
                # 插件已被停用/卸载（核心不保证调用 terminate）：自己摘掉监听并停止转发
                if not _plugin_alive(plugin):
                    plugin._self_disable("插件已停用或卸载")
                    return
                author = getattr(message, "author", None)
                if author is None or not getattr(author, "bot", False):
                    return
                bot_user = getattr(client, "user", None)
                if bot_user is not None and getattr(author, "id", None) == getattr(bot_user, "id", None):
                    return  # 机器人自身消息，跳过以避免自转发回环
                convert = getattr(platform, "_convert_message_to_abm", None)
                if convert is None:
                    logger.warning("[astrbot_plugin_msg_forward_cc] ⚠️ Discord 适配器缺少消息转换方法，本条机器人消息跳过")
                    return
                abm = convert({"message": message})
                if asyncio.iscoroutine(abm):
                    # 兼容核心把消息转换改为异步的版本
                    abm = await abm
                if not abm.message:
                    # 无正文也无附件（系统提示、纯 Embed 卡片等）跳过；前几条记日志便于排查
                    if plugin._discord_empty_skipped < 5:
                        plugin._discord_empty_skipped += 1
                        logger.info(
                            "[astrbot_plugin_msg_forward_cc] ℹ️ 跳过一条无正文/附件的 Discord 机器人消息"
                            f"（频道 {getattr(abm, 'session_id', '')}，Discord 卡片 Embed 暂不转换）"
                        )
                    return
                if not abm.self_id and bot_user is not None:
                    abm.self_id = str(bot_user.id)
                # 与 forward_message 里的认领配合：已认领过（核心管道先到，或另一个监听先到）就直接退出，
                # 省掉构造事件的开销；真正的去重在 forward_message 里做，这里只是快速路径
                message_id = str(getattr(abm, "message_id", "") or "")
                if message_id and message_id in plugin._discord_handled_ids:
                    return
                event = event_cls(
                    message_str=abm.message_str,
                    message_obj=abm,
                    platform_meta=platform.meta(),
                    session_id=abm.session_id,
                    client=client,
                )
                # 标记事件来自补挂监听（仅用于日志/排查，去重不再依赖它）
                setattr(event, _DISCORD_HOOK_EVENT_ATTR, True)
                await plugin.forward_message(event)
            except Exception as e:
                logger.error(f"[astrbot_plugin_msg_forward_cc] ❌ Discord 机器人消息转发异常：{e}")

        return _on_discord_bot_message

    @filter.event_message_type(filter.EventMessageType.ALL)
    async def forward_message(self, event: AstrMessageEvent):
        """主转发逻辑"""
        try:
            source_umo = str(event.unified_msg_origin)
            # Discord 消息有多条投递通道：核心事件管道 + 本插件补挂的客户端监听（插件重载/更新后
            # 若旧监听没摘干净，还可能同时挂着多个监听）。它们在同一个事件循环里并发调用本函数，
            # 因此按消息 ID 做一次性认领：谁先到谁登记并转发，其余一律跳过。
            # 检查与登记之间不能有 await，否则并发投递会同时通过检查导致重复转发。
            message_id = str(getattr(event.message_obj, "message_id", "") or "")
            if event.get_platform_name() == "discord" and message_id:
                if message_id in self._discord_handled_ids:
                    return
                if len(self._discord_handled_ids) >= _DISCORD_HANDLED_IDS_MAX:
                    self._discord_handled_ids.clear()
                self._discord_handled_ids.add(message_id)
            # 带上 1-based 规则编号（与 /mf list 显示的编号一致）
            rules = [(rid, r) for rid, r in enumerate(self.config.get("rules", []), start=1)
                     if source_umo in MsgForward._umo_list(r, "source_umo")]
            if not rules:
                return
            # 一条消息命中多条规则时会分别转发（每个规则 × 每个目标各一条），命中数记一行日志，
            # 便于区分「插件重复发送」和「本来就有多条规则/多个目标」
            if len(rules) > 1:
                logger.info(
                    f"[astrbot_plugin_msg_forward_cc] 📋 消息 {message_id or '-'}（{source_umo}）同时命中 "
                    f"{len(rules)} 条规则：{'、'.join('#' + str(rid) for rid, _ in rules)}，将分别转发"
                )

            raw_chain = event.get_messages()
            # 清洗无效的 @ 提及（空目标）
            sanitized_chain = _sanitize_chain_for_forward(raw_chain)
            # 清洗 File 组件的本地路径：NapCat 读不到源端本地路径，仅保留 URL 走下载
            sanitized_chain = _sanitize_file_chain_for_forward(sanitized_chain)
            # 为无 URL 的 File 组件尝试从原始 OneBot 消息获取下载 URL（get_group_file_url）
            sanitized_chain = await self._resolve_file_urls(event, sanitized_chain)
            # At 可透传的目标平台集合（内置 QQ 系 + 配置追加）
            at_passthrough = _at_passthrough_platforms(self.config)
            now = time.time()
            # 本次事件里「已实际发送过的目标 → 首次发送它的规则编号」：同一条源消息对同一目标
            # 只允许发一次（多条规则命中同源同目标、或同一目标写了两遍，都只会造成刷屏）
            sent_targets: dict[str, int] = {}

            for rid, rule in rules:
                targets = MsgForward._umo_list(rule, "target_umo")
                if not targets:
                    continue
                # 规则启用开关：关闭的规则直接跳过（默认启用，兼容旧版规则）
                if not rule.get("enabled", True):
                    continue
                # 队列归集用的稳定规则标识（不依赖编号，规则增删/排序后仍有效）
                rule_key = self._rule_key(rule)
                # 逐规则过滤检查
                if not self._should_forward(event, rule):
                    continue

                # 内容类型筛选（v0.5.0）：仅保留规则选中的类型，默认全选
                allowed = _content_types_for(rule, self.config)
                filtered_chain = _filter_chain_by_types(sanitized_chain, allowed)
                if not filtered_chain:
                    # 消息不含任何选中类型，跳过该规则（不转发、不占冷却）
                    continue

                # 转发时翻译（规则级开关）：只翻文字组件，媒体与来源信息头都不动
                translate_on = self._should_translate(rule)
                if translate_on:
                    filtered_chain = await self._translate_chain(filtered_chain)

                # 冷却检查
                cooldown_sec = self._cooldown_for(rule)

                # 发送队列间隔：> 0 时消息进入队列，由后台 worker 每隔该秒数发送一条
                queue_interval = self._queue_interval_for(rule)
                if queue_interval > 0 and not self.config.get("queue_enabled", False):
                    queue_interval = 0
                # 队列模式下冷却检查与写入都会被跳过（队列分支先于冷却检查 continue），冷却实际失效；
                # 同时配置两者容易误判，按 rule_key 只告警一次
                if queue_interval > 0 and cooldown_sec > 0 and rule_key not in self._cooldown_warned:
                    self._cooldown_warned.add(rule_key)
                    logger.warning(
                        f"⚠️ 规则 #{rid}（{self._rule_name(rule)}）同时设置了冷却 ❄{cooldown_sec}s 与队列间隔 "
                        f"⏳{queue_interval}s：队列模式下冷却检查被跳过，实际只有队列间隔在限流。"
                        f"如需冷却生效请关闭该规则的队列间隔（/mf queue set {rid} 0）"
                    )

                # 主消息链：默认透传（正常网络，媒体交给目标端自行处理）；
                # 开启 download_media_before_send 时，发送前先本地化。
                if self._should_download_media(rule):
                    message_chain = await _prepare_chain_for_forward(filtered_chain)
                else:
                    message_chain = filtered_chain

                # 来源头：仅当「文字」在选中类型中才前置（hide_header 时始终不前置）。
                # 只转发图片/视频等纯媒体时，消息里不含任何文字，来源头也不附带。
                header_text = ""
                if _should_attach_header(rule, allowed):
                    header_text = self._format_origin_header(event, source_umo) + "\n\n\u200b"

                # 是否含媒体组件（决定失败时是否值得本地化后重试）
                has_media = any(isinstance(c, (Image, Record, Video, File)) for c in filtered_chain)
                # 规则级代理三态：use_proxy 关→直连；开且 proxy_url 空→系统代理；开且非空→该地址
                use_proxy = bool(rule.get("use_proxy", False))
                proxy_url = (rule.get("proxy_url") or "").strip() or None
                # @昵称反查（v0.5.0 可选增强，默认关闭）：仅当选中 @提及 类型时生效
                at_lookup = self._should_at_lookup(rule) and "at" in allowed
                fallback_chain = None

                # 逐目标发送：一个目标失败不影响其他目标（冷却按 源|目标 对记录）
                for target in targets:
                    # 目标级链：at_nickname_lookup 开启（高级 @）→ QQ 系按 qq 透传真实 At，
                    # 并按目标群成员列表反查昵称精确 @；默认关闭 → At 一律转为文本 @昵称
                    # （不发送真实 At 组件，彻底规避协议端 At 解析/群成员查询超时）
                    if at_lookup:
                        base_chain = _sanitize_at_chain_for_target(message_chain, target, at_passthrough)
                        base_chain = await self._resolve_at_mentions(base_chain, target)
                    else:
                        base_chain = _textify_at_chain(message_chain)
                    new_chain = base_chain if not header_text else [Plain(text=header_text)] + base_chain

                    # 同一个目标对同一条源消息只发一次：命中多条规则时后面的规则直接跳过并告警，
                    # 避免「一个群收到好几分原文/译文」（需要两种内容时请合并到同一条规则里）
                    if target in sent_targets:
                        logger.warning(
                            f"[astrbot_plugin_msg_forward_cc] ⚠️ 规则 #{rid}（{self._rule_name(rule)}）与规则 "
                            f"#{sent_targets[target]} 都把同一条消息发往 {target}，本次只由先命中的规则发一次"
                        )
                        continue

                    # 队列模式：入队前本地化媒体到自有目录，再交给后台 worker 按间隔依次转发
                    if queue_interval > 0:
                        # 队列模式下必须本地化媒体，防止源端临时文件延迟后被清理
                        try:
                            queue_chain = await _prepare_chain_for_queue(
                                base_chain, use_proxy=use_proxy, proxy_url=proxy_url,
                            )
                        except Exception as e:
                            # 单目标失败不中断其他规则/目标（与直接发送路径的降级语义一致）
                            logger.error(f"❌ 规则 #{rid} 入队前媒体本地化失败，本目标跳过: {e}")
                            continue
                        sent_targets[target] = rid
                        self._enqueue_send(
                            target, event.chain_result(queue_chain), queue_interval,
                            base_chain, header_text, has_media,
                            use_proxy, proxy_url,
                            rule_key=rule_key, rule_label=f"#{rid}",
                        )
                        continue
                    if cooldown_sec > 0:
                        cd_key = f"{source_umo}|{target}"
                        cd_end = self._cooldowns.get(cd_key, 0)
                        if now < cd_end:
                            continue
                    # 冷却跳过时不算「已发送」：否则别的规则命中同一目标也会被拦下，消息直接丢失
                    sent_targets[target] = rid
                    try:
                        self._log_send(rid, target, message_id, len(new_chain), "｜🌐译文" if translate_on else "｜原文")
                        await self.context.send_message(target, event.chain_result(new_chain))
                        # 转发成功后设置冷却
                        if cooldown_sec > 0:
                            self._cooldowns[cd_key] = now + cooldown_sec
                    except ValueError as e:
                        logger.error(f"❌ 不合法的 session 字符串，转发失败: {e}")
                    except Exception as e:
                        # 只在链中含媒体时降级重试，且**只重试一次**：
                        # 发送抛异常并不代表没发出去（协议端超时但已投递很常见），每多重试一次就多一份重复消息；
                        # 纯文字链重发更没有收益，直接记录失败即可
                        if not has_media:
                            logger.error(f"❌ 转发失败（纯文字链不重试，避免重复发送）: {e}")
                            continue
                        try:
                            if fallback_chain is None:
                                # 规则配了代理就用自带的远程 URL 本地化，否则用核心重新本地化
                                if use_proxy:
                                    localized = await _prepare_chain_fallback(
                                        filtered_chain, use_proxy=True, proxy_url=proxy_url,
                                    )
                                else:
                                    localized = await _prepare_chain_for_forward(filtered_chain)
                                fallback_chain = localized if not header_text else [Plain(text=header_text)] + localized
                            self._log_send(rid, target, message_id, len(fallback_chain), "｜媒体本地化重试")
                            await self.context.send_message(target, event.chain_result(fallback_chain))
                            logger.warning(f"⚠️ 转发首次失败（{e}），已重新本地化媒体后重试成功（只重试一次）")
                            if cooldown_sec > 0:
                                self._cooldowns[cd_key] = now + cooldown_sec
                        except Exception as e2:
                            logger.error(f"❌ 转发失败（媒体本地化重试后仍失败，不再重试）: {e2}")

        except Exception as e:
            logger.error(f"❌ 转发逻辑异常: {e}")

    def _log_send(self, rid: int, target: str, message_id: str, segments: int, note: str = "") -> None:
        """每次实际调用发送前记一行：排查「一条消息变成多条」时直接看这些行即可定位规则与目标。"""
        logger.info(
            f"[astrbot_plugin_msg_forward_cc] 📤 规则 #{rid} → {target} | 消息 {message_id or '-'} | "
            f"{segments} 段{note}"
        )

    async def terminate(self):
        # 注销活跃实例（仅当自己就是活跃实例时），避免重载后新实例被误清
        if _active_of(self.context) is self:
            _mark_active(self.context, None)
        # 与自检路径共用：两者都只会真正执行一次
        self._self_disabled = True
        if self._queue_worker_task is not None:
            self._queue_worker_task.cancel()
        if self._cleanup_task is not None:
            self._cleanup_task.cancel()
        if self._discord_hook_task is not None:
            self._discord_hook_task.cancel()
        # 摘除补挂的 Discord 监听：重载后旧实例的监听若残留会与新实例重复转发
        self._unhook_discord_clients()
        logger.info("MsgForward plugin terminated")
