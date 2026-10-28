#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Бот-корректор текста, кода и файлов локализации (ru / uk / en и ещё ~30 языков).

Зависимости: НЕТ (только стандартная библиотека, Python 3.8+). Нужен интернет
или собственный сервер LanguageTool (--server).

Быстрый старт
    python grammar_bot.py                        интерактивный бот
    python grammar_bot.py -t "Мы пошли в магазен"
    python grammar_bot.py -f script.py --strict  проверить файл (код выхода 2, если есть ошибки)
    python grammar_bot.py -f text.txt --review   по каждой ошибке спрашивать вариант
    python grammar_bot.py -f text.txt --diff --report report.html
    python grammar_bot.py --loc strings.json --loc-out fixed.json   файлы локализации
    python grammar_bot.py --server http://localhost:8081            свой сервер LanguageTool
    python grammar_bot.py --gui                  окно с кнопками (нужен tkinter)
    python grammar_bot.py --telegram             Telegram-бот (токен в TELEGRAM_BOT_TOKEN)
    python grammar_bot.py -f broken.py --ai      + разбор ИИ (нужен ai_code_fixer.py и ANTHROPIC_API_KEY)

Свой сервер LanguageTool (без лимитов и без отправки текста в интернет):
    java -cp languagetool-server.jar org.languagetool.server.HTTPServer --port 8081
"""
from __future__ import annotations

import argparse
import bisect
import builtins
import contextlib
import csv
import dataclasses
import difflib
import hashlib
import html
import io
import json
import keyword
import logging
import os
import re
import socket
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from typing import Optional

# --------------------------------------------------------------------------
#  Настройки
# --------------------------------------------------------------------------
DEFAULT_API_URL = "https://api.languagetool.org/v2/check"
API_URL = os.environ.get("LT_URL", DEFAULT_API_URL)
MAX_CHUNK = 9000          # безопасно меньше лимита публичного API (20 000)
TIMEOUT = 15              # секунд на запрос
RETRIES = 3
WORKERS = 3               # параллельные запросы (для публичного API не больше 3-4)
DEFAULT_CACHE = os.path.join(os.path.expanduser("~"), ".grammar_bot_cache.sqlite3")

if os.name == "nt":       # включаем ANSI-цвета в консоли Windows
    os.system("")

USE_COLOR = sys.stdout.isatty()


def c(text, code):
    return f"\033[{code}m{text}\033[0m" if USE_COLOR else str(text)


RED = lambda t: c(t, "31;1")      # noqa: E731
GREEN = lambda t: c(t, "32;1")    # noqa: E731
YELLOW = lambda t: c(t, "33")     # noqa: E731
CYAN = lambda t: c(t, "36;1")     # noqa: E731
DIM = lambda t: c(t, "2")         # noqa: E731


@contextlib.contextmanager
def no_color():
    global USE_COLOR
    old, USE_COLOR = USE_COLOR, False
    try:
        yield
    finally:
        USE_COLOR = old


@dataclass
class Opts:
    lang: str = "auto"
    mode: str = "auto"                 # auto | code | text
    style: Optional[str] = None        # python | c | sh | sql (None = определить само)
    review: bool = False               # спрашивать вариант по каждой ошибке
    diff: bool = False                 # показывать «было → стало»
    report: Optional[str] = None       # путь к отчёту (.html .json .csv .md)
    ai: bool = False                   # разбор ИИ после исправления кода
    ai_lang: str = "ru"                # на каком языке отвечает ИИ
    workers: int = WORKERS


# --------------------------------------------------------------------------
#  Логирование (для тестировщика): файл grammar_bot.log + --debug в консоль
# --------------------------------------------------------------------------
log = logging.getLogger("grammar_bot")


def setup_logging(debug: bool = False, log_file: str = "grammar_bot.log"):
    log.setLevel(logging.DEBUG)
    log.handlers.clear()
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")
    if log_file:
        try:
            fh = logging.FileHandler(log_file, encoding="utf-8")
            fh.setFormatter(fmt)
            log.addHandler(fh)
        except OSError as e:
            print(YELLOW(f"⚠ Не удалось открыть лог-файл {log_file}: {e}"))
    if debug:
        ch = logging.StreamHandler(sys.stderr)
        ch.setFormatter(fmt)
        log.addHandler(ch)
    if not log.handlers:
        log.addHandler(logging.NullHandler())


# --------------------------------------------------------------------------
#  Защита кавычек
# --------------------------------------------------------------------------
QUOTES = set("\"'`“”‘’«»„‚")
SAFE_CLOSERS = set("\"“”«»„`")      # ’ и ' могут быть апострофом — без пары не считаем кавычкой


def protect_quotes(original: str, replacement: str) -> str:
    """Если исходный фрагмент был в кавычках, а замена пришла без них — вернуть кавычки."""
    if not original or not replacement:
        return replacement
    lead = original[0] if original[0] in QUOTES else ""
    trail = ""
    if len(original) > 1 and original[-1] in QUOTES:
        if lead or original[-1] in SAFE_CLOSERS:
            trail = original[-1]
    result = replacement
    if lead and result[0] not in QUOTES:
        result = lead + result
    if trail and result[-1] not in QUOTES:
        result = result + trail
    return result


# --------------------------------------------------------------------------
#  Защита плейсхолдеров и тегов: {name} %d %s <b>..</b> [color=red] \n ${x}
# --------------------------------------------------------------------------
PLACEHOLDER_RE = re.compile(
    r"\{\{.*?\}\}"
    r"|\$\{[^}\n]*\}"
    r"|\{[^{}\n]*\}"
    r"|%\([A-Za-z_]\w*\)[-+#0]*\d*(?:\.\d+)?[sdifrxXeEgGc]"
    r"|%(?:\d+\$)?[-+#0]*\d*(?:\.\d+)?(?:ll|l|h)?[sdifuxXeEgGcp]"
    r"|%%"
    r"|</?[A-Za-z][^<>\n]*>"
    r"|\[/?[A-Za-z]+(?:=[^\]\n]*)?\]"
    r"|\\[nrtv]"
    r"|&[A-Za-z]+;|&#\d+;"
)


def placeholders_of(s: str) -> Counter:
    return Counter(m.group(0) for m in PLACEHOLDER_RE.finditer(s))


def _overlaps(spans, s, e):
    return any(s < b and e > a for a, b in spans)


def filter_placeholders(text: str, issues):
    spans = [(m.start(), m.end()) for m in PLACEHOLDER_RE.finditer(text)]
    if not spans:
        return issues, 0
    kept = [i for i in issues if not _overlaps(spans, i["offset"], i["offset"] + i["length"])]
    return kept, len(issues) - len(kept)


# --------------------------------------------------------------------------
#  Свой словарь: ignore.txt (слова, re:регулярки, rule:ID_ПРАВИЛА)
# --------------------------------------------------------------------------
class IgnoreList:
    def __init__(self):
        self.words, self.patterns, self.rules, self.path = set(), [], set(), None

    def load(self, path: str) -> int:
        self.path = path
        n = 0
        try:
            with open(path, "r", encoding="utf-8-sig") as f:
                for raw in f:
                    line = raw.strip()
                    if not line or line.startswith("#"):
                        continue
                    low = line.lower()
                    if low.startswith("re:"):
                        try:
                            self.patterns.append(re.compile(line[3:].strip(), re.I))
                        except re.error as e:
                            log.warning("ignore: плохая регулярка %r: %s", line, e)
                            continue
                    elif low.startswith("rule:"):
                        self.rules.add(line[5:].strip().upper())
                    else:
                        self.words.add(low)
                    n += 1
        except OSError as e:
            log.warning("ignore: не удалось прочитать %s: %s", path, e)
        return n

    def matches(self, wrong: str, rule: str = "") -> bool:
        if rule and rule.upper() in self.rules:
            return True
        w = wrong.strip()
        core = w.strip(".,;:!?\"'«»“”()[]{}").lower()
        if w.lower() in self.words or core in self.words:
            return True
        return any(p.fullmatch(w) or p.fullmatch(core) for p in self.patterns)

    def add(self, word: str, path: Optional[str] = None):
        word = word.strip()
        if not word:
            return
        self.words.add(word.lower())
        path = path or self.path or "ignore.txt"
        self.path = path
        try:
            with open(path, "a", encoding="utf-8") as f:
                f.write(word + "\n")
        except OSError as e:
            log.warning("ignore: не удалось записать %s: %s", path, e)


IGNORE = IgnoreList()


def load_default_ignore(path: Optional[str] = None) -> Optional[str]:
    candidates = [path] if path else [
        "ignore.txt", os.path.join(os.path.dirname(os.path.abspath(__file__)), "ignore.txt")]
    for p in candidates:
        if p and os.path.isfile(p):
            IGNORE.load(p)
            log.info("словарь игнорирования: %s (слов: %d, правил: %d)", p,
                     len(IGNORE.words) + len(IGNORE.patterns), len(IGNORE.rules))
            return p
    return None


def filter_ignored(text: str, issues):
    if not (IGNORE.words or IGNORE.patterns or IGNORE.rules):
        return issues, 0
    kept = [i for i in issues
            if not IGNORE.matches(text[i["offset"]:i["offset"] + i["length"]], i["rule"])]
    return kept, len(issues) - len(kept)


# --------------------------------------------------------------------------
#  Защита программного кода (Python, JS/TS, C/C++/C#/Java/Go/Rust/PHP, Shell, SQL)
# --------------------------------------------------------------------------
PY_WORDS = set(keyword.kwlist) | set(keyword.softkwlist) | {
    n for n in dir(builtins) if not n.startswith("_")}
C_WORDS = set("""if else for while do switch case break continue return function const let var new
class struct enum interface public private protected static void int float double char bool boolean
string long short unsigned namespace using import export default try catch finally throw throws
null undefined true false this super typeof instanceof async await yield extends implements
package fn mut impl pub use match func go defer chan range""".split())
CODE_WORDS = PY_WORDS | C_WORDS

CASING_RULES = ("UPPERCASE_SENTENCE_START", "UPPERCASE", "CASING", "SENTENCE_START")

STYLES = {
    "python": {"line": ("#",), "block": (), "strings": ('"""', "'''", '"', "'"), "escape": True},
    "c": {"line": ("//",), "block": (("/*", "*/"),), "strings": ('"', "'", "`"), "escape": True},
    "sh": {"line": ("#",), "block": (), "strings": ('"', "'"), "escape": True},
    "sql": {"line": ("--",), "block": (("/*", "*/"),), "strings": ("'", '"'), "escape": False},
}
EXT_STYLE = {
    ".py": "python", ".pyw": "python",
    ".js": "c", ".jsx": "c", ".ts": "c", ".tsx": "c", ".java": "c", ".c": "c", ".h": "c",
    ".cpp": "c", ".hpp": "c", ".cc": "c", ".cs": "c", ".go": "c", ".rs": "c", ".php": "c",
    ".kt": "c", ".swift": "c", ".dart": "c",
    ".sh": "sh", ".bash": "sh", ".rb": "sh", ".yml": "sh", ".yaml": "sh",
    ".sql": "sql", ".lua": "sql",
}

CODE_LINE_RE = re.compile(r"""^\s*(?:
    def\s+\w+\s*\( | class\s+\w+ | import\s+[\w.{*]+ | from\s+[\w.]+\s+import\s |
    (?:if|elif|while)\b(?=.*(?:==|!=|<=|>=|[<>]|[()]|\bnot\b|\band\b|\bor\b|\bis\b)).*:\s*(?:\#.*)?$ |
    for\s+\w+(?:\s*,\s*\w+)*\s+in\s+\S.*:\s*(?:\#.*)?$ | (?:with|except)\b.*:\s*(?:\#.*)?$ |
    else\s*: | try\s*: | finally\s*: | return\b | print\s*\( | @\w+ | [{}]\s*$ |
    (?:const|let|var)\s+\w+\s*=? | function\s*\w*\s*\( |
    (?:public|private|protected|static)\s+\w+ | (?:void|int|float|double|string|bool)\s+\w+\s*[(=;] |
    using\s+[\w.]+\s*; | package\s+[\w.]+\s*;? | namespace\s+\w+ |
    \#(?:include|define|ifdef|ifndef|endif|pragma)\b |
    [A-Za-z_][\w.\[\]]*\s*(?:[-+*/%|&]?=)(?!=).* |
    [A-Za-z_][\w.]*\(.*\)\s*;?\s*$ |
    (?=.*[(=]).*;\s*$
)""", re.X)


def looks_like_code(text: str) -> bool:
    lines = [l for l in text.splitlines() if l.strip()]
    if not lines:
        return False
    hits = sum(bool(CODE_LINE_RE.match(l)) for l in lines)
    return hits >= 1 and hits / len(lines) >= 0.3


def resolve_mode(text: str, mode: str = "auto") -> bool:
    """True, если текст нужно проверять как код. mode: auto | code | text."""
    if mode == "code":
        return True
    if mode == "text":
        return False
    return looks_like_code(text)


def detect_style(text: str, filename: Optional[str] = None) -> str:
    if filename:
        ext = os.path.splitext(filename)[1].lower()
        if ext in EXT_STYLE:
            return EXT_STYLE[ext]
    py = len(re.findall(r"^\s*(?:def|class|elif|import|from\s+\S+\s+import)\b|:\s*$|\bprint\(",
                        text, re.M))
    cs = len(re.findall(r";\s*$|^\s*[{}]\s*$|\bfunction\b|\b(?:const|let|var)\s+\w+|#include|=>|"
                        r"\bpublic\s+(?:static|class)|^\s*//", text, re.M))
    return "c" if cs > py else "python"


def code_spans(text: str, style: str = "python"):
    """Участки КОДА (вне строк и комментариев) — их проверять нельзя.
    Строки в кавычках и комментарии остаются проверяемыми как обычный текст."""
    cfg = STYLES.get(style, STYLES["python"])
    openers = sorted(cfg["strings"], key=len, reverse=True)
    spans, n, i, start = [], len(text), 0, 0
    while i < n:
        hit = False
        for o, cl in cfg["block"]:
            if text.startswith(o, i):
                spans.append((start, i))
                j = text.find(cl, i + len(o))
                start = i = n if j == -1 else j + len(cl)
                hit = True
                break
        if hit:
            continue
        for lc in cfg["line"]:
            if text.startswith(lc, i):
                spans.append((start, i))
                j = text.find("\n", i)
                start = i = n if j == -1 else j
                hit = True
                break
        if hit:
            continue
        for q in openers:
            if text.startswith(q, i):
                spans.append((start, i))
                multi = len(q) == 3 or q == "`"
                j = i + len(q)
                while j < n:
                    if cfg["escape"] and text[j] == "\\":
                        j += 2
                        continue
                    if text.startswith(q, j):
                        j += len(q)
                        break
                    if not multi and text[j] == "\n":
                        break
                    j += 1
                start = i = min(j, n)
                hit = True
                break
        if hit:
            continue
        i += 1
    spans.append((start, n))
    out = []
    for a, b in spans:
        seg = text[a:b]
        if seg.strip():
            out.append((a + len(seg) - len(seg.lstrip()), b - (len(seg) - len(seg.rstrip()))))
    return out


def filter_code_issues(text: str, issues, style: str = "python"):
    """Убирает ложные срабатывания на коде. Возвращает (оставшиеся, сколько убрано)."""
    spans = code_spans(text, style)
    kept = []
    for i in issues:
        s, e = i["offset"], i["offset"] + i["length"]
        wrong = text[s:e]
        if any(k in i["rule"].upper() for k in CASING_RULES):     # def -> Def, print -> Print
            continue
        if _overlaps(spans, s, e):                                # имена, ключевые слова, операторы
            continue
        if wrong.strip() in CODE_WORDS:
            continue
        kept.append(i)
    return kept, len(issues) - len(kept)


def filter_keyword_case(text: str, issues):
    """Для обычного текста: не менять только регистр служебных слов (print -> Print)."""
    kept = []
    for i in issues:
        wrong = text[i["offset"]:i["offset"] + i["length"]].strip()
        reps = i["replacements"]
        if wrong in CODE_WORDS and reps and all(r.lower() == wrong.lower() for r in reps):
            continue
        kept.append(i)
    return kept


# --------------------------------------------------------------------------
#  Кэш (память + диск SQLite)
# --------------------------------------------------------------------------
class Cache:
    def __init__(self, path: Optional[str] = None, ttl: float = 30 * 86400, mem_limit: int = 512):
        self.mem, self.lock, self.ttl, self.mem_limit, self.db = {}, threading.Lock(), ttl, mem_limit, None
        if path:
            try:
                self.db = sqlite3.connect(path, check_same_thread=False, timeout=5)
                self.db.execute("CREATE TABLE IF NOT EXISTS cache "
                                "(k TEXT PRIMARY KEY, v TEXT NOT NULL, t REAL NOT NULL)")
                self.db.execute("DELETE FROM cache WHERE t < ?", (time.time() - ttl,))
                self.db.commit()
            except (sqlite3.Error, OSError) as e:
                log.warning("кэш на диске недоступен (%s) — работаю только в памяти", e)
                self.db = None

    def _remember(self, k, v):
        if len(self.mem) >= self.mem_limit:
            self.mem.pop(next(iter(self.mem)))
        self.mem[k] = v

    def get(self, k):
        with self.lock:
            if k in self.mem:
                return self.mem[k]
            if self.db is not None:
                try:
                    row = self.db.execute("SELECT v, t FROM cache WHERE k=?", (k,)).fetchone()
                except sqlite3.Error:
                    row = None
                if row and time.time() - row[1] < self.ttl:
                    self._remember(k, row[0])
                    return row[0]
        return None

    def set(self, k, v):
        with self.lock:
            self._remember(k, v)
            if self.db is not None:
                try:
                    self.db.execute("INSERT OR REPLACE INTO cache (k, v, t) VALUES (?, ?, ?)",
                                    (k, v, time.time()))
                    self.db.commit()
                except sqlite3.Error as e:
                    log.warning("кэш: не удалось записать: %s", e)


CACHE = Cache(None)


# --------------------------------------------------------------------------
#  Работа с API LanguageTool
# --------------------------------------------------------------------------
class CheckError(Exception):
    """Ошибка проверки. code — HTTP-код (500, 429...) либо метка: NETWORK, TIMEOUT, BAD_JSON..."""

    def __init__(self, message, code=None):
        super().__init__(message)
        self.code = code


def _request(text: str, lang: str) -> str:
    """Один запрос к API с повторами и подробным логом каждой попытки."""
    params = {"text": text, "language": lang, "level": "default"}
    if lang == "auto":
        params["preferredVariants"] = "en-US,de-DE,pt-PT,ru-RU,uk-UA"
    data = urllib.parse.urlencode(params).encode("utf-8")
    req = urllib.request.Request(
        API_URL, data=data,
        headers={"Content-Type": "application/x-www-form-urlencoded",
                 "Accept": "application/json",
                 "User-Agent": "grammar-bot/2.0"})
    last = None
    log.debug("Отправка запроса к LanguageTool (длина: %d, язык: %s, %s)", len(text), lang, API_URL)
    for attempt in range(1, RETRIES + 1):
        t0 = time.time()
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT) as r:
                body = r.read().decode("utf-8")
                log.info("попытка %d/%d: HTTP %s за %.2f c (текст %d симв., язык %s)",
                         attempt, RETRIES, r.status, time.time() - t0, len(text), lang)
                return body
        except urllib.error.HTTPError as e:
            detail = e.read().decode("utf-8", "ignore")[:200].replace("\n", " ")
            last = CheckError(f"HTTP {e.code} {e.reason}: {detail}", e.code)
            log.warning("попытка %d/%d: HTTP %s %s | %s", attempt, RETRIES, e.code, e.reason, detail)
            if e.code == 429 or e.code >= 500:
                time.sleep(2 * attempt if e.code == 429 else attempt)
                continue
            log.error("фатальная ошибка HTTP %s, повторы не помогут", e.code)
            raise last
        except urllib.error.URLError as e:
            code = "TIMEOUT" if isinstance(e.reason, (socket.timeout, TimeoutError)) else "NETWORK"
            last = CheckError(f"{e.reason}", code)
            log.warning("попытка %d/%d: %s (%s) за %.2f c", attempt, RETRIES, code, e.reason, time.time() - t0)
        except (TimeoutError, socket.timeout):
            last = CheckError(f"нет ответа за {TIMEOUT} c", "TIMEOUT")
            log.warning("попытка %d/%d: TIMEOUT за %.2f c", attempt, RETRIES, time.time() - t0)
        except OSError as e:
            last = CheckError(f"{e}", "NETWORK")
            log.warning("попытка %d/%d: OSError %r", attempt, RETRIES, e)
        if attempt < RETRIES:
            time.sleep(attempt)
    log.error("сервис недоступен после %d попыток: [%s] %s", RETRIES, last.code, last)
    raise CheckError(f"{last} (после {RETRIES} попыток, {API_URL})", last.code)


def fetch(text: str, lang: str) -> str:
    """Запрос с кэшем: повторные проверки одного и того же текста — мгновенные."""
    key = hashlib.sha256(f"{API_URL}\0{lang}\0{text}".encode("utf-8")).hexdigest()
    hit = CACHE.get(key)
    if hit is not None:
        log.debug("кэш: попадание (%d симв.)", len(text))
        return hit
    body = _request(text, lang)
    CACHE.set(key, body)
    return body


def split_chunks(text: str, limit: int = MAX_CHUNK):
    """Режем длинный текст по границам строк/предложений. Возвращает (offset, chunk)."""
    chunks, pos = [], 0
    n = len(text)
    while pos < n:
        end = min(pos + limit, n)
        if end < n:
            window = text[pos:end]
            cut = max(window.rfind("\n"),
                      max(window.rfind(s) for s in (". ", "! ", "? ")) + 1)
            if cut > limit // 2:
                end = pos + cut + 1
        chunks.append((pos, text[pos:end]))
        pos = end
    return chunks


def _check_chunk(item, lang):
    offset, chunk = item
    body = fetch(chunk, lang)
    try:
        return offset, chunk, json.loads(body)
    except json.JSONDecodeError:
        log.error("некорректный JSON от сервера")
        raise CheckError("Сервис вернул некорректный ответ.", "BAD_JSON")


def check_text(text: str, lang: str = "auto", mode: str = "auto",
               style: Optional[str] = None, workers: Optional[int] = None):
    """Возвращает (список ошибок, определённый язык)."""
    workers = workers or WORKERS
    is_code = resolve_mode(text, mode)
    style = style or detect_style(text)
    chunks = [(o, ch) for o, ch in split_chunks(text) if ch.strip()]
    if len(chunks) > 1 and workers > 1:
        with ThreadPoolExecutor(max_workers=min(workers, len(chunks))) as ex:
            results = list(ex.map(lambda it: _check_chunk(it, lang), chunks))
    else:
        results = [_check_chunk(it, lang) for it in chunks]

    issues, detected = [], lang
    for offset, chunk, data in results:
        lg = data.get("language", {})
        detected = lg.get("detectedLanguage", {}).get("name") or lg.get("name", detected)
        for m in data.get("matches", []):
            wrong = chunk[m["offset"]:m["offset"] + m["length"]]
            issues.append({
                "offset": offset + m["offset"],
                "length": m["length"],
                "wrong": wrong,
                "message": m.get("message", ""),
                "short": m.get("shortMessage", ""),
                "replacements": [protect_quotes(wrong, r["value"])
                                 for r in m.get("replacements", [])][:5],
                "rule": m.get("rule", {}).get("id", ""),
                "category": m.get("rule", {}).get("category", {}).get("name", ""),
            })
    issues.sort(key=lambda i: i["offset"])
    issues, n_ph = filter_placeholders(text, issues)
    issues, n_ig = filter_ignored(text, issues)
    if is_code:
        issues, n_code = filter_code_issues(text, issues, style)
    else:
        issues, n_code = filter_keyword_case(text, issues), 0
    log.info("режим %s (%s): плейсхолдеры -%d, словарь -%d, код -%d, осталось %d",
             "КОД" if is_code else "ТЕКСТ", style, n_ph, n_ig, n_code, len(issues))
    return issues, detected


# --------------------------------------------------------------------------
#  Применение исправлений (с защитой)
# --------------------------------------------------------------------------
def _compiles(code: str) -> bool:
    try:
        compile(code, "<fixed>", "exec")
        return True
    except (SyntaxError, ValueError):
        return False


def _brackets(s: str) -> Counter:
    return Counter(ch for ch in s if ch in "()[]{}")


def apply_fixes_ex(text: str, issues, code_mode: bool = False, style: str = "python"):
    """Применяет исправления справа налево. Возвращает (текст, предупреждения).
    Не применяет замену, которая: ломает синтаксис Python, меняет баланс скобок в коде
    или теряет/портит плейсхолдер ({name}, %d, <b>...)."""
    result, last_start, warnings = text, len(text) + 1, []
    guard_compile = code_mode and style == "python" and _compiles(text)
    guard_brackets = code_mode and style != "python"
    for i in sorted(issues, key=lambda x: x["offset"], reverse=True):
        if i.get("skip"):
            continue
        rep = i.get("choice")
        if rep is None:
            if not i["replacements"]:
                continue
            rep = i["replacements"][0]
        start, end = i["offset"], i["offset"] + i["length"]
        if end > last_start:                  # пересекающиеся ошибки пропускаем
            continue
        wrong = text[start:end]
        fix = rep if i.get("custom") else protect_quotes(wrong, rep)
        reason = None
        if placeholders_of(wrong) != placeholders_of(fix):
            reason = "портит плейсхолдер/тег"
        elif guard_brackets and _brackets(wrong) != _brackets(fix):
            reason = "ломает баланс скобок"
        elif guard_compile and not _compiles(result[:start] + fix + result[end:]):
            reason = "ломает синтаксис Python"
        if reason:
            warnings.append(f"Пропущено исправление {wrong!r} → {fix!r}: {reason}")
            log.warning(warnings[-1])
            continue
        result, last_start = result[:start] + fix + result[end:], start
    return result, warnings


def apply_fixes(text: str, issues, code_mode: bool = False, style: str = "python") -> str:
    return apply_fixes_ex(text, issues, code_mode, style)[0]


# --------------------------------------------------------------------------
#  Анализ, отчёт, экспорт
# --------------------------------------------------------------------------
def line_col(text: str, offset: int):
    line = text.count("\n", 0, offset) + 1
    col = offset - (text.rfind("\n", 0, offset) + 1) + 1
    return line, col


def context(text: str, offset: int, length: int, width: int = 35) -> str:
    s = max(0, offset - width)
    e = min(len(text), offset + length + width)
    before = text[s:offset].replace("\n", " ")
    wrong = text[offset:offset + length].replace("\n", " ")
    after = text[offset + length:e].replace("\n", " ")
    return f"{'…' if s else ''}{before}{RED('[' + wrong + ']')}{after}{'…' if e < len(text) else ''}"


def analyze(text: str, opts: Opts, filename: Optional[str] = None) -> dict:
    """Проверяет текст. Ничего не печатает и не применяет. Бросает CheckError."""
    style = opts.style or detect_style(text, filename)
    issues, detected = check_text(text, opts.lang, opts.mode, style, opts.workers)
    return {"text": text, "issues": issues, "language": detected, "style": style,
            "code_mode": resolve_mode(text, opts.mode), "fixed": None, "warnings": []}


def finalize(res: dict) -> dict:
    res["fixed"], res["warnings"] = apply_fixes_ex(
        res["text"], res["issues"], res["code_mode"], res["style"])
    return res


def fix_of(issue):
    if issue.get("skip"):
        return None
    if issue.get("choice") is not None:
        return issue["choice"]
    return issue["replacements"][0] if issue["replacements"] else None


def result_rows(res: dict):
    rows = []
    for i in res["issues"]:
        ln, col = line_col(res["text"], i["offset"])
        rows.append({"line": ln, "column": col, "wrong": res["text"][i["offset"]:i["offset"] + i["length"]],
                     "fix": fix_of(i) or "", "alternatives": " | ".join(i["replacements"]),
                     "message": i["message"], "rule": i["rule"], "category": i["category"]})
    return rows


def colored_diff(a: str, b: str) -> str:
    out = []
    for l in difflib.unified_diff(a.splitlines(), b.splitlines(), "было", "стало", lineterm="", n=1):
        if l.startswith(("+++", "---")):
            out.append(DIM(l))
        elif l.startswith("@@"):
            out.append(CYAN(l))
        elif l.startswith("+"):
            out.append(GREEN(l))
        elif l.startswith("-"):
            out.append(RED(l))
        else:
            out.append(l)
    return "\n".join(out)


def render_report(res: dict, color: bool = True, diff: bool = False) -> str:
    with (contextlib.nullcontext() if color else no_color()):
        text, issues = res["text"], res["issues"]
        kind = "КОД" if res["code_mode"] else "ТЕКСТ"
        out = []
        if not issues:
            out.append(GREEN(f"✔ Ошибок не найдено ({kind}). Текст или программный код написаны правильно!"))
            return "\n".join(out)
        out.append(CYAN(f"Режим: {kind}   Язык: {res['language']}   Найдено реальных ошибок: {len(issues)}\n"))
        for n, i in enumerate(issues, 1):
            ln, col = line_col(text, i["offset"])
            wrong = text[i["offset"]:i["offset"] + i["length"]]
            out.append(f"{YELLOW(str(n) + '.')} строка {ln}, символ {col}  "
                       f"{DIM('(' + (i['category'] or i['rule']) + ')')}")
            out.append(f"   {context(text, i['offset'], i['length'])}")
            fx = fix_of(i)
            if fx is not None:
                out.append(f"   Замена:  {RED(repr(wrong))} → {GREEN(repr(fx))}")
            else:
                out.append(f"   Ошибка:  {RED(repr(wrong))}" + (DIM("  (пропущено)") if i.get("skip") else ""))
            if len(i["replacements"]) > 1:
                out.append(f"   Варианты: " + " | ".join(i["replacements"]))
            out.append(f"   Пояснение: {i['message']}\n")
        fixed = res["fixed"] if res["fixed"] is not None else text
        out.append(CYAN("═" * 60))
        out.append(GREEN("Исправленный код:" if res["code_mode"] else "Исправленный текст:"))
        out.append(fixed)
        out.append(CYAN("═" * 60))
        for w in res["warnings"]:
            out.append(YELLOW("⚠ " + w))
        if diff and fixed != text:
            out.append(CYAN("Изменения (было → стало):"))
            out.append(colored_diff(text, fixed))
        return "\n".join(out)


def _highlight_html(text, issues):
    parts, pos = [], 0
    for i in sorted(issues, key=lambda x: x["offset"]):
        s, e = i["offset"], i["offset"] + i["length"]
        if s < pos:
            continue
        parts.append(html.escape(text[pos:s]))
        parts.append(f"<mark title=\"{html.escape(i['message'], quote=True)}\">{html.escape(text[s:e])}</mark>")
        pos = e
    parts.append(html.escape(text[pos:]))
    return "".join(parts)


def export_rows(path: str, title: str, rows, extra: Optional[dict] = None, original_html: str = ""):
    """Сохраняет отчёт: .json .csv .html .md/.txt (по расширению)."""
    ext = os.path.splitext(path)[1].lower()
    extra = extra or {}
    summary = {"title": title, "total": len(rows)}
    if ext == ".json":
        with open(path, "w", encoding="utf-8") as f:
            json.dump({**summary, **extra, "rows": rows}, f, ensure_ascii=False, indent=2)
    elif ext == ".csv":
        cols = list(rows[0].keys()) if rows else ["info"]
        with open(path, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
            w.writeheader()
            w.writerows(rows)
    elif ext in (".html", ".htm"):
        cols = list(rows[0].keys()) if rows else []
        th = "".join(f"<th>{html.escape(str(c_))}</th>" for c_ in cols)
        trs = "".join("<tr>" + "".join(f"<td>{html.escape(str(r.get(c_, '')))}</td>" for c_ in cols) + "</tr>"
                      for r in rows)
        fixed = extra.get("fixed")
        body = (f"<h1>{html.escape(title)}</h1><p>Найдено: <b>{len(rows)}</b></p>"
                + (f"<h2>Исходный текст</h2><pre>{original_html}</pre>" if original_html else "")
                + (f"<h2>Исправленный результат</h2><pre>{html.escape(fixed)}</pre>" if fixed else "")
                + (f"<table><tr>{th}</tr>{trs}</table>" if rows else "<p>✔ Ошибок нет.</p>"))
        with open(path, "w", encoding="utf-8") as f:
            f.write("<!doctype html><html lang=\"ru\"><head><meta charset=\"utf-8\">"
                    f"<title>{html.escape(title)}</title><style>"
                    "body{font:15px/1.5 system-ui,sans-serif;max-width:1100px;margin:2rem auto;padding:0 1rem;color:#222}"
                    "pre{background:#f5f5f5;padding:1rem;border-radius:8px;white-space:pre-wrap}"
                    "mark{background:#ffd2d2;border-bottom:2px solid #d33}"
                    "table{border-collapse:collapse;width:100%}td,th{border:1px solid #ddd;padding:6px 8px;text-align:left}"
                    "th{background:#eee}</style></head><body>" + body + "</body></html>")
    else:
        lines = [f"# {title}", "", f"Найдено: **{len(rows)}**", ""]
        if rows:
            cols = list(rows[0].keys())
            lines += ["| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]
            for r in rows:
                lines.append("| " + " | ".join(str(r.get(c_, "")).replace("|", "\\|").replace("\n", " ")
                                               for c_ in cols) + " |")
        if extra.get("fixed"):
            lines += ["", "## Исправленный результат", "", "```", extra["fixed"], "```"]
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
    log.info("отчёт сохранён: %s", path)


def export_result(res: dict, path: str):
    export_rows(path, "Отчёт проверки", result_rows(res),
                {"language": str(res["language"]), "fixed": res["fixed"] if res["fixed"] is not None else res["text"]},
                _highlight_html(res["text"], res["issues"]))


# --------------------------------------------------------------------------
#  Пошаговый выбор замен (--review)
# --------------------------------------------------------------------------
def review_issues(res: dict, input_fn=input, out=print):
    """По каждой ошибке спрашивает: принять / вариант N / пропустить / свой текст."""
    text, issues = res["text"], res["issues"]
    k = 0
    while k < len(issues):
        i = issues[k]
        ln, col = line_col(text, i["offset"])
        out(f"\n{YELLOW(f'[{k + 1}/{len(issues)}]')} строка {ln}, символ {col}  "
            f"{DIM('(' + (i['category'] or i['rule']) + ')')}")
        out(f"   {context(text, i['offset'], i['length'])}")
        out(f"   {i['message']}")
        for n, r in enumerate(i["replacements"], 1):
            out(f"   {n}) {GREEN(r)}")
        out(DIM("   Enter=1-й · номер · s=пропустить · e=свой текст · a=принять остальные · q=пропустить остальные"))
        try:
            ans = input_fn("   > ").strip().lower()
        except EOFError:
            return
        if ans == "":
            if not i["replacements"]:
                i["skip"] = True
        elif ans.isdigit() and 1 <= int(ans) <= len(i["replacements"]):
            i["choice"] = i["replacements"][int(ans) - 1]
        elif ans == "s":
            i["skip"] = True
        elif ans == "e":
            try:
                custom = input_fn("   свой текст: ")
            except EOFError:
                return
            if custom:
                i["choice"], i["custom"] = custom, True
            else:
                i["skip"] = True
        elif ans == "a":
            return
        elif ans == "q":
            for j in issues[k:]:
                j["skip"] = True
            return
        else:
            out(YELLOW("   Не понял. Попробуйте ещё раз."))
            continue
        k += 1


# --------------------------------------------------------------------------
#  Файлы локализации: .json .csv .tsv .po .properties
# --------------------------------------------------------------------------
LT_CODES = {"ru": "ru-RU", "uk": "uk-UA", "en": "en-US", "de": "de-DE", "fr": "fr", "es": "es",
            "it": "it", "pl": "pl-PL", "pt": "pt-PT", "nl": "nl", "cs": "cs", "tr": "tr",
            "ja": "ja-JP", "zh": "zh-CN", "ko": "ko", "sv": "sv", "ro": "ro-RO", "be": "be-BY"}


def norm_lang(code) -> Optional[str]:
    if not isinstance(code, str):
        return None
    p = code.strip().lower().replace("_", "-").split("-")[0]
    p = "uk" if p == "ua" else p
    return p if p in LT_CODES else None


def lt_lang(code: str) -> str:
    return LT_CODES.get(code, "auto")


def read_file(path: str) -> str:
    for enc in ("utf-8-sig", "cp1251", "utf-16"):
        try:
            with open(path, "r", encoding=enc) as f:
                return f.read()
        except UnicodeError:
            continue
    raise CheckError("Не удалось определить кодировку файла.", "ENCODING_ERROR")


def _walk(obj, prefix=""):
    if isinstance(obj, str):
        yield prefix, obj
    elif isinstance(obj, dict):
        if obj and all(isinstance(v, str) for v in obj.values()) and all(norm_lang(k) for k in obj):
            yield prefix, dict(obj)                     # {"ru": "...", "en": "..."}
        else:
            for k, v in obj.items():
                yield from _walk(v, f"{prefix}.{k}" if prefix else str(k))
    elif isinstance(obj, list):
        for n, v in enumerate(obj):
            yield from _walk(v, f"{prefix}[{n}]")


def _load_json(path, hint):
    try:
        data = json.loads(read_file(path))
    except json.JSONDecodeError as e:
        raise CheckError(f"Некорректный JSON: {e}", "BAD_JSON")
    out = {}
    if isinstance(data, dict) and data and all(norm_lang(k) and isinstance(v, dict) for k, v in data.items()):
        for lg, sub in data.items():                    # {"ru": {...}, "en": {...}}
            for k, v in _walk(sub):
                if isinstance(v, str):
                    out.setdefault(norm_lang(lg), {})[k] = v
        return out
    for key, val in _walk(data):
        if isinstance(val, dict):                       # {"key": {"ru": ..., "en": ...}}
            for lg, v in val.items():
                out.setdefault(norm_lang(lg), {})[key] = v
        else:
            out.setdefault(norm_lang(hint) or "auto", {})[key] = val
    return out


def _load_csv(path, hint):
    raw = read_file(path)
    sample = raw[:2048]
    delim = max(",;\t", key=sample.count)
    rows = list(csv.reader(io.StringIO(raw), delimiter=delim))
    if not rows:
        return {}
    header = [h.strip().lower() for h in rows[0]]
    key_idx = next((n for n, h in enumerate(header) if h in ("key", "id", "name", "ключ")), 0)
    lang_cols = {n: norm_lang(h) for n, h in enumerate(header) if n != key_idx and norm_lang(h)}
    if not lang_cols:
        val_idx = next((n for n, h in enumerate(header) if h in ("value", "text", "string", "translation")),
                       1 if len(header) > 1 else 0)
        lang_cols = {val_idx: norm_lang(hint) or "auto"}
    out = {}
    for row in rows[1:]:
        if not row or key_idx >= len(row) or not row[key_idx].strip():
            continue
        for idx, lg in lang_cols.items():
            out.setdefault(lg, {})[row[key_idx].strip()] = row[idx] if idx < len(row) else ""
    return out


def _po_unescape(s):
    return re.sub(r"\\(.)", lambda m: {"n": "\n", "t": "\t", '"': '"', "\\": "\\"}.get(m.group(1), m.group(0)), s)


def _load_po(path, hint):
    entries, cur, field = [], {}, None
    for line in read_file(path).splitlines():
        line = line.strip()
        m = re.match(r'^(msgid|msgstr)\s+"(.*)"$', line)
        if m:
            if m.group(1) == "msgid":
                if cur:
                    entries.append(cur)
                cur = {"msgid": _po_unescape(m.group(2)), "msgstr": ""}
            else:
                cur["msgstr"] = _po_unescape(m.group(2))
            field = m.group(1)
        elif line.startswith('"') and line.endswith('"') and cur and field:
            cur[field] += _po_unescape(line[1:-1])
    if cur:
        entries.append(cur)
    lang = norm_lang(hint)
    out = {}
    for e in entries:
        if e["msgid"] == "":
            m = re.search(r"Language:\s*([A-Za-z_-]+)", e["msgstr"])
            lang = norm_lang(m.group(1)) if m else lang
    lang = lang or "auto"
    for e in entries:
        if e["msgid"]:
            out.setdefault(lang, {})[e["msgid"]] = e["msgstr"]
    return out


def _load_properties(path, hint):
    out = {}
    lang = norm_lang(hint) or "auto"
    for line in read_file(path).splitlines():
        line = line.strip()
        if not line or line.startswith(("#", "!")):
            continue
        m = re.match(r"^([^=:\s]+)\s*[=:]\s*(.*)$", line)
        if m:
            out.setdefault(lang, {})[m.group(1)] = m.group(2)
    return out


def load_loc(path: str, lang_hint: Optional[str] = None) -> dict:
    """Возвращает {язык: {ключ: значение}}."""
    ext = os.path.splitext(path)[1].lower()
    loaders = {".json": _load_json, ".csv": _load_csv, ".tsv": _load_csv,
               ".po": _load_po, ".properties": _load_properties}
    if ext not in loaders:
        raise CheckError(f"Неподдерживаемый формат {ext or '(без расширения)'}. "
                         f"Поддерживаются: {', '.join(loaders)}", "FORMAT")
    data = loaders[ext](path, lang_hint)
    data = {(lg or "auto"): vals for lg, vals in data.items() if vals}
    if not data:
        raise CheckError("В файле не найдено ни одной строки перевода.", "EMPTY_FILE")
    return data


def check_localization(path: str, opts: Opts) -> dict:
    data = load_loc(path, opts.lang if opts.lang != "auto" else None)
    langs = list(data)
    ref = "en" if "en" in data else langs[0]
    findings, fixed = [], {lg: dict(vals) for lg, vals in data.items()}

    def add(key, lg, kind, wrong="", fix="", message=""):
        findings.append({"key": key, "lang": lg, "kind": kind, "wrong": wrong, "fix": fix, "message": message})

    keys, seen = [], set()
    for lg in langs:
        for k in data[lg]:
            if k not in seen:
                seen.add(k)
                keys.append(k)

    # 1) пропуски, пустые значения, плейсхолдеры, непереведённое
    for key in keys:
        if len(langs) > 1:
            for lg in langs:
                if key not in data[lg]:
                    add(key, lg, "MISSING_KEY", message=f"Нет строки для языка «{lg}»")
                elif not data[lg][key].strip():
                    add(key, lg, "EMPTY", message=f"Пустой перевод для «{lg}»")
        elif not data[langs[0]][key].strip():
            add(key, langs[0], "EMPTY", message="Пустое значение")
        ref_val = data[ref].get(key, "")
        if not ref_val.strip():
            continue
        ref_ph = placeholders_of(ref_val)
        for lg in langs:
            val = data[lg].get(key, "")
            if lg == ref or not val.strip():
                continue
            ph = placeholders_of(val)
            if ph != ref_ph:
                lost, extra = sorted((ref_ph - ph).elements()), sorted((ph - ref_ph).elements())
                add(key, lg, "PLACEHOLDERS", wrong=val,
                    message=f"Плейсхолдеры не совпадают с «{ref}»: нет {lost or '—'}, лишние {extra or '—'}")
            if (ref == "en" and lg in ("ru", "uk") and val.strip().lower() == ref_val.strip().lower()
                    and len(val.strip()) >= 4 and re.search(r"[A-Za-z]{3}", PLACEHOLDER_RE.sub("", val))):
                add(key, lg, "UNTRANSLATED", wrong=val, message="Совпадает с английским — возможно, не переведено")

    # 2) орфография и грамматика: все строки языка — одним запросом
    for lg in langs:
        items = [(k, v) for k, v in data[lg].items() if v.strip()]
        if not items:
            continue
        joined, starts = "", []
        for _, v in items:
            starts.append(len(joined))
            joined += v + "\n\n"
        issues, _ = check_text(joined, lt_lang(lg), "text", None, opts.workers)
        grouped = {}
        for i in issues:
            idx = bisect.bisect_right(starts, i["offset"]) - 1
            k, v = items[idx]
            lo = i["offset"] - starts[idx]
            if lo + i["length"] > len(v):
                continue
            grouped.setdefault(idx, []).append(dict(i, offset=lo))
        for idx, local_issues in grouped.items():
            k, v = items[idx]
            new_v, _warns = apply_fixes_ex(v, local_issues)
            fixed[lg][k] = new_v
            for li in local_issues:
                wrong = v[li["offset"]:li["offset"] + li["length"]]
                kind = "SPELLING" if re.search(r"SPELL|MORFOLOGIK|TYPO|ОРФОГР", li["rule"] + li["category"], re.I) \
                    else "GRAMMAR"
                add(k, lg, kind, wrong, li["replacements"][0] if li["replacements"] else "", li["message"])
    return {"findings": findings, "fixed": fixed, "languages": langs, "keys": len(keys), "reference": ref}


def render_loc_report(res: dict, color: bool = True) -> str:
    with (contextlib.nullcontext() if color else no_color()):
        f = res["findings"]
        out = [CYAN(f"Языки: {', '.join(res['languages'])}   Ключей: {res['keys']}   Находок: {len(f)}")]
        if not f:
            out.append(GREEN("✔ Проблем не найдено."))
            return "\n".join(out)
        counts = Counter(x["kind"] for x in f)
        out.append("Сводка: " + ", ".join(f"{k}={v}" for k, v in counts.most_common()) + "\n")
        for x in f:
            paint = YELLOW if x["kind"] == "UNTRANSLATED" else RED
            line = f"{paint('[' + x['kind'] + ']')} {x['lang']} · {x['key']}"
            if x["wrong"] and x["fix"]:
                line += f": {RED(repr(x['wrong']))} → {GREEN(repr(x['fix']))}"
            elif x["wrong"]:
                line += f": {x['wrong']!r}"
            out.append(line + (f"  — {x['message']}" if x["message"] else ""))
        return "\n".join(out)


def save_loc_fixed(fixed: dict, path: str):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(fixed, f, ensure_ascii=False, indent=2)


# --------------------------------------------------------------------------
#  ИИ-разбор (использует ai_code_fixer.py из той же папки)
# --------------------------------------------------------------------------
def ai_review(text: str, ai_lang: str = "ru"):
    try:
        import ai_code_fixer as acf
    except ImportError:
        print(YELLOW("⚠ ai_code_fixer.py не найден — положите его в одну папку с ботом."))
        return None
    key = os.environ.get("ANTHROPIC_API_KEY", "").strip()
    if not key:
        print(YELLOW("⚠ Не задан ANTHROPIC_API_KEY — ИИ-разбор пропущен."))
        return None
    print(CYAN("\n🤖 Глубокий разбор ИИ (логика, типы, импорты):"))
    bot = acf.Bot(key)
    bot.lang = ai_lang if ai_lang in ("ru", "uk", "en") else "ru"
    bot.ask(text, is_code=True)
    return bot.last_code


# --------------------------------------------------------------------------
#  Вывод для консоли
# --------------------------------------------------------------------------
def process(text: str, opts: Opts, filename: Optional[str] = None, input_fn=input):
    """Полный цикл для консоли. Возвращает результат (dict) или None при ошибке."""
    text = text.strip("\r\n")
    if not text.strip():
        print(YELLOW("Пустой текст."))
        return None
    try:
        res = analyze(text, opts, filename)
    except CheckError as e:
        print(RED(f"✖ Ошибка проверки (Код: {e.code}): {e}"))
        return None
    if opts.review and res["issues"]:
        review_issues(res, input_fn)
    finalize(res)
    print(render_report(res, diff=opts.diff))
    if opts.report:
        try:
            export_result(res, opts.report)
            print(GREEN(f"✔ Отчёт сохранён: {opts.report}"))
        except OSError as e:
            print(RED(f"✖ Не удалось сохранить отчёт: {e}"))
    if opts.ai and res["code_mode"]:
        ai_review(res["fixed"], opts.ai_lang)
    return res


def safe_process(text: str, opts: Opts, filename: Optional[str] = None):
    """process() с защитой: непредвиденная ошибка не роняет бота, а пишется в лог."""
    try:
        return process(text, opts, filename)
    except Exception as e:                      # noqa: BLE001
        log.exception("внутренняя ошибка при обработке")
        print(RED(f"✖ Внутренняя ошибка [{type(e).__name__}]: {e}  (подробности в логе)"))
        return None


def run_loc(path: str, opts: Opts, out_path: Optional[str] = None) -> Optional[dict]:
    try:
        res = check_localization(path, opts)
    except (OSError, CheckError) as e:
        print(RED(f"✖ Ошибка (Код: {getattr(e, 'code', type(e).__name__)}): {e}"))
        return None
    print(render_loc_report(res))
    if out_path:
        try:
            save_loc_fixed(res["fixed"], out_path)
            print(GREEN(f"✔ Исправленные строки сохранены: {out_path}"))
        except OSError as e:
            print(RED(f"✖ Не удалось сохранить: {e}"))
    if opts.report:
        try:
            export_rows(opts.report, "Отчёт по локализации", res["findings"])
            print(GREEN(f"✔ Отчёт сохранён: {opts.report}"))
        except OSError as e:
            print(RED(f"✖ Не удалось сохранить отчёт: {e}"))
    return res


# --------------------------------------------------------------------------
#  Интерактивный режим
# --------------------------------------------------------------------------
HELP = """Команды:
  просто введите текст  — проверить его (автоопределение код/текст)
  /multi                — ввод нескольких строк (завершить пустой строкой)
  /file путь            — проверить файл
  /loc путь             — проверить файл локализации (.json .csv .po .properties)
  /save путь            — сохранить последний исправленный результат
  /report путь          — сохранить отчёт (.html .json .csv .md)
  /mode auto|code|text  — режим: сам определять / код / обычный текст
  /lang код             — язык: auto, ru-RU, uk-UA, en-US ...
  /review on|off        — спрашивать вариант замены по каждой ошибке
  /diff on|off          — показывать «было → стало»
  /ai                   — глубокий разбор ИИ последнего кода (нужен ai_code_fixer.py)
  /ignore слово         — добавить слово в словарь игнорирования
  /help                 — эта справка
  /exit                 — выход"""


def _onoff(arg: str):
    a = arg.strip().lower()
    return True if a in ("on", "1", "yes", "да") else False if a in ("off", "0", "no", "нет") else None


def interactive(opts: Opts):
    print(CYAN("🤖 Продвинутый ИИ-Бот-корректор запущен. /help — справка."))
    last = None
    while True:
        try:
            line = input(CYAN("\n>>> ")).strip()
        except (EOFError, KeyboardInterrupt):
            print("\nПока!")
            return
        if not line.strip():                  # пустой Enter / одни пробелы — игнорируем
            continue
        low = line.lower()
        cmd, _, arg = line.partition(" ")
        cmd, arg = cmd.lower(), arg.strip().strip('"')
        if low in ("/exit", "/quit", "exit", "выход", "/выход"):
            print(GREEN("Пока! Удачи в разработке."))
            return
        if cmd in ("/help", "/?"):
            print(HELP)
        elif cmd == "/mode":
            if arg.lower() in ("auto", "code", "text"):
                opts.mode = arg.lower()
                print(GREEN(f"Режим: {opts.mode}"))
            else:
                print(YELLOW("Пример: /mode code   (auto | code | text)"))
        elif cmd == "/lang":
            if re.fullmatch(r"[A-Za-z]{2,3}(-[A-Za-z]{2,4})?|auto", arg):
                opts.lang = arg
                print(GREEN(f"Язык: {opts.lang}"))
            else:
                print(YELLOW("Пример: /lang ru-RU   или   /lang auto"))
        elif cmd in ("/review", "/diff"):
            v = _onoff(arg)
            if v is None:
                print(YELLOW(f"Пример: {cmd} on   или   {cmd} off"))
            else:
                setattr(opts, cmd[1:], v)
                print(GREEN(f"{cmd[1:]}: {'вкл' if v else 'выкл'}"))
        elif cmd == "/ignore":
            if arg:
                IGNORE.add(arg)
                print(GREEN(f"✔ «{arg}» добавлено в {IGNORE.path}"))
            else:
                print(YELLOW("Пример: /ignore NPC"))
        elif cmd == "/file":
            if not arg:
                print(YELLOW("Укажите путь: /file text.txt"))
                continue
            try:
                text = read_file(arg)
            except (OSError, CheckError) as e:
                print(RED(f"✖ Ошибка файла: {e}"))
                continue
            print(CYAN(f"Анализируем файл {arg}..."))
            last = safe_process(text, opts, arg) or last
        elif cmd == "/loc":
            if not arg:
                print(YELLOW("Укажите путь: /loc strings.json"))
                continue
            run_loc(arg, opts)
        elif cmd == "/save":
            if last is None:
                print(YELLOW("Пока нечего сохранять."))
            elif not arg:
                print(YELLOW("Укажите путь: /save result.txt"))
            else:
                try:
                    with open(arg, "w", encoding="utf-8") as f:
                        f.write(last["fixed"])
                    print(GREEN(f"✔ Сохранено в файл {arg}"))
                except OSError as e:
                    print(RED(f"✖ Ошибка сохранения: {e}"))
        elif cmd == "/report":
            if last is None:
                print(YELLOW("Пока нечего сохранять."))
            elif not arg:
                print(YELLOW("Укажите путь: /report report.html"))
            else:
                try:
                    export_result(last, arg)
                    print(GREEN(f"✔ Отчёт сохранён: {arg}"))
                except OSError as e:
                    print(RED(f"✖ Не удалось сохранить отчёт: {e}"))
        elif cmd == "/ai":
            if last is None:
                print(YELLOW("Сначала проверьте код."))
            else:
                ai_review(last["fixed"], opts.ai_lang)
        elif low == "/multi":
            print(DIM("Вводите текст, пустая строка — конец:"))
            buf = []
            while True:
                try:
                    s = input()
                except (EOFError, KeyboardInterrupt):
                    break
                if not s:
                    break
                buf.append(s)
            last = safe_process("\n".join(buf), opts) or last
        elif line.startswith("/"):
            print(YELLOW("Неизвестная команда. /help — справка."))
        else:
            last = safe_process(line, opts) or last


# --------------------------------------------------------------------------
#  Telegram-бот (long polling, без сторонних библиотек)
# --------------------------------------------------------------------------
TG_HELP = ("Пришлите текст или код — я найду ошибки и верну исправленный вариант.\n"
           "Можно отправить файл (.txt, .py, .js, .json ... до 1 МБ).\n\n"
           "/mode auto|code|text — режим\n/lang ru-RU|uk-UA|en-US|auto — язык\n/help — справка")


class TelegramBot:
    def __init__(self, token: str, opts: Opts, allowed=None):
        self.token, self.base_opts = token, opts
        self.base = f"https://api.telegram.org/bot{token}"
        self.allowed = set(allowed or [])
        self.chat_opts = {}

    def api(self, method: str, _timeout: int = 30, **params):
        req = urllib.request.Request(f"{self.base}/{method}", data=json.dumps(params).encode("utf-8"),
                                     headers={"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=_timeout) as r:
                data = json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            raise CheckError(f"Telegram: HTTP {e.code} {e.reason}", e.code)
        except (urllib.error.URLError, OSError) as e:
            raise CheckError(f"Telegram: {getattr(e, 'reason', e)}", "NETWORK")
        if not data.get("ok"):
            raise CheckError(f"Telegram: {data.get('description', 'ошибка')}", data.get("error_code"))
        return data["result"]

    def send(self, chat_id, text: str):
        text = text or "—"
        for k in range(0, len(text), 4000):
            self.api("sendMessage", chat_id=chat_id, text=text[k:k + 4000], disable_web_page_preview=True)

    def download_text(self, doc: dict) -> str:
        if doc.get("file_size", 0) > 1_000_000:
            raise CheckError("Файл больше 1 МБ.", "TOO_BIG")
        info = self.api("getFile", file_id=doc["file_id"])
        url = f"https://api.telegram.org/file/bot{self.token}/{info['file_path']}"
        try:
            with urllib.request.urlopen(url, timeout=30) as r:
                raw = r.read(1_000_001)
        except (urllib.error.URLError, OSError) as e:
            raise CheckError(f"Не удалось скачать файл: {e}", "NETWORK")
        for enc in ("utf-8-sig", "cp1251"):
            try:
                return raw.decode(enc)
            except UnicodeError:
                continue
        raise CheckError("Не удалось определить кодировку файла.", "ENCODING_ERROR")

    def command(self, chat_id, text: str, opts: Opts):
        cmd, _, arg = text.partition(" ")
        cmd, arg = cmd.split("@")[0].lower(), arg.strip()
        if cmd in ("/start", "/help"):
            self.send(chat_id, TG_HELP)
        elif cmd == "/mode" and arg in ("auto", "code", "text"):
            opts.mode = arg
            self.send(chat_id, f"Режим: {arg}")
        elif cmd == "/lang" and re.fullmatch(r"[A-Za-z]{2,3}(-[A-Za-z]{2,4})?|auto", arg):
            opts.lang = arg
            self.send(chat_id, f"Язык: {arg}")
        else:
            self.send(chat_id, "Неизвестная команда или неверный аргумент. /help")

    def handle_update(self, upd: dict):
        msg = upd.get("message") or {}
        chat_id = (msg.get("chat") or {}).get("id")
        if chat_id is None:
            return
        uid = (msg.get("from") or {}).get("id")
        if self.allowed and uid not in self.allowed:
            self.send(chat_id, "⛔ Нет доступа.")
            return
        opts = self.chat_opts.setdefault(chat_id, dataclasses.replace(self.base_opts))
        filename = None
        try:
            if msg.get("document"):
                filename = msg["document"].get("file_name")
                text = self.download_text(msg["document"])
            else:
                text = msg.get("text")
            if not text or not text.strip():
                return
            if msg.get("text") and text.startswith("/"):
                self.command(chat_id, text.strip(), opts)
                return
            if len(text) > 50_000:
                self.send(chat_id, "Слишком длинный текст (максимум 50 000 символов).")
                return
            res = finalize(analyze(text.strip("\r\n"), opts, filename))
            self.send(chat_id, render_report(res, color=False))
        except CheckError as e:
            self.send(chat_id, f"✖ Ошибка (Код: {e.code}): {e}")

    def run(self):
        print(GREEN("✔ Telegram-бот запущен. Остановить: Ctrl+C"))
        offset, backoff = None, 1
        while True:
            try:
                params = {"timeout": 30, "allowed_updates": ["message"]}
                if offset:
                    params["offset"] = offset
                updates = self.api("getUpdates", _timeout=45, **params)
                backoff = 1
                for u in updates:
                    offset = u["update_id"] + 1
                    try:
                        self.handle_update(u)
                    except Exception:           # noqa: BLE001
                        log.exception("ошибка обработки обновления %s", u.get("update_id"))
            except KeyboardInterrupt:
                print("\nОстановлено.")
                return
            except CheckError as e:
                log.warning("Telegram недоступен [%s]: %s (повтор через %d c)", e.code, e, backoff)
                time.sleep(backoff)
                backoff = min(backoff * 2, 60)


# --------------------------------------------------------------------------
#  Окно (tkinter)
# --------------------------------------------------------------------------
def run_gui(opts: Opts) -> int:
    try:
        import tkinter as tk
        from tkinter import filedialog, messagebox, ttk
    except ImportError:
        print(RED("✖ tkinter не установлен. Windows/macOS: переустановите Python с галочкой tcl/tk; "
                  "Linux: sudo apt install python3-tk"))
        return 1

    root = tk.Tk()
    root.title("Бот-корректор")
    root.geometry("1150x700")
    state = {"res": None, "file": None, "busy": False}

    bar = ttk.Frame(root, padding=6)
    bar.pack(fill="x")
    mode_var, lang_var = tk.StringVar(value=opts.mode), tk.StringVar(value=opts.lang)
    ttk.Label(bar, text="Режим:").pack(side="left")
    ttk.Combobox(bar, textvariable=mode_var, values=("auto", "code", "text"), width=6, state="readonly").pack(side="left", padx=4)
    ttk.Label(bar, text="Язык:").pack(side="left", padx=(10, 0))
    ttk.Combobox(bar, textvariable=lang_var, values=("auto", "ru-RU", "uk-UA", "en-US"), width=8).pack(side="left", padx=4)

    paned = ttk.PanedWindow(root, orient="horizontal")
    paned.pack(fill="both", expand=True, padx=6, pady=4)
    left = ttk.Frame(paned)
    right = ttk.Frame(paned)
    paned.add(left, weight=3)
    paned.add(right, weight=2)

    txt = tk.Text(left, wrap="word", undo=True, font=("Consolas", 11))
    sb = ttk.Scrollbar(left, command=txt.yview)
    txt.configure(yscrollcommand=sb.set)
    sb.pack(side="right", fill="y")
    txt.pack(fill="both", expand=True)
    txt.tag_configure("err", background="#ffd2d2", underline=True)
    txt.tag_configure("sel", background="#ffe58a")

    lst = tk.Listbox(right, activestyle="none", font=("Consolas", 10))
    lst.pack(fill="both", expand=True)
    info = ttk.Label(right, text="", wraplength=380, justify="left")
    info.pack(fill="x", pady=4)
    rep_var = tk.StringVar()
    rep_box = ttk.Combobox(right, textvariable=rep_var)
    rep_box.pack(fill="x")
    status = ttk.Label(root, text="Вставьте текст или код и нажмите «Проверить»", anchor="w")
    status.pack(fill="x", padx=6, pady=(0, 4))

    def set_status(s):
        status.config(text=s)

    def cur_opts():
        o = dataclasses.replace(opts)
        o.mode, o.lang = mode_var.get(), (lang_var.get().strip() or "auto")
        return o

    def show(res, snapshot):
        state["busy"] = False
        if txt.get("1.0", "end-1c") != snapshot:
            return                                   # текст изменили, пока шла проверка
        state["res"] = res
        txt.tag_remove("err", "1.0", "end")
        lst.delete(0, "end")
        for n, i in enumerate(res["issues"], 1):
            s, e = i["offset"], i["offset"] + i["length"]
            txt.tag_add("err", f"1.0+{s}c", f"1.0+{e}c")
            lst.insert("end", f"{n}. {i['wrong']!r} → {i['replacements'][0] if i['replacements'] else '?'}")
        set_status(f"Режим: {'КОД' if res['code_mode'] else 'ТЕКСТ'} · язык: {res['language']} · ошибок: {len(res['issues'])}")

    def fail(e):
        state["busy"] = False
        set_status("Ошибка")
        messagebox.showerror("Ошибка проверки", f"Код: {getattr(e, 'code', '')}\n{e}")

    def check():
        if state["busy"]:
            return
        snapshot = txt.get("1.0", "end-1c")
        if not snapshot.strip():
            set_status("Пустой текст")
            return
        state["busy"] = True
        set_status("Проверяю...")
        o, fname = cur_opts(), state["file"]

        def work():
            try:
                res = analyze(snapshot, o, fname)
                root.after(0, show, res, snapshot)
            except CheckError as e:
                root.after(0, fail, e)
            except Exception as e:                   # noqa: BLE001
                log.exception("GUI: внутренняя ошибка")
                root.after(0, fail, e)
        threading.Thread(target=work, daemon=True).start()

    def on_select(_=None):
        sel = lst.curselection()
        if not sel or not state["res"]:
            return
        i = state["res"]["issues"][sel[0]]
        info.config(text=i["message"])
        rep_box.config(values=i["replacements"])
        rep_var.set(i["replacements"][0] if i["replacements"] else "")
        txt.tag_remove("sel", "1.0", "end")
        a, b = f"1.0+{i['offset']}c", f"1.0+{i['offset'] + i['length']}c"
        txt.tag_add("sel", a, b)
        txt.see(a)

    def apply_one():
        sel = lst.curselection()
        if not sel or not state["res"]:
            return
        i = state["res"]["issues"][sel[0]]
        rep = rep_var.get()
        a, b = f"1.0+{i['offset']}c", f"1.0+{i['offset'] + i['length']}c"
        txt.delete(a, b)
        txt.insert(a, rep)
        check()

    def apply_all():
        res = state["res"]
        if not res:
            return
        finalize(res)
        txt.delete("1.0", "end")
        txt.insert("1.0", res["fixed"])
        if res["warnings"]:
            messagebox.showwarning("Пропущено", "\n".join(res["warnings"]))
        check()

    def open_file():
        p = filedialog.askopenfilename()
        if p:
            try:
                data = read_file(p)
            except (OSError, CheckError) as e:
                messagebox.showerror("Ошибка", str(e))
                return
            state["file"] = p
            txt.delete("1.0", "end")
            txt.insert("1.0", data)
            check()

    def save_file():
        p = filedialog.asksaveasfilename(defaultextension=".txt", initialfile=os.path.basename(state["file"] or "fixed.txt"))
        if p:
            with open(p, "w", encoding="utf-8") as f:
                f.write(txt.get("1.0", "end-1c"))
            set_status(f"Сохранено: {p}")

    def copy_all():
        root.clipboard_clear()
        root.clipboard_append(txt.get("1.0", "end-1c"))
        set_status("Скопировано в буфер обмена")

    for label, fn in (("Открыть", open_file), ("Проверить", check), ("Применить все", apply_all),
                      ("Сохранить", save_file), ("Копировать", copy_all)):
        ttk.Button(bar, text=label, command=fn).pack(side="left", padx=3)
    ttk.Button(right, text="Применить эту замену", command=apply_one).pack(fill="x", pady=4)
    lst.bind("<<ListboxSelect>>", on_select)
    lst.bind("<Double-Button-1>", lambda _e: apply_one())
    root.bind("<Control-Return>", lambda _e: check())
    root.mainloop()
    return 0


# --------------------------------------------------------------------------
#  Запуск
# --------------------------------------------------------------------------
def normalize_server(url: str) -> str:
    url = url.strip().rstrip("/")
    return url if url.endswith("/v2/check") else url + "/v2/check"


def configure(args):
    global API_URL, CACHE
    if args.server:
        API_URL = normalize_server(args.server)
    CACHE = Cache(None if args.no_cache else args.cache_file)
    load_default_ignore(args.ignore_file)


def build_parser():
    ap = argparse.ArgumentParser(description="Бот-корректор текста, кода и файлов локализации")
    ap.add_argument("-t", "--text", help="проверить переданный текст и выйти")
    ap.add_argument("-f", "--file", help="проверить файл и выйти")
    ap.add_argument("-l", "--lang", default="auto", help="код языка (по умолчанию auto)")
    ap.add_argument("-m", "--mode", choices=("auto", "code", "text"), default="auto",
                    help="auto — определять сам; code — это код; text — обычный текст")
    ap.add_argument("--style", choices=tuple(STYLES), help="стиль комментариев кода (по умолчанию — по файлу/тексту)")
    ap.add_argument("--review", action="store_true", help="спрашивать вариант замены по каждой ошибке")
    ap.add_argument("--diff", action="store_true", help="показать «было → стало»")
    ap.add_argument("--report", help="сохранить отчёт (.html .json .csv .md)")
    ap.add_argument("--loc", help="проверить файл локализации (.json .csv .tsv .po .properties)")
    ap.add_argument("--loc-out", help="куда сохранить исправленные строки локализации (JSON)")
    ap.add_argument("--ai", action="store_true", help="после исправления кода — глубокий разбор ИИ")
    ap.add_argument("--ai-lang", choices=("ru", "uk", "en"), default="ru", help="язык ответа ИИ")
    ap.add_argument("--server", help="адрес своего сервера LanguageTool, напр. http://localhost:8081")
    ap.add_argument("--workers", type=int, default=WORKERS, help="параллельных запросов (по умолчанию 3)")
    ap.add_argument("--cache-file", default=DEFAULT_CACHE, help="файл кэша на диске")
    ap.add_argument("--no-cache", action="store_true", help="не использовать кэш на диске")
    ap.add_argument("--ignore-file", help="словарь игнорирования (по умолчанию ignore.txt)")
    ap.add_argument("--gui", action="store_true", help="запустить окно (tkinter)")
    ap.add_argument("--telegram", action="store_true", help="запустить Telegram-бота")
    ap.add_argument("--tg-token", help="токен бота (или TELEGRAM_BOT_TOKEN)")
    ap.add_argument("--tg-allow", help="ID пользователей через запятую, которым разрешён доступ")
    ap.add_argument("--debug", action="store_true", help="выводить лог запросов в консоль")
    ap.add_argument("--log-file", default="grammar_bot.log", help="лог-файл (пусто = выключить)")
    ap.add_argument("--strict", action="store_true", help="код выхода 2, если найдены ошибки (для автотестов)")
    return ap


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    setup_logging(args.debug, args.log_file)
    log.info("запуск: %s", " ".join(argv if argv is not None else sys.argv[1:]) or "интерактивный режим")
    configure(args)
    opts = Opts(lang=args.lang, mode=args.mode, style=args.style, review=args.review, diff=args.diff,
                report=args.report, ai=args.ai, ai_lang=args.ai_lang, workers=max(1, args.workers))

    if args.gui:
        return run_gui(opts)

    if args.telegram:
        token = args.tg_token or os.environ.get("TELEGRAM_BOT_TOKEN", "")
        if not token:
            print(RED("✖ Нужен токен: --tg-token ... или переменная TELEGRAM_BOT_TOKEN (получить у @BotFather)"))
            return 1
        allowed = [int(x) for x in re.findall(r"-?\d+", args.tg_allow or "")]
        TelegramBot(token, opts, allowed).run()
        return 0

    if args.loc:
        res = run_loc(args.loc, opts, args.loc_out)
        if res is None:
            return 1
        return 2 if (res["findings"] and args.strict) else 0

    if args.text is not None or args.file:
        try:
            text = args.text if args.text is not None else read_file(args.file)
        except (OSError, CheckError) as e:
            print(RED(f"✖ Ошибка (Код: {e.code}): {e}" if isinstance(e, CheckError)
                      else f"✖ Ошибка [{type(e).__name__}]: {e}"))
            return 1
        res = safe_process(text, opts, args.file)
        if res is None:
            return 0 if not text.strip() else 1
        return 2 if (res["issues"] and args.strict) else 0

    interactive(opts)
    return 0


if __name__ == "__main__":
    sys.exit(main())

    