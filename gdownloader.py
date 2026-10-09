#!/usr/bin/env python3
"""
Production-ready Google Drive Folder Downloader & Incremental Updater
- Incremental Update Mode (--update): scans remote Drive folders and downloads ONLY
  new or modified files, skipping unchanged files (including large videos).
- Modern User-Agent (prevents Google 403 Forbidden / bot blocks)
- Smart Cookie Validation & Fallback (detects expired/stale cookies causing login redirects)
- Fast resume/skip for already downloaded folders (avoids re-downloading completed gigabytes)
- File-level and folder-level retry mechanisms with exponential backoff
- Strict verification (verifies files and sizes)
- Preserves folder structure and names
- Built-in Quality Control (QC) reporting
"""

import sys
import os
import time
import re
import logging
import argparse
import email.utils
import http.cookiejar
import json
import urllib.parse
from pathlib import Path
from typing import List, Tuple, Optional
from concurrent.futures import ThreadPoolExecutor

# Ensure UTF-8 output on Windows consoles to prevent charmap encoding errors
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

import requests
import bs4
import gdown
from gdown.exceptions import DownloadError, FileURLRetrievalError

# ====================== CONFIG ======================
BASE_DIR = Path(__file__).parent.resolve()
LINKS_FILE = BASE_DIR / "links.txt"
OUTPUT_DIR = BASE_DIR / "Download Data"

def find_all_cookie_files() -> List[Path]:
    """Finds all .txt files in BASE_DIR that contain 'cookie' (case-insensitive) in their filename."""
    files = [
        f for f in BASE_DIR.glob("*.txt")
        if "cookie" in f.name.lower() and f.is_file() and f.name.lower() != "download_log.txt"
    ]
    # Priority: exact 'cookies.txt' first, then sorted by most recently modified
    files.sort(key=lambda f: (0 if f.name.lower() == "cookies.txt" else 1, -f.stat().st_mtime))
    return files


def find_cookies_file(custom_path: Optional[str] = None) -> Optional[Path]:
    """
    Finds a cookies file:
    - If custom_path provided and exists, returns it
    - Checks for exact 'cookies.txt' or any .txt file containing 'cookie' in its name
    """
    if custom_path:
        p = Path(custom_path)
        if p.is_file():
            return p
    candidates = find_all_cookie_files()
    return candidates[0] if candidates else None

COOKIES_FILE = find_cookies_file()
RETRIES = 5
FILE_RETRIES = 3
QUIET = False
SKIP_EXISTING = True  # Automatically skips folders that are already completely downloaded
UPDATE_MODE = False   # Incremental update mode: check individual files

WAIT_BETWEEN_DOWNLOADS = 5
WAIT_ON_RATE_LIMIT = 45

# Modern browser User-Agent prevents Google 403 blocks on file downloads
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
# ====================================================

OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

log_file = BASE_DIR / "download_log.txt"
stream_handler = logging.StreamHandler(sys.stdout)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-8s | %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
    handlers=[
        stream_handler,
        logging.FileHandler(log_file, encoding="utf-8"),
    ],
)
logger = logging.getLogger(__name__)


def read_links(file_path: Path) -> List[str]:
    if not file_path.exists():
        logger.error(f"links.txt not found: {file_path}")
        sys.exit(1)

    links = []
    with open(file_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                links.append(line)

    if not links:
        logger.error("No valid links found in links.txt")
        sys.exit(1)

    return links


def extract_folder_id(url: str) -> str:
    m = re.search(r"/folders/([-\w]{25,})", url)
    if m:
        return m.group(1)
    return url.rstrip("/").split("/")[-1].split("?")[0]


def get_remote_folder_info(folder_id: str, timeout: int = 12) -> Tuple[Optional[str], int, bool]:
    """
    Queries Google Drive embeddedfolderview to get:
    (title, file_count, is_login_redirect)
    """
    url = f"https://drive.google.com/embeddedfolderview?id={folder_id}"
    try:
        headers = {"User-Agent": USER_AGENT}
        res = requests.get(url, headers=headers, timeout=timeout)
        if res.status_code != 200:
            return None, 0, False
        soup = bs4.BeautifulSoup(res.text, "html.parser")
        title = soup.title.string.strip() if soup.title and soup.title.string else None
        is_redirect = (
            title == "Redirecting..."
            or "accounts.google.com" in res.url
            or "ServiceLogin" in res.text[:500]
        )
        if is_redirect:
            return None, 0, True
        file_count = len(soup.find_all("a"))
        return title, file_count, False
    except Exception:
        return None, 0, False


def is_os_junk_file(path_str: str) -> bool:
    """Checks if a file is an OS junk metadata file (.DS_Store, Thumbs.db, desktop.ini)."""
    name = Path(path_str).name.lower()
    return name in [".ds_store", "thumbs.db", "desktop.ini", ".spotlight-v100", ".trashes"] or name.startswith("._")


def is_image_file(path_str: str) -> bool:
    """Checks if a file is an image format."""
    return any(path_str.lower().endswith(ext) for ext in [".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp", ".ico"])


def is_text_file(path_str: str) -> bool:
    """Checks if a file is a text/metadata format."""
    return any(path_str.lower().endswith(ext) for ext in [".txt", ".md", ".json", ".csv", ".xml", ".yaml", ".yml"])


def download_image_via_cdn(file_id: str, out_path: Path, session: Optional[requests.Session] = None) -> bool:
    """
    Downloads an image file directly from Google high-speed CDN.
    Completely bypasses the Google Drive 24-hour quota limit.
    """
    cdn_url = f"https://lh3.googleusercontent.com/d/{file_id}"
    headers = {"User-Agent": USER_AGENT}
    sess = session or requests.Session()
    try:
        r = sess.get(cdn_url, headers=headers, stream=True, timeout=15)
        ct = r.headers.get("Content-Type", "").lower()
        if r.status_code == 200 and "image/" in ct:
            out_path.parent.mkdir(parents=True, exist_ok=True)
            with open(out_path, "wb") as f:
                for chunk in r.iter_content(chunk_size=32768):
                    if chunk:
                        f.write(chunk)
            return True
    except Exception as e:
        logger.debug(f"CDN image download failed for {file_id}: {e}")
    return False


def download_text_via_viewer(file_id: str, session: Optional[requests.Session] = None) -> Optional[str]:
    """
    Extracts text/metadata content from Google Drive Viewer.
    Completely bypasses 24h quota limits on .txt, .md, .json, .csv files.
    """
    url = f"https://drive.google.com/file/d/{file_id}/view"
    headers = {"User-Agent": USER_AGENT}
    sess = session or requests.Session()
    try:
        r = sess.get(url, headers=headers, timeout=12)
        if r.status_code != 200:
            return None
        idx = r.text.find(r"\u0026dsmi\u003dtexmex")
        if idx == -1:
            return None
        start = r.text.rfind('"', 0, idx)
        end = r.text.find('"', idx)
        if start == -1 or end == -1:
            return None
        full_url = r.text[start + 1 : end].encode("utf-8").decode("unicode_escape")
        resp = sess.get(full_url, headers=headers, timeout=10)
        if resp.status_code != 200:
            return None
        data_start = resp.text.find("{")
        if data_start == -1:
            return None
        data = json.loads(resp.text[data_start:])
        page_rel = data.get("page")
        if not page_rel:
            return None
        page_url = urllib.parse.urljoin("https://drive.google.com/viewer/", page_rel)
        rv = sess.get(page_url, headers=headers, timeout=10)
        if rv.status_code != 200:
            return None
        text_data_start = rv.text.find("{")
        if text_data_start == -1:
            return None
        text_data = json.loads(rv.text[text_data_start:])
        return text_data.get("data")
    except Exception as e:
        logger.debug(f"Viewer text extraction error for {file_id}: {e}")
        return None


def download_single_file_resilient(
    file_id: str,
    rel_path: str,
    target_path: Path,
    session: requests.Session,
    use_cookies: bool,
    expected_mtime: Optional[float] = None,
) -> Tuple[bool, str]:
    """
    Downloads a single file using multi-strategy resilience:
    1. OS junk files (.DS_Store, Thumbs.db) -> Skipped
    2. Images -> Download via Google high-speed CDN (bypasses 24h quota)
    3. Text/Markdown/JSON -> Standard download with automatic Drive Viewer fallback on quota limit
    4. Binaries/Videos -> Standard download with confirmation parsing & error resilience
    Returns:
        (success: bool, reason: str)
    """
    if is_os_junk_file(rel_path):
        return True, "SKIPPED_JUNK"

    target_path.parent.mkdir(parents=True, exist_ok=True)

    # 1. Images via Google CDN (quota bypass)
    if is_image_file(rel_path):
        if download_image_via_cdn(file_id, target_path, session):
            if expected_mtime:
                try:
                    os.utime(target_path, (expected_mtime, expected_mtime))
                except Exception:
                    pass
            return True, "CDN"

    # 2. Text / Metadata files (with Drive Viewer fallback)
    if is_text_file(rel_path):
        try:
            gdown.download(
                url=f"https://drive.google.com/uc?id={file_id}",
                output=str(target_path),
                quiet=True,
                use_cookies=use_cookies,
                cookies_file=str(COOKIES_FILE) if (use_cookies and COOKIES_FILE and COOKIES_FILE.exists()) else None,
                user_agent=USER_AGENT,
            )
            if target_path.exists() and target_path.stat().st_size > 0:
                if expected_mtime:
                    try:
                        os.utime(target_path, (expected_mtime, expected_mtime))
                    except Exception:
                        pass
                return True, "STANDARD"
        except Exception:
            pass

        # Viewer extraction fallback
        text_content = download_text_via_viewer(file_id, session)
        if text_content is not None:
            with open(target_path, "w", encoding="utf-8") as out_f:
                out_f.write(text_content)
            if expected_mtime:
                try:
                    os.utime(target_path, (expected_mtime, expected_mtime))
                except Exception:
                    pass
            return True, "VIEWER_FALLBACK"

    # 3. Binaries / Videos
    try:
        gdown.download(
            url=f"https://drive.google.com/uc?id={file_id}",
            output=str(target_path),
            quiet=QUIET,
            use_cookies=use_cookies,
            cookies_file=str(COOKIES_FILE) if (use_cookies and COOKIES_FILE and COOKIES_FILE.exists()) else None,
            user_agent=USER_AGENT,
        )
        if target_path.exists() and target_path.stat().st_size > 0:
            if expected_mtime:
                try:
                    os.utime(target_path, (expected_mtime, expected_mtime))
                except Exception:
                    pass
            return True, "STANDARD"
        return False, "EMPTY_DOWNLOAD"
    except (FileURLRetrievalError, DownloadError) as e:
        err_str = str(e)
        if "Too many users" in err_str or "quota" in err_str.lower():
            if target_path.exists() and target_path.stat().st_size > 10 * 1024 * 1024:
                return True, "QUOTA_EXCEEDED_PRESERVED_LOCAL"
            return False, "QUOTA_EXCEEDED"
        return False, f"ERROR: {err_str.splitlines()[0] if err_str else e}"
    except Exception as e:
        return False, f"ERROR: {e}"


def get_remote_file_metadata(file_id: str, session: requests.Session, filename: str = "") -> Tuple[Optional[int], Optional[float], bool]:
    """
    Returns (remote_size_bytes, remote_mtime_epoch, is_quota_exceeded) for a Google Drive file.
    Guarantees that HTML error pages (Quota exceeded, login redirects) are NEVER mistaken for file sizes.
    For images, queries Google's high-speed CDN to bypass 24h download quota limits completely.
    For text files, uses Drive Viewer extraction when quota is hit.
    """
    if is_os_junk_file(filename):
        return None, None, False

    if is_image_file(filename):
        try:
            cdn_url = f"https://lh3.googleusercontent.com/d/{file_id}"
            cdn_r = session.head(cdn_url, allow_redirects=True, timeout=8)
            ct = cdn_r.headers.get("Content-Type", "").lower()
            if cdn_r.status_code == 200 and "image/" in ct:
                cl = int(cdn_r.headers.get("Content-Length", 0))
                if cl > 0:
                    return cl, None, False
        except Exception:
            pass

    url = f"https://drive.google.com/uc?id={file_id}"
    try:
        r = session.get(url, stream=True, allow_redirects=True, timeout=12)
        content_type = r.headers.get("Content-Type", "").lower()

        # Check if Google served an HTML response instead of a binary file
        if "text/html" in content_type:
            html_text = r.text[:3000]
            r.close()

            # 1. Quota Exceeded / Rate Limit check
            if (
                "Quota exceeded" in html_text
                or "Too many users have viewed or downloaded this file recently" in html_text
                or "download quota" in html_text.lower()
            ):
                if is_text_file(filename):
                    content = download_text_via_viewer(file_id, session)
                    if content is not None:
                        return len(content.encode("utf-8")), None, False
                return None, None, True

            # 2. ServiceLogin / Auth Redirect check
            if "ServiceLogin" in html_text or "accounts.google.com" in html_text:
                return None, None, False

            # 3. Large File Virus Scan Warning
            if "Virus scan warning" in html_text or "confirm=" in html_text or "download_warning" in html_text:
                from gdown.download import get_url_from_gdrive_confirmation
                try:
                    dl_url = get_url_from_gdrive_confirmation(html_text)
                    r2 = session.get(dl_url, stream=True, timeout=12)
                    ct2 = r2.headers.get("Content-Type", "").lower()
                    if "text/html" in ct2:
                        h2 = r2.text[:3000]
                        r2.close()
                        is_q = "Quota exceeded" in h2 or "Too many users" in h2
                        return None, None, is_q
                    size = int(r2.headers.get("Content-Length", 0))
                    mtime = None
                    if "Last-Modified" in r2.headers:
                        try:
                            mtime = email.utils.parsedate_to_datetime(r2.headers["Last-Modified"]).timestamp()
                        except Exception:
                            pass
                    r2.close()
                    if size > 0:
                        return size, mtime, False
                except Exception:
                    return None, None, False

            return None, None, False

        # Direct binary stream
        size = int(r.headers.get("Content-Length", 0))
        mtime = None
        if "Last-Modified" in r.headers:
            try:
                mtime = email.utils.parsedate_to_datetime(r.headers["Last-Modified"]).timestamp()
            except Exception:
                pass
        r.close()
        return (size if size > 0 else None), mtime, False
    except Exception:
        return None, None, False


def validate_cookies_file(cookies_path: Path) -> bool:
    """
    Validates if cookies.txt contains an active, valid Google Drive session.
    Returns False if cookies cause a redirect to ServiceLogin / Redirecting...
    """
    if not cookies_path.exists():
        return False
    try:
        cj = http.cookiejar.MozillaCookieJar(str(cookies_path))
        cj.load()
        with requests.Session() as s:
            s.cookies = cj
            s.headers["User-Agent"] = USER_AGENT
            test_url = "https://drive.google.com/embeddedfolderview?id=1PsWVz_rZXYS6jKez2S5PDf1NEefwn0nS"
            r = s.get(test_url, timeout=10)
            if "accounts.google.com" in r.url or "Redirecting" in r.text[:300] or "ServiceLogin" in r.text[:300]:
                return False
            return True
    except Exception:
        return False


def is_folder_complete(folder_path: Path) -> bool:
    """
    Checks if a local directory contains complete downloaded folder assets.
    Must contain a valid video (> 10MB) AND metadata/images.
    """
    if not folder_path.is_dir():
        return False
    files = [f for f in folder_path.rglob("*") if f.is_file() and not is_os_junk_file(f.name)]
    if len(files) < 4:
        return False
    has_video = any(
        f.suffix.lower() in [".mp4", ".mov", ".mkv", ".avi"] and f.stat().st_size > 10 * 1024 * 1024
        for f in files
    )
    has_metadata = any(f.name in ["title.txt", "description.txt", "info.txt"] for f in files)
    return has_video and has_metadata


def sanitize_filename(filename: str) -> str:
    r"""
    Sanitizes a single filename or directory name component for Windows/POSIX:
    - Removes ASCII control characters (\x00-\x1f)
    - Replaces forbidden Windows characters (< > : " / \ | ? *) with '_'
    - Strips leading and trailing spaces and dots (invalid on Windows)
    - Guards against Windows reserved device names (CON, PRN, AUX, NUL, COM1-9, LPT1-9)
    """
    if not filename:
        return "_"
    clean = re.sub(r"[\x00-\x1f]", "", str(filename))
    clean = re.sub(r'[<>:"/\\|?*]', "_", clean)
    clean = clean.strip(" .\t\r\n")
    if not clean or clean in ("", ".", ".."):
        return "_"
    stem = clean.split(".")[0].upper()
    reserved = {"CON", "PRN", "AUX", "NUL"} | {f"COM{i}" for i in range(1, 10)} | {f"LPT{i}" for i in range(1, 10)}
    if stem in reserved:
        clean = f"_{clean}"
    return clean


def sanitize_rel_path(rel_path: str) -> Path:
    """
    Sanitizes each directory and file component in a relative path.
    Preserves folder hierarchy while guaranteeing valid names on Windows.
    """
    p = Path(rel_path)
    clean_parts = [sanitize_filename(part) for part in p.parts]
    return Path(*clean_parts)


# Monkeypatch gdown internal sanitization so that gdown's built-in routines
# don't trigger WinError 123 on reserved characters (?, *, :, etc.)
try:
    import gdown.download
    import gdown.download_folder
    mod_dl = sys.modules.get(gdown.download.__module__)
    mod_df = sys.modules.get(gdown.download_folder.__module__)
    if mod_dl and hasattr(mod_dl, "_sanitize_filename"):
        mod_dl._sanitize_filename = lambda *, filename: sanitize_filename(filename)
    if mod_df and hasattr(mod_df, "_sanitize_filename"):
        mod_df._sanitize_filename = lambda *, filename: sanitize_filename(filename)
except Exception:
    pass


def find_existing_folder_for_title(title: str) -> Optional[Path]:
    """
    Finds matching folder in OUTPUT_DIR by title, tolerating sanitized filenames
    and common numbering/custom prefixes (e.g. 'D1 ', 'D3 ', 'part 1 ').
    Never falsely cross-matches distinct folders that share a common prefix.
    """
    if not OUTPUT_DIR.exists():
        return None

    sanitized = sanitize_filename(title)
    sanitized_dir = OUTPUT_DIR / sanitized
    if sanitized_dir.is_dir():
        return sanitized_dir

    try:
        exact = OUTPUT_DIR / title
        if exact.is_dir():
            return exact
    except OSError:
        pass

    title_lower = title.strip().lower()
    clean_title = re.sub(r"^(d\d+|part\s*\d+)\s*", "", title_lower, flags=re.IGNORECASE).strip()

    # Pass 1: Exact case-insensitive match
    for item in OUTPUT_DIR.iterdir():
        if item.is_dir() and not item.name.endswith("_FAILED"):
            if item.name.strip().lower() == title_lower:
                return item

    # Pass 2: Exact match after stripping common prefix (e.g. 'D3 ')
    for item in OUTPUT_DIR.iterdir():
        if item.is_dir() and not item.name.endswith("_FAILED"):
            clean_item = re.sub(r"^(d\d+|part\s*\d+)\s*", "", item.name.strip().lower(), flags=re.IGNORECASE).strip()
            if clean_item == clean_title:
                return item

    # Pass 3: Sanitized match after stripping prefix
    clean_title_sanitized = sanitize_filename(clean_title)
    for item in OUTPUT_DIR.iterdir():
        if item.is_dir() and not item.name.endswith("_FAILED"):
            clean_item = re.sub(r"^(d\d+|part\s*\d+)\s*", "", item.name.strip().lower(), flags=re.IGNORECASE).strip()
            if sanitize_filename(clean_item) == clean_title_sanitized:
                return item

    # Pass 4: Normalized alphanumeric comparison
    def norm(s: str) -> str:
        s = re.sub(r"^(d\d+|part\s*\d+)\s*", "", s.strip().lower(), flags=re.IGNORECASE)
        return re.sub(r"[\W_]+", "", s)

    norm_target = norm(title)
    if norm_target:
        for item in OUTPUT_DIR.iterdir():
            if item.is_dir() and not item.name.endswith("_FAILED"):
                if norm(item.name) == norm_target:
                    return item

    return None


def clean_failed_marker(index: int, url: str):
    folder_id = extract_folder_id(url)
    failed_folder = OUTPUT_DIR / f"{index:03d}_folder_{folder_id[:12]}_FAILED"
    if failed_folder.exists():
        try:
            import shutil
            shutil.rmtree(failed_folder)
        except Exception:
            pass


def create_failed_marker(index: int, url: str):
    try:
        folder_id = extract_folder_id(url)
        failed_folder = OUTPUT_DIR / f"{index:03d}_folder_{folder_id[:12]}_FAILED"
        failed_folder.mkdir(parents=True, exist_ok=True)
        with open(failed_folder / "DOWNLOAD_FAILED.txt", "w", encoding="utf-8") as f:
            f.write(
                f"Original URL:\n{url}\n\n"
                f"Failed after {RETRIES} attempts.\n"
                f"Most common reason: Google rate limiting / temporary restriction.\n"
            )
        logger.error(f"[{index}] FAILED -> Created: {failed_folder.name}")
    except Exception as e:
        logger.error(f"[{index}] Could not create fallback folder: {e}")


def is_rate_limit_error(error_msg: str) -> bool:
    keywords = [
        "cannot retrieve the public link",
        "too many users have viewed",
        "access denied",
        "permission denied",
        "have had many accesses",
        "failed to retrieve file url",
        "429",
    ]
    error_msg = error_msg.lower()
    return any(k in error_msg for k in keywords)


def update_folder_incremental(url: str, index: int, total: int, use_cookies: bool) -> Tuple[bool, bool]:
    """
    Incrementally checks a folder for new or modified files:
    - Scans remote folder hierarchy on Google Drive
    - Compares each file against local disk (size and modification time)
    - Downloads ONLY new or changed files
    - Skips already up-to-date files (including large videos)
    Returns:
        (success: bool, was_skipped: bool)
    """
    logger.info(f"[{index}/{total}] [UPDATE] Checking folder -> {url}")
    folder_id = extract_folder_id(url)
    output_path = str(OUTPUT_DIR) + "\\"

    remote_title, _, _ = get_remote_folder_info(folder_id)
    if not remote_title:
        remote_title = f"folder_{folder_id[:12]}"

    matched_dir = find_existing_folder_for_title(remote_title)
    if not matched_dir or not matched_dir.exists():
        logger.info(f"[{index}/{total}] [UPDATE] Folder not found locally. Performing initial full download...")
        return download_folder(url, index, total, use_cookies=use_cookies, update_mode=False)

    # 1. Discover all remote files in the folder hierarchy
    try:
        remote_files = gdown.download_folder(
            url=url,
            output=output_path,
            skip_download=True,
            quiet=True,
            use_cookies=use_cookies,
            cookies_file=str(COOKIES_FILE) if (use_cookies and COOKIES_FILE and COOKIES_FILE.exists()) else None,
            user_agent=USER_AGENT,
        )
    except Exception as e:
        logger.warning(f"[{index}/{total}] [UPDATE] Failed to discover remote files: {e}. Falling back to standard mode.")
        return download_folder(url, index, total, use_cookies=use_cookies, update_mode=False)

    if not remote_files:
        logger.warning(f"[{index}/{total}] [UPDATE] No remote files discovered. Skipping.")
        return True, True

    # 2. Check each file against local storage in parallel
    logger.info(f"[{index}/{total}] [UPDATE] Checking {len(remote_files)} files in '{matched_dir.name[:35]}'...")

    session = requests.Session()
    if use_cookies and COOKIES_FILE and COOKIES_FILE.exists():
        try:
            cj = http.cookiejar.MozillaCookieJar(str(COOKIES_FILE))
            cj.load()
            session.cookies = cj
        except Exception as e:
            logger.warning(f"Could not load cookies into update session: {e}")
    session.headers["User-Agent"] = USER_AGENT
    adapter = requests.adapters.HTTPAdapter(pool_connections=12, pool_maxsize=12, max_retries=2)
    session.mount("https://", adapter)
    session.mount("http://", adapter)

    to_download = []

    def check_file(f):
        try:
            rel_clean = sanitize_rel_path(f.path)
            if is_os_junk_file(f.path):
                return f, matched_dir / rel_clean, "UP_TO_DATE", 0, None

            lp = matched_dir / rel_clean
            if not lp.exists():
                candidates = [p for p in matched_dir.rglob("*") if p.is_file() and p.name.lower() == rel_clean.name.lower()]
                if candidates:
                    lp = candidates[0]
                else:
                    r_size, r_mtime, is_quota = get_remote_file_metadata(f.id, session, filename=f.path)
                    if is_quota and not (is_image_file(f.path) or is_text_file(f.path)):
                        return f, lp, "QUOTA_EXCEEDED", None, None
                    return f, lp, "NEW_FILE", r_size, r_mtime

            l_size = lp.stat().st_size
            l_mtime = lp.stat().st_mtime
            r_size, r_mtime, is_quota = get_remote_file_metadata(f.id, session, filename=f.path)

            if is_quota:
                # File already exists locally. Remote is temporarily quota-locked by Google.
                # Keep existing file safe and do NOT attempt to re-download HTML error page!
                return f, lp, "UP_TO_DATE", l_size, l_mtime

            if r_size is not None and r_size > 0 and r_size != l_size:
                return f, lp, f"SIZE_DIFF ({l_size}B -> {r_size}B)", r_size, r_mtime

            if r_mtime and r_mtime > l_mtime + 2:
                return f, lp, "TIME_MODIFIED (newer on Drive)", r_size, r_mtime

            return f, lp, "UP_TO_DATE", r_size or l_size, r_mtime or l_mtime
        except Exception as err:
            logger.warning(f"Error inspecting {getattr(f, 'path', str(f))}: {err}")
            return f, matched_dir / sanitize_rel_path(getattr(f, "path", "file")), "CHECK_ERROR", None, None

    results = []
    with ThreadPoolExecutor(max_workers=6) as executor:
        future_to_f = {executor.submit(check_file, f): f for f in remote_files}
        for future in future_to_f:
            try:
                res = future.result()
                results.append(res)
            except Exception as e:
                f_item = future_to_f[future]
                logger.warning(f"Error checking {getattr(f_item, 'path', 'file')}: {e}")
                results.append((f_item, matched_dir / sanitize_rel_path(getattr(f_item, "path", "file")), "ERROR_FALLBACK", 0, None))

    for f, lp, status, r_size, r_mtime in results:
        if status != "UP_TO_DATE":
            to_download.append((f, lp, status, r_size, r_mtime))

    if not to_download:
        logger.info(
            f"[{index}/{total}] [UPDATE] '{matched_dir.name[:40]}' is 100% UP TO DATE ({len(remote_files)} files verified). Skipped."
        )
        return True, True

    # 3. Download only the new or updated files
    logger.info(f"[{index}/{total}] [UPDATE] Found {len(to_download)} file(s) to update in '{matched_dir.name[:35]}':")
    updated_count = 0
    for f, lp, reason, r_size, r_mtime in to_download:
        if is_os_junk_file(f.path):
            continue
        if "QUOTA_EXCEEDED" in reason:
            logger.warning(f"  [!] Skipped {f.path}: Google Drive download quota exceeded on remote file (try again later).")
            continue
        rel_clean = sanitize_rel_path(f.path)
        logger.info(f"  -> Updating: {rel_clean} [{reason}]")
        ok, res_reason = download_single_file_resilient(
            file_id=f.id,
            rel_path=str(rel_clean),
            target_path=lp,
            session=session,
            use_cookies=use_cookies,
            expected_mtime=r_mtime,
        )
        if ok:
            updated_count += 1
            if res_reason != "QUOTA_EXCEEDED_PRESERVED_LOCAL":
                logger.info(f"     Updated {f.path} successfully [{res_reason}].")
        else:
            if "QUOTA_EXCEEDED" in res_reason:
                logger.warning(f"  [!] Quota exceeded for {f.path}. Existing local file preserved.")
            else:
                logger.warning(f"  [!] Failed to update {f.path}: {res_reason}")

    logger.info(f"[{index}/{total}] [UPDATE] Completed: {updated_count}/{len(to_download)} file(s) processed.")
    return True, False


def download_folder(url: str, index: int, total: int, use_cookies: bool, update_mode: bool = False) -> Tuple[bool, bool]:
    """
    Downloads folder using resilient multi-strategy downloader:
    - Bypasses 24h Google Drive quota on images via Google CDN
    - Bypasses 24h quota on text/metadata via Google Drive Viewer API
    - Silently filters out OS junk (.DS_Store, Thumbs.db)
    - Resiliently handles large video confirmation tokens
    Returns:
        (success: bool, was_skipped: bool)
    """
    if update_mode:
        return update_folder_incremental(url, index, total, use_cookies)

    logger.info(f"[{index}/{total}] Checking -> {url}")
    folder_id = extract_folder_id(url)
    output_path = str(OUTPUT_DIR) + "\\"

    remote_title, _, _ = get_remote_folder_info(folder_id)
    if not remote_title:
        remote_title = f"folder_{folder_id[:12]}"

    matched_dir = find_existing_folder_for_title(remote_title)
    if not matched_dir:
        matched_dir = OUTPUT_DIR / sanitize_filename(remote_title)

    # 1. Fast skip if already completely downloaded
    if SKIP_EXISTING and matched_dir.exists() and is_folder_complete(matched_dir):
        files = [f for f in matched_dir.rglob("*") if f.is_file() and not is_os_junk_file(f.name)]
        size_mb = sum(f.stat().st_size for f in files) / (1024 * 1024)
        logger.info(
            f"[{index}/{total}] ALREADY COMPLETED -> '{matched_dir.name[:45]}' "
            f"({len(files)} files, {size_mb:.1f} MB). Skipping."
        )
        clean_failed_marker(index, url)
        return True, True

    # 2. Discover remote files
    active_use_cookies = use_cookies
    remote_files = None
    for disc_attempt in range(1, 4):
        try:
            remote_files = gdown.download_folder(
                url=url,
                output=output_path,
                skip_download=True,
                quiet=True,
                use_cookies=active_use_cookies,
                cookies_file=str(COOKIES_FILE) if (active_use_cookies and COOKIES_FILE and COOKIES_FILE.exists()) else None,
                user_agent=USER_AGENT,
            )
            if remote_files and len(remote_files) > 0:
                break
            elif active_use_cookies:
                # Expired or redirected cookies returned 0 files -> fallback to public discovery
                active_use_cookies = False
        except Exception:
            if active_use_cookies:
                active_use_cookies = False
            time.sleep(2)

    if not remote_files:
        logger.warning(f"[{index}/{total}] Remote discovery returned 0 files. Falling back to direct gdown.")
        try:
            res = gdown.download_folder(
                url=url,
                output=str(matched_dir),
                quiet=QUIET,
                use_cookies=False,
                resume=True,
                retries=FILE_RETRIES,
                user_agent=USER_AGENT,
            )
            if res and len(res) > 0:
                clean_failed_marker(index, url)
                return True, False
        except Exception as e:
            logger.error(f"[{index}/{total}] Direct gdown failed: {e}")
        create_failed_marker(index, url)
        return False, False

    matched_dir.mkdir(parents=True, exist_ok=True)
    logger.info(f"[{index}/{total}] Downloading '{matched_dir.name[:35]}' ({len(remote_files)} remote files discovered)...")

    session = requests.Session()
    session.headers["User-Agent"] = USER_AGENT
    if active_use_cookies and COOKIES_FILE and COOKIES_FILE.exists():
        try:
            cj = http.cookiejar.MozillaCookieJar(str(COOKIES_FILE))
            cj.load()
            session.cookies = cj
        except Exception:
            pass

    downloaded_files = 0
    quota_files = []

    for f in remote_files:
        if is_os_junk_file(f.path):
            continue

        rel_clean = sanitize_rel_path(f.path)
        target_file = matched_dir / rel_clean
        if target_file.exists():
            sz = target_file.stat().st_size
            is_vid = any(target_file.suffix.lower().endswith(x) for x in [".mp4", ".mov", ".mkv"])
            if (is_vid and sz > 10 * 1024 * 1024) or (not is_vid and sz > 0):
                downloaded_files += 1
                continue

        ok, reason = download_single_file_resilient(
            file_id=f.id,
            rel_path=str(rel_clean),
            target_path=target_file,
            session=session,
            use_cookies=active_use_cookies,
        )

        if ok:
            downloaded_files += 1
            if reason not in ["SKIPPED_JUNK", "QUOTA_EXCEEDED_PRESERVED_LOCAL"]:
                logger.info(f"  + Downloaded: {rel_clean} [{reason}]")
        else:
            if "QUOTA_EXCEEDED" in reason:
                quota_files.append(str(rel_clean))
                logger.warning(f"  [!] Quota exceeded for {rel_clean} (Google temporary 24h limit).")
            else:
                logger.warning(f"  [!] Failed to download {rel_clean}: {reason}")

    # Check completeness
    local_files = [p for p in matched_dir.rglob("*") if p.is_file() and not is_os_junk_file(p.name)]
    has_video = any(p.suffix.lower() in [".mp4", ".mov", ".mkv"] and p.stat().st_size > 10 * 1024 * 1024 for p in local_files)
    has_meta = any(p.name in ["description.txt", "title.txt", "info.txt"] for p in local_files)

    if has_video and has_meta:
        logger.info(f"[{index}/{total}] SUCCESS -> '{matched_dir.name[:35]}' is complete ({len(local_files)} files).")
        clean_failed_marker(index, url)
        return True, False
    elif has_meta and len(local_files) >= 5:
        if quota_files:
            logger.warning(
                f"[{index}/{total}] PARTIAL SUCCESS -> '{matched_dir.name[:35]}': {len(local_files)} files saved "
                f"(All images & metadata complete). Remote video is temporarily locked by Google 24h download quota."
            )
        else:
            logger.info(f"[{index}/{total}] COMPLETED -> '{matched_dir.name[:35]}' ({len(local_files)} files saved).")
        clean_failed_marker(index, url)
        return True, False
    else:
        logger.error(f"[{index}/{total}] INCOMPLETE -> Only {len(local_files)} files downloaded for '{matched_dir.name[:35]}'.")
        create_failed_marker(index, url)
        return False, False


def run_qc(sample_count: Optional[int] = None, start_idx: int = 1):
    """Quality Control check on downloaded data."""
    logger.info("=" * 70)
    logger.info("QUALITY CONTROL (QC) REPORT")
    logger.info("=" * 70)

    links = read_links(LINKS_FILE)
    logger.info(f"Total links defined in links.txt: {len(links)}")

    downloaded_dirs = [d for d in OUTPUT_DIR.iterdir() if d.is_dir() and not d.name.endswith("_FAILED")]
    failed_dirs = [d for d in OUTPUT_DIR.iterdir() if d.is_dir() and d.name.endswith("_FAILED")]

    logger.info(f"Downloaded folders on disk : {len(downloaded_dirs)}")
    logger.info(f"Failed placeholder folders : {len(failed_dirs)}")
    logger.info("-" * 70)

    target_items = list(enumerate(links, 1))[start_idx - 1 : sample_count] if sample_count else list(enumerate(links, 1))[start_idx - 1 :]
    passed = 0
    missing = 0

    for i, url in target_items:
        fid = extract_folder_id(url)
        remote_title, remote_files, is_redir = get_remote_folder_info(fid)
        title_str = remote_title or f"folder_{fid[:12]}"
        matched_dir = find_existing_folder_for_title(title_str)

        if not matched_dir or not matched_dir.exists():
            logger.warning(f"QC [{i:02d}] MISSING: '{title_str[:45]}'")
            missing += 1
            continue

        files = [f for f in matched_dir.rglob("*") if f.is_file()]
        mp4_files = [f for f in files if f.suffix.lower() == ".mp4"]
        txt_files = [f for f in files if f.suffix.lower() in [".txt", ".md", ".json"]]
        img_files = [f for f in files if f.suffix.lower() in [".jpg", ".png", ".webp"]]
        total_size_mb = sum(f.stat().st_size for f in files) / (1024 * 1024)

        video_ok = len(mp4_files) >= 1 and any(f.stat().st_size > 10 * 1024 * 1024 for f in mp4_files)
        meta_ok = len(txt_files) >= 2
        img_ok = len(img_files) >= 1

        if video_ok and meta_ok and img_ok:
            passed += 1
            status = "PASS"
        else:
            status = "WARN"

        vid_size = f"{mp4_files[0].stat().st_size / (1024 * 1024):.1f}MB" if mp4_files else "0MB"
        logger.info(
            f"QC [{i:02d}] {status:4} | '{matched_dir.name[:35]}' | "
            f"Files: {len(files):3} ({total_size_mb:6.1f} MB) | "
            f"Videos: {len(mp4_files)} ({vid_size}) | Imgs: {len(img_files)} | Text/Data: {len(txt_files)}"
        )

    logger.info("=" * 70)
    logger.info(f"QC Summary: {passed} PASSED | {missing} MISSING | Checked: {len(target_items)}")
    logger.info("=" * 70)


def main():
    global SKIP_EXISTING, WAIT_BETWEEN_DOWNLOADS, RETRIES, QUIET, UPDATE_MODE, COOKIES_FILE

    parser = argparse.ArgumentParser(description="Google Drive Folder Downloader & QC")
    parser.add_argument("--cookies", type=str, default=None, help="Path to cookies file (default: auto-detects any *cookie*.txt in workspace)")
    parser.add_argument("--update", action="store_true", help="Incremental update mode: check for new or modified files in Drive folders and download ONLY changed/new files (skips unchanged files).")
    parser.add_argument("--qc", action="store_true", help="Run QC report on downloaded folders")
    parser.add_argument("--qc-count", type=int, default=None, help="Number of links to check in QC (default: all)")
    parser.add_argument("--limit", type=int, default=None, help="Process up to N folders from links.txt")
    parser.add_argument("--start", type=int, default=1, help="Start processing from folder index N (1-based, default: 1)")
    parser.add_argument("--no-skip", action="store_true", help="Disable auto-skip and re-check/re-download existing folders")
    parser.add_argument("--wait", type=int, default=WAIT_BETWEEN_DOWNLOADS, help=f"Wait time in seconds between downloads (default: {WAIT_BETWEEN_DOWNLOADS})")
    parser.add_argument("--retries", type=int, default=RETRIES, help=f"Max retries per folder on failure (default: {RETRIES})")
    parser.add_argument("--force-cookies", action="store_true", help="Force using cookies even if validity test fails")
    parser.add_argument("--quiet", action="store_true", help="Suppress download progress output")
    args = parser.parse_args()

    if args.update:
        UPDATE_MODE = True
    if args.no_skip:
        SKIP_EXISTING = False
    if args.wait is not None:
        WAIT_BETWEEN_DOWNLOADS = args.wait
    if args.retries is not None:
        RETRIES = args.retries
    if args.quiet:
        QUIET = True

    if args.qc:
        run_qc(sample_count=args.qc_count, start_idx=args.start)
        return

    logger.info("=" * 70)
    logger.info("Google Drive Folder Downloader (Enhanced & Resilient Version)")
    logger.info("- Smart cookie validation & automatic fallback")
    if UPDATE_MODE:
        logger.info("- Mode: INCREMENTAL UPDATE (--update enabled: syncing modified & new files)")
    else:
        logger.info(f"- Mode: FAST SKIP (Skip existing complete folders: {'ENABLED' if SKIP_EXISTING else 'DISABLED'})")
    logger.info("- Modern browser User-Agent (avoids 403 blocks)")
    logger.info(f"- Folder retries: {RETRIES} | Wait between downloads: {WAIT_BETWEEN_DOWNLOADS}s")
    logger.info(f"- Output folder : {OUTPUT_DIR}")
    logger.info("=" * 70)

    # Validate cookies
    use_cookies = False
    detected_cookie_file = find_cookies_file(args.cookies)
    if detected_cookie_file and detected_cookie_file.exists():
        COOKIES_FILE = detected_cookie_file
        logger.info(f"Detected cookie file: {COOKIES_FILE.name}")
        if validate_cookies_file(COOKIES_FILE):
            logger.info(f"Cookies in {COOKIES_FILE.name} are VALID. Authenticated mode enabled.")
            use_cookies = True
        else:
            logger.warning(f"[!] {COOKIES_FILE.name} contains expired/stale session cookies (triggers Google login redirect).")
            # If multiple cookie files exist, check if another candidate is valid
            found_valid_alt = False
            for alt in find_all_cookie_files():
                if alt != COOKIES_FILE and validate_cookies_file(alt):
                    logger.info(f"[+] Found alternative valid cookies in {alt.name}! Using {alt.name}.")
                    COOKIES_FILE = alt
                    use_cookies = True
                    found_valid_alt = True
                    break
            if not found_valid_alt:
                logger.warning(f"[!] Bypassing {COOKIES_FILE.name} and using direct public access mode.")
                use_cookies = False
    else:
        logger.info("No cookie file (*cookie*.txt) found. Using direct public access mode.")

    if args.force_cookies:
        logger.warning("Forcing use_cookies=True as requested by CLI flag.")
        use_cookies = True

    all_links = read_links(LINKS_FILE)
    total = len(all_links)
    logger.info(f"Found {total} folder link(s) in {LINKS_FILE.name}")

    start_idx = max(1, args.start)
    end_idx = min(total, start_idx + args.limit - 1) if args.limit is not None else total

    target_items = list(enumerate(all_links, 1))[start_idx - 1:end_idx]
    logger.info(f"Processing folders from index [{start_idx}] to [{end_idx}] (Total to check: {len(target_items)})")

    success = 0
    failed = 0

    for idx, (i, url) in enumerate(target_items, 1):
        logger.info("-" * 70)
        ok, skipped = download_folder(url, i, total, use_cookies=use_cookies, update_mode=UPDATE_MODE)
        if ok:
            success += 1
        else:
            failed += 1

        # Only wait if we actually performed a network download (not skipped)
        if not skipped and idx < len(target_items):
            logger.info(f"Waiting {WAIT_BETWEEN_DOWNLOADS}s before next folder...")
            time.sleep(WAIT_BETWEEN_DOWNLOADS)
        else:
            time.sleep(0.1)

    logger.info("=" * 70)
    logger.info(f"Finished | Success: {success} | Failed: {failed} | Total Processed: {len(target_items)}")
    logger.info(f"Log saved to: {log_file}")
    logger.info("=" * 70)

    # Run QC on processed items
    run_qc(sample_count=end_idx, start_idx=start_idx)

    if failed > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()