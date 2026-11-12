import os
import sys
import json
import hashlib
import hmac
import secrets
import sqlite3
import shutil
import zipfile
import re
import stat
import getpass
import math
from datetime import datetime, timezone
from pathlib import Path
from contextlib import contextmanager
import defusedxml.ElementTree as DET
from xml.etree import ElementTree as ET


DB_PATH = os.environ.get("FM_DB", os.path.join(os.path.dirname(os.path.abspath(__file__)), "fm.db"))
STORAGE_ROOT = os.environ.get("FM_ROOT", os.path.join(os.path.dirname(os.path.abspath(__file__)), "storage"))
MAX_XML_BYTES = 2 * 1024 * 1024
MAX_JSON_BYTES = 4 * 1024 * 1024
ZIP_MAX_FILE_SIZE = 100 * 1024 * 1024
ZIP_MAX_TOTAL_SIZE = 500 * 1024 * 1024
ZIP_MAX_FILES = 1000
ZIP_MAX_RATIO = 50.0
SCRYPT_N = 2 ** 14
SCRYPT_R = 8
SCRYPT_P = 1
SAFE_NAME_RE = re.compile(r"^[A-Za-z0-9_.\-]{1,128}$")


class AppError(Exception):
    pass


class AuthError(AppError):
    pass


class ValidationError(AppError):
    pass


def utcnow():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def ensure_dir(path):
    os.makedirs(path, exist_ok=True)


def safe_join(root, name):
    if not isinstance(name, str) or not SAFE_NAME_RE.match(name):
        raise ValidationError("Недопустимое имя файла")
    if name in (".", ".."):
        raise ValidationError("Недопустимое имя файла")
    root_real = os.path.realpath(root)
    target = os.path.realpath(os.path.join(root_real, name))
    if not (target == root_real or target.startswith(root_real + os.sep)):
        raise ValidationError("Выход за пределы каталога запрещён")
    return target


def read_limited(path, limit):
    st = os.stat(path, follow_symlinks=False)
    if not stat.S_ISREG(st.st_mode):
        raise ValidationError("Ожидался обычный файл")
    if st.st_size > limit:
        raise ValidationError("Файл превышает допустимый размер")
    with open(path, "rb") as f:
        data = f.read(limit + 1)
    if len(data) > limit:
        raise ValidationError("Файл превышает допустимый размер")
    return data


class Database:
    def __init__(self, path):
        self.path = path
        self._init()

    def _connect(self):
        conn = sqlite3.connect(self.path, timeout=10, isolation_level=None)
        conn.execute("PRAGMA foreign_keys=ON")
        conn.execute("PRAGMA journal_mode=WAL")
        conn.row_factory = sqlite3.Row
        return conn

    @contextmanager
    def transaction(self, immediate=False):
        conn = self._connect()
        try:
            conn.execute("BEGIN IMMEDIATE" if immediate else "BEGIN")
            yield conn
            conn.execute("COMMIT")
        except Exception:
            try:
                conn.execute("ROLLBACK")
            except Exception:
                pass
            raise
        finally:
            conn.close()

    def _init(self):
        ensure_dir(os.path.dirname(self.path) or ".")
        with self.transaction(immediate=True) as c:
            c.execute("""
                CREATE TABLE IF NOT EXISTS Users (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    username TEXT NOT NULL UNIQUE,
                    password_hash TEXT NOT NULL
                )
            """)
            c.execute("""
                CREATE TABLE IF NOT EXISTS Files (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    filename TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    size INTEGER NOT NULL,
                    location TEXT NOT NULL,
                    owner_id INTEGER NOT NULL REFERENCES Users(id)
                )
            """)
            c.execute("""
                CREATE TABLE IF NOT EXISTS Operations (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    timestamp TEXT NOT NULL,
                    operation_type TEXT NOT NULL CHECK (operation_type IN ('create','modify','delete','login','logout','register','zip_create','zip_extract','json_write','json_read','xml_write','xml_read')),
                    file_id INTEGER REFERENCES Files(id) ON DELETE SET NULL,
                    user_id INTEGER NOT NULL REFERENCES Users(id),
                    details TEXT
                )
            """)

    def create_user(self, username, password_hash):
        with self.transaction(immediate=True) as c:
            cur = c.execute(
                "INSERT INTO Users (username, password_hash) VALUES (?, ?)",
                (username, password_hash),
            )
            return cur.lastrowid

    def get_user(self, username):
        conn = self._connect()
        try:
            row = conn.execute(
                "SELECT id, username, password_hash FROM Users WHERE username = ?",
                (username,),
            ).fetchone()
            return dict(row) if row else None
        finally:
            conn.close()

    def register_file(self, filename, size, location, owner_id):
        with self.transaction(immediate=True) as c:
            cur = c.execute(
                "INSERT INTO Files (filename, created_at, size, location, owner_id) VALUES (?, ?, ?, ?, ?)",
                (filename, utcnow(), size, location, owner_id),
            )
            return cur.lastrowid

    def update_file_size(self, file_id, new_size):
        with self.transaction(immediate=True) as c:
            c.execute("UPDATE Files SET size = ? WHERE id = ?", (new_size, file_id))

    def delete_file_record(self, file_id):
        with self.transaction(immediate=True) as c:
            c.execute("DELETE FROM Files WHERE id = ?", (file_id,))

    def find_file(self, location, owner_id):
        conn = self._connect()
        try:
            row = conn.execute(
                "SELECT id, filename, size, location FROM Files WHERE location = ? AND owner_id = ?",
                (location, owner_id),
            ).fetchone()
            return dict(row) if row else None
        finally:
            conn.close()

    def log_operation(self, operation_type, user_id, file_id=None, details=None):
        with self.transaction(immediate=True) as c:
            c.execute(
                "INSERT INTO Operations (timestamp, operation_type, file_id, user_id, details) VALUES (?, ?, ?, ?, ?)",
                (utcnow(), operation_type, file_id, user_id, details),
            )

    def list_operations(self, user_id, limit=50):
        conn = self._connect()
        try:
            rows = conn.execute(
                "SELECT timestamp, operation_type, file_id, details FROM Operations WHERE user_id = ? ORDER BY id DESC LIMIT ?",
                (user_id, limit),
            ).fetchall()
            return [dict(r) for r in rows]
        finally:
            conn.close()


class AuthService:
    def __init__(self, db):
        self.db = db

    @staticmethod
    def hash_password(password):
        salt = secrets.token_bytes(16)
        derived = hashlib.scrypt(
            password.encode("utf-8"),
            salt=salt,
            n=SCRYPT_N,
            r=SCRYPT_R,
            p=SCRYPT_P,
            dklen=32,
        )
        return "scrypt${}${}${}${}".format(
            SCRYPT_N, SCRYPT_R, SCRYPT_P, salt.hex() + "$" + derived.hex()
        )

    @staticmethod
    def verify_password(password, stored):
        try:
            scheme, n, r, p, rest = stored.split("$", 4)
            if scheme != "scrypt":
                return False
            salt_hex, hash_hex = rest.split("$", 1)
            derived = hashlib.scrypt(
                password.encode("utf-8"),
                salt=bytes.fromhex(salt_hex),
                n=int(n),
                r=int(r),
                p=int(p),
                dklen=32,
            )
            return hmac.compare_digest(derived.hex(), hash_hex)
        except Exception:
            return False

    def register(self, username, password):
        if self.db.get_user(username) is not None:
            raise ValidationError("Пользователь уже существует")
        pwd_hash = self.hash_password(password)
        uid = self.db.create_user(username, pwd_hash)
        self.db.log_operation("register", uid)
        return uid

    def authenticate(self, username, password):
        user = self.db.get_user(username)
        if user is None:
            dummy = AuthService.hash_password("dummy_password_123")
            AuthService.verify_password(password, dummy)
            raise AuthError("Неверный логин или пароль")
        if not AuthService.verify_password(password, user["password_hash"]):
            raise AuthError("Неверный логин или пароль")
        self.db.log_operation("login", user["id"])
        return user["id"], user["username"]


class AuditService:
    def __init__(self, db):
        self.db = db

    def log(self, op_type, user_id, file_id=None, details=None):
        self.db.log_operation(op_type, user_id, file_id, details)


class FileService:
    def __init__(self, db, audit, root):
        self.db = db
        self.audit = audit
        self.root = os.path.realpath(root)
        ensure_dir(self.root)

    def _user_dir(self, user_id):
        d = os.path.join(self.root, "u{}".format(user_id))
        ensure_dir(d)
        return d

    def write_text(self, user_id, name, content):
        path = safe_join(self._user_dir(user_id), name)
        flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        fd = os.open(path, flags, 0o600)
        try:
            data = content.encode("utf-8")
            os.write(fd, data)
            size = os.fstat(fd).st_size
        finally:
            os.close(fd)
        rec = self.db.find_file(path, user_id)
        if rec:
            self.db.update_file_size(rec["id"], size)
            self.audit.log("modify", user_id, rec["id"], name)
        else:
            fid = self.db.register_file(name, size, path, user_id)
            self.audit.log("create", user_id, fid, name)
        return path

    def read_text(self, user_id, name):
        path = safe_join(self._user_dir(user_id), name)
        data = read_limited(path, MAX_JSON_BYTES)
        return data.decode("utf-8")

    def delete(self, user_id, name):
        path = safe_join(self._user_dir(user_id), name)
        if not os.path.lexists(path):
            raise ValidationError("Файл не найден")
        st = os.lstat(path)
        if stat.S_ISDIR(st.st_mode):
            raise ValidationError("Это каталог")
        
        rec = self.db.find_file(path, user_id)
        if rec:
            with self.db.transaction(immediate=True) as c:
                c.execute("UPDATE Operations SET file_id = NULL WHERE file_id = ?", (rec["id"],))
            self.db.delete_file_record(rec["id"])
            self.audit.log("delete", user_id, None, name)
            
        os.unlink(path)

    def list_files(self, user_id):
        d = self._user_dir(user_id)
        result = []
        for entry in os.scandir(d):
            if entry.is_file(follow_symlinks=False):
                result.append((entry.name, entry.stat().st_size))
        result.sort()
        return result


class JsonService:
    def __init__(self, fs, audit):
        self.fs = fs
        self.audit = audit

    def write(self, user_id, name, obj):
        if not isinstance(obj, (dict, list)):
            raise ValidationError("Корень JSON должен быть объектом или массивом")
        text = json.dumps(obj, ensure_ascii=False, indent=2)
        path = self.fs.write_text(user_id, name, text)
        self.audit.log("json_write", user_id, None, name)
        return path

    def read(self, user_id, name):
        text = self.fs.read_text(user_id, name)
        if len(text.encode("utf-8")) > MAX_JSON_BYTES:
            raise ValidationError("JSON превышает допустимый размер")
        try:
            obj = json.loads(text)
        except json.JSONDecodeError as e:
            raise ValidationError("Некорректный JSON: {}".format(e.msg))
        if not isinstance(obj, (dict, list)):
            raise ValidationError("Корень JSON должен быть объектом или массивом")
        self.audit.log("json_read", user_id, None, name)
        return obj


class XmlService:
    def __init__(self, fs, audit):
        self.fs = fs
        self.audit = audit

    def write(self, user_id, name, root_tag, items):
        if not re.match(r"^[A-Za-z_][A-Za-z0-9_\-]{0,63}$", root_tag):
            raise ValidationError("Недопустимое имя корневого тега")
        root = ET.Element(root_tag)
        for item in items:
            if not isinstance(item, dict):
                raise ValidationError("Элемент должен быть словарём")
            el = ET.SubElement(root, "item")
            for k, v in item.items():
                if not re.match(r"^[A-Za-z_][A-Za-z0-9_\-]{0,63}$", str(k)):
                    raise ValidationError("Недопустимое имя поля")
                sub = ET.SubElement(el, str(k))
                sub.text = str(v)
        text = ET.tostring(root, encoding="unicode")
        path = self.fs.write_text(user_id, name, text)
        self.audit.log("xml_write", user_id, None, name)
        return path

    def read(self, user_id, name):
        text = self.fs.read_text(user_id, name)
        if len(text.encode("utf-8")) > MAX_XML_BYTES:
            raise ValidationError("XML превышает допустимый размер")
        if "<!DOCTYPE" in text or "<!ENTITY" in text:
            raise ValidationError("DTD и сущности запрещены")
        try:
            root = DET.fromstring(text)
        except Exception as e:
            raise ValidationError("Некорректный XML: {}".format(e))
        items = []
        for item in root.findall("item"):
            d = {}
            for child in item:
                d[child.tag] = child.text
            items.append(d)
        self.audit.log("xml_read", user_id, None, name)
        return {"root": root.tag, "items": items}


class ZipService:
    def __init__(self, fs, audit):
        self.fs = fs
        self.audit = audit

    @staticmethod
    def _validate_member(info, target_dir):
        name = info.filename
        if not name or name.startswith("/") or name.startswith("\\"):
            raise ValidationError("Абсолютный путь в архиве запрещён")
        if ".." in name.replace("\\", "/").split("/"):
            raise ValidationError("Обход пути в архиве запрещён")
        mode = (info.external_attr >> 16) & 0o170000
        if mode == stat.S_IFLNK:
            raise ValidationError("Символические ссылки в архиве запрещены")
        target = os.path.realpath(os.path.join(target_dir, name))
        base = os.path.realpath(target_dir)
        if not (target == base or target.startswith(base + os.sep)):
            raise ValidationError("Выход за пределы каталога запрещён")

    def extract(self, user_id, zip_name, dest_name):
        base = self.fs._user_dir(user_id)
        zip_path = safe_join(base, zip_name)
        dest_dir = safe_join(base, dest_name)
        ensure_dir(dest_dir)
        with zipfile.ZipFile(zip_path, "r") as zf:
            infos = zf.infolist()
            if len(infos) > ZIP_MAX_FILES:
                raise ValidationError("Слишком много файлов в архиве")
            total = 0
            for info in infos:
                if info.is_dir():
                    continue
                self._validate_member(info, dest_dir)
                if info.file_size > ZIP_MAX_FILE_SIZE:
                    raise ValidationError("Файл в архиве слишком большой")
                total += info.file_size
                if total > ZIP_MAX_TOTAL_SIZE:
                    raise ValidationError("Суммарный размер распаковки превышен")
                if info.compress_size > 0 and info.file_size / info.compress_size > ZIP_MAX_RATIO:
                    raise ValidationError("Подозрительный коэффициент сжатия (ZIP-бомба)")
            for info in infos:
                if info.is_dir():
                    continue
                target = os.path.join(dest_dir, info.filename)
                ensure_dir(os.path.dirname(target))
                with zf.open(info, "r") as src:
                    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
                    if hasattr(os, "O_NOFOLLOW"):
                        flags |= os.O_NOFOLLOW
                    fd = os.open(target, flags, 0o600)
                    try:
                        remaining = info.file_size
                        while remaining > 0:
                            chunk = src.read(min(65536, remaining))
                            if not chunk:
                                break
                            os.write(fd, chunk)
                            remaining -= len(chunk)
                    finally:
                        os.close(fd)
        self.audit.log("zip_extract", user_id, None, "{} -> {}".format(zip_name, dest_name))

    def create(self, user_id, zip_name, files):
        base = self.fs._user_dir(user_id)
        zip_path = safe_join(base, zip_name)
        with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
            for name in files:
                src = safe_join(base, name)
                if not os.path.isfile(src):
                    raise ValidationError("Файл не найден: {}".format(name))
                zf.write(src, arcname=name)
        size = os.path.getsize(zip_path)
        rec = self.db_find(zip_path, user_id)
        if rec:
            self.fs.db.update_file_size(rec["id"], size)
        else:
            fid = self.fs.db.register_file(zip_name, size, zip_path, user_id)
            self.audit.log("zip_create", user_id, fid, zip_name)
        return zip_path

    def db_find(self, path, user_id):
        return self.fs.db.find_file(path, user_id)


class DiskService:
    @staticmethod
    def list_disks():
        result = []
        if os.name == 'nt':
            import ctypes
            drives = []
            bitmask = ctypes.windll.kernel32.GetLogicalDrives()
            for letter in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ':
                if bitmask & 1:
                    drives.append(letter + ':\\')
                bitmask >>= 1
            for d in drives:
                try:
                    free_bytes = ctypes.c_ulonglong(0)
                    total_bytes = ctypes.c_ulonglong(0)
                    ctypes.windll.kernel32.GetDiskFreeSpaceExW(
                        ctypes.c_wchar_p(d), None, ctypes.pointer(total_bytes), ctypes.pointer(free_bytes)
                    )
                    total = total_bytes.value
                    free = free_bytes.value
                    if total > 0:
                        result.append({
                            "mount": d,
                            "total": total,
                            "free": free,
                            "used": total - free,
                            "percent": round((total - free) / total * 100, 2),
                        })
                except Exception:
                    pass
        else:
            try:
                with open("/proc/mounts", "r") as f:
                    for line in f:
                        parts = line.split()
                        if len(parts) >= 2:
                            m = parts[1]
                            try:
                                st = os.statvfs(m)
                                total = st.f_blocks * st.f_frsize
                                free = st.f_bavail * st.f_frsize
                                if total > 0:
                                    result.append({
                                        "mount": m,
                                        "total": total,
                                        "free": free,
                                        "used": total - free,
                                        "percent": round((total - free) / total * 100, 2),
                                    })
                            except OSError:
                                continue
            except FileNotFoundError:
                pass
        return result


class CLI:
    def __init__(self):
        self.db = Database(DB_PATH)
        self.auth = AuthService(self.db)
        self.audit = AuditService(self.db)
        self.fs = FileService(self.db, self.audit, STORAGE_ROOT)
        self.json_svc = JsonService(self.fs, self.audit)
        self.xml_svc = XmlService(self.fs, self.audit)
        self.zip_svc = ZipService(self.fs, self.audit)
        self.user_id = None
        self.username = None

    def run(self):
        print("Файловый менеджер (Python). Введите help для списка команд.")
        while True:
            try:
                line = input("fm> ").strip()
            except (EOFError, KeyboardInterrupt):
                print()
                return
            if not line:
                continue
            cmd, _, rest = line.partition(" ")
            cmd = cmd.lower()
            rest = rest.strip()
            
            try:
                if not self._dispatch(cmd, rest):
                    return
            except (AppError, ValidationError, AuthError) as e:
                print("Ошибка:", e)
            except Exception as e:
                print("Непредвиденная ошибка:", type(e).__name__, e)

    def _dispatch(self, cmd, rest):
        if cmd in ("quit", "exit", "q"):
            return False
        if cmd == "help":
            self._help()
            return True
        if cmd == "register":
            if not rest:
                print("Использование: register <username>")
                return True
            pwd = getpass.getpass("Пароль: ")
            self.auth.register(rest, pwd)
            print("Пользователь зарегистрирован")
            return True
        if cmd == "login":
            if not rest:
                print("Использование: login <username>")
                return True
            pwd = getpass.getpass("Пароль: ")
            uid, uname = self.auth.authenticate(rest, pwd)
            self.user_id = uid
            self.username = uname
            print("Вход выполнен:", uname)
            return True
        if self.user_id is None:
            print("Сначала выполните login")
            return True
        if cmd == "logout":
            self.db.log_operation("logout", self.user_id)
            self.user_id = None
            self.username = None
            print("Выход выполнен")
            return True
        if cmd == "disks":
            self._cmd_disks()
        elif cmd == "ls":
            self._cmd_ls()
        elif cmd == "write":
            if " " not in rest:
                print("Использование: write <name> <text>")
            else:
                name, text = rest.split(" ", 1)
                self.fs.write_text(self.user_id, name, text)
                print("Записано:", name)
        elif cmd == "read":
            if not rest:
                print("Использование: read <name>")
            else:
                print(self.fs.read_text(self.user_id, rest))
        elif cmd == "rm":
            if not rest:
                print("Использование: rm <name>")
            else:
                self.fs.delete(self.user_id, rest)
                print("Удалено:", rest)
        elif cmd == "json_write":
            if " " not in rest:
                print("Использование: json_write <name> <json>")
            else:
                name, raw = rest.split(" ", 1)
                try:
                    obj = json.loads(raw)
                except json.JSONDecodeError as e:
                    print("Некорректный JSON:", e.msg)
                    return True
                self.json_svc.write(self.user_id, name, obj)
                print("JSON записан:", name)
        elif cmd == "json_read":
            if not rest:
                print("Использование: json_read <name>")
            else:
                obj = self.json_svc.read(self.user_id, rest)
                print(json.dumps(obj, ensure_ascii=False, indent=2))
        elif cmd == "xml_write":
            if rest.count(" ") < 2:
                print("Использование: xml_write <name> <root> <json-массив>")
            else:
                parts = rest.split(" ", 2)
                name, root_tag, raw = parts[0], parts[1], parts[2]
                try:
                    items = json.loads(raw)
                except json.JSONDecodeError as e:
                    print("Некорректный JSON:", e.msg)
                    return True
                if not isinstance(items, list):
                    print("Ожидался JSON-массив объектов")
                    return True
                self.xml_svc.write(self.user_id, name, root_tag, items)
                print("XML записан:", name)
        elif cmd == "xml_read":
            if not rest:
                print("Использование: xml_read <name>")
            else:
                obj = self.xml_svc.read(self.user_id, rest)
                print(json.dumps(obj, ensure_ascii=False, indent=2))
        elif cmd == "zip_create":
            if " " not in rest:
                print("Использование: zip_create <zipname> <f1,f2,...>")
            else:
                zip_name, raw = rest.split(" ", 1)
                files = [x.strip() for x in raw.split(",") if x.strip()]
                if not files:
                    print("Список файлов пуст")
                    return True
                path = self.zip_svc.create(self.user_id, zip_name, files)
                print("ZIP создан:", path)
        elif cmd == "zip_extract":
            if " " not in rest:
                print("Использование: zip_extract <zipname> <dest>")
            else:
                zip_name, dest = rest.split(" ", 1)
                self.zip_svc.extract(self.user_id, zip_name, dest)
                print("ZIP извлечён в", dest)
        elif cmd == "audit":
            self._cmd_audit()
        else:
            print("Неизвестная команда. help — список.")
        return True

    def _help(self):
        print("""Команды:
  register <username>         регистрация
  login <username>            вход
  logout                      выход
  disks                       список дисков
  ls                          список файлов пользователя
  write <name> <text>         записать текстовый файл
  read <name>                 прочитать текстовый файл
  rm <name>                   удалить файл
  json_write <name> <json>    записать JSON
  json_read <name>            прочитать JSON
  xml_write <name> <root> <json-массив>  записать XML
  xml_read <name>             прочитать XML
  zip_create <zipname> <f1,f2,...>       создать ZIP
  zip_extract <zipname> <dest>          извлечь ZIP
  audit                       последние операции
  quit                        выход""")

    def _cmd_disks(self):
        for d in DiskService.list_disks():
            print("{mount}: total={total} free={free} used={used} ({percent}%)".format(**d))

    def _cmd_ls(self):
        for name, size in self.fs.list_files(self.user_id):
            print("{:>10}  {}".format(size, name))

    def _cmd_audit(self):
        for row in self.db.list_operations(self.user_id):
            print("{timestamp}  {operation_type}  file={file_id}  {details}".format(**row))


def main():
    ensure_dir(STORAGE_ROOT)
    CLI().run()


if __name__ == "__main__":
    main()