#!/usr/bin/env python3
"""Verify integrity and release hygiene for the public release module."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path
from zipfile import ZipFile


ROOT = Path(__file__).resolve().parent
CHECKSUMS = ROOT / "SHA256SUMS"

FORBIDDEN_GENERIC_LITERALS = (
    "overleaf.com/project",
    "/users/",
    "/home/",
)
SECRET_PATTERNS = (
    re.compile(r"sk-[A-Za-z0-9_-]{16,}"),
    re.compile(r"gh[pousr]_[A-Za-z0-9]{20,}"),
    re.compile(r"AKIA[A-Z0-9]{16}"),
    re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----"),
)


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def published_files() -> list[Path]:
    files = []
    for path in ROOT.rglob("*"):
        if not path.is_file() or path == CHECKSUMS:
            continue
        relative = path.relative_to(ROOT)
        if ".lake" in relative.parts:
            continue
        files.append(path)
    return sorted(files)


def scan_text(label: str, text: str, errors: list[str]) -> None:
    lowered = text.lower()
    for literal in FORBIDDEN_GENERIC_LITERALS:
        if literal in lowered:
            errors.append(f"forbidden identifier in {label}: {literal}")
    for pattern in SECRET_PATTERNS:
        if pattern.search(text):
            errors.append(f"credential-like text in {label}: {pattern.pattern}")


def main() -> None:
    errors: list[str] = []
    if not CHECKSUMS.is_file():
        raise SystemExit("Missing SHA256SUMS")

    expected: dict[str, str] = {}
    for line in CHECKSUMS.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        checksum, relative = line.split(None, 1)
        relative = relative.lstrip("*")
        if relative in expected:
            errors.append(f"duplicate checksum entry: {relative}")
        expected[relative] = checksum

    actual = {path.relative_to(ROOT).as_posix(): path for path in published_files()}
    for relative in sorted(set(actual) - set(expected)):
        errors.append(f"file missing from SHA256SUMS: {relative}")
    for relative in sorted(set(expected) - set(actual)):
        errors.append(f"checksum entry has no file: {relative}")
    for relative in sorted(set(actual) & set(expected)):
        if digest(actual[relative]) != expected[relative]:
            errors.append(f"checksum mismatch: {relative}")

    for path in ROOT.rglob("*"):
        relative = path.relative_to(ROOT)
        if ".lake" in relative.parts:
            continue
        if path.is_symlink():
            errors.append(f"symbolic link is not allowed: {relative}")
        if path.is_dir() and path.name == ".git":
            errors.append(f"nested Git history: {relative}")
        if path.is_file() and (
            path.name == ".DS_Store"
            or path.name == "OVERLEAF_SYNC.md"
            or path.suffix in {".pyc", ".pyo", ".olean"}
        ):
            errors.append(f"excluded artifact present: {relative}")

    for relative, path in actual.items():
        # The verifier necessarily contains the deny-list literals themselves.
        if relative == "VERIFY_RELEASE.py":
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        scan_text(relative, text, errors)

    for archive in ROOT.rglob("*.zip"):
        if ".lake" in archive.relative_to(ROOT).parts:
            continue
        with ZipFile(archive) as bundle:
            for name in bundle.namelist():
                member = Path(name)
                if member.is_absolute() or ".." in member.parts:
                    errors.append(f"unsafe archive path in {archive.relative_to(ROOT)}: {name}")
                    continue
                try:
                    text = bundle.read(name).decode("utf-8")
                except (UnicodeDecodeError, IsADirectoryError):
                    continue
                scan_text(f"{archive.relative_to(ROOT)}::{name}", text, errors)

    required = (
        "README.md",
        "ANONYMIZATION.md",
        "LICENSE",
        "GenLimitLean/lean-toolchain",
        "GenLimitLean/lakefile.toml",
        "GenLimitLean/lake-manifest.json",
        "GenLimitLean/Section4.lean",
        "scripts/verify_section4.sh",
        "scripts/section4_axioms.lean",
        "registry/section4/README.md",
        "registry/section4/verification/STATUS.md",
        "manuscript/section4/proofs.tex",
        "manuscript/section4/proofs.pdf",
    )
    for relative in required:
        if not (ROOT / relative).is_file():
            errors.append(f"required release file missing: {relative}")

    section_files = list((ROOT / "GenLimitLean/Section4").glob("*.lean"))
    if len(section_files) != 20:
        errors.append(f"expected 20 Section4 modules, found {len(section_files)}")

    if errors:
        raise SystemExit("FAIL:\n" + "\n".join(f"- {error}" for error in errors))
    print(
        f"PASS: {len(actual)} checksummed files, 20 Section4 modules, "
        "no excluded private-path/credential/history/build artifacts detected"
    )


if __name__ == "__main__":
    main()
