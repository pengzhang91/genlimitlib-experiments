#!/usr/bin/env python3
"""Regenerate the integrity manifest for the publishable release files."""

from __future__ import annotations

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "SHA256SUMS"


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def main() -> None:
    paths = []
    for path in ROOT.rglob("*"):
        if not path.is_file() or path == MANIFEST:
            continue
        relative = path.relative_to(ROOT)
        if ".lake" in relative.parts:
            continue
        paths.append(path)

    lines = [
        f"{digest(path)}  {path.relative_to(ROOT).as_posix()}\n"
        for path in sorted(paths)
    ]
    MANIFEST.write_text("".join(lines), encoding="utf-8")
    print(f"Wrote {len(lines)} entries to {MANIFEST.name}")


if __name__ == "__main__":
    main()
