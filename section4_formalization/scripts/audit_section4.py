#!/usr/bin/env python3
"""Fail closed on admissions or unexpected/missing endpoint axiom reports."""
from collections import Counter
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent

def code_only(text):
    """Remove Lean line comments, nested block comments, and quoted strings."""
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith("/-", i):
            out.append(" ")
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise SystemExit("Unterminated Lean comment during admission scan.")
    return "".join(out)

def scan(report):
    source = ROOT / "GenLimitLean"
    files = [source / "Section4.lean", *sorted((source / "Section4").rglob("*.lean")),
             ROOT / "scripts/section4_axioms.lean"]
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b")
    for path in files:
        hits = forbidden.findall(code_only(path.read_text()))
        if hits:
            raise SystemExit(f"Forbidden proof tokens in {path}: {hits}")
    message = (f"PASS: scanned {len(files)} Lean files after removing comments and strings.\n"
               "No sorry, admit, custom axiom, unsafe, or native_decide token found.\n")
    Path(report).write_text(message)
    print(message, end="")

def axioms(log, report):
    source = code_only((ROOT / "scripts/section4_axioms.lean").read_text())
    expected = re.findall(r"^\s*#print\s+axioms\s+([\w.]+)\s*$", source, re.M)
    if not expected:
        raise SystemExit("No expected endpoint declarations found.")
    text = Path(log).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
    reports += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    actual = [name for name, _ in reports]
    if Counter(actual) != Counter(expected):
        missing = Counter(expected) - Counter(actual)
        extra = Counter(actual) - Counter(expected)
        raise SystemExit(f"Axiom endpoint mismatch; missing={dict(missing)}, extra={dict(extra)}")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for theorem, names in reports:
        unexpected = {name.strip() for name in names.split(",") if name.strip()} - allowed
        if unexpected:
            raise SystemExit(f"Unexpected axioms for {theorem}: {sorted(unexpected)}")
    message = (f"PASS: all {len(expected)} declared endpoints produced exactly one axiom report.\n"
               "Every reported axiom belongs to {propext, Classical.choice, Quot.sound}.\n")
    Path(report).write_text(message)
    print(message, end="")

if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "scan":
        scan(sys.argv[2])
    elif len(sys.argv) == 4 and sys.argv[1] == "axioms":
        axioms(sys.argv[2], sys.argv[3])
    else:
        raise SystemExit("Usage: audit_section4.py scan REPORT | axioms LOG REPORT")
