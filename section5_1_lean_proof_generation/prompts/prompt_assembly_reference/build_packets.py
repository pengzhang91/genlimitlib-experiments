#!/usr/bin/env python3
"""Build packets whose target is stated over the library's vocabulary.

Two things happen here that the earlier arms did not need.

`Stage3Model.lean` is the single canonical active specification. It points at
the shared ordered-language vocabulary so that the treatment contrast does not
also include avoidable conversion and bridging work between duplicate types.

The vocabulary is shipped to every condition, because a target stated over it
cannot be stated without it. P receives the six modules with their theorems
removed. PML receives the full research closure plus statement cards and
navigation material. The experiment therefore estimates the effect of this
bundled library resource, not the isolated effect of proved declarations.

Launches nothing.
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from experiment import CONTROL, ROOT, digest, records, save, utc  # noqa: E402

DESIGN = ROOT / "design"
ORIGIN = ROOT.parent / "stage3_case017_condition_comparison"
ANALYSIS = ROOT.parent / "analysis_reusable_surface"
CFG = json.loads((CONTROL / "arm_config.json").read_text())
SOURCE = ORIGIN / "runs" / CFG["source_run"]
REFERENCE = ORIGIN / "control/design_freeze.json"
VOCAB_SRC = Path(os.environ.get("STAGE3_VOCAB_PACKET",
                                str(Path.home() / "_libvocab/vocab_packet")))
MODEL = "Stage3Model.lean"
REBASED = ["LEAN_ENV.json", "LEAN_ENV.sh"]
REMOVED_AUTHOR_INPUTS = {"MODEL_SPEC.md", "RUN_CONFIG.md"}
SANITIZED_AUTHOR_INPUTS = {"supplement/RELATIONS.md", "RESEARCH_MODULES.tsv"}
LEDGER = CONTROL / "PACKETS.json"

PATH_LEAK_MARKERS = (
    "stage3_case017_libvocab_pml_openrouter_sol",
    "stage3_case017_libvocab_p_openrouter_sol",
)
LEAK_MARKERS = PATH_LEAK_MARKERS + (
    "PM and PML",
    "for all evidence conditions",
    "experimental condition",
    "other runs, pilots",
)


def machine_roots(env):
    sysroot = Path(os.environ.get("STAGE3_LEAN_SYSROOT") or env["LEAN_SYSROOT"])
    std = Path(os.environ.get("STAGE3_STANDARD_ROOT") or env["standard_root"])
    for label, p, var in (("LEAN_SYSROOT", sysroot, "STAGE3_LEAN_SYSROOT"),
                          ("standard package root", std, "STAGE3_STANDARD_ROOT")):
        if not p.is_dir():
            raise SystemExit("%s not found: %s\nset %s" % (label, p, var))
    return sysroot, std


def neutralize_author_metadata(packet: Path) -> None:
    relations = packet / "supplement/RELATIONS.md"
    if relations.is_file():
        text = relations.read_text()
        text = text.replace(
            "Provenance is descriptive only: `paper-explicit`, `paper-inferred`, and\n"
            "`lean-derived` relations are all visible in PM and PML.",
            "Provenance labels describe how each relationship was obtained:\n"
            "`paper-explicit`, `paper-inferred`, or `lean-derived`.")
        relations.write_text(text)
    manifest = packet / "RESEARCH_MODULES.tsv"
    if manifest.is_file():
        rows = [line.split("\t") for line in manifest.read_text().splitlines()]
        if rows and rows[0] == ["module", "source_path", "role"]:
            rows = [row[:2] for row in rows]
        if not rows or rows[0] != ["module", "source_path"] or any(len(row) != 2 for row in rows):
            raise RuntimeError("unexpected RESEARCH_MODULES.tsv schema")
        manifest.write_text("\n".join("\t".join(row) for row in rows) + "\n")


def audit_author_packet(packet: Path) -> None:
    skip_roots = {"papers", "research", "vocabulary", "output"}
    findings = []
    for path in sorted(packet.rglob("*")):
        rel = path.relative_to(packet)
        if not path.is_file():
            continue
        content = path.read_bytes()
        markers = PATH_LEAK_MARKERS if rel.parts[0] in skip_roots else LEAK_MARKERS
        for marker in markers:
            if marker.encode() in content:
                findings.append(f"{rel}: {marker}")
    if findings:
        raise RuntimeError("author-visible experiment metadata: " + "; ".join(findings[:8]))


def main() -> int:
    reference = json.loads(REFERENCE.read_text())
    frozen = reference["run_inputs"][CFG["source_run"]]
    base = records(SOURCE, exclude_output=True)
    if base != frozen:
        print("source packet does not match the original freeze; refusing")
        return 1
    print("source packet %s verified against the original freeze (%d files)"
          % (CFG["source_run"], len(base)))

    for name in CFG["must_be_absent"]:
        if [k for k in base if k == name or k.startswith(name)]:
            print("condition %s must not contain %s" % (CFG["condition"], name))
            return 1
    if CFG["must_be_absent"]:
        print("confirmed absent: %s" % ", ".join(CFG["must_be_absent"]))

    replacement = DESIGN / MODEL
    if not replacement.is_file():
        print("missing model replacement: %s" % replacement)
        return 1
    if CFG["vocabulary"] == "stripped" and not (VOCAB_SRC / "GenLimit").is_dir():
        print("missing stripped vocabulary at %s; set STAGE3_VOCAB_PACKET" % VOCAB_SRC)
        return 1

    src_env = json.loads((SOURCE / "LEAN_ENV.json").read_text())
    old_root = src_env["LEAN_PATH"].split(":")[0]
    old_sys, old_std = src_env["LEAN_SYSROOT"], reference["environment"]["standard_root"]
    NEW_SYS, NEW_STD = machine_roots(reference["environment"])

    ledger = json.loads(LEDGER.read_text()) if LEDGER.is_file() else {}
    for run_id in CFG["run_ids"]:
        dest = ROOT / "runs" / run_id
        if dest.exists():
            print("%s already exists; skipping" % run_id)
            continue
        new_root = str(dest.resolve())
        dest.mkdir(parents=True)
        for rel in base:
            out = dest / rel
            out.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SOURCE / rel, out)
        (dest / "output").mkdir(exist_ok=True)

        # Overlay the simplified author-facing design while leaving papers,
        # supplement, and research material unchanged.
        for name in REMOVED_AUTHOR_INPUTS:
            (dest / name).unlink(missing_ok=True)
        design_overrides = {p.name for p in DESIGN.iterdir()
                            if p.is_file() and p.name != MODEL}
        for name in design_overrides:
            shutil.copy2(DESIGN / name, dest / name)

        entry = {"utc": utc(), "condition": CFG["condition"], "source_run": CFG["source_run"],
                 "new_root": new_root, "vocabulary": CFG["vocabulary"]}

        # model substitution
        entry["model"] = {"file": MODEL,
                          "sha256_frozen": base[MODEL]["sha256"],
                          "sha256_replacement": digest(replacement)}
        shutil.copy2(replacement, dest / MODEL)
        (dest / (MODEL[:-5] + ".olean")).unlink(missing_ok=True)

        # vocabulary
        vocab_root = dest / "vocabulary"
        if CFG["vocabulary"] == "stripped":
            shutil.copytree(VOCAB_SRC, vocab_root)
            entry["vocabulary_files"] = len(list(vocab_root.rglob("*")))
            vocab_path = ["vocabulary/lib/lean"]
        else:
            vocab_path = []          # PML already carries the closure under research/
        entry["vocabulary_lean_path"] = vocab_path

        # LEAN_ENV: rebuild component-wise, then prepend the vocabulary
        env = json.loads((dest / "LEAN_ENV.json").read_text())
        rebuilt, unknown = [], []
        for comp in env["LEAN_PATH"].split(":"):
            if comp == old_root:
                rebuilt.append(new_root)
            elif comp.startswith(old_root + "/"):
                rebuilt.append(new_root + comp[len(old_root):])
            elif comp.startswith(old_std):
                rebuilt.append(str(NEW_STD) + comp[len(old_std):])
            elif comp.startswith(old_sys):
                rebuilt.append(str(NEW_SYS) + comp[len(old_sys):])
            else:
                unknown.append(comp)
        if unknown:
            print("%s: unclassifiable LEAN_PATH component(s): %s" % (run_id, unknown[:3]))
            return 1
        rebuilt = rebuilt[:1] + vocab_path + rebuilt[1:]
        rebuilt = ["." if comp == new_root else
                   Path(comp).relative_to(dest).as_posix()
                   if comp.startswith(new_root + "/") else comp
                   for comp in rebuilt]
        if "." not in rebuilt:
            print("%s: packet root missing from LEAN_PATH; refusing" % run_id)
            return 1
        new_env = {"LEAN_PATH": ":".join(rebuilt), "LEAN_SYSROOT": str(NEW_SYS)}
        (dest / "LEAN_ENV.json").write_text(json.dumps(new_env, indent=2) + "\n")
        (dest / "LEAN_ENV.sh").write_text(
            "export LEAN_SYSROOT=%s\nexport LEAN_PATH='%s'\n"
            % (new_env["LEAN_SYSROOT"], new_env["LEAN_PATH"]))
        for name in REBASED:
            entry.setdefault("lean_env", {})[name] = {
                "sha256_source": base[name]["sha256"], "sha256_rebuilt": digest(dest / name)}

        neutralize_author_metadata(dest)
        audit_author_packet(dest)

        current = records(dest, exclude_output=True)
        added = set(current) - set(base)
        expect_added = ({p for p in added if p.startswith("vocabulary/")}
                        | (design_overrides - set(base)))
        if added - expect_added:
            print("%s: unexpected additions %s" % (run_id, sorted(added - expect_added)[:4]))
            return 1
        removed = set(base) - set(current)
        if removed - ({MODEL[:-5] + ".olean"} | REMOVED_AUTHOR_INPUTS):
            print("%s: unexpectedly missing %s" % (run_id, sorted(removed)[:4]))
            return 1
        exempt = (set(REBASED) | {MODEL, MODEL[:-5] + ".olean"}
                  | REMOVED_AUTHOR_INPUTS | SANITIZED_AUTHOR_INPUTS | design_overrides)
        drift = sorted(k for k in base if k not in exempt and current.get(k) != base[k])
        if drift:
            print("%s: inherited files differ: %s" % (run_id, drift[:5]))
            return 1
        if any((dest / "output").iterdir()):
            print("%s: output/ is not empty" % run_id)
            return 1
        print("%s: %d inherited byte-identical, model replaced, vocabulary=%s (%d files)"
              % (run_id, len(base) - len(exempt), CFG["vocabulary"],
                 entry.get("vocabulary_files", 0)))
        ledger[run_id] = entry

    save(LEDGER, ledger)
    print("ledger written: control/PACKETS.json")
    print("NOTE Stage3Model.olean was removed; it must be rebuilt before preflight.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
