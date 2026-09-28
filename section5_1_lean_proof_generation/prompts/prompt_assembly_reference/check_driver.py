#!/usr/bin/env python3
"""Pinned targeted Lean checker. Root gate never reads author reports/ledgers."""
from __future__ import annotations
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
RESERVED_MODULES = {"ControllerFinalCheck", "ControllerDependencyCheck", "ControllerAudit", "TargetTemplate"}
GATE_PREFIX = "STAGE3_GATE "
DEPENDENCY_PREFIX = "STAGE3_DEPENDENCIES "


def within(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except ValueError:
        return False


def without_comments(raw: str) -> str:
    result, depth, i, quoted = [], 0, 0, False
    while i < len(raw):
        if not depth and raw[i] == '"':
            quoted = not quoted
            result.append(raw[i]); i += 1
        elif quoted:
            result.append(raw[i])
            if raw[i] == "\\" and i + 1 < len(raw):
                i += 1; result.append(raw[i])
            i += 1
        elif raw[i:i + 2] == "/-":
            depth += 1; i += 2
        elif depth and raw[i:i + 2] == "-/":
            depth -= 1; i += 2
            if not depth:
                result.append(" ")
        elif depth:
            if raw[i] == "\n":
                result.append("\n")
            i += 1
        elif raw[i:i + 2] == "--":
            end = raw.find("\n", i)
            i = len(raw) if end < 0 else end
        else:
            result.append(raw[i]); i += 1
    return "".join(result)


def imports(path: Path) -> list[str]:
    modules = []
    for match in re.finditer(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)",
                             without_comments(path.read_text())):
        modules.extend(match.group(1).split())
    return modules


def source_closure(output: Path, source: Path) -> list[Path]:
    done, visiting, ordered = set(), set(), []
    def visit(path):
        path = path.resolve()
        if path in done:
            return
        if not within(path, output) or path in visiting:
            raise ValueError("escaped or cyclic local import")
        visiting.add(path)
        for name in imports(path):
            if name in RESERVED_MODULES:
                raise ValueError("controller modules cannot be proof inputs")
            if name == "Stage3Model":
                continue
            local = output / (name.replace(".", "/") + ".lean")
            if local.is_file():
                visit(local)
            elif local.with_suffix(".olean").exists():
                raise ValueError("compiled-only author module: " + name)
        visiting.remove(path); done.add(path); ordered.append(path)
    visit(source)
    return ordered


def hashes(paths: list[Path], output: Path) -> dict:
    return {p.relative_to(output).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def parse_axioms(log: str) -> dict:
    result = {name: [a.strip() for a in axioms.split(",") if a.strip()]
              for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        result[name] = []
    return result


def root_gate(exit_code: int, log: str) -> dict:
    axioms = parse_axioms(log)
    bad = {name: [a for a in deps if a not in ALLOWED_AXIOMS] for name, deps in axioms.items()
           if name in {"stage3_result", "controller_exact_target"} and any(a not in ALLOWED_AXIOMS for a in deps)}
    return {"target_kernel_pass": exit_code == 0
            and all(n in axioms for n in ["stage3_result", "controller_exact_target"]) and not bad,
            "exact_target_compile_exit": exit_code, "axioms": axioms, "inadmissible_axioms": bad}


def compile_file(run: Path, source: Path, env: dict, root: Path) -> subprocess.CompletedProcess:
    return subprocess.run([str(Path(env["LEAN_SYSROOT"]) / "bin/lean"), "-j", "1",
         f"--root={root}", "-o", str(source.with_suffix(".olean")), str(source)],
         cwd=run, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def check(run: Path, argument: str) -> int:
    run = run.resolve(); output = run / "output"
    env = dict(os.environ, **json.loads((run / "LEAN_ENV.json").read_text()))
    dependencies = argument == "--dependencies"
    inventory = argument == "--inventory"
    final = argument in {"--final", "--dependencies", "--inventory"}
    source = (output / "Case017Formalization.lean" if final else run / argument).resolve()
    if not within(source, output) or source.suffix != ".lean" or not source.is_file():
        raise ValueError("target must be an existing .lean file below output/")
    paths = source_closure(output, source)
    before = hashes(paths, output)
    # Conservative mechanism guard on imported author sources, not scratch.
    # Axiom eligibility itself is decided transitively by Lean below.
    banned = []
    for p in paths:
        clean = without_comments(p.read_text())
        for token in ["native_decide", "ofReduceBool", "debug.skipKernelTC", "implemented_by"]:
            if token in clean:
                banned.append({"file": p.relative_to(output).as_posix(), "mechanism": token})
    file_exit = 0
    for path in paths:
        proc = compile_file(run, path, env, output)
        print(proc.stdout, end="")
        if proc.returncode:
            file_exit = proc.returncode; break
    if source != output / "Case017Formalization.lean":
        return file_exit
    gate = {"target_kernel_pass": False, "entry_compile_exit": file_exit, "source_hashes": before}
    if not file_exit:
        probe = output / "ControllerFinalCheck.lean"
        probe.write_text("import Stage3Model\nimport Case017Formalization\n"
            "theorem controller_exact_target : Stage3Case017.MainClaim := @stage3_result\n"
            "#print axioms controller_exact_target\n#print axioms stage3_result\n")
        proc = compile_file(run, probe, env, output)
        print(proc.stdout, end="")
        gate.update(root_gate(proc.returncode, proc.stdout))
    gate["prohibited_mechanisms"] = banned
    gate["sources_unchanged_during_check"] = hashes(paths, output) == before
    gate["target_kernel_pass"] = bool(gate["target_kernel_pass"] and not banned
                                      and gate["sources_unchanged_during_check"])
    (output / "ROOT_GATE.json").write_text(json.dumps(gate, indent=2) + "\n")
    print(GATE_PREFIX + json.dumps(gate, separators=(",", ":")), flush=True)
    if (dependencies or inventory) and not file_exit:
        # Auxiliary analysis is a separate command / exit status.
        probe = output / "ControllerDependencyCheck.lean"
        modules = ",".join(p.relative_to(output).as_posix()[:-5].replace("/", ".") for p in paths)
        command = "#stage3_inventory " + json.dumps(modules) if inventory else "#stage3_dependencies stage3_result"
        probe.write_text("import ControllerAudit\nimport Case017Formalization\n" + command + "\n")
        proc = compile_file(run, probe, env, output)
        payload = None
        prefix = "STAGE3_INVENTORY " if inventory else DEPENDENCY_PREFIX
        for line in proc.stdout.splitlines():
            if prefix in line:
                payload = json.loads(line.split(prefix, 1)[1])
            else:
                print(line)
        if payload is not None:
            name = "DECLARATION_INVENTORY.json" if inventory else "DEPENDENCIES.json"
            (output / name).write_text(json.dumps(payload, indent=2) + "\n")
            print("Dependency extraction completed (auxiliary, not part of root gate).")
        return proc.returncode if proc.returncode else (0 if payload is not None else 3)
    return (0 if gate["target_kernel_pass"] else 2) if final else file_exit


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: CHECK_DRIVER.py output/FILE.lean|--final|--dependencies|--inventory")
    raise SystemExit(check(Path.cwd(), sys.argv[1]))
