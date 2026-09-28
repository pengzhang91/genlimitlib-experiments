#!/usr/bin/env python3
"""Single-condition Case 017 controller for the bundled-library pilot.

This is one arm of a development experiment on a previously used Case 017 task.
Its results are pilot diagnostics, not evidence from an untouched benchmark.
The treatment contrast and pre-launch corrections are recorded in
``control/RUN_CONFIG.md``.

Only the explicit `run` subcommand launches author models.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import random
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import threading
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path

from check_driver import imports, within, GATE_PREFIX
from measurements import capture, gate_messages, efficiency, reuse_summary
from codex_adapter import OpenRouterProxy

CONTROL = Path(__file__).resolve().parent
ROOT = CONTROL.parent
DESIGN = ROOT / "design"
ORIGINAL = Path(os.environ.get("STAGE3_ORIGINAL_ROOT", str(ROOT / "_unavailable_original"))).resolve()
UPSTREAM = ROOT.parent / "stage2_5_s2b_canonical_proof"
CANONICAL = UPSTREAM / "canonical"
# Run ids and condition come from arm_config.json so that changing the number
# of replicates does not change this file's hash, which verify() pins.
_ARM = json.loads((CONTROL / "arm_config.json").read_text())
SOURCE_RUNS = {_ARM["condition"]: _ARM["run_ids"][0]}
RUNS = {r: _ARM["condition"] for r in _ARM["run_ids"]}
PAPER_MODULES = [
    "GenLimit.Paper06_NoisyExamples", "GenLimit.Paper12_NoiseLossAndFeedback",
    "GenLimit.Paper17_InfiniteContamination", "GenLimit.Paper19_EffectOfNoise",
    "GenLimit.Paper39_DenseGeneration",
]
IDS = [
    "C01_FAMILY_AND_INFORMATION_CORE",
    "C02_ONE_GENERATOR_EVENTUAL_VALIDITY",
    "C03_HALF_CORE_DENSITY",
    "C04_NEVER_PRESENTED_CORE",
    "C05_ASSEMBLY_AND_SCOPE",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FREEZE = CONTROL / "design_freeze.json"


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def records(folder: Path, exclude_output=False) -> dict:
    return {p.relative_to(folder).as_posix(): {"sha256": digest(p), "bytes": p.stat().st_size}
            for p in sorted(folder.rglob("*")) if p.is_file()
            and (not exclude_output or "output" not in p.relative_to(folder).parts)
            and "__pycache__" not in p.parts}


def save(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@contextmanager
def neutral_workspace(packet: Path):
    """Copy an author packet under a randomized path with no arm/run labels."""
    temp_root = Path(os.environ.get("STAGE3_TMPDIR") or os.environ.get("SLURM_TMPDIR") or tempfile.gettempdir()).resolve()
    temp_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="formalization-", dir=str(temp_root)) as folder:
        workspace = Path(folder) / "workspace"
        shutil.copytree(packet, workspace)
        yield workspace


def checkpoint_lean_path(values: dict, packet: Path, snapshot: Path) -> str:
    """Relocate packet-relative dependencies for an immutable checkpoint."""
    local = {packet.resolve(), (packet / "output").resolve()}
    remaining = []
    for component in values["LEAN_PATH"].split(":"):
        path = Path(component)
        resolved = path.resolve() if path.is_absolute() else (packet / path).resolve()
        if resolved not in local:
            remaining.append(str(resolved))
    return ":".join([str(snapshot), str(snapshot / "output")] + remaining)


def normalize_lookup(packet: Path) -> None:
    for path in sorted((packet / "supplement/lean_lookup").glob("P*.md")):
        text = path.read_text().replace(
            "Mode: `READ_ONLY` source lookup. This experiment does not compile or type-check Lean.",
            "Mode: read-only research sources; importing these modules and compiling your own Lean proofs is permitted.")
        text = text.replace("](../lean/", "](../../research/GenLimit/")
        text = text.replace("[lean/", "[research/GenLimit/")
        path.write_text(text)
        for link in re.findall(r"\]\(([^)]+\.lean)\)", text):
            target = (path.parent / link).resolve()
            if not within(target, packet / "research") or not target.is_file():
                raise RuntimeError("lookup target missing from frozen closure: " + link)
    (packet / "supplement/LEAN_PATHS.md").write_text(
        "# Frozen research Lean sources\n\nLookup links point directly to accessible "
        "research/GenLimit sources. RESEARCH_MODULES.tsv lists all modules. "
        "Matching compiled modules are under research/lib/lean and may be imported. "
        "Research inputs are read-only; compile your work under output/.\n")


def closure() -> list[str]:
    seen, todo = set(), list(PAPER_MODULES)
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        if not module.startswith("GenLimit."):
            continue
        source = ORIGINAL / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            raise RuntimeError(f"missing scientific module {module}")
        seen.add(module)
        todo.extend(imports(source))
    return sorted(seen)


def base_environment() -> dict:
    # Reuse the earlier resolved environment; remove the research root itself.
    frozen_env = ROOT.parent / "stage3_case017_canonical_completion_pilot/runs/pilot_001/LEAN_ENV.sh"
    raw = subprocess.check_output(
        ["/bin/bash", "-c", 'source "$1"; /usr/bin/env', "environment", str(frozen_env)], text=True,
    )
    values = dict(line.split("=", 1) for line in raw.splitlines() if "=" in line)
    packages_root = ORIGINAL / ".lake/packages"
    standard_paths = [str(Path(p).resolve()) for p in values["LEAN_PATH"].split(":")
                      if within(Path(p), packages_root)]
    if not standard_paths or any("GenLimit/.lake/build" in p for p in standard_paths):
        raise RuntimeError("invalid standard package path set")
    return {"LEAN_SYSROOT": values["LEAN_SYSROOT"], "standard_paths": standard_paths,
            "standard_root": str(packages_root)}


def prepare() -> None:
    # Re-materializing would re-derive the packet from the live research repo
    # and could silently differ from the bytes the ground-truth run received.
    # This pilot instead reuses the original packet, copied and hash-verified
    # against the original freeze; control/refreeze.py rebuilds this pilot's
    # own freeze from those copied bytes.
    raise SystemExit("prepare is disabled in this pilot; the packet is a "
                     "hash-verified copy. Use control/refreeze.py instead.")


def _prepare_original_unused() -> None:
    if FREEZE.exists() or (ROOT / "runs").exists():
        raise SystemExit("refusing to overwrite a prepared experiment")
    env = base_environment()
    common = ROOT / "environment/common"
    common.mkdir(parents=True)
    shutil.copy2(DESIGN / "Stage3Model.lean", common / "Stage3Model.lean")
    lean = Path(env["LEAN_SYSROOT"]) / "bin/lean"
    lean_env = dict(os.environ, LEAN_SYSROOT=env["LEAN_SYSROOT"], LEAN_PATH=":".join(env["standard_paths"]))
    # A compile-only preparation check: no author model is invoked.
    subprocess.run([str(lean), "-j", "1", "--root=" + str(common), "-o",
                    str(common / "Stage3Model.olean"), str(common / "Stage3Model.lean")],
                   env=lean_env, check=True)
    subprocess.run([str(lean), "-j", "1", "--root=" + str(CONTROL), "-o",
                    str(common / "ControllerAudit.olean"), str(CONTROL / "ControllerAudit.lean")],
                   env=lean_env, check=True)
    modules = closure()
    module_manifest = []
    for name in modules:
        relative = Path(name.replace(".", "/"))
        source = ORIGINAL / relative.with_suffix(".lean")
        compiled = ORIGINAL / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        if not compiled.is_file():
            raise RuntimeError(f"missing prebuilt {name}; prepare does not build the original library")
        module_manifest.append({"module": name, "source_sha256": digest(source),
                                "olean_sha256": digest(compiled),
                                "selected_paper_module": name in PAPER_MODULES})
    codex = Path(shutil.which("codex") or "").resolve()
    if not codex.is_file():
        raise RuntimeError("Codex executable unavailable")
    version = subprocess.check_output([str(codex), "--version"], text=True).strip().splitlines()[-1]
    codex_path = codex.parent.parent / "codex-path"
    if not (codex_path / "rg").is_file():
        raise RuntimeError(f"rg unavailable at {codex_path}")
    common_names = [p.name for p in DESIGN.iterdir() if p.is_file() and p.name != "Stage3Model.lean"]
    snapshots = {}
    for run_id, condition in RUNS.items():
        packet = ROOT / "runs" / run_id
        (packet / "output").mkdir(parents=True)
        for name in common_names:
            shutil.copy2(DESIGN / name, packet / name)
        shutil.copy2(common / "Stage3Model.lean", packet / "Stage3Model.lean")
        shutil.copy2(common / "Stage3Model.olean", packet / "Stage3Model.olean")
        shutil.copy2(CONTROL / "check_driver.py", packet / "CHECK_DRIVER.py")
        shutil.copy2(CONTROL / "LEAN_CHECK.sh", packet / "LEAN_CHECK.sh")
        shutil.copy2(CONTROL / "ControllerAudit.lean", packet / "ControllerAudit.lean")
        shutil.copy2(common / "ControllerAudit.olean", packet / "ControllerAudit.olean")
        source_run = UPSTREAM / "runs" / SOURCE_RUNS[condition]
        shutil.copytree(source_run / "papers", packet / "papers")
        if condition != "P":
            # All map/card content is copied identically from the PM packet.
            shutil.copytree(UPSTREAM / "runs/run_002/supplement", packet / "supplement")
        paths = [str(packet), str(packet / "output")] + env["standard_paths"]
        if condition == "PML":
            lookup = source_run / "supplement/lean_lookup"
            shutil.copytree(lookup, packet / "supplement/lean_lookup")
            for name in modules:
                rel = Path(name.replace(".", "/"))
                for suffix, src_root, dst_root in [
                    (".lean", ORIGINAL, packet / "research"),
                    (".olean", ORIGINAL / ".lake/build/lib/lean", packet / "research/lib/lean"),
                ]:
                    dest = dst_root / rel.with_suffix(suffix)
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(src_root / rel.with_suffix(suffix), dest)
            paths.append(str(packet / "research/lib/lean"))
            with (packet / "RESEARCH_MODULES.tsv").open("w") as handle:
                handle.write("module\tsource_path\trole\n")
                for name in modules:
                    role = "selected-paper" if any(name == x or name.startswith(x + ".") for x in PAPER_MODULES) else "transitive-support"
                    handle.write(f"{name}\tresearch/{name.replace('.', '/')}.lean\t{role}\n")
            normalize_lookup(packet)
        values = {"LEAN_SYSROOT": env["LEAN_SYSROOT"], "LEAN_PATH": ":".join(paths)}
        save(packet / "LEAN_ENV.json", values)
        (packet / "LEAN_ENV.sh").write_text("\n".join(f"export {k}={shlex.quote(v)}" for k, v in values.items()) + "\n")
        snapshots[run_id] = records(packet, exclude_output=True)
    shared = ["Stage3Model.lean", "Stage3Model.olean"] + common_names
    for name in shared:
        if len({snapshots[run][name]["sha256"] for run in RUNS}) != 1:
            raise RuntimeError(f"common input mismatch {name}")
    for packet in (ROOT / "runs").iterdir():
        if records(packet / "papers") != records(ROOT / "runs/run_001/papers"):
            raise RuntimeError("PDF corpus differs")
    order = list(RUNS)
    random.Random("stage3-case017-3run-v1-order").shuffle(order)
    blind = list(RUNS)
    random.Random("stage3-case017-3run-v1-blind").shuffle(blind)
    save(CONTROL / "private_mapping.json", {"conditions": RUNS, "launch_order": order,
         "anonymous_mapping": dict(zip("ABC", blind))})
    save(CONTROL / "research_module_hashes.json", module_manifest)
    external = [lean, Path(env["LEAN_SYSROOT"]) / "lib/lean/Init.olean",
                ORIGINAL / "lake-manifest.json", ORIGINAL / "lean-toolchain",
                ORIGINAL / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"]
    # Standard packages remain shared read-only infrastructure. Their commits
    # and lockfile are pinned; research .lean/.olean contents are fully hashed.
    commits = {}
    for pkg in sorted((ORIGINAL / ".lake/packages").iterdir()):
        if (pkg / ".git").exists():
            commits[pkg.name] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=pkg, text=True).strip()
    save(FREEZE, {"created_utc": utc(), "experiment": "stage3-case017-3condition-v2",
         "state": "PREPARED_NOT_STARTED", "model": "gpt-5.6-sol", "reasoning": "medium",
         "seconds_per_run": 5400, "codex_binary": str(codex), "codex_sha256": digest(codex),
         "codex_version": version, "codex_path": str(codex_path), "environment": env,
         "run_inputs": snapshots, "external_hashes": {str(p): digest(p) for p in external},
         "standard_package_commits": commits,
         "design_hashes": records(DESIGN),
         "review_design_hashes": records(ROOT / "review_design"),
         "protocol_hashes": {name: digest(ROOT / name) for name in ["README.md", "DESIGN.md", "AGENTS.md"]},
         "controller_hashes": {p.name: digest(p) for p in CONTROL.iterdir()
                               if p.suffix in {".py", ".sh", ".txt", ".lean", ".md"}},
         "support_module_count": len(modules), "common_inputs": shared})
    (ROOT / "logs").mkdir(exist_ok=True)
    (ROOT / "results").mkdir(exist_ok=True)
    print(f"Prepared 3 packets; {len(modules)} frozen research modules for PML; no model launched.")


def frozen() -> dict:
    return json.loads(FREEZE.read_text())


def verify() -> None:
    data = frozen()
    for run, expected in data["run_inputs"].items():
        if records(ROOT / "runs" / run, exclude_output=True) != expected:
            raise RuntimeError(f"frozen input changed in {run}")
    if records(DESIGN) != data["design_hashes"]:
        raise RuntimeError("design files changed after freeze")
    if records(ROOT / "review_design") != data["review_design_hashes"]:
        raise RuntimeError("review design changed after freeze")
    for name, sha in data["protocol_hashes"].items():
        if digest(ROOT / name) != sha:
            raise RuntimeError("experiment protocol changed: " + name)
    for name, sha in data["controller_hashes"].items():
        if digest(CONTROL / name) != sha:
            raise RuntimeError(f"controller changed after freeze: {name}")
    if digest(CONTROL / "private_mapping.json") != data["private_mapping_sha256"]:
        raise RuntimeError("private cross-arm mapping changed after freeze")
    if data.get("arm_config_sha256") and digest(CONTROL / "arm_config.json") != data["arm_config_sha256"]:
        raise RuntimeError("arm configuration changed after freeze")
    if data.get("packet_build_ledger_sha256") and digest(CONTROL / "PACKETS.json") != data["packet_build_ledger_sha256"]:
        raise RuntimeError("packet build ledger changed after freeze")
    for name, sha in data.get("campaign_controller_hashes", {}).items():
        if digest(ROOT.parent / name) != sha:
            raise RuntimeError("campaign controller changed after freeze: " + name)
    for path, sha in data["external_hashes"].items():
        if digest(Path(path)) != sha:
            raise RuntimeError(f"pinned infrastructure changed: {path}")
    for package, expected in data["standard_package_commits"].items():
        package_dir = Path(data["environment"]["standard_root"]) / package
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=package_dir, text=True).strip()
        if actual != expected:
            raise RuntimeError("standard dependency commit changed: " + package)
    if digest(Path(data["codex_binary"])) != data["codex_sha256"]:
        raise RuntimeError("pinned Codex executable changed")
    print("Packet/controller hashes, configured executable/toolchain hashes, and dependency pins verified.")


def runtime_args(run_id: str, extra_read_roots=()) -> tuple[list[str], list[str]]:
    data = frozen()
    packet = ROOT / "runs" / run_id
    read_roots = ["/usr/bin", "/bin", "/usr/local/bin", "/etc/ssl",
                  str(Path(sys.executable).resolve().parent.parent),
                  str(Path(data["codex_binary"]).parent),
                  data["codex_path"], data["environment"]["LEAN_SYSROOT"],
                  data["environment"]["standard_root"]] + list(extra_read_roots)
    entries = ['":minimal"="read"'] + [f'{json.dumps(p)}="read"' for p in read_roots]
    # Request least privilege for every existing input and write access only
    # for output/. The hard integrity boundary is the disposable copy: only
    # output/ is copied back, and validation uses the separately frozen packet.
    workspace = ['"."="read"']
    workspace += [f'{json.dumps(path.name)}="{("write" if path.name == "output" else "read")}"'
                  for path in sorted(packet.iterdir())]
    entries += ['":workspace_roots"={' + ",".join(workspace) + '}']
    config = ["-c", 'default_permissions="stage3_case017_comparison"',
              "-c", 'permissions.stage3_case017_comparison.filesystem={' + ",".join(entries) + "}",
              "-c", 'permissions.stage3_case017_comparison.network={enabled=false}',
              "-c", 'tool_output_token_limit=3000',
              "-c", 'model_auto_compact_token_limit=96000',
              "-c", 'shell_environment_policy.set={LC_ALL="C",LANG="C",PATH=' +
                    json.dumps(data["codex_path"] + ":" + str(Path(sys.executable).resolve().parent) + ":/usr/local/bin:/usr/bin:/bin") + '}',
              # --- OpenRouter transport (see PATCHES.md) ---
              # Codex reaches OpenRouter through the local pinning proxy, which
              # holds the real credential and forces provider.only=["openai"].
              "-c", 'model_provider="openrouter"',
              "-c", 'model_providers.openrouter={name="openrouter",base_url=' +
                    json.dumps(data["proxy_base_url"]) + ',env_key="OPENROUTER_API_KEY"}',
              # A custom provider disables catalog fetch, so values the original
              # run obtained automatically must now be stated. Both are set to
              # the same values the catalog reported.
              "-c", 'model_context_window=' + str(data["model_context_window"]),
              "-c", 'service_tier="default"',
              # `/bin/bash -lc` would otherwise source the host login profile.
              "-c", 'allow_login_shell=false']
    features = []
    for feature in ["apps", "browser_use", "browser_use_external", "in_app_browser", "computer_use",
                    "image_generation", "plugins", "recommended_plugins", "skill_search", "memories",
                    "multi_agent", "multi_agent_v2", "remote_plugin"]:
        features += ["--disable", feature]
    return config, features


def preflight() -> None:
    verify()
    data = frozen()
    rows = []
    for run_id, condition in RUNS.items():
        packet = ROOT / "runs" / run_id
        if not packet.is_dir():
            continue                      # replicate not created yet
        if (ROOT / "logs" / run_id).exists():
            rows.append({"run_id": run_id, "skipped": "already started; "
                         "probing would write into archived output/"})
            continue
        config, _ = runtime_args(run_id)
        with neutral_workspace(packet) as workspace:
            command = [data["codex_binary"], "sandbox", "-C", str(workspace), *config,
                       "-P", "stage3_case017_comparison", "--", sys.executable, "-c",
                       PREFLIGHT_CODE, str(ORIGINAL), str(ROOT), "1" if condition == "PML" else "0"]
            probe_env = dict(os.environ)
            probe_env.pop("OLDPWD", None)
            probe_env["PWD"] = str(workspace)
            result = subprocess.run(command, text=True, capture_output=True, cwd=workspace,
                                    env=probe_env)
        rows.append({"run_id": run_id, "exit_code": result.returncode,
                     "stdout": result.stdout, "stderr": result.stderr})
        if result.returncode:
            save(ROOT / "preflight/RESULTS.json", {"state": "FAILED", "checks": rows})
            raise RuntimeError(f"preflight failed for {run_id}: {result.stdout}\n{result.stderr}")
    save(ROOT / "preflight/RESULTS.json", {"state": "PASS", "checks": rows, "utc": utc(),
         "model_calls": 0})
    verify()
    probed = [r for r in rows if "skipped" not in r]
    print("%d sandbox and Lean environment probe(s) passed (%d skipped); "
          "zero model calls." % (len(probed), len(rows) - len(probed)))


PREFLIGHT_CODE = r'''
import json, os, subprocess, sys
from pathlib import Path
original, experiment, has_research = sys.argv[1:]
cwd = str(Path.cwd())
assert Path(cwd).name == "workspace"
assert Path(cwd).parent.name.startswith("formalization-")
assert not any(marker in cwd for marker in ["libvocab_pml", "libvocab_p_", "run_00"])
assert Path("Stage3Model.lean").is_file()
assert Path("CANONICAL_FULL_PROOF.md").is_file()
assert Path("TargetTemplate.lean").is_file()
assert not Path("MODEL_SPEC.md").exists()
assert not Path("RUN_CONFIG.md").exists()
assert not Path("OBLIGATIONS.md").exists()
assert not Path("OBLIGATION_LEDGER.tsv").exists()
assert len(list(Path("papers").glob("*.pdf"))) == 5
for p in [Path(original)/"GenLimit/Paper12_NoiseLossAndFeedback.lean",
          Path(original)/".lake/build/lib/lean/GenLimit/Paper12_NoiseLossAndFeedback.olean",
          Path(experiment)/"control/private_mapping.json",
          Path(experiment).parent/"stage3_case017_canonical_completion_pilot/runs/pilot_001/output/Case017Formalization.lean"]:
    try:
        p.read_bytes()
    except (PermissionError, FileNotFoundError):
        pass
    else:
        raise AssertionError("unexpected access: " + str(p))
values = json.loads(Path("LEAN_ENV.json").read_text())
markers = ["stage3_case017_libvocab_pml_openrouter_sol",
           "stage3_case017_libvocab_p_openrouter_sol", "PM and PML",
           "for all evidence conditions", "experimental condition",
           "other runs, pilots"]
visible_environment = json.dumps(dict(os.environ, **values))
for marker in markers:
    assert marker not in visible_environment, marker
for path in Path.cwd().rglob("*"):
    rel = path.relative_to(Path.cwd())
    if not path.is_file():
        continue
    content = path.read_bytes()
    file_markers = markers[:2] if rel.parts[0] in {"papers", "research", "vocabulary", "output"} else markers
    for marker in file_markers:
        assert marker.encode() not in content, str(rel) + ": " + marker
env = dict(os.environ, **values)
lean = str(Path(values["LEAN_SYSROOT"])/"bin/lean")
probe = Path("output/PreflightEnvironment.lean")
try:
    probe.write_text("import Stage3Model\n"
                     "#check Stage3Case017.MainClaim\n"
                     "#check GenLimit.Generic.InfinitePartialPresentation\n"
                     "#check GenLimit.Generic.StreamIn\n"
                     "#check GenLimit.NovelGeneratesInLimit\n"
                     "#check GenLimit.GeneratorFirst\n"
                     "#check GenLimit.PatientScope.relativeLowerDensity\n")
    p = subprocess.run([lean, "-j", "1", str(probe)], env=env, text=True, capture_output=True)
    assert p.returncode == 0, p.stdout + p.stderr
    probe.write_text("import GenLimit.Paper12_NoiseLossAndFeedback.FiniteFeedback\n#check GenLimit.NoiseLossFeedback.FeedbackGenerator\n")
    p = subprocess.run([lean, "-j", "1", str(probe)], env=env, text=True, capture_output=True)
    if has_research == "1":
        assert p.returncode == 0, p.stdout + p.stderr
    else:
        forbidden = Path("GenLimit/Paper12_NoiseLossAndFeedback/FiniteFeedback.olean")
        assert not (Path("research/lib/lean") / forbidden).exists()
        assert not (Path("vocabulary/lib/lean") / forbidden).exists()
        assert p.returncode != 0, "forbidden research module unexpectedly imported"
finally:
    probe.unlink(missing_ok=True)
print("PASS shared vocabulary/model/mathlib, isolated frozen originals, hidden original library/pilots/controller, behavioral research import policy")
'''


def check_snapshot(run_id: str, snapshot: Path) -> dict:
    packet = ROOT / "runs" / run_id
    record = json.loads((snapshot / "CAPTURE.json").read_text())
    entry = snapshot / "output/Case017Formalization.lean"
    if not entry.is_file() or not record["stable_capture"]:
        result = dict(record, target_kernel_pass=False, reason="missing root or unstable snapshot")
        save(snapshot / "VALIDATION.json", result)
        return result
    for name in ["Stage3Model.lean", "Stage3Model.olean", "ControllerAudit.lean", "ControllerAudit.olean",
                 "CHECK_DRIVER.py"]:
        shutil.copy2(packet / name, snapshot / name)
    values = json.loads((packet / "LEAN_ENV.json").read_text())
    # Never permit a checkpoint to import a newer author output.
    values["LEAN_PATH"] = checkpoint_lean_path(values, packet, snapshot)
    save(snapshot / "LEAN_ENV.json", values)
    config, _ = runtime_args(run_id, extra_read_roots=[str(packet / name)
        for name in ["papers", "supplement", "research", "vocabulary"] if (packet / name).exists()])
    checker = [frozen()["codex_binary"], "sandbox", "-C", str(snapshot), *config,
               "-P", "stage3_case017_comparison", "--", sys.executable, "-B", "CHECK_DRIVER.py"]
    with (snapshot / "root_check.log").open("w") as out:
        process = subprocess.run(checker + ["--final"], stdout=out, stderr=subprocess.STDOUT)
    gate_path = snapshot / "output/ROOT_GATE.json"
    gate = json.loads(gate_path.read_text()) if gate_path.is_file() else {"target_kernel_pass": False}
    result = dict(record, **{k: v for k, v in gate.items() if k != "source_hashes"})
    result["root_source_hashes"] = gate.get("source_hashes", {})
    result["checker_exit"] = process.returncode
    result["target_kernel_pass"] = bool(process.returncode == 0 and gate.get("target_kernel_pass"))
    # Always keep the root result fixed before attempting auxiliary analysis.
    save(snapshot / "VALIDATION.json", result)
    try:
        if gate.get("entry_compile_exit") == 0 and not result["target_kernel_pass"]:
            with (snapshot / "inventory_check.log").open("w") as out:
                inventory = subprocess.run(checker + ["--inventory"], stdout=out, stderr=subprocess.STDOUT)
            result["inventory_analysis_exit"] = inventory.returncode
        if result["target_kernel_pass"]:
            with (snapshot / "dependency_check.log").open("w") as out:
                dep = subprocess.run(checker + ["--dependencies"], stdout=out, stderr=subprocess.STDOUT)
            result["dependency_analysis_exit"] = dep.returncode
            graph = snapshot / "output/DEPENDENCIES.json"
            if dep.returncode == 0 and graph.is_file():
                manifest = packet / "RESEARCH_MODULES.tsv"
                modules = set()
                if manifest.is_file():
                    with manifest.open() as handle:
                        modules = {r["module"] for r in csv.DictReader(handle, delimiter="\t")}
                local_modules = {name[:-5].replace("/", ".") for name in record["source_hashes"]}
                save(snapshot / "REUSE.json", reuse_summary(json.loads(graph.read_text()), modules - local_modules))
    except Exception as exc:
        result["auxiliary_analysis_error"] = str(exc)
    save(snapshot / "VALIDATION.json", result)
    return result


def validate(run_id: str) -> dict:
    verify()
    packet = ROOT / "runs" / run_id
    output = packet / "output"
    logs = ROOT / "logs" / run_id
    if not (logs / "STATUS.json").is_file():
        raise RuntimeError("cannot validate an unstarted author run")
    status_record = json.loads((logs / "STATUS.json").read_text())
    if status_record["state"] == "RUNNING":
        raise RuntimeError("post-run validation requires the author to have stopped")
    result_dir = ROOT / "results" / run_id
    result_dir.mkdir(parents=True, exist_ok=True)
    final = logs / "checkpoints/final"
    if not final.exists():
        capture(output, final, status_record["elapsed_seconds"], "final_artifact")
    checked = []
    for snapshot in sorted((logs / "checkpoints").iterdir()):
        if snapshot.is_dir():
            try:
                check = check_snapshot(run_id, snapshot)
            except Exception as exc:
                check = {"target_kernel_pass": False, "stable_capture": False,
                         "checkpoint_error": str(exc)}
            check["checkpoint"] = snapshot.name
            checked.append(check)
    # The final cutoff is recorded separately from first observed successful
    # checking. No post-budget proof edit is permitted.
    eligible = [c for c in checked if c["target_kernel_pass"] and c["stable_capture"]
                and (c["kind"] == "final_artifact" or c["elapsed_seconds"] <= frozen()["seconds_per_run"])]
    result = {"run_id": run_id, "checked_utc": utc(), "checkpoints": checked,
              "primary_success": bool(eligible), "target_kernel_pass": bool(eligible),
              "final_artifact_kernel_pass": next((c["target_kernel_pass"] for c in checked if c["checkpoint"] == "final"), False),
              "semantic_review_required": False, "partial_review_eligible": not bool(eligible),
              "selected_checkpoint": min(eligible, key=lambda c: c["elapsed_seconds"])["checkpoint"] if eligible else None,
              "author_status": status_record}
    result["efficiency"] = efficiency(logs / "timestamped_events.jsonl", checked)
    # Metadata is diagnostic only; no branch here can invalidate a theorem.
    reports = {}
    for name in ["STATUS.md"]:
        path = output / name
        reports[name] = {"present": path.is_file()}
        if path.is_file():
            text = path.read_text()
            reports[name].update({"sha256": digest(path), "words": len(text.split()),
                                  "within_word_limit": len(text.split()) <= 500})
    result["auxiliary_reports"] = reports
    files = [p for p in output.rglob("*.lean") if not p.name.startswith("Controller")]
    result["author_lean_size"] = {"files": len(files), "bytes": sum(p.stat().st_size for p in files),
                                 "lines": sum(len(p.read_text().splitlines()) for p in files),
                                 "scope": "All retained author Lean, including unimported scratch; not a quality score."}
    if result["selected_checkpoint"]:
        selected = logs / "checkpoints" / result["selected_checkpoint"]
        selected_check = next(c for c in checked if c["checkpoint"] == result["selected_checkpoint"])
        certified = [selected / "output" / name for name in selected_check["root_source_hashes"]]
        result["certified_lean_size"] = {"files": len(certified),
            "bytes": sum(p.stat().st_size for p in certified),
            "lines": sum(len(p.read_text().splitlines()) for p in certified),
            "scope": "Author source closure of selected certified checkpoint, excluding frozen research library."}
        if (selected / "REUSE.json").is_file():
            shutil.copy2(selected / "REUSE.json", result_dir / "REUSE.json")
    save(result_dir / "VALIDATION.json", result)
    print(json.dumps({k: result[k] for k in ["run_id", "primary_success", "partial_review_eligible"]}))
    return result


def run_author(run_id: str) -> None:
    verify()
    data = frozen()
    report = ROOT / "preflight/RESULTS.json"
    if not report.is_file() or json.loads(report.read_text())["state"] != "PASS":
        raise RuntimeError("all non-generative preflights must pass before author launch")
    regression = ROOT / "preflight/REGRESSION.json"
    if not regression.is_file() or json.loads(regression.read_text())["state"] != "PASS":
        raise RuntimeError("root-gate regression tests must pass before author launch")
    tested = json.loads(regression.read_text())
    for key, filename in [("checker_sha256", "check_driver.py"), ("audit_sha256", "ControllerAudit.lean"),
                          ("metrics_sha256", "measurements.py"), ("controller_sha256", "experiment.py")]:
        if tested.get(key) != digest(CONTROL / filename):
            raise RuntimeError("regression results are stale: " + filename)
    if not tested.get("sandbox_snapshot_tested"):
        raise RuntimeError("the real sandbox snapshot regression must pass before launch")
    # Transport prerequisites are checked before `logs.mkdir()`: once that
    # directory exists the controller refuses to reuse the packet, so a fault
    # found later would lock this run out with no retry authorized.
    OpenRouterProxy.precheck(data)
    packet = ROOT / "runs" / run_id
    logs = ROOT / "logs" / run_id
    if logs.exists() or any((packet / "output").iterdir()):
        raise RuntimeError("refusing to rerun or overwrite a started packet")
    logs.mkdir()
    proxy = OpenRouterProxy(data, logs)
    config, features = runtime_args(run_id)
    prompt = (CONTROL / "AUTHOR_PROMPT.txt").read_text()
    status_record = {"run_id": run_id, "state": "RUNNING", "started_utc": utc(),
                     "author_budget_seconds": data["seconds_per_run"]}
    monitor_errors = []
    def interrupted(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    with neutral_workspace(packet) as workspace:
        command = [data["codex_binary"], "-a", "never", "-m", data["model"],
                   "-C", str(workspace), "exec", "--skip-git-repo-check", "--ephemeral",
                   "--ignore-user-config", "--ignore-rules", "--strict-config", *features,
                   "-c", 'default_permissions="stage3_case017_comparison"', *config,
                   "-c", 'model_reasoning_effort="medium"', "-c", 'model_verbosity="medium"',
                   "--color", "never", "--json", prompt]
        save(logs / "STATUS.json", status_record)
        start = time.monotonic()
        try:
            with proxy, (logs / "stderr.log").open("w") as err:
                # Discard inherited provider credentials and model overrides.
                author_env = {k: v for k, v in os.environ.items()
                              if not k.startswith(("CODEX_", "OPENAI_", "ANTHROPIC_", "CLAUDE_"))}
                author_env.pop("OLDPWD", None)
                author_env["PWD"] = str(workspace)
                # The author receives a throwaway local token, never the real credential.
                author_env["OPENROUTER_API_KEY"] = proxy.local_token
                proc = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                        stderr=err, start_new_session=True, text=True, bufsize=1,
                                        env=author_env, cwd=workspace)
                def monitor():
                    checkpoint_no = 0
                    with (logs / "events.jsonl").open("w") as raw, \
                            (logs / "timestamped_events.jsonl").open("w") as journal:
                        for line in proc.stdout:
                            elapsed = time.monotonic() - start
                            raw.write(line); raw.flush()
                            try:
                                event = json.loads(line)
                                journal.write(json.dumps({"elapsed_seconds": elapsed, "event": event}) + "\n")
                                journal.flush()
                                for gate in gate_messages(event):
                                    if gate.get("target_kernel_pass") and elapsed <= data["seconds_per_run"]:
                                        checkpoint_no += 1
                                        capture(workspace / "output", logs / "checkpoints" / f"{checkpoint_no:04d}",
                                                elapsed, "observed_gate", gate.get("source_hashes"))
                            except Exception as exc:
                                monitor_errors.append({"elapsed_seconds": elapsed, "error": str(exc)})
                reader = threading.Thread(target=monitor, daemon=True)
                reader.start()
                try:
                    proc.wait(timeout=max(0, data["seconds_per_run"] - (time.monotonic() - start)))
                    status_record["state"] = "FINISHED" if proc.returncode == 0 else "AUTHOR_ERROR"
                except subprocess.TimeoutExpired:
                    status_record["state"] = "TIMEOUT"
                    os.killpg(proc.pid, signal.SIGKILL); proc.wait()
                except KeyboardInterrupt:
                    status_record["state"] = "ABORTED_USER_INTERRUPT"
                    os.killpg(proc.pid, signal.SIGKILL); proc.wait()
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stopped = time.monotonic() - start
                reader.join(timeout=10)
                status_record.update({"exit_code": proc.returncode, "ended_utc": utc(),
                    "elapsed_seconds": round(stopped, 6), "monitor_errors": monitor_errors,
                    "monitor_finished": not reader.is_alive(),
                    "deadline_overshoot_seconds": max(0, stopped - data["seconds_per_run"])})
        finally:
            shutil.copytree(workspace / "output", packet / "output", dirs_exist_ok=True)
    status_record["routing_audit"] = proxy.audit(logs)
    save(logs / "STATUS.json", status_record)
    validate(run_id)


def status() -> None:
    for run in RUNS:
        path = ROOT / "logs" / run / "STATUS.json"
        print(json.dumps(json.loads(path.read_text()) if path.is_file() else
                         {"run_id": run, "state": "NOT_STARTED", "condition": RUNS[run]}))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["prepare", "verify", "preflight", "run", "validate", "status"])
    parser.add_argument("run_id", nargs="?", choices=list(RUNS))
    args = parser.parse_args()
    if args.action == "prepare":
        prepare()
    elif args.action == "verify":
        verify()
    elif args.action == "preflight":
        preflight()
    elif args.action == "status":
        status()
    else:
        if not args.run_id:
            parser.error("run/validate requires run_id")
        (run_author if args.action == "run" else validate)(args.run_id)


if __name__ == "__main__":
    main()
