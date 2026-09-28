#!/usr/bin/env python3
"""Build the five-task canonical-proof high-vs-medium report from frozen evidence.

This script is deliberately outside every source bundle.  It is a post-run,
read-only consumer of the independently validated artifacts and therefore does
not alter any submitted scientific input or source-manifest hash.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import re
import statistics
from collections import OrderedDict
from datetime import datetime, timedelta, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
REPORT = ROOT / "reports" / "CANONICAL_REASONING_HIGH_VS_MEDIUM_EXPERIMENT.md"
OUT_DIR = ROOT / "reports" / "reasoning_medium_v1"
ARMS = ("P", "PML", "PML-FileOracle")
ARM_SLUG = {"P": "p", "PML": "pml", "PML-FileOracle": "file_oracle"}
TOKEN_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
)
LOGICAL_KINDS = {"theorem", "definition", "opaque"}
PERMITTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

TASKS = OrderedDict(
    [
        (
            "s2b",
            {
                "title": "S2-B",
                "bundle": "lean2paper_s2b_reasoning_medium_v1",
                "high_table": "reports/s2b_delta_v1/S2B_RUN_LEVEL_RESULTS.csv",
                "high_kind": "csv",
            },
        ),
        (
            "case017",
            {
                "title": "Case 017",
                "bundle": "lean2paper_case017_reasoning_medium_v1",
                "high_table": "reports/case017_delta_v1/CASE017_FIVE_RUN_SUMMARY.json",
                "high_kind": "case017_json",
            },
        ),
        (
            "case019",
            {
                "title": "Case 019",
                "bundle": "lean2paper_case019_reasoning_medium_v1",
                "high_table": "reports/case019_delta_v1/CASE019_RUN_LEVEL_RESULTS.csv",
                "high_kind": "csv",
            },
        ),
        (
            "case024",
            {
                "title": "Case 024",
                "bundle": "lean2paper_case024_reasoning_medium_v1",
                "high_table": "reports/case024_delta_v1/CASE024_RUN_LEVEL_RESULTS.csv",
                "high_kind": "csv",
            },
        ),
        (
            "case025",
            {
                "title": "Case 025",
                "bundle": "lean2paper_case025_reasoning_medium_v1",
                "high_table": "reports/case025_delta_v1/CASE025_RUN_LEVEL_RESULTS.csv",
                "high_kind": "csv",
            },
        ),
    ]
)


def load(path: Path):
    with path.open(encoding="utf-8") as stream:
        return json.load(stream)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def parse_utc(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def parse_bool(value) -> bool:
    if isinstance(value, bool):
        return value
    if str(value).lower() in {"true", "1", "yes"}:
        return True
    if str(value).lower() in {"false", "0", "no"}:
        return False
    raise ValueError(f"not a boolean: {value!r}")


def optional_float(value):
    if value in (None, "", "null", "None"):
        return None
    return float(value)


def run_number(run_id: str) -> int:
    match = re.search(r"_r([1-5])(?:$|_)", run_id)
    if not match:
        raise ValueError(f"cannot parse replicate from {run_id}")
    return int(match.group(1))


def stats(values: list[float]) -> dict:
    if not values:
        return {
            "count": 0,
            "sum": 0.0,
            "mean": None,
            "median": None,
            "minimum": None,
            "maximum": None,
            "sample_stdev": None,
        }
    return {
        "count": len(values),
        "sum": sum(values),
        "mean": statistics.mean(values),
        "median": statistics.median(values),
        "minimum": min(values),
        "maximum": max(values),
        "sample_stdev": statistics.stdev(values) if len(values) > 1 else None,
    }


def wilson(successes: int, runs: int, z: float = 1.959963984540054) -> list[float]:
    proportion = successes / runs
    denominator = 1 + z * z / runs
    center = (proportion + z * z / (2 * runs)) / denominator
    half = z * math.sqrt(
        proportion * (1 - proportion) / runs + z * z / (4 * runs * runs)
    ) / denominator
    return [center - half, center + half]


def duration(value: float | None) -> str:
    if value is None:
        return "—"
    seconds = int(round(value))
    hours, remainder = divmod(seconds, 3600)
    minutes, seconds = divmod(remainder, 60)
    if hours:
        return f"{hours}h {minutes:02d}m {seconds:02d}s"
    return f"{minutes}m {seconds:02d}s"


def money(value: float | None) -> str:
    return "—" if value is None else f"${value:,.4f}"


def integer(value: int | float | None) -> str:
    return "—" if value is None else f"{int(value):,}"


def percent_change(old: float, new: float) -> str:
    if old == 0:
        return "—"
    return f"{100 * (new / old - 1):+.1f}%"


def selected_reuse(arm_root: Path, run_id: str, validation: dict) -> dict | None:
    selected = validation.get("selected_checkpoint")
    if selected is None:
        return None
    record = next(
        item for item in validation["checkpoints"] if item["checkpoint"] == selected
    )
    checkpoint = arm_root / "logs" / run_id / "checkpoints" / selected
    reuse_path = checkpoint / "REUSE.json"
    graph_path = checkpoint / "output" / "DEPENDENCIES.json"
    if not reuse_path.is_file() or not graph_path.is_file():
        raise RuntimeError(f"{run_id}: selected dependency evidence is missing")
    reuse = load(reuse_path)
    graph = load(graph_path)
    research = sum(
        item.get("kind") in LOGICAL_KINDS for item in reuse["research_declarations"]
    )
    author_modules: set[str] = set()
    for name in record["root_source_hashes"]:
        module = Path(name).with_suffix("").as_posix().replace("/", ".")
        author_modules.update({module, Path(module).name, f"output.{module}"})
    author = sum(
        item.get("kind") in LOGICAL_KINDS and item.get("module") in author_modules
        for item in graph["nodes"]
    )
    root_lines = 0
    for name in record["root_source_hashes"]:
        source = checkpoint / "output" / name
        if not source.is_file():
            raise RuntimeError(f"{run_id}: selected root source is missing: {name}")
        root_lines += len(source.read_text(encoding="utf-8").splitlines())
    return {
        "research_logical_declarations": research,
        "author_logical_declarations": author,
        "reuse_share": research / (research + author) if research + author else None,
        "author_root_lines": root_lines,
        "reuse_path": relative(reuse_path),
        "reuse_sha256": sha256(reuse_path),
        "dependencies_path": relative(graph_path),
        "dependencies_sha256": sha256(graph_path),
    }


def proxy_usage(log_path: Path) -> tuple[int, dict[str, int]]:
    """Sum authoritative per-call provider usage from the local proxy log."""
    totals = {field: 0 for field in TOKEN_FIELDS}
    calls = 0
    for line in log_path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        record = json.loads(line)
        if not record.get("path", "").startswith("/v1/responses"):
            continue
        usage = record.get("usage")
        if not isinstance(usage, dict):
            raise RuntimeError(f"{relative(log_path)}: response call lacks usage")
        calls += 1
        totals["input_tokens"] += int(usage.get("input_tokens", 0))
        totals["cached_input_tokens"] += int(
            usage.get("input_tokens_details", {}).get("cached_tokens", 0)
        )
        totals["cache_write_input_tokens"] += int(
            usage.get("input_tokens_details", {}).get("cache_write_tokens", 0)
        )
        totals["output_tokens"] += int(usage.get("output_tokens", 0))
        totals["reasoning_output_tokens"] += int(
            usage.get("output_tokens_details", {}).get("reasoning_tokens", 0)
        )
    return calls, totals


def collect_medium_rows() -> tuple[list[dict], list[dict]]:
    rows: list[dict] = []
    missing: list[dict] = []
    for task, config in TASKS.items():
        bundle = ROOT / config["bundle"]
        campaign = load(bundle / "CAMPAIGN.json")
        expected_protocol = {
            "model": "openai/gpt-5.6-sol",
            "reasoning_effort": "medium",
            "seconds_per_run": 5400,
            "provider_pin": {"only": ["openai"], "allow_fallbacks": False},
        }
        for field, expected in expected_protocol.items():
            if campaign.get(field) != expected:
                raise RuntimeError(
                    f"{task}: campaign {field} is {campaign.get(field)!r}, expected {expected!r}"
                )
        if campaign.get("replicates_per_arm") != 5:
            raise RuntimeError(f"{task}: expected five replicates per arm")
        reviews = list((bundle / "cohort").rglob("REVIEW.json"))
        if reviews:
            raise RuntimeError(f"{task}: reviewer output unexpectedly present: {reviews}")

        for arm in ARMS:
            spec = campaign["arms"][arm]
            if spec["slug"] != ARM_SLUG[arm] or len(spec["run_ids"]) != 5:
                raise RuntimeError(f"{task}/{arm}: malformed run inventory")
            arm_root = bundle / "cohort" / "arms" / spec["slug"]
            for run_id in spec["run_ids"]:
                validation_path = arm_root / "results" / run_id / "VALIDATION.json"
                status_path = arm_root / "logs" / run_id / "STATUS.json"
                routing_path = arm_root / "logs" / run_id / "ROUTING_AUDIT.json"
                absent = [
                    relative(path)
                    for path in (validation_path, status_path, routing_path)
                    if not path.is_file()
                ]
                if absent:
                    missing.append({"task": task, "arm": arm, "run_id": run_id, "missing": absent})
                    continue

                validation = load(validation_path)
                status = load(status_path)
                routing = load(routing_path)
                if validation.get("run_id") != run_id or status.get("run_id") != run_id:
                    raise RuntimeError(f"{run_id}: run identity mismatch")
                author_state = status.get("state")
                if author_state not in {"FINISHED", "TIMEOUT"}:
                    raise RuntimeError(f"{run_id}: non-terminal author state {author_state}")
                # A controller-enforced scientific timeout is a valid terminal
                # observation, not an infrastructure error.  The controller
                # kills the author process group with SIGKILL exactly at the
                # frozen 5,400-second budget, so Python records exit code -9.
                # Accept it only when the full budget was actually delivered
                # and the event monitor shut down cleanly; shorter/unclean
                # terminations remain fail-closed infrastructure errors.
                if author_state == "FINISHED":
                    valid_terminal_exit = status.get("exit_code") == 0
                else:
                    budget = float(status.get("author_budget_seconds", 0))
                    elapsed = float(status.get("elapsed_seconds", 0))
                    overshoot = float(status.get("deadline_overshoot_seconds", 0))
                    valid_terminal_exit = (
                        status.get("exit_code") == -9
                        and budget == 5400
                        and elapsed >= budget
                        and 0 <= overshoot <= 10
                    )
                if (
                    not valid_terminal_exit
                    or status.get("monitor_errors")
                    or status.get("monitor_finished") is not True
                ):
                    raise RuntimeError(f"{run_id}: author/controller error")
                embedded = status.get("routing_audit", {})
                if not routing.get("pass") or not embedded.get("pass"):
                    raise RuntimeError(f"{run_id}: routing audit failed")
                if routing.get("unverifiable") != 0:
                    raise RuntimeError(f"{run_id}: unverifiable upstream calls")
                if set(routing.get("providers", {})) != {"OpenAI"}:
                    raise RuntimeError(f"{run_id}: provider was not exclusively OpenAI")
                if routing.get("calls") != embedded.get("calls"):
                    raise RuntimeError(f"{run_id}: routing call-count mismatch")

                observations = validation["efficiency"]["usage_observations"]
                proxy_calls, proxy_totals = proxy_usage(
                    arm_root / "logs" / run_id / "proxy_requests.jsonl"
                )
                if proxy_calls != int(routing["calls"]):
                    raise RuntimeError(f"{run_id}: proxy/routing call-count mismatch")
                if len(observations) == 1:
                    usage = observations[0]["usage"]
                    if any(int(usage[field]) != proxy_totals[field] for field in TOKEN_FIELDS):
                        raise RuntimeError(f"{run_id}: event/proxy usage mismatch")
                elif not observations and author_state == "TIMEOUT":
                    # Codex is deliberately SIGKILLed at the frozen budget and
                    # therefore may not emit its final cumulative usage event.
                    # Every completed upstream response is still recorded by
                    # the controller-owned proxy, whose per-call totals match
                    # the cumulative event exactly on normally finished runs.
                    usage = proxy_totals
                else:
                    raise RuntimeError(f"{run_id}: invalid usage observations")
                first_valid = validation["efficiency"][
                    "first_valid_observed_pass_seconds"
                ]
                success = bool(validation["primary_success"])
                if success != (first_valid is not None):
                    raise RuntimeError(f"{run_id}: success/first-valid mismatch")
                if bool(validation.get("target_kernel_pass")) != success:
                    raise RuntimeError(f"{run_id}: primary/target-kernel mismatch")

                selected = validation.get("selected_checkpoint")
                selected_record = next(
                    (
                        item
                        for item in validation["checkpoints"]
                        if item["checkpoint"] == selected
                    ),
                    None,
                )
                allowed_axioms: list[str] = []
                if success:
                    if selected_record is None:
                        raise RuntimeError(f"{run_id}: successful run lacks selected checkpoint")
                    allowed_axioms = sorted(
                        {
                            axiom
                            for names in selected_record.get("axioms", {}).values()
                            for axiom in names
                        }
                    )
                    invariants = {
                        "target_kernel_pass": selected_record.get("target_kernel_pass") is True,
                        "entry_compile_exit": selected_record.get("entry_compile_exit") == 0,
                        "exact_target_compile_exit": selected_record.get("exact_target_compile_exit") == 0,
                        "dependency_analysis_exit": selected_record.get("dependency_analysis_exit") == 0,
                        "stable_capture": selected_record.get("stable_capture") is True,
                        "sources_unchanged": selected_record.get("sources_unchanged_during_check") is True,
                        "no_inadmissible_axioms": not selected_record.get("inadmissible_axioms"),
                        "no_prohibited_mechanisms": not selected_record.get("prohibited_mechanisms"),
                        "permitted_axioms_only": set(allowed_axioms) <= PERMITTED_AXIOMS,
                    }
                    failed = [name for name, passed in invariants.items() if not passed]
                    if failed:
                        raise RuntimeError(f"{run_id}: selected-checkpoint failures: {failed}")

                cost_to_first = None
                calls_to_first = None
                if first_valid is not None:
                    cutoff = parse_utc(status["started_utc"]) + timedelta(
                        seconds=float(first_valid)
                    )
                    eligible = [
                        call
                        for call in routing["audit"]
                        if call.get("utc") and parse_utc(call["utc"]) <= cutoff
                    ]
                    calls_to_first = len(eligible)
                    cost_to_first = sum(
                        float(call.get("usage_usd") or 0.0) for call in eligible
                    )

                row = {
                    "task": task,
                    "task_title": config["title"],
                    "arm": arm,
                    "replicate": run_number(run_id),
                    "run_id": run_id,
                    "author_state": status["state"],
                    "primary_success": success,
                    "target_kernel_pass": bool(validation["target_kernel_pass"]),
                    "selected_checkpoint": selected,
                    "first_valid_seconds": first_valid,
                    "author_elapsed_seconds": float(status["elapsed_seconds"]),
                    "started_utc": status["started_utc"],
                    "ended_utc": status["ended_utc"],
                    "model_calls": int(routing["calls"]),
                    "provider": "OpenAI",
                    "served_models": sorted(
                        {call.get("model") for call in routing["audit"] if call.get("model")}
                    ),
                    "total_upstream_usd": float(routing["total_upstream_usd"]),
                    "cost_to_first_valid_usd": cost_to_first,
                    "calls_to_first_valid": calls_to_first,
                    "allowed_axioms": allowed_axioms,
                    "reuse": selected_reuse(arm_root, run_id, validation) if success else None,
                    "validation_path": relative(validation_path),
                    "validation_sha256": sha256(validation_path),
                    "status_path": relative(status_path),
                    "status_sha256": sha256(status_path),
                    "routing_audit_path": relative(routing_path),
                    "routing_audit_sha256": sha256(routing_path),
                }
                for field in TOKEN_FIELDS:
                    row[field] = int(usage[field])
                row["non_reasoning_output_tokens"] = (
                    row["output_tokens"] - row["reasoning_output_tokens"]
                )
                if row["non_reasoning_output_tokens"] < 0:
                    raise RuntimeError(f"{run_id}: reasoning tokens exceed output tokens")
                rows.append(row)

    if missing:
        return rows, missing
    expected = len(TASKS) * len(ARMS) * 5
    if len(rows) != expected:
        raise RuntimeError(f"expected {expected} medium rows, found {len(rows)}")
    order = {name: index for index, name in enumerate(TASKS)}
    rows.sort(key=lambda row: (order[row["task"]], ARMS.index(row["arm"]), row["replicate"]))
    return rows, []


def normalize_high_csv(task: str, source: dict) -> dict:
    if task == "case024":
        success = parse_bool(source["final_success"])
        calls = int(source["total_api_calls"])
        cost = float(source["total_api_cost_usd"])
        reasoning = int(source["reasoning_tokens"])
        first_valid = optional_float(source["seconds_to_first_valid"])
        cost_to_first = optional_float(source["api_cost_usd_to_first_valid"])
    else:
        success = parse_bool(source["primary_success"])
        calls = int(source["model_calls"])
        cost = float(source["total_upstream_usd"])
        reasoning = int(source["reasoning_output_tokens"])
        first_valid = optional_float(source.get("first_valid_seconds"))
        cost_to_first = optional_float(source.get("cost_to_first_valid_usd"))
    return {
        "task": task,
        "task_title": TASKS[task]["title"],
        "arm": source["arm"],
        "replicate": int(source["replicate"]),
        "run_id": source["run_id"],
        "primary_success": success,
        "author_elapsed_seconds": float(source["author_elapsed_seconds"]),
        "model_calls": calls,
        "total_upstream_usd": cost,
        "first_valid_seconds": first_valid,
        "cost_to_first_valid_usd": cost_to_first,
        "input_tokens": int(source["input_tokens"]),
        "cached_input_tokens": int(source["cached_input_tokens"]),
        "cache_write_input_tokens": int(source["cache_write_input_tokens"]),
        "output_tokens": int(source["output_tokens"]),
        "reasoning_output_tokens": reasoning,
        "non_reasoning_output_tokens": int(source["output_tokens"]) - reasoning,
    }


def collect_high_rows() -> list[dict]:
    rows: list[dict] = []
    for task, config in TASKS.items():
        path = ROOT / config["high_table"]
        if config["high_kind"] == "case017_json":
            for source in load(path)["runs"]:
                usage = source["usage"]
                reasoning = int(usage["reasoning_output_tokens"])
                rows.append(
                    {
                        "task": task,
                        "task_title": config["title"],
                        "arm": source["arm"],
                        "replicate": run_number(source["run_id"]),
                        "run_id": source["run_id"],
                        "primary_success": bool(source["primary_success"]),
                        "author_elapsed_seconds": float(source["author_elapsed_seconds"]),
                        "model_calls": int(source["total_api_calls"]),
                        "total_upstream_usd": float(source["total_api_cost_usd"]),
                        "first_valid_seconds": optional_float(source["seconds_to_first_valid"]),
                        "cost_to_first_valid_usd": optional_float(
                            source["api_cost_usd_to_first_valid"]
                        ),
                        "input_tokens": int(usage["input_tokens"]),
                        "cached_input_tokens": int(usage["cached_input_tokens"]),
                        "cache_write_input_tokens": int(
                            usage["cache_write_input_tokens"]
                        ),
                        "output_tokens": int(usage["output_tokens"]),
                        "reasoning_output_tokens": reasoning,
                        "non_reasoning_output_tokens": int(usage["output_tokens"])
                        - reasoning,
                    }
                )
        else:
            with path.open(newline="", encoding="utf-8") as stream:
                rows.extend(
                    normalize_high_csv(task, source)
                    for source in csv.DictReader(stream)
                )
        current = [row for row in rows if row["task"] == task]
        if len(current) != 15:
            raise RuntimeError(f"{task}: expected 15 high rows, found {len(current)}")
        for arm in ARMS:
            reps = sorted(row["replicate"] for row in current if row["arm"] == arm)
            if reps != [1, 2, 3, 4, 5]:
                raise RuntimeError(f"{task}/{arm}: malformed high replicate inventory {reps}")
    if len(rows) != 75:
        raise RuntimeError(f"expected 75 high rows, found {len(rows)}")
    return rows


def aggregate(rows: list[dict]) -> dict:
    if not rows:
        raise ValueError("cannot aggregate an empty row set")
    successes = sum(row["primary_success"] for row in rows)
    result = {
        "runs": len(rows),
        "successes": successes,
        "failures": len(rows) - successes,
        "success_rate": successes / len(rows),
        "success_rate_wilson_95": wilson(successes, len(rows)),
        "model_calls": sum(row["model_calls"] for row in rows),
        "total_upstream_usd": sum(row["total_upstream_usd"] for row in rows),
        "cost_to_first_valid_successes_usd": sum(
            row["cost_to_first_valid_usd"] or 0.0 for row in rows
        ),
        "author_elapsed_seconds": stats(
            [row["author_elapsed_seconds"] for row in rows]
        ),
        "first_valid_seconds_successes": stats(
            [
                row["first_valid_seconds"]
                for row in rows
                if row["first_valid_seconds"] is not None
            ]
        ),
        "cost_to_first_valid_successes": stats(
            [
                row["cost_to_first_valid_usd"]
                for row in rows
                if row["cost_to_first_valid_usd"] is not None
            ]
        ),
    }
    for field in TOKEN_FIELDS + ("non_reasoning_output_tokens",):
        result[field] = sum(row[field] for row in rows)
    result["total_tokens"] = result["input_tokens"] + result["output_tokens"]
    result["cache_hit_fraction_of_input"] = (
        result["cached_input_tokens"] / result["input_tokens"]
        if result["input_tokens"]
        else None
    )
    reuse_rows = [row["reuse"] for row in rows if row.get("reuse") is not None]
    research = sum(row["research_logical_declarations"] for row in reuse_rows)
    author = sum(row["author_logical_declarations"] for row in reuse_rows)
    result["reuse"] = {
        "successful_runs_with_evidence": len(reuse_rows),
        "research_logical_declarations": research,
        "author_logical_declarations": author,
        "pooled_research_share": research / (research + author)
        if research + author
        else None,
        "author_root_lines": stats([row["author_root_lines"] for row in reuse_rows]),
    }
    return result


def grouped(rows: list[dict]) -> dict:
    by_task = {}
    by_task_arm = {}
    for task in TASKS:
        task_rows = [row for row in rows if row["task"] == task]
        by_task[task] = aggregate(task_rows)
        for arm in ARMS:
            by_task_arm[f"{task}/{arm}"] = aggregate(
                [row for row in task_rows if row["arm"] == arm]
            )
    return {
        "overall": aggregate(rows),
        "by_task": by_task,
        "by_task_arm": by_task_arm,
    }


def report_results(medium: dict, high: dict, rows: list[dict]) -> str:
    generated = datetime.now(timezone.utc).isoformat()
    lines = [
        "",
        f"Final post-run aggregation generated at `{generated}` from 75 independently validated medium runs.",
        "The high cohort contains the corresponding 75 canonical-proof runs. No reviewer stage is used.",
        "",
        "### Overall comparison",
        "",
        "| Reasoning | Lean success | API calls | API cost | Input tokens | Output tokens | Reasoning output¹ | Non-reasoning output¹ | Mean author time |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for label, data in (("High", high["overall"]), ("Medium", medium["overall"])):
        lines.append(
            f"| {label} | {data['successes']}/{data['runs']} ({data['success_rate']:.1%}) "
            f"| {data['model_calls']:,} | {money(data['total_upstream_usd'])} "
            f"| {data['input_tokens']:,} | {data['output_tokens']:,} "
            f"| {data['reasoning_output_tokens']:,} | {data['non_reasoning_output_tokens']:,} "
            f"| {duration(data['author_elapsed_seconds']['mean'])} |"
        )
    lines += [
        "",
        "¹ Provider telemetry reports reasoning output as a subset of output tokens. Non-reasoning output is `output_tokens − reasoning_output_tokens`; neither subset is added again to total tokens.",
        "",
        "### Task-level high versus medium",
        "",
        "| Task | High Lean | Medium Lean | High cost | Medium cost | Cost change | High calls | Medium calls | High mean time | Medium mean time |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for task, config in TASKS.items():
        old = high["by_task"][task]
        new = medium["by_task"][task]
        lines.append(
            f"| {config['title']} | {old['successes']}/15 | {new['successes']}/15 "
            f"| {money(old['total_upstream_usd'])} | {money(new['total_upstream_usd'])} "
            f"| {percent_change(old['total_upstream_usd'], new['total_upstream_usd'])} "
            f"| {old['model_calls']:,} | {new['model_calls']:,} "
            f"| {duration(old['author_elapsed_seconds']['mean'])} "
            f"| {duration(new['author_elapsed_seconds']['mean'])} |"
        )
    lines += [
        "",
        "### Task × arm comparison",
        "",
        "| Task | Arm | High Lean | Medium Lean | High cost | Medium cost | Cost Δ | High input | Medium input | High reasoning | Medium reasoning | High mean time | Medium mean time |",
        "|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for task, config in TASKS.items():
        for arm in ARMS:
            key = f"{task}/{arm}"
            old = high["by_task_arm"][key]
            new = medium["by_task_arm"][key]
            lines.append(
                f"| {config['title']} | {arm} | {old['successes']}/5 | {new['successes']}/5 "
                f"| {money(old['total_upstream_usd'])} | {money(new['total_upstream_usd'])} "
                f"| {percent_change(old['total_upstream_usd'], new['total_upstream_usd'])} "
                f"| {old['input_tokens']:,} | {new['input_tokens']:,} "
                f"| {old['reasoning_output_tokens']:,} | {new['reasoning_output_tokens']:,} "
                f"| {duration(old['author_elapsed_seconds']['mean'])} "
                f"| {duration(new['author_elapsed_seconds']['mean'])} |"
            )
    lines += [
        "",
        "### Medium token, cost, and time detail",
        "",
        "| Task | Cached input | Cache-write input | Output | Reasoning output | Non-reasoning output | Cost to first valid² | Mean first valid² | Total author time³ |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for task, config in TASKS.items():
        data = medium["by_task"][task]
        lines.append(
            f"| {config['title']} | {data['cached_input_tokens']:,} "
            f"| {data['cache_write_input_tokens']:,} | {data['output_tokens']:,} "
            f"| {data['reasoning_output_tokens']:,} | {data['non_reasoning_output_tokens']:,} "
            f"| {money(data['cost_to_first_valid_successes_usd'])} "
            f"| {duration(data['first_valid_seconds_successes']['mean'])} "
            f"| {duration(data['author_elapsed_seconds']['sum'])} |"
        )
    lines += [
        "",
        "² Defined only for successful runs and measured at the first independently observed valid Lean gate. Full-run cost includes failed runs. ³ Sum across independent author runs, not campaign makespan or queue time.",
        "",
        "### Medium library-code reuse",
        "",
        "The reuse metric follows the earlier case reports: within the transitive dependency closure of the kernel-checked `stage3_result`, it counts research-tree theorem/definition/opaque declarations over research plus author declarations. It excludes Mathlib/Lean runtime and is not a textual-copy rate.",
        "",
        "| Task | Arm | Successful runs | Research declarations | Author declarations | Pooled research share | Mean author root LOC |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for task, config in TASKS.items():
        for arm in ARMS:
            reuse = medium["by_task_arm"][f"{task}/{arm}"]["reuse"]
            share = reuse["pooled_research_share"]
            share_text = "N/A" if share is None else f"{share:.1%}"
            lines.append(
                f"| {config['title']} | {arm} | {reuse['successful_runs_with_evidence']} "
                f"| {reuse['research_logical_declarations']:,} "
                f"| {reuse['author_logical_declarations']:,} | {share_text} "
                f"| {integer(reuse['author_root_lines']['mean'])} |"
            )
    lines += [
        "",
        "### Interpretation and limitations",
        "",
        "- The comparison changes reasoning effort from high to medium while retaining the canonical natural-language proof and all other audited scientific inputs. Sampling remains stochastic, so the five replicates per cell are independent rather than seed-paired.",
        "- Success is the independent exact-target Lean endpoint, not author self-report. A run that writes plausible code but fails the frozen kernel gate is a failure.",
        "- A controller-enforced `TIMEOUT` is retained when the author received the full 5,400-second budget; it is not rerun as infrastructure censoring. It can still succeed if an independently reverified checkpoint was captured within budget. Because SIGKILL prevents Codex from emitting its final cumulative usage event, token totals for such runs are summed from the controller-owned per-call proxy log; normally finished runs require exact agreement between that sum and the Codex cumulative event.",
        "- API cost and token counts are directly comparable under the pinned model/provider protocol. Author wall time is compared only because both cohorts ran on Delta; scheduler queue time is excluded.",
        "- Five runs give 20-percentage-point observed-success resolution per task/arm cell. Wilson intervals are retained in the machine-readable metrics; 5/5 does not imply a true 100% success probability.",
        "- PML-FileOracle is an oracle-ceiling condition, not a realistic retrieval-system estimate. Reuse shares describe successful proof dependency closures and are not causal estimates of assistance quality.",
        "",
        "### Reproducible evidence",
        "",
        "- `reports/reasoning_medium_v1/REASONING_MEDIUM_RUN_LEVEL_RESULTS.csv`: all 75 medium runs.",
        "- `reports/reasoning_medium_v1/REASONING_HIGH_VS_MEDIUM_METRICS.json`: normalized high/medium aggregates plus run-level hashes.",
        "- `reports/reasoning_medium_v1/REPORT_CHECKSUMS.sha256`: report-artifact checksums.",
        "- `reports/generate_reasoning_medium_report.py`: deterministic post-run aggregator.",
        "- Each medium bundle also contains its independently produced `cohort/DELTA_RESULTS_SUMMARY.json` and timestamped verified result archive.",
        "",
    ]
    return "\n".join(lines)


def write_csv(path: Path, rows: list[dict]) -> None:
    fields = [
        "task",
        "task_title",
        "arm",
        "replicate",
        "run_id",
        "author_state",
        "primary_success",
        "target_kernel_pass",
        "selected_checkpoint",
        "first_valid_seconds",
        "author_elapsed_seconds",
        "started_utc",
        "ended_utc",
        "model_calls",
        "provider",
        "served_models",
        "total_upstream_usd",
        "cost_to_first_valid_usd",
        "calls_to_first_valid",
        *TOKEN_FIELDS,
        "non_reasoning_output_tokens",
        "allowed_axioms",
        "reuse",
        "validation_path",
        "validation_sha256",
        "status_path",
        "status_sha256",
        "routing_audit_path",
        "routing_audit_sha256",
    ]
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    field: json.dumps(row[field], sort_keys=True)
                    if isinstance(row.get(field), (dict, list))
                    else row.get(field)
                    for field in fields
                }
            )


def main() -> int:
    medium_rows, missing = collect_medium_rows()
    if missing:
        print(
            json.dumps(
                {
                    "state": "WAITING_FOR_MEDIUM_RESULTS",
                    "complete_runs": len(medium_rows),
                    "expected_runs": 75,
                    "missing_runs": missing,
                },
                indent=2,
            )
        )
        return 2

    high_rows = collect_high_rows()
    medium = grouped(medium_rows)
    high = grouped(high_rows)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    csv_path = OUT_DIR / "REASONING_MEDIUM_RUN_LEVEL_RESULTS.csv"
    metrics_path = OUT_DIR / "REASONING_HIGH_VS_MEDIUM_METRICS.json"
    write_csv(csv_path, medium_rows)
    metrics = {
        "schema_version": 1,
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "protocol": {
            "model": "openai/gpt-5.6-sol",
            "provider_only": ["OpenAI"],
            "allow_fallbacks": False,
            "canonical_full_proof_author_visible": True,
            "author_budget_seconds": 5400,
            "slurm_wrapper_seconds": 5700,
            "replicates_per_task_arm": 5,
            "high_reasoning_effort": "high",
            "medium_reasoning_effort": "medium",
        },
        "high_sources": {
            task: {
                "path": config["high_table"],
                "sha256": sha256(ROOT / config["high_table"]),
            }
            for task, config in TASKS.items()
        },
        "medium": medium,
        "high": high,
        "medium_runs": medium_rows,
    }
    metrics_path.write_text(
        json.dumps(metrics, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    current = REPORT.read_text(encoding="utf-8")
    marker = "## Results"
    if marker not in current:
        raise RuntimeError(f"missing {marker!r} section in {relative(REPORT)}")
    prefix = current.split(marker, 1)[0].rstrip()
    REPORT.write_text(
        prefix + "\n\n" + marker + "\n" + report_results(medium, high, medium_rows),
        encoding="utf-8",
    )
    checksum_path = OUT_DIR / "REPORT_CHECKSUMS.sha256"
    checksum_path.write_text(
        "".join(
            f"{sha256(path)}  {relative(path)}\n"
            for path in (REPORT, metrics_path, csv_path)
        ),
        encoding="utf-8",
    )
    print(
        f"PASS: medium {medium['overall']['successes']}/75; "
        f"high {high['overall']['successes']}/75; "
        f"medium cost {money(medium['overall']['total_upstream_usd'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
