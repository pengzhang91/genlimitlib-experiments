#!/usr/bin/env python3
"""Compare frozen kernel-valid proofs across canonical/no-canonical conditions."""

import hashlib
import itertools
import json
import re
import statistics
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ARMS = ("P", "PML", "PML-FileOracle")
SLUG_ARM = {"p": "P", "pml": "PML", "file_oracle": "PML-FileOracle"}
CASES = {
    "S2-B": {
        "root": "S2BFormalization.lean",
        "canonical": ("lean2paper_delta_v1", "lean2paper_delta_v1_r3r5"),
        "nocanonical_metrics": "reports/s2b_nocanonical_v1/S2B_NOCANONICAL_FIVE_RUN_METRICS.json",
    },
    "Case 017": {
        "root": "Case017Formalization.lean",
        "canonical": ("lean2paper_case017_delta_v1", "lean2paper_case017_delta_v1_r3r5"),
        "nocanonical_metrics": "reports/case017_nocanonical_v1/CASE017_NOCANONICAL_FIVE_RUN_METRICS.json",
    },
    "Case 024": {
        "root": "Case024Formalization.lean",
        "canonical": ("lean2paper_case024_delta_v1", "lean2paper_case024_delta_v1_r3r5"),
        "nocanonical_metrics": "reports/case024_nocanonical_v1/CASE024_NOCANONICAL_FIVE_RUN_METRICS.json",
    },
}
LOGICAL = {"theorem", "definition", "opaque"}


def load(path):
    return json.loads(path.read_text())


def strip_comments(text):
    # Lean block comments nest; replace them with a small state machine.
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def tokens(text):
    text = strip_comments(text)
    return re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|[0-9]+|:=|=>|[^\s]", text)


def shingles(items, size=5):
    return {tuple(items[i:i + size]) for i in range(max(0, len(items) - size + 1))}


def jaccard(left, right):
    return len(left & right) / len(left | right) if left or right else 1.0


def checkpoint_data(bundle, run_id, selected, corrected=False):
    arm_slug = run_id.split("_", 1)[0]
    if run_id.startswith("file_oracle_"):
        arm_slug = "file_oracle"
    base = ROOT / bundle / "cohort" / "arms" / arm_slug
    output = base / "logs" / run_id / "checkpoints" / selected / "output"
    candidates = sorted(
        path for path in output.glob("*.lean")
        if not path.name.startswith("Controller")
        and path.name not in {"Stage3Model.lean", "TargetTemplate.lean"}
    )
    graph_path = output / "DEPENDENCIES.json"
    graph = load(graph_path)["nodes"] if graph_path.is_file() else []
    candidate_modules = {path.stem for path in candidates}
    used_modules = {node["module"] for node in graph} & candidate_modules
    sources = [path for path in candidates if path.stem in used_modules]
    if not sources:
        sources = candidates
    source_text = "\n".join(path.read_text() for path in sources)
    author_modules = {path.stem for path in sources}
    author_dependencies = {
        node["name"] for node in graph
        if node["kind"] in LOGICAL and node["module"] in author_modules
    }
    reuse_path = base / "results" / run_id / "REUSE.json"
    research_dependencies = set()
    if reuse_path.is_file():
        research_dependencies = {
            item["name"] for item in load(reuse_path)["research_declarations"]
            if item["kind"] in LOGICAL
        }
    root_name = next((name for name in ("S2BFormalization.lean",
                                        "Case017Formalization.lean",
                                        "Case024Formalization.lean")
                      if (output / name).is_file()), None)
    return {
        "bundle": bundle,
        "run_id": run_id,
        "replicate": int(run_id.rsplit("r", 1)[1]),
        "arm": SLUG_ARM[arm_slug],
        "checkpoint": selected,
        "corrected_offline": corrected,
        "files": [path.name for path in sources],
        "total_loc": sum(len(path.read_text().splitlines()) for path in sources),
        "source_sha256": hashlib.sha256(source_text.encode()).hexdigest(),
        "tokens": tokens(source_text),
        "shingles": shingles(tokens(source_text)),
        "root_loc": len((output / root_name).read_text().splitlines()),
        "author_dependencies": author_dependencies,
        "research_dependencies": research_dependencies,
    }


def canonical_runs(config):
    rows = []
    for bundle in config["canonical"]:
        for validation_path in (ROOT / bundle / "cohort" / "arms").glob(
                "*/results/*/VALIDATION.json"):
            validation = load(validation_path)
            run_id = validation["run_id"]
            selected = validation["selected_checkpoint"]
            corrected = False
            if run_id == "file_oracle_case024_delta_v1_r1":
                selected, corrected = "final", True
            elif not validation["primary_success"]:
                continue
            rows.append(checkpoint_data(bundle, run_id, selected, corrected))
    return rows


def nocanonical_runs(config):
    metrics = load(ROOT / config["nocanonical_metrics"])
    rows = []
    for row in metrics["runs"]:
        if not row["primary_success"]:
            continue
        rows.append(checkpoint_data(
            row["source_bundle"], row["run_id"], row["selected_checkpoint"]))
    return rows


def median(values):
    return statistics.median(values) if values else None


def summarize(left, right):
    cross = [(a, b, jaccard(a["shingles"], b["shingles"]))
             for a in left for b in right]
    nearest = [
        max((score, a["run_id"]) for a, other, score in cross if other is b)
        for b in right
    ]
    same_rep = [
        jaccard(a["shingles"], b["shingles"])
        for a in left for b in right if a["replicate"] == b["replicate"]
    ]
    within_left = [jaccard(a["shingles"], b["shingles"])
                   for a, b in itertools.combinations(left, 2)]
    within_right = [jaccard(a["shingles"], b["shingles"])
                    for a, b in itertools.combinations(right, 2)]
    research_cross = [
        jaccard(a["research_dependencies"], b["research_dependencies"])
        for a in left for b in right
        if a["research_dependencies"] or b["research_dependencies"]
    ]
    author_cross = [
        jaccard(a["author_dependencies"], b["author_dependencies"])
        for a in left for b in right
    ]
    return {
        "canonical_successful_proofs": len(left),
        "nocanonical_successful_proofs": len(right),
        "exact_source_matches_cross_condition": sum(
            a["source_sha256"] == b["source_sha256"] for a in left for b in right),
        "token_5gram_jaccard": {
            "cross_condition_median_all_pairs": median([x[2] for x in cross]),
            "nearest_canonical_per_nocanonical_mean": statistics.mean(x[0] for x in nearest),
            "nearest_canonical_per_nocanonical_range": [
                min(x[0] for x in nearest), max(x[0] for x in nearest)],
            "same_replicate_mean": statistics.mean(same_rep) if same_rep else None,
            "canonical_within_condition_median": median(within_left),
            "nocanonical_within_condition_median": median(within_right),
        },
        "logical_dependency_name_jaccard_cross_condition": {
            "author_median": median(author_cross),
            "research_median": median(research_cross),
        },
        "root_loc": {
            "canonical_mean": statistics.mean(x["root_loc"] for x in left),
            "nocanonical_mean": statistics.mean(x["root_loc"] for x in right),
        },
        "total_author_source_loc": {
            "canonical_mean": statistics.mean(x["total_loc"] for x in left),
            "nocanonical_mean": statistics.mean(x["total_loc"] for x in right),
        },
        "nearest_pairs": [
            {"nocanonical": b["run_id"], "canonical": run_id, "jaccard": score}
            for b, (score, run_id) in zip(right, nearest)
        ],
    }


def main():
    output = {}
    for case, config in CASES.items():
        canonical, nocanonical = canonical_runs(config), nocanonical_runs(config)
        output[case] = {
            arm: summarize(
                [x for x in canonical if x["arm"] == arm],
                [x for x in nocanonical if x["arm"] == arm])
            for arm in ARMS
        }
    print(json.dumps(output, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
