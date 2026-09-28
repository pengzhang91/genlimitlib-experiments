#!/usr/bin/env python3
import csv
import json
from collections import Counter
from pathlib import Path

root = Path(__file__).resolve().parent
with (root / "data/RUN_LEVEL_RESULTS_300.csv").open(newline="", encoding="utf-8") as stream:
    rows = list(csv.DictReader(stream))
assert len(rows) == 300, len(rows)
keys = [(r["condition"], r["task"], r["arm"], r["replicate"]) for r in rows]
assert all(value == 1 for value in Counter(keys).values())
assert len(set(keys)) == 300
summary = json.loads((root / "data/SUMMARY_300.json").read_text(encoding="utf-8"))
assert summary["runs"] == 300
assert sum(item["runs"] for item in summary["conditions"].values()) == 300
prompts = json.loads((root / "prompts/PROMPT_MANIFEST.json").read_text(encoding="utf-8"))
assert prompts["counts"] == {
    "arms": 3,
    "conditions": 4,
    "formal_runs": 300,
    "prompt_sets": 60,
    "tasks": 5,
}
assert len(prompts["prompt_sets"]) == 60
assert len(prompts["formal_runs"]) == 300
assert {item["run_id"] for item in prompts["formal_runs"]} == {row["run_id"] for row in rows}
for item in prompts["prompt_sets"]:
    prompt_root = root / item["prompt_root"]
    assert (prompt_root / "control/AUTHOR_PROMPT.txt").is_file()
    assert (prompt_root / "AGENTS.md").is_file()
    assert (prompt_root / "design/AGENTS.md").is_file()
    canonical = item["condition"].startswith("canonical_")
    assert (prompt_root / "design/CANONICAL_FULL_PROOF.md").is_file() is canonical
evidence = json.loads((root / "evidence/EVIDENCE_MANIFEST.json").read_text(encoding="utf-8"))
assert evidence["counts"] == {
    "failed_runs": 92,
    "formal_runs": 300,
    "model_calls": 16108,
    "successful_runs": 208,
}
assert len(evidence["runs"]) == 300
assert {item["run_id"] for item in evidence["runs"]} == {row["run_id"] for row in rows}
row_by_id = {row["run_id"]: row for row in rows}
for item in evidence["runs"]:
    packet = root / item["evidence_root"]
    assert (packet / "RUN_RECEIPT.json").is_file()
    assert (packet / "STATUS.json").is_file()
    assert (packet / "ROUTING_SUMMARY.json").is_file()
    assert (packet / "USAGE_SUMMARY.json").is_file()
    assert (packet / "USAGE_LEDGER.jsonl").is_file()
    assert (packet / "VALIDATION.json").is_file()
    assert (packet / "final_output").is_dir()
    row = row_by_id[item["run_id"]]
    usage = json.loads((packet / "USAGE_SUMMARY.json").read_text(encoding="utf-8"))
    assert usage["model_calls"] == int(row["model_calls"])
    assert usage["input_tokens"] == int(row["input_tokens"])
    assert usage["output_tokens"] == int(row["output_tokens"])
    assert usage["reasoning_output_tokens"] == int(row["reasoning_output_tokens"])
    with (packet / "USAGE_LEDGER.jsonl").open(encoding="utf-8") as stream:
        assert sum(1 for line in stream if line.strip()) == int(row["model_calls"])
    successful = row["lean_success"] == "True"
    assert (packet / "selected_proof").is_dir() is successful
    assert (packet / "FAILURE.json").is_file() is (not successful)
print("PASS: 300 formal runs, 60 prompt sets, 300 evidence packets, and condition summaries")
