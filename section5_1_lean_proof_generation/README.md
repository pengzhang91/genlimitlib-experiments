# Lean proof-generation experiment module

This module contains the processed materials for the five-task Lean
proof-generation experiment in Shuangping Li and Peng Zhang's GenLimitLib paper.  It covers four factorial cells
(canonical proof present/absent x reasoning high/medium), three arms (P, PML,
PML-FileOracle), and five independent replicates per task/arm/cell: 300 author
runs in total.

## Contents

- `tasks/`: the exact task-facing design files for canonical and no-canonical
  conditions, including each original Lean statement and canonical proof input.
- `prompts/`: all 60 task x condition x arm experiment-controlled prompt
  sets plus a 300-run mapping and per-batch model/configuration receipts.
- `data/RUN_LEVEL_RESULTS_300.csv`: one normalized row per formal author run.
- `evidence/`: compact sanitized evidence for all 300 runs, including
  terminal status, strict routing, per-call token/cost ledgers, Lean
  validation, final outputs, and every successful selected proof.
- `data/SUMMARY_300.json`: condition-level totals.
- `reports/by_condition/`: machine-readable per-task metrics and run-level
  tables, plus the retained English reports.
- `reports/cross_condition/`: the retained English cross-condition report.
- `audits/`: the published no-canonical input/source audits.
- `reference_reporting_scripts/`: retained English-only analysis and reporting
  scripts.
- `SOURCE_INVENTORY.json` and `SHA256SUMS`: provenance and transfer integrity.

This includes the compact evidence needed to audit the reported outcomes. It
deliberately omits raw Slurm logs, complete API request/response transcripts,
credentials and request identifiers, compiled/cache artifacts, redundant
bundles, unselected intermediate checkpoints, and non-English derived narrative
reports and their historical generators. The underlying machine-readable
metrics and run evidence remain included.

## Verify the released records

Run from this directory:

```bash
shasum -a 256 -c SHA256SUMS
python3 VERIFY_INVENTORY.py
```

## Reproducibility and licensing

The inventory checker validates the released run inventory and evidence. It
does not rerun the model experiment or freshly compile every generated proof.
Saved outputs and historical validation records do not guarantee identical
outputs from a new model run. See [the reproducibility scope](../REPRODUCIBILITY.md).

Frozen tasks, prompts, outputs, and provenance records retain their released
bytes, including review-time path redactions. `SOURCE_INVENTORY.json` is the
historical export inventory; `SHA256SUMS` records current release integrity.

Project-owned code uses Apache-2.0 and project-owned documentation and data use
CC BY 4.0, with existing licenses and third-party material excluded as described
in [the repository license scope](../LICENSE.md).
