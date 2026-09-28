# Compact per-run evidence

This directory contains one evidence packet for every one of the 300 formal
author runs. Paths have the form
`<condition>/<task>/<arm-slug>/r<replicate>/`.

Each packet contains:

- `RUN_RECEIPT.json`: formal/attempt/source mapping and source hashes;
- `STATUS.json`: terminal author state and strict-routing summary;
- `ROUTING_SUMMARY.json`: provider/model counts and upstream API cost;
- `USAGE_LEDGER.jsonl` and `USAGE_SUMMARY.json`: a sanitized per-call token,
  cost, timing, model, and provider ledger without prompts, responses,
  generation IDs, URLs, credentials, or headers;
- `VALIDATION.json`: the independent Lean validation receipt;
- `final_output/`: final author-created Lean/Markdown/JSON output for every run;
- `selected_proof/` plus selected-checkpoint capture/environment/reuse receipts
  for successful runs; and
- `FAILURE.json` for unsuccessful runs.

The selected proof is the source snapshot independently rechecked by the Lean
gate. Compiled `.olean` files, scratch `.tmp` files, raw event/API transcripts,
Slurm stdout/stderr, and unselected intermediate checkpoints are intentionally
excluded. `EVIDENCE_MANIFEST.json` maps all packets and records aggregate
counts. Original source and exported-file hashes are recorded in the module's
`SOURCE_INVENTORY.json` and `SHA256SUMS`.

Full `DEPENDENCIES.json` graphs are also omitted: the 208 proof-specific graphs
would add about 3.4 GB of largely repeated library structure. Their SHA-256 and
byte size are retained in each successful `RUN_RECEIPT.json`; compact reuse
receipts and the reported per-run reuse counts remain in this module.

Case 024 FileOracle r1 additionally contains `OFFLINE_REVALIDATION.json`. Its
original checker failed to include a helper module, so the original failed
`VALIDATION.json` is preserved and the unchanged frozen sources from its final
checkpoint are accompanied by the corrected zero-model-call Lean revalidation.
