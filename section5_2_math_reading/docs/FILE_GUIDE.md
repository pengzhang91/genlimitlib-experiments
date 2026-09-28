# File guide

## Start here

| Purpose | Path |
| --- | --- |
| Current human-readable results | `results/section5_2_results.md` |
| Current machine-readable results | `results/section5_2_results.json` |
| Detailed reconstruction and validation | `results/recount.json` |
| Portable reproduction command | `scripts/reproduce_appendix_c.py` |
| Final question bank and answer keys | `experiments/01_final_evaluation/inputs/` |
| Frozen prompts | `experiments/01_final_evaluation/prompts/` |
| Saved model responses | `experiments/01_final_evaluation/runs/` |
| Methods and historical question examples | `experiments/01_final_evaluation/reports/` |
| Frozen source snapshots | `sources/` |
| Historical reference for numerical and hash checks | `archive/recount_e24_20260920.json` |
| Release audit | `verification/ANONYMITY_REPORT.json` |

In prompt filenames, `t1` is the single-paper experiment and `t2` is the map experiment. `screen` is the question-only screening stage and `confirm` is the held-out evaluation stage. Request IDs join prompts, answer keys, and saved responses.

`inputs/bank24.json.gz`, `prompts/t1_confirm.jsonl.gz`, and `prompts/t2_confirm.jsonl.gz` use deterministic gzip. The portable script automatically reads these when their logical `.json`/`.jsonl` paths are absent.

## Current analysis and historical records

Run `python3 scripts/reproduce_appendix_c.py` from the release root. Its filename is unchanged for compatibility; its outputs now cover Section 5.2's accuracies, two-paper subset, and source-exclusion sensitivity. It does not calculate confidence intervals or recreate the removed appendix tables.

The following files are retained as historical records:

- `experiments/01_final_evaluation/scripts/build_bank.py`: documents the evidence builder; depends on earlier authoring workspaces not included in this release.
- `experiments/01_final_evaluation/scripts/build_prompts.py`: historical prompt-generation code. Frozen released prompts remain the inputs for current reproduction.
- `experiments/01_final_evaluation/scripts/analyze.py`: historical screening and analysis code, including earlier subset and interval analyses. It is not the authoritative current analysis entry point.
- `experiments/01_final_evaluation/analysis/results.json`: original analysis output used for integrity checks. Historical mean accuracies in this file need not equal the manuscript's equally weighted source-group accuracies.
- `archive/recount_e24_20260920.json`: historical numerical reference, with selected supporting quotations abbreviated in the public copy, used to verify source/input hashes and point estimates. Its older interval and supplemental-analysis fields are archival, not current reported results.

`analysis/screen.json` supplies the frozen retained question IDs; the portable script independently checks them against the saved screening responses. Do not regenerate frozen inputs or historical reference files to reproduce the current results.

## Curated release scope

The release retains the final experiment and every source needed by the portable analysis, including material needed to reconstruct the reported 78.40% accuracy after source exclusions. The earlier question-development tree retains only `MAP5.txt` and `SHAMMAP5.txt`, the frozen blocks checked against map-study prompts.

Superseded manuscript drafts, duplicate reports and table dumps, the editorial audit memo, and the predecessor recount script are omitted. Intermediate authoring records and handoff archives remain excluded. Selected paper excerpts are abbreviated in this public distribution; PUBLIC_RELEASE.json records their original hashes and locators, and scripts/public_inputs.py validates the derivative or restores locally supplied complete excerpts. See [ANONYMIZATION.md](../ANONYMIZATION.md), [runtime and provenance notes](RUNTIME_AND_PROVENANCE.md), and [LICENSES.md](../LICENSES.md).
