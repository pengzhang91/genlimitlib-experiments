# Runtime and provenance

## Documented reader configuration

The historical run records specify:

- reader model: `Qwen/Qwen3.6-27B`, revision `6a9e13bd6fc8f0983b9b99948120bc37f49c13e9`;
- BF16 inference through vLLM 0.19.0 on one H100 80 GB;
- maximum model length 16,384 and maximum sequences 16;
- thinking disabled, temperature 0, top-p 1, and one generated token;
- server seed 20260919 and request seed 20260915;
- first-token top-20 log probabilities, selecting the largest recorded A–E score.

These are historical records, not new hardware or runtime attestations. All 10,894 saved calls completed; three lack scores for all five option letters. The analysis preserves their historical choice of the largest recorded option score.

## Offline reconstruction

The portable analysis validates:

- matching prompt, answer-key, and response IDs;
- the complete condition and rotation schedule;
- answer-option rotations and released prompt hashes;
- screening decisions recomputed from question-only responses;
- the two frozen map blocks;
- 573 source-file hashes, unchanged analysis-input hashes, and declared public derivative hashes;
- point estimates against the historical recount.

It reconstructs the Section 5.2 accuracies, two-paper subset, and source-exclusion sensitivity from saved responses using Python 3 only. The current analysis does not compute confidence intervals. Older interval fields remain in the historical reference JSON and original analysis output for archival integrity.

The source-exclusion calculation is a post hoc sensitivity check. It identifies exact extracted declaration signatures outside the designated source module and Core; it does not establish that mathematically equivalent statements were absent elsewhere. The two-paper subset follows the recorded auditor classification, not an independent proof that each question requires two papers.

## Remaining runtime limitation

No independently frozen final-run server startup receipt or exact executed runtime image is included. The bundle supports offline reconstruction of the saved statistics; it does not establish that fresh GPU inference would reproduce every response bit-for-bit.

## Review-snapshot provenance

The review snapshot replaced personal repository handles, author/contact strings,
and local absolute paths with neutral placeholders, then recomputed prompt
lengths, prompt hashes, and the archived bank hash. Lean source snapshots were
not rewritten. The bank and two large prompt files use deterministic gzip;
decompression restores the stored text exactly. Source-repository history,
private authoring workspaces, handoff archives, and unneeded intermediate
question-development records were excluded.

Identity and contact strings in released metadata and prompt evidence were redacted after inference, and corresponding prompt hashes and character counts were recomputed. Response records and screening decisions remain unchanged. The public export additionally abbreviates selected paper excerpts. Default verification checks the public presentation and compares reconstructed point estimates with the historical recount. It does not claim to verify omitted original text. With `--private-excerpts`, complete review-snapshot bank, prompt, and historical-reference bytes are reconstructed in memory and checked against original hashes. This still does not undo earlier identity redactions.

Historical evidence budgets describe the original run. Redaction can change released prompt character counts, so refreshed metadata describes the released text. Both released map blocks are 19,102 characters, matching the recorded original length. The sham map shares the relevant map's heading and length but contains Lean statements from outside the five-paper collection; it does not match the relevant map's relationship structure.

The full early question-development and model-assisted authoring lineage is excluded from the released snapshot. It is not used by the portable command. See [LICENSES.md](../LICENSES.md) for source-material licensing.
