# Public distribution and omitted excerpts

This repository is a separate public distribution of the GenLimitLib research
artifact. The experiment used complete paper excerpts. In this distribution,
**414 distinct excerpt blocks** associated with sources whose redistribution
basis was not established are displayed as boundary snippets, an explicit
omission notice, source links, and an original SHA-256 digest. This affects
**835 bank items and 4,521 prompt records** in three files:

- `section5_2_math_reading/experiments/01_final_evaluation/inputs/bank24.json.gz`
- `section5_2_math_reading/experiments/01_final_evaluation/prompts/t1_confirm.jsonl.gz`
- `section5_2_math_reading/experiments/01_final_evaluation/prompts/t2_confirm.jsonl.gz`

An additional **199 supporting `basis` fields (192 distinct quotations)** are
abbreviated in the bank and the historical numerical reference
`section5_2_math_reading/archive/recount_e24_20260920.json`. Generated recount
files use these abbreviated annotations too. All numerical reference values
remain unchanged. Thus the full-input audit restores four input files.

Identical blocks are abbreviated in all occurrences, including questions with
different source labels. Mixed-source blocks are abbreviated as a whole where
the record lacks reliable per-paper boundaries. Blocks not selected for omission
are unchanged. No question stem, answer, Lean context, map, saved model response,
screening rule, or statistical estimator was changed.

## What a locator means

A locator contains the exact beginning and ending of the historical extracted
block, normally the first/last sentence where a short boundary can be identified.
A boundary is capped at 240 characters and can be a sentence fragment: the
original extraction itself sometimes starts or ends mid-sentence. The locator
is **not the text supplied to the model** and must not be used as a replacement
input to claim a rerun of the original experiment.

`section5_2_math_reading/PUBLIC_RELEASE.json` records original character/byte
counts, excerpt hashes, associated question/paper IDs, boundary snippets,
public presentation strings, supporting-quotation mappings, and original versus
public input-file hashes.
For changed prompt records it separately retains original prompt hashes and
character counts. Existing `prompt_sha256`/`chars` in the public files describe
the public presentation. Source links identify checked paper editions; they do
not establish a page-level match for every passage. Unrecorded page/section or
internal mixed-paper boundaries are explicitly left unknown.

## Offline statistical reconstruction

Run from the repository root:

```bash
recount_dir=$(mktemp -d)
python3 section5_2_math_reading/scripts/reproduce_appendix_c.py \
  --output "$recount_dir/recount.json"
```

This verifies the public input hashes and prompt-bank consistency, unchanged
Lean sources, response schedules, answer rotations, screening decisions, and
reported point estimates. It produces the same numerical results as the full
review snapshot. Its output explicitly reports
`original_full_input_hashes_verified: false`: omitted text cannot be verified
from the public distribution alone. The verification metadata differs from the
full snapshot even though the numerical results do not.

## Optional audit of complete historical inputs

If you have lawfully obtained the exact historical extracted fragments, create
a local UTF-8 JSON object mapping each omitted excerpt's SHA-256 to its complete
text. The required keys, lengths, boundaries, and source locators are in
`PUBLIC_RELEASE.json`. Keep that file outside the repository, or under the
ignored `private_inputs/` directory. The authors retain the original snapshot
and a matching local fragment mapping separately.

```bash
recount_dir=$(mktemp -d)
python3 section5_2_math_reading/scripts/reproduce_appendix_c.py \
  --private-excerpts /path/to/private-excerpts.json \
  --output "$recount_dir/recount.json"
```

The script validates each supplied fragment, reconstructs the four original
JSON/JSONL input byte streams **in memory**, checks their original SHA-256
values, and runs the full prompt consistency and statistical checks. It does
not upload fragments or write restored prompts. A missing/wrong fragment or
mismatched original hash fails the audit. Different PDF text extraction can
produce different whitespace or characters, so PDF access alone does not
guarantee byte-identical reconstruction. No approximate-match bypass is used.

Successful restoration recovers the review snapshot after its historical
identity redactions, not the original unredacted model requests. It does not
rerun inference or guarantee that a fresh model run would reproduce responses.

## Licensing and history

See [LICENSE.md](LICENSE.md) and
[the source-rights review](section5_2_math_reading/THIRD_PARTY_NOTICES.md).
Boundary snippets remain third-party text and are excluded from the project
license grant; abbreviation is not a blanket permission determination.

This distribution starts a new Git history containing only the public files.
The complete original artifact and private reconstruction material are retained
separately and must not be merged into this publication history. Historical
reports inside the artifact describe their original snapshots; current release
checksums cover the public distribution.
