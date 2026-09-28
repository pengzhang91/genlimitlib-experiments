# Mathematical-reading experiment artifact

This module contains the mathematical-reading experiments in Section 5.2 of the GenLimitLib paper by Shuangping Li and Peng Zhang, with the protocol described in Appendix C. It contains a public presentation of the final question bank and prompts, the unchanged answer keys and saved model responses, source snapshots, and a portable script that reconstructs reported accuracies offline. Selected paper excerpts are abbreviated; the original experiment used complete excerpts. See [the public-release guide](../REPRODUCIBILITY.md).

No network access, API key, model download, GPU, or Lean installation is required for the offline analysis.

## Reproduce the reported results

From this module directory, run:

```bash
recount_dir=$(mktemp -d)
python3 scripts/reproduce_appendix_c.py --output "$recount_dir/recount.json"
```

The script filename is retained for compatibility. The command validates request schedules, answer rotations, prompt contents, saved responses, screening decisions, map inputs, source hashes, and historical point estimates. In the temporary directory it writes:

- `section5_2_results.md`: the main accuracies, the two-paper subset, and the source-exclusion sensitivity retained in the manuscript;
- `section5_2_results.json`: the same results in machine-readable form;
- `recount.json`: detailed reconstruction and validation records.

These outputs leave the frozen release files unchanged. This workflow reconstructs saved statistics; it does not establish that fresh model inference would produce identical responses. See [the reproducibility scope](../REPRODUCIBILITY.md).

The current entry point does not calculate or report confidence intervals. It uses only Python 3's standard library.

## Contents

- `experiments/01_final_evaluation/`: final evaluation inputs, public prompt presentations, raw responses, methods, question examples, and historical scripts.
- `experiments/02_question_development/01_initial_batches/inputs/`: the two frozen map blocks checked against the final prompts.
- `sources/`: frozen Lean source snapshots and study-key declarations used by provenance validation.
- `scripts/`: the portable reproduction entry point.
- `results/`: reconstructed current results and detailed validation records.
- `archive/`: historical numerical reference; selected supporting quotations are abbreviated, while every numerical value is retained.
- `docs/`: file guide, runtime notes, and provenance limitations.

The question bank and two large evaluation prompt files use deterministic gzip (`bank24.json.gz`, `t1_confirm.jsonl.gz`, and `t2_confirm.jsonl.gz`). The portable script reads them transparently.

The scripts under `experiments/01_final_evaluation/scripts/` and the original `analysis/results.json` are historical records, not the authoritative current analysis. They include earlier analyses that are no longer reported in the manuscript. Use the command above; see [the file guide](docs/FILE_GUIDE.md) for their scope.

## Review-snapshot provenance

During preparation of the review snapshot, direct author identifiers, contact strings, repository handles, and local machine paths were removed or replaced. The public documentation now identifies the authors. This derivative keeps those earlier redactions and additionally replaces selected paper excerpts with boundary locators. Historical authoring workspaces, handoff archives, and intermediate question-development records not required for the final results were excluded.

Source citations, short boundary snippets, and original excerpt hashes are recorded in `PUBLIC_RELEASE.json`. Mixed-source blocks with unresolved material are abbreviated as a whole where reliable internal boundaries are unavailable.

The saved model responses predate both the identity redactions and this public excerpt abbreviation. Inference was not rerun. Public prompts have refreshed character counts and SHA-256 values; their preceding snapshot hashes are retained separately in `PUBLIC_RELEASE.json`. Response records, screening decisions, and reconstructed point estimates are unchanged. The released prompt text is therefore not a byte-for-byte copy of the original inference input. See [runtime and provenance notes](docs/RUNTIME_AND_PROVENANCE.md) for the scope and limitations.

## Integrity

After downloading the repository, verify the release files with:

```bash
shasum -a 256 -c SHA256SUMS
```

`RELEASE_MANIFEST.json` records each payload file's size and SHA-256 digest. Project-owned code is Apache-2.0 and project-owned documentation and data are CC BY 4.0, subject to [LICENSES.md](LICENSES.md). Existing upstream licenses remain in force. Paper excerpts are excluded from our grant; source licenses and unresolved redistribution questions are recorded in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
