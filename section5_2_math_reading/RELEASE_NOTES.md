# Public excerpt-locator distribution (2026-09-28)

This separate distribution abbreviates 414 distinct excerpt blocks in 835 bank
items and 4,521 prompt records. It also abbreviates 199 supporting basis fields
(192 distinct quotations) and their copies in the historical numerical reference.
Original fragment and input hashes are retained
in PUBLIC_RELEASE.json. Shared blocks are abbreviated in all occurrences;
mixed-source blocks are not split without reliable boundaries. Saved responses,
questions, answers, Lean context, source snapshots, and scoring remain unchanged.
The optional --private-excerpts audit restores exact review-snapshot input bytes
in memory. Earlier release notes below describe earlier snapshots, not the
present distribution.

# Public documentation update (2026-09-28)

Author and repository metadata, license scope, third-party source notices, and
reproducibility documentation have been updated. Frozen experimental inputs,
source snapshots, saved outputs, and historical audit records are unchanged.
The current README directs new reproduction output to a temporary directory.
Current release manifests have been refreshed; earlier release notes follow.

# Shortened manuscript release

This revision aligns the artifact's presentation with Section 5.2 and the shortened Appendix C. Experimental inputs, source snapshots, saved responses, screening decisions, and reported point estimates are unchanged.

The portable command remains:

```bash
python3 scripts/reproduce_appendix_c.py
```

It now writes `results/section5_2_results.md`, `results/section5_2_results.json`, and `results/recount.json`. The summary contains the main accuracies, the 15-question exclusion check, and the map-category point estimates supporting the main-text qualification. It does not calculate or report confidence intervals. The previous `appendix_c_tables.md` and `.json` outputs have been replaced.

Six superseded files were removed:

- `experiments/01_final_evaluation/latex/experiments_library_value_e24.tex`
- `experiments/01_final_evaluation/reports/TABLES.md`
- `experiments/01_final_evaluation/reports/FULL_REPORT_E24.md`
- `experiments/01_final_evaluation/scripts/make_tables.py`
- `archive/reading_model_audit_20260921.md`
- `archive/recount_e24_original.py`

Useful methods and examples remain. The three older construction/analysis scripts are retained as historical records and are not the portable reproduction workflow. In particular, the older analysis reports item-weighted means; the portable script implements the manuscript's group-weighted estimator.

The original reference JSON files remain unchanged for input-hash and point-estimate verification. They retain historical analysis fields, including intervals; these fields are not part of the revised reported results. Full source provenance checks are also retained, including material needed for the exclusion result still stated in the main text.

Release checksums and the file manifest were regenerated after the cleanup. See `ANONYMIZATION.md` for the original identity-only transformations and the limits of reproducing model inference from the released records.
