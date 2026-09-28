# Section 4 formalization artifact

This module contains the written proofs and Lean 4 formalization for the three
mathematical findings reported in Section 4 of the GenLimitLib paper by
Shuangping Li and Peng Zhang. The public release retains the sources from the
review snapshot and updates documentation and release checks only.

## Contents

- `GenLimitLean/Section4/`: the Section 4 Lean development;
- `GenLimitLean/GenLimit/`: the bundled library sources required by the proofs;
- `manuscript/section4/`: standalone written proofs for the Section 4 results;
- `../section4_other_findings/`: the separate companion-notes module;
- `registry/section4/`: theorem-to-code correspondence and verification records;
- `scripts/`: the focused build, admission scan, and axiom audit;
- `SHA256SUMS`: hashes for every published file in this module.

## Verify

Verify the downloaded files first, from this directory:

```bash
python3 VERIFY_RELEASE.py
```

This checks release integrity and excludes private paths, credential-like
strings, nested history, and build artifacts. Public author names and repository
links are permitted. It does not compile Lean.

For an independent Lean rerun, with Lean/Elan installed:

```bash
bash scripts/verify_section4.sh --fetch-cache
```

This builds the `Section4` target and checks the declared theorem axioms. It can
update local verification records, so use a separate checkout to preserve the
downloaded snapshot. `scripts/refresh_release_checksums.py` is a maintainer
tool for intentional release changes, not a verification step.
The pinned toolchain is Lean 4.24.0 with the Mathlib revision recorded in
`GenLimitLean/lake-manifest.json`.

**Historical Lean verification status: passed.** The included source-repository records
show a complete `Section4` build (3130 jobs), a successful static source audit,
and successful checks of all 18 declared axiom endpoints. The Lean sources in
the review snapshot were compared byte-for-byte with the verified sources.
See `registry/section4/verification/STATUS.md` for the evidence boundary. The
command above remains available to reviewers who want an independent rerun.

## Scope

The formalization verifies the deterministic mathematical statements mapped in
`registry/section4/README.md`. It does not claim executable oracle
implementations, running-time bounds, or Lean certification of the separate
“Other Findings” module at `../section4_other_findings/`.

The public library is
[generation-in-the-limit-lib](https://github.com/pengzhang91/generation-in-the-limit-lib).
This release preserves the review snapshot's source-history boundary; it does
not recover omitted private records or original revisions. See the root
[reproducibility scope](../REPRODUCIBILITY.md). The existing
[Apache-2.0 license](LICENSE) remains in force.
