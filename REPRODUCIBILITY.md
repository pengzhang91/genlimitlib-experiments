# Reproducibility scope

This public distribution supports inspection of research artifacts, verification
of their released integrity, and offline reconstruction from saved responses.
Selected paper excerpts in reading inputs are replaced by boundary locators.
These are distinct from a new Lean build or a new model experiment.

| Workflow | What it establishes | What it does not establish |
| --- | --- | --- |
| Root and module `SHA256SUMS` | Files match the released integrity manifests | Independent correctness of the science or authenticity of an unsigned manifest |
| Section 4 `VERIFY_RELEASE.py` | Manifest consistency, required files, 20 modules, and release-hygiene checks | A fresh Lean compilation |
| Section 4 `scripts/verify_section4.sh --fetch-cache` | A fresh targeted build and axiom audit in the pinned Lean environment | Verification of the separate Other Findings module |
| Section 5.1 `VERIFY_INVENTORY.py` | Inventory consistency for 300 runs, 60 prompt sets, and the retained evidence | A new model run or a fresh validation of every generated proof |
| Section 5.2 `scripts/reproduce_appendix_c.py` | Public prompt/response consistency and the reported accuracies and sensitivity analyses reconstructed from saved responses | Identical responses from fresh GPU/model inference |

## Offline checks

Run from the artifact repository root, using Python 3 and `shasum`:

```bash
shasum -a 256 -c SHA256SUMS
(cd section4_formalization && python3 VERIFY_RELEASE.py)
(cd section4_other_findings && shasum -a 256 -c SHA256SUMS)
(cd section5_1_lean_proof_generation && python3 VERIFY_INVENTORY.py)
(cd section5_1_lean_proof_generation && shasum -a 256 -c SHA256SUMS)
(cd section5_2_math_reading && shasum -a 256 -c SHA256SUMS)
recount_dir=$(mktemp -d)
python3 section5_2_math_reading/scripts/reproduce_appendix_c.py \
  --output "$recount_dir/recount.json"
```

The final command writes `recount.json`, `section5_2_results.json`, and
`section5_2_results.md` to the temporary directory. It uses the Python standard
library and requires no API key, network, GPU, or Lean installation. Do not
regenerate manifests to make a failed integrity check pass: inspect the changed
files first.

## Lean verification

The recorded Section 4 verification is a historical successful build and axiom
audit, with the evidence boundary documented in
`section4_formalization/registry/section4/verification/STATUS.md`.
An independent rerun requires Lean/Elan and the dependencies pinned in
`GenLimitLean/lean-toolchain` and `GenLimitLean/lake-manifest.json`:

```bash
cd section4_formalization
python3 VERIFY_RELEASE.py
bash scripts/verify_section4.sh --fetch-cache
```

The build script can update local verification records. Run it in a separate
checkout if you want to preserve the downloaded release unchanged. The `.lake`
directory is an excluded dependency/build cache; rebuilding may recreate it
and download several gigabytes. It is not required for the offline checks.

## Model experiments and frozen inputs

Section 5.1 includes processed run-level results, selected proofs, and compact
validation evidence. Full API transcripts, scheduler logs, and parts of the
original execution environment are not included. The inventory checker audits
the released records, rather than executing the original experiment pipeline.

Section 5.2 reconstructs statistics from 10,894 saved calls. Its documented
model and inference settings are historical records; no independently frozen
final server startup receipt or exact executed runtime image is supplied.
Neither fixed seeds nor temperature zero establish response-by-response
identity across a fresh runtime. See
[runtime and provenance](section5_2_math_reading/docs/RUNTIME_AND_PROVENANCE.md).

Review-time identity redactions were applied after inference. The released
prompt hashes describe that redacted text, not a byte-for-byte recovery of the
original model requests. This public derivative additionally abbreviates selected paper excerpts in
the question bank and two prompt files, plus duplicated supporting quotations
in the bank and historical numerical reference. The original complete excerpts were
used in the experiment; the shortened presentations were never sent to the
model. Questions, answers, source snapshots, model responses, and scores are
unchanged. Original hashes remain separate from public presentation hashes.
See [PUBLIC_RELEASE.md](PUBLIC_RELEASE.md) for an optional full-input audit
using locally supplied complete excerpts. Historical manifests and audit reports
inside experiment records describe their original snapshots; current root and
module integrity manifests describe this release.
