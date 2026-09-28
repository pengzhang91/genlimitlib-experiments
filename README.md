# GenLimitLib: proofs and experiments

Research materials for **GenLimitLib: A Formal Library for Language Generation
in the Limit and AI-Assisted Mathematical Research**, by **Shuangping Li**
(Yale University) and **Peng Zhang** (Rutgers University).

The experiment repository is
[genlimitlib-experiments](https://github.com/pengzhang91/genlimitlib-experiments).
The accompanying library is available at
[generation-in-the-limit-lib](https://github.com/pengzhang91/generation-in-the-limit-lib).
This artifact contains the formalization, supplementary mathematical findings,
and the two experiment packages:

- `section4_formalization/`: Lean 4 sources, written proofs, theorem maps, and
  verification records for Section 4.
- `section4_other_findings/`: five additional mathematical findings, complete
  proofs, LaTeX sources, audit notes, and finite diagnostic checks.
- `section5_1_lean_proof_generation/`: the complete 300-run Lean
  proof-generation experiment release.
- `section5_2_math_reading/`: the mathematical-reading experiment release,
  including public prompt presentations, saved responses, sources, and offline reproduction.

Each module has its own README and integrity records. No network access is
needed for the two experiment-data verification workflows. Rebuilding the Lean
formalization requires the pinned Lean toolchain and Mathlib dependencies.

Verify the complete downloaded release first with:

```bash
shasum -a 256 -c SHA256SUMS
```

## Verification entry points

```bash
(cd section4_formalization && python3 VERIFY_RELEASE.py)
(cd section4_other_findings && shasum -a 256 -c SHA256SUMS)
(cd section5_1_lean_proof_generation && python3 VERIFY_INVENTORY.py)
(cd section5_1_lean_proof_generation && shasum -a 256 -c SHA256SUMS)
(cd section5_2_math_reading && shasum -a 256 -c SHA256SUMS)
recount_dir=$(mktemp -d)
python3 section5_2_math_reading/scripts/reproduce_appendix_c.py \
  --output "$recount_dir/recount.json"
```

## Licenses and provenance

Project-owned code uses [Apache-2.0](LICENSE-CODE); project-owned documentation
and data use [CC BY 4.0](LICENSE-DATA.md), subject to [license scope and third-party
exclusions](LICENSE.md).
See [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for excerpt omissions and provenance.
