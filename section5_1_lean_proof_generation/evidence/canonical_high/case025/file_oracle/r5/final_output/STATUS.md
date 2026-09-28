Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case025.MainClaim` is implemented in `Case025Formalization.lean`. The proof supplies both decomposition milestones: a positive-presentation half-density engine and a finite occurrence-noise transfer.

The positive engine adapts `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` to the case-local presenter-first `OnlineGenerator`, including a checked causality bridge from finite input prefixes. The transfer enumerates finite expansions using the supplied Paper 17 coding, proves the actual repeated stream is an exact presentation of one expansion, transfers eventual novelty after the finite extraneous set has appeared, and compares ambient-prefix lower densities through a vanishing finite-error ratio.

Material declarations used include `patientScope_generation_and_lowerDensity`, `finiteExpansionOracleFamily`, `displayedNoise_finite`, `finiteExpansion_displayedNoise_displayedOmissions`, `finset_eventually_subset_sample`, and `tendsto_prefixCount_atTop`.

Both required checks succeeded:
- `bash LEAN_CHECK.sh output/Case025Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The checker reports `target_kernel_pass: true`, no prohibited mechanisms, no inadmissible axioms, and only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.
