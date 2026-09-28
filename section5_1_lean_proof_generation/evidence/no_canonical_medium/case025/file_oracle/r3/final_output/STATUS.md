Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case025.MainClaim` is proved and checked. The construction runs the supplied patient-scope machine on an explicitly enumerated family of finite expansions. A prefix-causality argument packages that machine as the required presenter-first online generator. Finite occurrence noise is absorbed into a finite expansion of the target; eventual freshness transfers validity back to the original target, and a finite-reference perturbation estimate transfers the relative lower-density bound.

Materially used declarations include `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`, `GenLimit.InfiniteContamination.finiteExpansionOracleFamily`, `GenLimit.InfiniteContamination.displayedNoise_finite`, `GenLimit.Generic.finset_eventually_subset_sample`, and `GenLimit.PatientScope.tendsto_prefixCount_atTop`.

Required checks completed without `sorryAx` or prohibited mechanisms. The audited axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
