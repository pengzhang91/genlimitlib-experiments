Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case025.MainClaim` is proved in `Case025Formalization.lean` and passes the targeted Lean checker without `sorryAx` or prohibited mechanisms.

The proof packages the supplied patient-scope machine as the required presenter-first online generator, proves finite-prefix causality, and applies `patientScope_generation_and_lowerDensity` / `patientScope_lowerDensity_half` for exact positive presentations. For finite occurrence noise, it applies the supplied finite-expansion family, codes the finitely many displayed off-target values as an add-only expansion, transfers eventual novelty after those values have appeared, and transfers the half-density bound through a one-sided ambient-prefix comparison with a vanishing finite-error term.

Material declarations include `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`, `GenLimit.PatientMachine.patientScope_lowerDensity_half`, `GenLimit.InfiniteContamination.finiteExpansionOracleFamily`, `GenLimit.InfiniteContamination.displayedNoise_finite`, and `GenLimit.PatientScope.tendsto_prefixCount_atTop`.
