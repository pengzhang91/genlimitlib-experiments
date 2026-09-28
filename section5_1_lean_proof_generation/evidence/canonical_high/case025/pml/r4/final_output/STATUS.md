Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case025.MainClaim` is proved in `Case025Formalization.lean`. The checked construction wraps the supplied patient-scope machine as the required presenter-first `OnlineGenerator`, proves causality from finite-prefix agreement, runs it over the supplied coded finite-expansion family, transfers eventual target validity using output injectivity and finiteness of noisy values, and transfers the half-density bound through a finite-superlanguage ambient-prefix estimate.

Material declarations used include `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`, `stream_ne_output`, `output_ne_of_lt`, `GenLimit.InfiniteContamination.finiteExpansionOracleFamily`, `finiteExpansion_displayedNoise_displayedOmissions`, `displayedNoise_finite`, and `GenLimit.PatientScope.tendsto_prefixCount_atTop`.

`bash LEAN_CHECK.sh output/Case025Formalization.lean` passes. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
