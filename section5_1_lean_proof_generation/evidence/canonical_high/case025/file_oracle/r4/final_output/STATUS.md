Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case025.MainClaim` is proved in `Case025Formalization.lean`. The checked construction wraps the P39 patient-scope machine as the required presenter-first online generator, proves prefix causality, applies `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` for exact repeated presentations, and transfers the result through the P17 finite-expansion family.

For occurrence-counted finite noise, the proof shows the distinct displayed-noise set is finite, codes the actual stream range as a finite expansion with no omissions, transfers eventual validity using finite sample coverage and same-round freshness, and proves that changing the density reference from the finite extension back to the original infinite target cannot decrease relative lower density.

Material declarations include `finiteExpansionOracleFamily`, `finiteExpansionCode_encode`, `stream_presents_range`, `finset_eventually_subset_sample`, `tendsto_prefixCount_atTop`, and the patient-machine operational theorem. The entry-point check accepts only `propext`, `Classical.choice`, and `Quot.sound`.
