Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case025.MainClaim` is proved and checked. The proof constructs the positive-presentation generator from `GenLimit.PatientMachine`, establishes its online prefix causality, and transfers the result to finitely contaminated complete presentations by enumerating finite language additions. Eventual target validity follows because every finite noise value is eventually observed and freshness excludes it thereafter. The half-density bound transfers through a proved finite-extension prefix-count inequality with vanishing error.

Material declarations used include `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`, `GenLimit.PatientMachine.patientScope_lowerDensity_half`, `GenLimit.Generic.valuesOutside_eq_image_violationIndices`, `GenLimit.Generic.finset_eventually_subset_sample`, and `GenLimit.PatientScope.tendsto_prefixCount_atTop`.
