Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case025.MainClaim` is proved in `Case025Formalization.lean` without `sorry`, new axioms, unsafe definitions, native evaluation, or kernel-bypass mechanisms.

The proof constructs a within-round online adapter for the certified patient-scope generator, proves the positive-presentation half-density engine, closes the indexed family under coded finite additions, transfers eventual novel generation by waiting until all finitely many extraneous values have appeared, and transfers relative lower density through a finite extension using ambient prefix-count inequalities and a vanishing error term.

Materially used declarations include `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`, `GenLimit.PatientMachine.patientScope_lowerDensity_half`, finite-expansion coding from `GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency`, `GenLimit.Generic.valuesOutside_eq_image_violationIndices`, `GenLimit.Generic.finset_eventually_subset_sample`, and the patient-scope prefix-count convergence lemmas.

Checks completed successfully:
- `bash LEAN_CHECK.sh output/Case025Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The final gate reports kernel success, no prohibited mechanisms, and only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.
