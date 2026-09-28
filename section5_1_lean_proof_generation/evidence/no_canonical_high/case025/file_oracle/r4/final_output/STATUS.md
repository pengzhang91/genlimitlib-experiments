Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case025.MainClaim` is proved in `Case025Formalization.lean`. The proof packages the supplied patient-scope machine as a presenter-first online generator, obtains the positive-presentation half-density theorem, encodes each finite-occurrence-noise presentation as an exact presentation of a coded finite expansion, and transfers both eventual novelty/validity and ambient-prefix relative lower density back to the original target.

Both required checks succeeded:
- `bash LEAN_CHECK.sh output/Case025Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The final audit reports no inadmissible axioms or prohibited mechanisms. Dependencies are only the permitted `propext`, `Classical.choice`, and `Quot.sound`.

Material supplied declarations include `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`, the finite-expansion coding in `FiniteContaminationSufficiency.lean`, finite-noise facts from `FiniteExpansionTransfer.lean`, and ambient-prefix density definitions and prefix-count divergence from `TargetDensity.lean`.
