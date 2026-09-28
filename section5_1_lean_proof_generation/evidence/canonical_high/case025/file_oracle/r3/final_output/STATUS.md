Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case025.MainClaim` is implemented in `Case025Formalization.lean`. Both the direct entry-point check and `LEAN_CHECK.sh --final` passed. The final audit reports only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`, with no inadmissible axioms or prohibited mechanisms.

The proof uses `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` to build the positive-presentation half-density engine, proves the required online causality wrapper, encodes finite additions via `Nat.pair` and `Finset.equivBitIndices`, and establishes a finite-perturbation transfer theorem for relative lower density. These components yield the finite-noise transfer principle and hence the exact main claim.

Material supplied declarations include the shared definitions in `Stage3Model.lean` and the patient-scope generation/lower-density theorem from the supplied research modules.
