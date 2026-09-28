Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case025.MainClaim` is implemented in `Case025Formalization.lean` and passes the entry-point kernel check. The proof first adapts `GenLimit.PatientMachine.output` to the case-local presenter-first `OnlineGenerator`; `PatientCausality.lean` proves that each output depends only on the input through the current round. It then applies `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity` to establish the positive-presentation engine.

For finite occurrence-counted contamination, the proof enumerates all finite additions using `Nat.pair`, `Nat.unpair`, and `Finset.equivBitIndices`. Every contaminated stream exactly presents one expanded language. Eventual validity transfers back by combining finite extra values with eventual output nonrepetition. Two ambient-prefix lemmas transfer lower density: finite removal from the numerator cannot lower the asymptotic bound, and enlarging the denominator can only lower the relative density.

Material declarations include `PatientMachine.patientScope_generation_and_lowerDensity`, `PatientScope.tendsto_prefixCount_atTop`, `PatientScope.prefixCount_mono`, `Generic.valuesOutside_eq_image_violationIndices`, and the patient machine definitions in `Patient/Machine.lean`.

The checked axiom dependency is exactly `propext`, `Classical.choice`, and `Quot.sound`; no prohibited mechanism is used.
