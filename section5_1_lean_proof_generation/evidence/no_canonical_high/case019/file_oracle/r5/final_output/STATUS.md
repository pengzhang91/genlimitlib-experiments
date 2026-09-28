Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case019.MainClaim` is proved in `Case019Formalization.lean`. The complete entry point passes the supplied checker with only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`; no prohibited mechanism is used.

The countable clause uses the supplied patient-scope generation theorem, a causal prefix-generator bridge, finite-expansion transfer of novelty, and finite-expansion invariance of relative lower density.

The separation clause uses `finiteOmissionClass q`. Its uncountability is proved by an injection from `Set ℕ`; infinitude comes from `finiteOmissionClass_uus`; the adjacent-level negative result is transferred from `finiteNoiseLevel_lower`. The positive generator is a stateful pair-sweep generator. Pair capture in the balanced integer order yields one generator-first target value in every eventual four-rank block, proving relative lower density at least `1/4`.

Remaining gap: none.

Material supplied declarations include `PatientMachine.patientScope_generation_and_lowerDensity`, `InfiniteContamination.exists_finiteExpansion_index_for_stream`, `finiteOmissionClass_uus`, and `finiteNoiseLevel_lower`.
