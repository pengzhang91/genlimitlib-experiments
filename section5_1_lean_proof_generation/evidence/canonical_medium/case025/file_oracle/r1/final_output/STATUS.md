Overall outcome: COMPLETE

Proved the exact theorem `stage3_result : Stage3Case025.MainClaim` with no placeholders or unapproved axioms. The proof builds a causal online wrapper around the supplied patient machine, applies its positive-presentation novelty and half-density theorems, codes each repetition-allowing finite-occurrence-noise stream as a finite expansion, transfers eventual validity using tail injectivity and finiteness of extraneous values, and transfers relative lower density across the finite target extension.

Material declarations used include `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`, `GenLimit.PatientMachine.patientScope_lowerDensity_half`, the finite-expansion coding definitions from `FiniteContaminationSufficiency.lean`, and `GenLimit.PatientScope.tendsto_prefixCount_atTop`.

Both required checker entry points pass, and the final target depends only on the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
