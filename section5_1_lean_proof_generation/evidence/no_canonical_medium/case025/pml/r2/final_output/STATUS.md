Overall outcome: COMPLETE

Implemented and checked `stage3_result : Stage3Case025.MainClaim` in `Case025Formalization.lean`.

The proof wraps the supplied Paper 39 patient-scope machine as a presenter-first online generator and establishes the positive-presentation half-density engine. It then transfers the result to finite occurrence contamination by enumerating every finite enlargement of the indexed family, identifying the contaminated stream as an exact presentation of a finite superlanguage, proving eventual return to the original target using freshness and bounded violation indices, and showing that finite enlargement cannot increase the relevant relative lower-density bound.

Material declarations used include `GenLimit.PatientMachine.patientScope_generation_and_lowerDensity`, `GenLimit.Generic.valuesOutside_eq_image_violationIndices`, `GenLimit.PatientScope.tendsto_prefixCount_atTop`, and standard mathlib liminf/limsup addition lemmas.

The entry-point checker reports `STAGE3_GATE` with no prohibited mechanisms or inadmissible axioms; dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
