Overall outcome: PARTIAL

`output/Case019Formalization.lean` compiles without `sorry`, `admit`, unsafe code, or added axioms. It proves these substantial parts of the separation clause:

- the supplied `finiteOmissionClass q` is extensionally uncountable, via an explicit injection from `Set ℕ` into its second subclass;
- every member of that family is infinite;
- at level `q`, the supplied sweep generator eventually outputs a target member fresh from the current sample (`SampleFreshGeneratesAfterInput`);
- at level `q+1`, every semantic generator has a fixed target and legal injective contaminated presentation on which that weaker eventual guarantee fails.

These are assembled as `Case019.weak_uncountable_separation`. The exact `stage3_result` declaration is intentionally absent rather than filled with a placeholder or unapproved axiom.

The remaining gap is the dense, output-novel strengthening: constructing and checking a history-semantic nonrepeating sweep with balanced relative lower density at least `1/4`, plus adapting the patient-scope half-density machine to finite contaminated prefixes and transferring its density across the finite expansion of each countable target.

Materially used declarations include `finiteNoiseLevel_upper`, `finiteNoiseLevel_lower`, `finiteOmissionClass_uus`, the finite-omission class definitions, signed-integer encodings, and `powerSet_not_countable`.
