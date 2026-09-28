Overall outcome: PARTIAL

The Lean source compiles without `sorry`, new axioms, unsafe code, or kernel-bypass mechanisms. It proves the following checked components:

- every level-`q` injective bounded-distinct-noise presentation of a countable target is a finite-noise/finite-omission enumeration and hence an exact presentation of a member of the supplied finite-expansion family (`countable_exact_expansion_reduction`);
- the supplied `finiteOmissionClass q` is extensionally uncountable and all its members are infinite;
- one supplied generator achieves eventual sample-fresh validity at level `q` on that class;
- every generator has a fixed target and legal level-`q+1` presentation on which eventual sample-fresh validity fails (`separation_checked_core`).

The exact `stage3_result` is not present. Remaining gaps are the stronger output-versus-output novelty and quantitative density conclusions: transporting the patient-scope half-density theorem through finite target perturbations for the countable clause, and constructing/proving a novelty-aware common-negative sweep with balanced-order quarter density for the uncountable positive clause.

Material declarations used include `PatientMachine.patientScope_generation_and_lowerDensity`, `InfiniteContamination.exists_finiteExpansion_index_for_stream`, `NoiseLossFeedback.finiteNoiseLevel_upper`, `NoiseLossFeedback.finiteNoiseLevel_lower`, `NoiseLossFeedback.finiteOmissionClass_uus`, and `UnionClosedness.powerSet_not_countable`.
