Overall outcome: PARTIAL

`output/Case019Formalization.lean` is checker-clean as a Lean source and contains no `sorry`, `admit`, new axioms, unsafe definitions, or kernel-bypass mechanisms.

Strongest checked results:

- `Case019.finiteOmissionClass_sampleFresh_lower` proves the complete negative conjunct required by the separation clause, in the exact `Stage3Model` predicates: every semantic generator has a fixed target in `finiteOmissionClass q` and a legal level-`q+1` injective value-contaminated presentation on which `SampleFreshGeneratesAfterInput` fails.
- `Case019.finiteOmissionClass_sampleFresh_upper` translates the supplied P12 level-`q` upper bound into the exact inclusive-time sample-fresh predicate used by the target.
- `Case019.finiteOmissionClass_infinite` proves every language in that witness class is infinite.
- `Case019.exists_exact_finiteExpansion` proves every legal bounded-contamination input in the countable clause is an exact presentation of a coded member of the P17 finite-expansion oracle family.

Remaining gaps are the two quantitative positive arguments: adapting the P39 patient stream machine to `Generic.Generator` and transferring its half-density through finite additions, and formalizing output novelty, uncountability, and balanced-order quarter density for the P12 witness family. Consequently no declaration named `stage3_result` is asserted.

Materially used declarations: `exists_finiteExpansion_index_for_stream`, `finiteNoiseLevel_upper`, `finiteNoiseLevel_lower`, and `finiteOmissionClass_uus`.
