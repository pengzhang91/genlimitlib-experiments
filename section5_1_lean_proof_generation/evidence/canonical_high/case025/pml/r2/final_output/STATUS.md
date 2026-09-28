Overall outcome: COMPLETE

Implemented `stage3_result : Stage3Case025.MainClaim` in `Case025Formalization.lean`.

The proof constructs the patient-machine online adapter, proves its finite-prefix causality, instantiates the supplied positive-presentation half-density theorem, closes the family under coded finite expansions, and transfers both eventual novelty and ambient-prefix relative lower density across the finite contamination set.

Validation completed with:
- `bash LEAN_CHECK.sh output/Case025Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The checked theorem uses only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
