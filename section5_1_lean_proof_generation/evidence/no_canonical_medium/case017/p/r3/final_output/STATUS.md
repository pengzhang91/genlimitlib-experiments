Overall outcome: COMPLETE

- Implemented the exact theorem `stage3_result : Stage3Case017.MainClaim` in `Case017Formalization.lean`.
- Constructed a causal greedy generator, proved finite-family stabilization and eventual novelty, and established the required missing-core and half-density bounds by prefix counting and liminf arguments.
- Materially used the shared definitions from `Stage3Model.lean` together with standard mathlib finite-set, cardinality, filter, and liminf/limsup infrastructure.
- The complete entry point passes the targeted Lean checker using only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.
