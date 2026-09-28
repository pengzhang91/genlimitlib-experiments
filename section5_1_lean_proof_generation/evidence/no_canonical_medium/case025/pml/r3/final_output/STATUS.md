Overall outcome: COMPLETE

Implemented `stage3_result : Stage3Case025.MainClaim` in `output/Case025Formalization.lean`.

The proof wraps the supplied patient machine as a causal online generator, applies the patient-scope generation and relative lower-density theorem, and uses the supplied finite-expansion encoding to reinterpret a complete finite-occurrence-noise stream as an exact positive presentation. Local checked lemmas transfer novelty after all finitely many extraneous values have appeared and transfer relative lower density from the finite expansion back to the original infinite target.

Validation:
- `bash LEAN_CHECK.sh output/Case025Formalization.lean` passed.
- The proof uses only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
- No prohibited mechanisms were detected.
