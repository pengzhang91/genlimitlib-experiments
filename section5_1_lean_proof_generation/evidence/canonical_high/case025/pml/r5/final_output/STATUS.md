Overall outcome: COMPLETE

Implemented the exact root-level theorem
`stage3_result : Stage3Case025.MainClaim` in
`output/Case025Formalization.lean`.

The proof uses the supplied patient-scope machine for exact positive
presentations, closes the indexed family under coded finite additions, proves
that every complete finite-occurrence-contaminated presentation exactly
presents one coded expansion, transfers eventual validity using global output
injectivity, and transfers relative lower density from the finite expansion
back to the original infinite target via a vanishing prefix-count error.

Supporting online-causality and positive-presentation lemmas are in
`output/Case025Helpers.lean`.

Verification completed successfully:
- `bash LEAN_CHECK.sh output/Case025Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The final gate reports `target_kernel_pass: true`, no inadmissible axioms, and
no prohibited mechanisms. The only dependencies reported are the permitted
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
