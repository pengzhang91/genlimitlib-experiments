Overall outcome: PARTIAL

`output/Case025Helpers.lean` and `output/Case025Formalization.lean` compile with
the supplied checker.  The strongest checked result is
`stage3_finite_noise_reduction`: assuming the exact positive-presentation
half-density engine, it constructs the fixed finite-addition expansion of the
family, proves every finitely contaminated complete stream presents one member
of that expansion, transfers eventual novelty back to the original target,
and preserves the half-density conclusion on the stream range.  The helper
also proves canonical trajectory existence for every local online generator.

The exact declaration `stage3_result : Stage3Case025.MainClaim` is not proved.
Two gaps remain: formalizing the patient-stack positive-presentation engine,
and completing the analytic lemma that deleting finitely many target values
preserves `relativeLowerDensity`.  No placeholder, new axiom, or prohibited
kernel mechanism is used.

Material sources and declarations: `CANONICAL_FULL_PROOF.md`,
`Stage3Model.lean`, `GenLimit.Presents`,
`GenLimit.Generic.FinitelyManyViolations`,
`GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and
`GenLimit.PatientScope.relativeLowerDensity`.
