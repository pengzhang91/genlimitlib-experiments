Overall outcome: COMPLETE

`output/Case017Formalization.lean` proves the exact declaration
`stage3_result : Stage3Case017.MainClaim`. The complete entry point passes the
supplied Lean checker and axiom audit.

The proof constructs one family-dependent noncomputable online generator. It
uses the current finite version intersection when that intersection is
infinite, selects its least point fresh from the current input prefix and all
prior outputs, and otherwise uses a total fresh fallback. Finite-family
stabilization identifies the version intersection with `informationCore`.
The formal proof establishes eventual novel validity for every compatible
family member, coverage of the information core, inclusion of every
never-presented core point in `GeneratorFirst`, and a finite-prefix injection
that yields the half-core density bound after a vanishing constant-error
liminf argument.

Material inputs: `Stage3Model.lean`, `THEOREM_STATEMENT.md`,
`CANONICAL_FULL_PROOF.md`, and the supplied GenLimit announcement, partial
presentation, online generation, and target-relative density declarations.
