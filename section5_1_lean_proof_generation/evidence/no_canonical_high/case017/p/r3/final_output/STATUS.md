Overall outcome: COMPLETE

`output/Case017Formalization.lean` proves the exact declaration
`stage3_result : Stage3Case017.MainClaim`.

The proof constructs a deterministic least-fresh generator over the languages
still compatible with the observed prefix. Finiteness of the indexed family
gives eventual stabilization to the information core. The checked helpers
establish eventual target validity, freshness, nonrepetition, inclusion of the
never-presented core in `GeneratorFirst`, and a finite-error prefix-count bound
that yields the one-half relative lower-density guarantee. Monotonicity of
relative lower density supplies the never-presented-core term.

Both required checks succeeded:
- `bash LEAN_CHECK.sh output/Case017Formalization.lean`
- `bash LEAN_CHECK.sh --final`

The final axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx` or prohibited mechanism. Material inputs
were `Stage3Model.lean` and its supplied GenLimit definitions for partial
presentations, novelty, first announcements, prefix counts, and relative lower
density, together with standard mathlib finite-set, filter, liminf, and
ordered-field results.
