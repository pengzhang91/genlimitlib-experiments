Overall outcome: PARTIAL

The checked artifact proves `stage3_positive_eventual_novel`: for every indexed
family of infinite languages, one deterministic online generator has a
following trajectory that is eventually target-valid, avoids the presenter
through the current round, and never repeats, on every exact positive
presentation (including repetitions).

`Case025Helpers.lean` contains the checked construction: finite-history nested
scopes, delayed scope depth, least fresh selection, the recursively defined
trajectory, freshness/injectivity, eventual containment of every fixed target
in each finite scope, eventual selection of the target scope, and the resulting
`NovelGeneratesInLimit` theorem.

The remaining gap is the half-density charging argument and then the finite
occurrence-noise transfer. Consequently the exact declaration
`stage3_result : Stage3Case025.MainClaim` is not claimed. The complete-entry
checker therefore fails honestly rather than relying on `sorry`, an added
axiom, or a kernel bypass.

Material sources used: `Stage3Model.lean`, `THEOREM_STATEMENT.md`,
`CANONICAL_FULL_PROOF.md`, and the supplied GenLimit vocabulary declarations.
