Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case017.MainClaim` is proved and passes the entry-point checker. The construction uses a family-tailored least-viable online generator and a recursively defined output trajectory. Finite-family stabilization yields eventual target validity and freshness for every compatible language.

The density proof establishes a finite-prefix pairing bound between presenter-first core elements and generator-first core elements, then passes to relative lower densities using bounded liminf monotonicity and a vanishing stabilization error. A separate inclusion proves the full lower-density bound for core elements never appearing in the input. These two estimates combine with `max_le`.

Materially used sources and declarations include `Stage3Model.lean`, `THEOREM_STATEMENT.md`, `CANONICAL_FULL_PROOF.md`, the supplied GenLimit vocabulary exposed by the model, `Stage3Case017.informationCore`, `Stage3Case017.Follows`, `Stage3Case017.SucceedsFor`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.relativeLowerDensity`.

Remaining gap: none. The checked axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
