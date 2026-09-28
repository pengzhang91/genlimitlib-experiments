Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case017.MainClaim` is proved in `Case017Formalization.lean` and checked through the supplied root gate. The proof constructs one family-dependent noncomputable online generator, proves finite-family stabilization to the information core, eventual novel target-valid generation for every compatible target, the half-core density bound by a finite-prefix pairing argument, and the never-presented-core bound by eventual announcement and monotonicity.

Material sources and declarations used: `Stage3Model.lean`, `THEOREM_STATEMENT.md`, `CANONICAL_FULL_PROOF.md`, `GenLimit.Generic.StreamIn`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.relativeLowerDensity`. The checked theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`; no prohibited mechanism or placeholder is used.
