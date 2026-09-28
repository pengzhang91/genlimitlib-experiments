Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case017.MainClaim` is proved in `Case017Formalization.lean`. The checked construction uses a family-tailored noncomputable online generator, finite-family version-space stabilization, global freshness and output injectivity, a finite-prefix charging injection proving the half-core bound, eventual announcement of every core point proving the never-presented-core bound, and liminf arguments for target-relative lower density.

Materially used declarations include `Stage3Case017.MainClaim`, `Stage3Case017.informationCore`, `Stage3Case017.Follows`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.relativeLowerDensity`, together with standard mathlib finset, filter, and liminf lemmas. The exact entry-point check passed using only `propext`, `Classical.choice`, and `Quot.sound`.

Remaining gap: none.
