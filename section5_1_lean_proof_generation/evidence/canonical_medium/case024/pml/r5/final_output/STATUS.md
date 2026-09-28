Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case024.MainClaim` is proved and checked. The construction uses the infinite set of perfect squares as the sparse common core, the supplied `sparseMergePresentation` to obtain one injective full-range stream with vanishing contamination, and finite initial sets of canonical nonsquares to form strictly nested finite families capped by `Set.univ`.

For every admissible randomized generator, eventual validity on the square core places its output range inside the core plus a finite set. Prefix-count bounds for squares then force the generator-first set to have relative upper density zero in `Set.univ`; the probability-one identity is integrated directly. A max-of-current-prefix square generator proves global feasibility on every common legal presentation.

Material declarations used include `GenLimit.InfiniteContamination.sparseMergePresentation`, its injectivity/range/vanishing-noise theorems, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and `GenLimit.PatientScope.prefixCount`.

Checked sources: `output/Case024Helpers.lean` and `output/Case024Formalization.lean`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
