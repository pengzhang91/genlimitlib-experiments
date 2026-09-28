Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved in `Case024Formalization.lean`. The checked proof supplies both the mandatory nested pair and the finite-many-target strengthening.

The construction uses the infinite set of perfect squares as the sparse common core, the supplied square-sparse merge presentation to obtain one injective full-universe stream with vanishing contamination for every target containing that core, and finite prefixes of canonical nonsquare markers to form strictly nested families. A target-independent generator outputs an increasing fresh square above the current input prefix, establishing global feasibility. Eventual validity for the square core makes all but finitely many generator-first values squares; the supplied square-count bound then forces upper density zero in the universe target. Pointwise density at the core is at most one, yielding the required expectation inequality.

Materially used declarations include `sparseMergePresentation`, `range_sparseMergePresentation`, `sparseMergePresentation_vanishingNoise_of_core_subset`, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, `GenLimit.NovelGeneratesInLimit`, and `GenLimit.GeneratorFirst`.

Both mandated checker commands pass. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no prohibited mechanisms.
