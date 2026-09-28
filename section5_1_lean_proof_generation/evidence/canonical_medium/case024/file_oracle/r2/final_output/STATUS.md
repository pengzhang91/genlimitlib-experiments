Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case024.MainClaim` is proved and checked. The construction uses the infinite language of perfect squares as the sparse common core, the supplied square-sparse merge presentation to obtain one injective full stream with vanishing contamination, and `Set.univ` as the second target. Eventual validity in the square language bounds every generator-first ambient prefix by the square count plus finitely many early outputs; the supplied square-count and limit lemmas imply pathwise upper density zero on `Set.univ`, yielding the required expectation inequality.

For every finite `r ≥ 2`, the proof builds a strictly nested family from the square core, finite initial segments of nonsquares, and a final universal target. A target-independent generator outputs a square larger than the entire current input prefix, with a time term ensuring outputs are strictly increasing; this proves global feasibility. The same pathwise argument forces expected upper density zero on the final target.

Material declarations include `squareSparseMerge`, `squareSparseMerge_injective`, `range_squareSparseMerge`, `squareSparseMerge_vanishingNoise_of_core_subset`, `count_sparseSquare_le_sqrt_add_one`, and `tendsto_sparseSqrt_add_one_div` from the supplied shared-presentation module, together with the shared Stage 3 model definitions.
