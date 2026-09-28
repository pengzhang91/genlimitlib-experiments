Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved and checked. The construction uses perfect squares as an infinite sparse common core, a square-sparse common input stream from `GenLimit.InfiniteContamination.SharedVanishingPresentation`, and nested targets obtained by adjoining progressively larger cofinite tails. Eventual validity for the square core confines generator-first announcements to the squares plus finitely many early outputs; prefix-count estimates and the supplied square-count limit then give zero relative upper density in every selected cofinite target. The pair bound follows by combining this zero density with the general upper bound of one.

For global feasibility, `squareGenerator` outputs a fresh perfect square whose root pairs the round index with a bound on the observed prefix. This makes outputs target-valid for every family member, larger than all inputs seen through the current round, and nonrepeating.

Materially used declarations include `SparseSquare`, `sparseBetweenSquares`, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, `squareSparseMerge`, `range_squareSparseMerge`, `squareSparseMerge_injective`, and `squareSparseMerge_vanishingNoise_of_core_subset`, together with the shared model definitions.
