Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved and passes the supplied entry-point checker. The proof constructs the infinite perfect-square core, the full universe as the outer target, and a common injective square-sparse presentation supplied by `GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation`.

The pathwise argument proves that eventual validity for the square core confines generator-first announcements to the square set plus a finite exception set, yielding zero ambient-prefix upper density on `Set.univ`. Integrability from the target hypotheses and the universal density bound by one then give the required expectation inequality and strict-half consequence.

For every finite `r ≥ 2`, the proof constructs a strictly nested family consisting of the square core with successive canonical nonsquare additions and `Set.univ` as the final member. A target-independent generator outputs fresh, nonrepeating perfect squares using an injective natural-number pairing code, proving global feasibility. Simultaneous validity again forces expected density zero on the final member.

Materially used declarations include `squareSparseMerge`, `squareSparseMerge_injective`, `range_squareSparseMerge`, `squareSparseMerge_vanishingNoise_of_core_subset`, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, `NovelGeneratesInLimit`, and `GeneratorFirst`.

Remaining gap: none.
