Overall outcome: COMPLETE

The exact theorem `stage3_result : Stage3Case024.MainClaim` is proved in `Case024Formalization.lean` and passes the supplied entry-point checker. The construction uses the infinite perfect-square core, its complement, and the supplied square-sparse merge to obtain one injective full-range stream with vanishing contamination for every target containing the core.

The pair obstruction is proved pathwise: eventual validity for the square core confines all but finitely many outputs to a set whose ambient prefix density tends to zero, so the generator-first upper density in `Set.univ` is zero almost surely. The other density is bounded by one, yielding the required expectation sum and strict-half consequence.

For every finite `r ≥ 2`, the proof constructs a strictly nested family by adjoining finitely many canonical nonsquares and ending with `Set.univ`. A target-independent fresh-core generator establishes global feasibility, while the same pathwise density argument gives the many-target zero witness.

Material declarations used include `squareSparseMerge`, `range_squareSparseMerge`, `squareSparseMerge_vanishingNoise_of_core_subset`, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, `prefixCount_mono`, and `GenLimit.Support.freshFromInfinite`.
