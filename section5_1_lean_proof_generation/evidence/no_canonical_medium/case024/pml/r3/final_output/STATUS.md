Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is implemented in `Case024Formalization.lean` and passes the supplied entry-point checker.

The construction uses the infinite set of perfect squares as a zero-density common core, finitely many canonical nonsquare markers for strict intermediate inclusions, and `Set.univ` as the largest target. A shared sparse-merge presentation is injective, covers every target, and has vanishing contamination for each. A target-independent generator repeatedly selects a fresh core element outside the current input and prior outputs, proving global feasibility.

For every admissible randomized trajectory, eventual validity for the smallest target leaves only finitely many generator-first announcements outside the square core. Prefix-count bounds and the supplied square-count asymptotics therefore force relative upper density zero in the largest target. The remaining density is bounded by one, yielding the pair inequality and strict-half consequence; selecting the largest target gives the finite-family zero obstruction.

Materially used declarations include `sparseMergePresentation_injective`, `range_sparseMergePresentation`, `sparseMergePresentation_vanishingNoise_of_core_subset`, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, and `GenLimit.Support.freshFromInfinite`.
