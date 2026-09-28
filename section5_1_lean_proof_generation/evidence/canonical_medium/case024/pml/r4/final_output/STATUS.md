Overall outcome: COMPLETE

`output/Case024Formalization.lean` proves the exact declaration `stage3_result : Stage3Case024.MainClaim`. The checked construction uses the supplied square-sparse presentation machinery with the perfect squares as the infinite common core and `Set.univ` as the largest target. A pathwise finite-exception argument proves zero ambient-prefix upper density for generator-first announcements whenever outputs are eventually valid for the square language; integration then gives the required two-target expectation inequality.

For every `r ≥ 2`, the source defines a strictly nested family formed by adjoining initial segments of the supplied nonsquare sequence and ending in `Set.univ`. The same common stream is legal for every member. A target-independent generator recursively selects a fresh square outside the finite observed-input and previous-output sets, establishing global feasibility. Simultaneous validity for the first family member forces expected upper density zero at the final member.

Materially used declarations include `sparseMergePresentation`, `sparseMergePresentation_injective`, `range_sparseMergePresentation`, `sparseMergePresentation_vanishingNoise_of_core_subset`, `count_sparseSquare_le_sqrt_add_one`, `tendsto_sparseSqrt_add_one_div`, `Nat.nth_mem_of_infinite`, `GenLimit.NovelGeneratesInLimit`, and `GenLimit.GeneratorFirst`.

The targeted checker passed with only `propext`, `Classical.choice`, and `Quot.sound`.
