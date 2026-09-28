Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3Case024.MainClaim` is proved in `Case024Formalization.lean`. Both the mandatory pair obstruction and the finite-many-target strengthening are included.

The checked construction uses the infinite set of perfect squares as a zero-density common core, finite strict extensions for intermediate targets, and `Set.univ` as the maximal target. A single sparse-merge presentation is legal for every target. Simultaneous eventual validity forces generator-first announcements to differ from the square core by only finitely many points, giving relative upper density zero in the maximal target. The pair bound combines this with the general upper-density bound by one. A direct square-above-the-observed-prefix generator proves global feasibility.

Material supplied declarations include `SparseSquare`, `sparseMergePresentation`, `sparseMergePresentation_injective`, `range_sparseMergePresentation`, `sparseMergePresentation_vanishingNoise_of_core_subset`, `count_sparseSquare_le_sqrt_add_one`, and `tendsto_sparseSqrt_add_one_div` from `GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation`, together with `GeneratorFirst`, `NovelGeneratesInLimit`, and `PatientScope.prefixCount` through the shared model.

Both `bash LEAN_CHECK.sh output/Case024Formalization.lean` and `bash LEAN_CHECK.sh --final` passed. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
