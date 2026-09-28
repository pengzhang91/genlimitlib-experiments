import Case024Helpers

open GenLimit.InfiniteContamination

open Case024


theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨core, Set.univ, commonStream, ?_, ?_, ?_, pairObstruction⟩
    · apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨Set.subset_univ _, ?_⟩
      intro heq
      have htwo : 2 ∈ (Set.univ : Set ℕ) := Set.mem_univ 2
      exact sparseBetweenSquares_not_core 0 (by
        convert heq ▸ htwo using 1 <;> norm_num [sparseBetweenSquares])
    · exact legal_commonStream_of_core_subset (Set.Subset.rfl) core_infinite
    · exact legal_commonStream_of_core_subset (Set.subset_univ _) Set.infinite_univ
  · intro r hr
    exact ⟨family r, commonStream, manyTargetWitness_family hr⟩
