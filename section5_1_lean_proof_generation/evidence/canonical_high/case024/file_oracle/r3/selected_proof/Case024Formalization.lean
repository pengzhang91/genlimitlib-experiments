import Case024Helpers

open GenLimit.InfiniteContamination

 theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024.Core, Set.univ, Case024.commonInput, ?_, ?_, ?_,
      Case024.pairObstruction⟩
    · have hsub : Case024.Core ⊆ (Set.univ : Stage3Case024.Language) :=
        Set.subset_univ _
      apply (Set.ssubset_iff_of_subset hsub).2
      exact ⟨sparseBetweenSquares 0, Set.mem_univ _,
        Case024.between_not_mem_core 0⟩
    · exact Case024.legal_of_core_subset Set.Subset.rfl Case024.core_infinite
    · exact Case024.legal_of_core_subset (Set.subset_univ _)
        Set.infinite_univ
  · intro r hr
    exact ⟨Case024.family r, Case024.commonInput,
      Case024.manyTargetWitness hr⟩
