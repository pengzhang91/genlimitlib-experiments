import Case024Helpers

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact ⟨Case024.sparseCore, Set.univ, Case024.commonInput,
      Case024.sparseCore_ssubset_univ,
      Case024.commonInput_legal_of_core_subset
        Case024.sparseCore_infinite Set.Subset.rfl,
      Case024.commonInput_legal_of_core_subset
        Set.infinite_univ (Set.subset_univ _),
      Case024.pairObstruction_core_univ⟩
  · intro r hr
    exact ⟨Case024.nestedFamily r, Case024.commonInput,
      Case024.nestedFamily_witness hr⟩
