import MainDraft

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨squares, Set.univ, sparseEnumeration, ?_, ?_, ?_, pairObstruction_squares_univ⟩
    · refine ⟨Set.subset_univ _, ?_⟩
      intro hreverse
      exact gapEven_not_square 0 (hreverse (Set.mem_univ _))
    · exact (sparseEnumeration_legal squares (Set.Subset.rfl)).2 squares_infinite
    · exact (sparseEnumeration_legal Set.univ (Set.subset_univ _)).2 Set.infinite_univ
  · intro r hr
    exact ⟨targetFamily r, sparseEnumeration, targetFamily_witness hr⟩
