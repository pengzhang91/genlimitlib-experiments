import Helpers

open Stage3Case024
open Case024Helpers

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨squareCore, Set.univ, commonInput, ?_,
      commonInput_legal squareCore (Set.Subset.rfl),
      commonInput_legal Set.univ (Set.subset_univ squareCore),
      pairObstruction⟩
    constructor
    · exact Set.subset_univ squareCore
    · intro hreverse
      exact exceptionalPoint_not_square 0 (hreverse (Set.mem_univ _))
  · intro r hr
    exact ⟨nestedFamily r, commonInput, nestedFamily_witness hr⟩
