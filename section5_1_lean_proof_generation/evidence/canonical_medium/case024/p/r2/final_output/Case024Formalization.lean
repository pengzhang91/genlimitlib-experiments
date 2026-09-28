import Helpers

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Pow2, Set.univ, input, ?_, legal_pow2, legal_univ, pair_obstruction⟩
    constructor
    · exact Set.subset_univ Pow2
    · intro h
      exact odd_ge_three_not_pow2 0 (h (Set.mem_univ 3))
  · intro r hr
    exact ⟨family r, input, manyTargetWitness hr⟩
