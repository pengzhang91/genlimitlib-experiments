import Helpers

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact ⟨squares, Set.univ, input, squares_ssubset_univ,
      legal_squares, legal_univ, pairObstruction⟩
  · intro r hr
    exact ⟨finiteFamily r, input, finiteFamily_witness hr⟩
