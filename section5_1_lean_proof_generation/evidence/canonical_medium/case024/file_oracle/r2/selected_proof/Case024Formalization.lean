import Stage3Model
import Case024Helpers

open Stage3Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨squareLanguage, Set.univ, commonInput, square_ssubset_univ,
      commonInput_legal_square, commonInput_legal_of_square_subset
        (Set.subset_univ _), pairObstruction⟩
  · intro r hr
    exact ⟨nestedFamily r, commonInput, manyTargetWitness hr⟩
