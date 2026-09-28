import Stage3Model
import Case024Helpers

open GenLimit.InfiniteContamination

 theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Stage3Case024Proof.Squares, Set.univ,
      Stage3Case024Proof.commonInput, ?_,
      Stage3Case024Proof.legal_commonInput_squares,
      Stage3Case024Proof.legal_commonInput_univ,
      Stage3Case024Proof.pairObstruction⟩
    rw [Set.ssubset_def]
    constructor
    · exact Set.subset_univ _
    · intro hback
      exact Stage3Case024Proof.marker_not_mem_squares 0
        (hback (Set.mem_univ _))
  · intro r hr
    exact ⟨Stage3Case024Proof.nestedFamily r,
      Stage3Case024Proof.commonInput,
      Stage3Case024Proof.manyTargetWitness hr⟩
