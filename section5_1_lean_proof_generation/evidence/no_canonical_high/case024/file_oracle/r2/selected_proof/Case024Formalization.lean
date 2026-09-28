import Case024Helpers

open Stage3Case024

 theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Stage3Case024Proof.Squares, Set.univ,
      Stage3Case024Proof.commonInput, ?_⟩
    exact ⟨Stage3Case024Proof.squares_ssubset_univ,
      Stage3Case024Proof.legal_commonInput Set.Subset.rfl,
      Stage3Case024Proof.legal_commonInput (Set.subset_univ _),
      Stage3Case024Proof.pairObstruction⟩
  · intro r hr
    exact ⟨Stage3Case024Proof.family r,
      Stage3Case024Proof.commonInput,
      Stage3Case024Proof.manyTargetWitness hr⟩
