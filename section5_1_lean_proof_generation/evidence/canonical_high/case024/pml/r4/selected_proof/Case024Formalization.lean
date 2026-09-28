import Stage3Model
import Case024Helpers

open Stage3Case024

 theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024Proof.core, Set.univ, Case024Proof.commonInput,
      Case024Proof.core_ssubset_univ,
      Case024Proof.commonInput_legal_of_core_subset Set.Subset.rfl,
      Case024Proof.commonInput_legal_of_core_subset (Set.subset_univ _),
      Case024Proof.pairObstruction⟩
  · intro r hr
    exact ⟨Case024Proof.nestedFamily r, Case024Proof.commonInput,
      Case024Proof.manyTargetWitness hr⟩
