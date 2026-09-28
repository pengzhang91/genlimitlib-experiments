import Stage3Model
import Case024Helpers

open Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨core, Set.univ, commonStream, core_ssubset_univ, ?_, ?_, pairObstruction⟩
    · exact commonStream_legal Set.Subset.rfl core_infinite
    · exact commonStream_legal (Set.subset_univ _) Set.infinite_univ
  · intro r hr
    exact ⟨family r, commonStream, manyTargetWitness hr⟩
