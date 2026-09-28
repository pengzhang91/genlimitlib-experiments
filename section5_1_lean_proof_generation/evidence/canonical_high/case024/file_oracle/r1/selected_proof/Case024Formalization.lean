import Stage3Model
import «output».Case024Helpers

open Stage3Case024

 theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024.core, Set.univ, Case024.commonStream,
      Case024.core_ssubset_univ, ?_, ?_, Case024.pairObstruction⟩
    · exact Case024.commonStream_legal Set.Subset.rfl Case024.core_infinite
    · exact Case024.commonStream_legal (Set.subset_univ _)
        Set.infinite_univ
  · intro r hr
    exact ⟨Case024.nestedFamily r, Case024.commonStream,
      Case024.manyTargetWitness r hr⟩
