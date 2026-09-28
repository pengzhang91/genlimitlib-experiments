import Stage3Model
import Case024Helpers

open Stage3Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Core, Set.univ, commonStream, core_ssubset_univ, ?_, ?_,
      pairObstruction⟩
    · exact commonStream_legal Set.Subset.rfl core_infinite
    · exact commonStream_legal (Set.subset_univ Core) Set.infinite_univ
  · intro r hr
    exact ⟨Family r, commonStream, manyTargetWitness hr⟩
