import Case024Helpers

open Stage3Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Core, Set.univ, commonStream, core_proper_univ, ?_, ?_, pair_obstruction⟩
    · exact commonStream_legal Set.Subset.rfl
    · exact commonStream_legal (Set.subset_univ _)
  · intro r hr
    refine ⟨family r, commonStream, family_strictlyNested r hr, ?_,
      family_globallyFeasible r hr, family_obstruction r hr⟩
    intro j
    exact commonStream_legal (core_subset_family r j)
