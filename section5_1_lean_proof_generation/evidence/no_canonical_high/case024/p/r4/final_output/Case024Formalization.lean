import Case024Helpers

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact
      ⟨Case024.core, Case024.full, Case024.commonInput,
        Case024.core_ssubset_full, Case024.legal_core,
        Case024.legal_full, Case024.pairObstruction_core_full⟩
  · intro r hr
    exact
      ⟨Case024.nestedFamily r, Case024.commonInput,
        Case024.manyTargetWitness_nested hr⟩
