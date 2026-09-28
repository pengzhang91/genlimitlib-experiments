import Stage3Model
import Case024Helpers

theorem stage3_result : Stage3Case024.MainClaim := by
  exact ⟨Case024Helpers.pairClaim, Case024Helpers.manyTargetClaim⟩
