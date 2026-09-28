import SeparationHelpers

theorem stage3_result : Stage3Case019.MainClaim := by
  exact ⟨Stage3Case019.stage3_countable_half_density,
    Stage3Case019.stage3_uncountable_separation⟩
