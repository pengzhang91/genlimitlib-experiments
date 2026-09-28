import output.SeparationProof

open Stage3Case019

theorem stage3_result : Stage3Case019.MainClaim := by
  exact ⟨Case019.countable_half_density, Case019.uncountable_separation⟩
