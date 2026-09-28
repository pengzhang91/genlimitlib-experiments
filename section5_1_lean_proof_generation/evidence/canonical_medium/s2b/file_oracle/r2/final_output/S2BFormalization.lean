import Helpers

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3S2B.targetClass_not_countable,
    Stage3S2B.uniform_generation, Stage3S2B.negative_claim⟩
