import Helpers

open Stage3Proof

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨targetClass_not_countable, uniform_without_samples, negative_claim⟩
