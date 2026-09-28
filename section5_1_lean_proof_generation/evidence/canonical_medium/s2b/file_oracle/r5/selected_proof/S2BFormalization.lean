import Helpers

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_not_countable,
    Stage3Proof.positive, Stage3Proof.negative⟩
