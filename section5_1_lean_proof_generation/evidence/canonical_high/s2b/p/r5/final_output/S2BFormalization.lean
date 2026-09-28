import Helpers

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3S2BProof.targetClass_uncountable,
    Stage3S2BProof.uniform_generation,
    Stage3S2BProof.negative_claim⟩
