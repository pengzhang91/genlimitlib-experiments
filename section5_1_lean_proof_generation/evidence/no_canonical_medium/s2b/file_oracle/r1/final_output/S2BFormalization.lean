import Helpers

open Stage3S2B

/-- Checked positive portion of `Stage3S2B.MainClaim`. -/
theorem stage3_positive :
    ¬ Stage3S2B.targetClass.Countable ∧
      Stage3S2B.UniformlyGeneratableWithoutSamples := by
  exact ⟨targetClass_not_countable, uniformly_generatable⟩
