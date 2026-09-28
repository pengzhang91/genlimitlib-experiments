import Helpers

open Stage3S2B

/-- Checked partial result: the uncountability and uniform no-sample clauses. -/
theorem stage3_result_first_two :
    ¬ targetClass.Countable ∧ UniformlyGeneratableWithoutSamples := by
  exact ⟨Stage3Proof.targetClass_not_countable,
    Stage3Proof.uniformly_generatable⟩
