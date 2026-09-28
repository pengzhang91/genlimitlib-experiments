import Transfer

open Stage3Case025

/-- Checked reduction of the exact endpoint to the positive-presentation engine. -/
theorem stage3_result_reduced
    (positive : PositivePresentationHalfDensity) : MainClaim := by
  exact stage3_finite_noise_transfer positive
