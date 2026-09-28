import Transfer

open Stage3Case025

/-- Checked Section 5 transfer: finite occurrence noise reduces to the
positive-presentation half-density engine by closing the family under finite
additions. -/
theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  exact checked_finite_noise_transfer

/-- The exact endpoint follows from the still-unformalized Section 4 positive
presentation engine and the checked Section 5 transfer. -/
theorem stage3_result_from_positive
    (hpositive : PositivePresentationHalfDensity) : Stage3Case025.MainClaim := by
  exact stage3_finite_noise_transfer hpositive
