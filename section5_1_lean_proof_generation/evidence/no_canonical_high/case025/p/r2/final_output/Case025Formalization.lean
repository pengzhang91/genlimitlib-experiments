import FiniteNoiseTransfer

open Stage3Case025

/-- Checked reduction of the exact Stage 3 claim to the positive-presentation
half-density engine. -/
theorem stage3_result_of_positive_engine
    (positiveEngine : PositivePresentationHalfDensity) : MainClaim := by
  exact stage3_finite_noise_transfer positiveEngine
