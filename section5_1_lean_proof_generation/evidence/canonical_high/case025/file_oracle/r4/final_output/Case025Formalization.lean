import Helpers

open Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
