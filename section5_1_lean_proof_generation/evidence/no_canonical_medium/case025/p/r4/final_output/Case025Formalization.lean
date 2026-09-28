import Stage3Model
import Helpers

open Stage3Case025

/-- Fully checked Section 5 reduction from the positive-presentation engine to
finite occurrence noise. -/
theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple :=
  Stage3Case025.finiteNoiseTransfer

/-- The exact target follows once the omitted patient-scope machine theorem is
supplied. -/
theorem stage3_result_of_positive_engine
    (hpositive : PositivePresentationHalfDensity) : MainClaim :=
  stage3_finite_noise_transfer hpositive
