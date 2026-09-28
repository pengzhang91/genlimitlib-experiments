import «output».Helpers

open Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact finiteNoiseTransferPrinciple positivePresentationHalfDensity
