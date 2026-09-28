import Helpers

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025.finiteNoiseTransfer
    Stage3Case025.positivePresentationHalfDensity
