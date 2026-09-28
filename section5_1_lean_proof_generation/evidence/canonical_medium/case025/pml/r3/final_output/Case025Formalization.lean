import Transfer

/-- Presentation-dependent half-density under finite occurrence noise. -/
theorem stage3_result : Stage3Case025.MainClaim := by
  exact Case025.Transfer.finiteNoiseTransfer Case025.positive
