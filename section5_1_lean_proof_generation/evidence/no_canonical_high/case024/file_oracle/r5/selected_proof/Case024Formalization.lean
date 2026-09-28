import Helpers

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  refine ⟨pairWitness, ?_⟩
  intro r hr
  obtain ⟨input, hwitness⟩ := targetFamily_manyTargetWitness hr
  exact ⟨targetFamily r, input, hwitness⟩
