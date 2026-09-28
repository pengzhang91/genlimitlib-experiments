import «output».Many

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  exact ⟨pairWitness, manyWitnesses⟩
