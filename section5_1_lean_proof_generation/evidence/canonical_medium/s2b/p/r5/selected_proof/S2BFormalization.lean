import Helpers
import Negative

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Work.targetClass_not_countable,
    Stage3Work.uniform_generation,
    Stage3Work.negative_claim⟩
