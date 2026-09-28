import Countable
import Separation

theorem stage3_result : Stage3Case019.MainClaim := by
  exact ⟨Case019Helpers.countable_half_density,
    Case019Helpers.uncountable_separation⟩
