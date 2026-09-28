import Case019Helpers

open Stage3Case019

namespace Case019Formalization

/-- Checked structural core of the separation clause: for every noise level,
the canonical marker-and-tail class is extensionally uncountable and all of
its languages are infinite. -/
theorem stage3_uncountable_family_core :
    ∀ q : ℕ, ∃ family : LanguageClass ℤ,
      family = separationFamily q ∧
      ¬family.Countable ∧ ∀ K ∈ family, K.Infinite := by
  intro q
  exact ⟨separationFamily q, rfl, separationFamily_not_countable q,
    separationFamily_infinite q⟩

end Case019Formalization
