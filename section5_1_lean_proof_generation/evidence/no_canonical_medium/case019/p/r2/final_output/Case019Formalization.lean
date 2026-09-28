import Case019Helpers

open Stage3Case019

namespace Case019Partial

/-- Checked structural part of the paper's adjacent-level hierarchy family. -/
theorem separation_family_exists (q : ℕ) :
    ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧ ∀ K ∈ family, K.Infinite := by
  exact ⟨hierarchyFamily q, hierarchyFamily_uncountable q,
    hierarchyFamily_infinite q⟩

end Case019Partial
