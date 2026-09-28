import Helpers

open Stage3Case019

/-- Checked structural part of the separation witness: at every noise level
there is an extensional uncountable class of infinite integer languages. -/
theorem stage3_separation_witness_structure :
    ∀ q : ℕ, ∃ family : LanguageClass ℤ,
      family = Case019.witnessFamily q ∧
      ¬family.Countable ∧ ∀ K ∈ family, K.Infinite := by
  intro q
  exact ⟨Case019.witnessFamily q, rfl, Case019.witnessFamily_structural q⟩
