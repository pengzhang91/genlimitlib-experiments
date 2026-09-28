import Stage3Model
open Set Function
#check iff_not_self
#check not_iff_self

namespace Trial

theorem sets_not_countable : ¬ Countable (Set ℕ) := by
  intro h
  letI : Countable (Set ℕ) := h
  obtain ⟨f, hf⟩ := (countable_iff_exists_surjective (α := Set ℕ)).mp inferInstance
  let D : Set ℕ := {n | n ∉ f n}
  obtain ⟨n, hn⟩ := hf D
  have hmem : n ∈ D ↔ n ∉ D := by
    change (n ∉ f n) ↔ n ∉ D
    rw [hn]
  exact iff_not_self hmem

end Trial
