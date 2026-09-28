import Section4.ReplayNecessity
import Section4.ReplayTriangle
import Section4.ReplayCorollary

/-! Endpoints corresponding to the proper-replay appendix.
The equivalence below uses GenLimitLib's existing P22 full-history replay
semantics. Finiteness of the index type and countability of the point type
are explicit; duplicate indices are allowed. The theorem is stronger than
the appendix in not requiring every language to be infinite. -/
namespace Section4.Replay

open Set
open GenLimit.Replay

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem criterion_iff_realized_profiles (L : ι → Set α) :
    Criterion L ↔ ∀ P : Finset ι,
      (∃ x, profile L x = P) → P.Nonempty → ∃ j, GoodFirst L P j := by
  constructor
  · intro hc P hreal hnonempty
    obtain ⟨x, rfl⟩ := hreal
    obtain ⟨i, hi⟩ := hnonempty
    exact hc x ⟨i, (mem_profile L x i).mp hi⟩
  · intro hc x hx
    obtain ⟨i, hi⟩ := hx
    exact hc (profile L x) ⟨x, rfl⟩ ⟨i, (mem_profile L x i).mpr hi⟩

/-- Exact finite-family characterization in the existing proper-replay model. -/
theorem finite_replay_characterization [Countable α] (L : ι → Set α) :
    ProperlyGeneratableInLimitWithReplay L ↔ Criterion L :=
  ⟨criterion_of_properlyGeneratable L, criterion_sufficient L⟩

/-- Equivalent form grouped by every nonempty realized membership profile. -/
theorem finite_replay_characterization_profiles [Countable α] (L : ι → Set α) :
    ProperlyGeneratableInLimitWithReplay L ↔
      ∀ P : Finset ι, (∃ x, profile L x = P) → P.Nonempty →
        ∃ j, ∀ i ∈ P, ∃ h, ∀ k ∈ group L j P i, L h ⊆ L k := by
  rw [finite_replay_characterization, criterion_iff_realized_profiles]
  rfl

#print axioms triangle_transfer
#print axioms finite_replay_characterization
#print axioms finite_replay_characterization_profiles
#print axioms finite_state_replay_corollary

end Section4.Replay
