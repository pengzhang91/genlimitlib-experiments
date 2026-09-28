import Section4.ReplayNecessity
import GenLimit.Paper31_BoundedMemory.IncrementalIndexObstruction

/-! The three-language construction transfer for an arbitrary countable universe,
infinite common core, and three distinct markers outside that core. -/

namespace Section4.Replay

open GenLimit.Replay GenLimit.BoundedMemory

variable {α : Type*} [Countable α]

theorem triangle_not_properly_generatable
    (T : Set α) (a b c : α) (hT : T.Infinite)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haT : a ∉ T) (hbT : b ∉ T) (hcT : c ∉ T) :
    ¬ ProperlyGeneratableInLimitWithReplay (appendixTriangleLanguages T a b c) := by
  classical
  let L := appendixTriangleLanguages T a b c
  intro hgen
  have hcrit := criterion_of_properlyGeneratable L hgen
  obtain ⟨x, hx⟩ := hT.nonempty
  have hxall : ∀ i, x ∈ L i := by
    intro i
    fin_cases i <;> simp [L, appendixTriangleLanguages, hx]
  obtain ⟨j, hj⟩ := hcrit x ⟨0, hxall 0⟩
  have hp : ∀ i, i ∈ profile L x := fun i => (mem_profile L x i).mpr (hxall i)
  have hpair : ∀ j : Fin 3, ∃ i k : Fin 3,
      i ≠ k ∧ residual L j i = residual L j k := by
    intro j
    fin_cases j
    · refine ⟨1, 2, by decide, ?_⟩
      ext y
      simp only [residual, L, appendixTriangleLanguages, Set.mem_diff, Set.mem_insert_iff]
      tauto
    · refine ⟨0, 2, by decide, ?_⟩
      ext y
      simp only [residual, L, appendixTriangleLanguages, Set.mem_diff, Set.mem_insert_iff]
      tauto
    · refine ⟨0, 1, by decide, ?_⟩
      ext y
      simp only [residual, L, appendixTriangleLanguages, Set.mem_diff, Set.mem_insert_iff]
      tauto
  obtain ⟨i, k, hik, hres⟩ := hpair j
  obtain ⟨h, hh⟩ := hj i (hp i)
  have hhi := hh i (self_mem_group L j (hp i))
  have hhk := hh k ((mem_group L j (profile L x) i k).mpr ⟨hp k, hres.symm⟩)
  have hanti := appendixTriangleLanguages_antichain hab hac hbc haT hbT hcT
  exact hik ((hanti h i hhi).symm.trans (hanti h k hhk))

theorem triangle_transfer
    (T : Set α) (a b c : α) (hT : T.Infinite)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haT : a ∉ T) (hbT : b ∉ T) (hcT : c ∉ T) :
    (∀ i, (appendixTriangleLanguages T a b c i).Infinite) ∧
      ¬ ProperlyGeneratableInLimitWithReplay (appendixTriangleLanguages T a b c) :=
  ⟨appendixTriangleLanguages_infinite hT a b c,
    triangle_not_properly_generatable T a b c hT hab hac hbc haT hbT hcT⟩

end Section4.Replay

#print axioms Section4.Replay.triangle_transfer
