import Section4.ReplaySufficiency
import Mathlib.Order.Preorder.Finite

/-! The characterization is preserved when all outputs are chosen inclusion-minimal. -/
namespace Section4.Replay

open Set
open GenLimit.Replay

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_minimal_below (L : ι → Set α) (h : ι) :
    ∃ i, L i ⊆ L h ∧ MinimalLanguage L i := by
  classical
  let C := Finset.univ.filter (fun i => L i ⊆ L h)
  have hC : C.Nonempty := ⟨h, by simp [C]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_minimalFor L C hC
  have hisub : L i ⊆ L h := (Finset.mem_filter.mp hi).2
  refine ⟨i, hisub, ?_⟩
  intro k hk
  exact hmin (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk.trans hisub⟩) hk

noncomputable def minimalBelow (L : ι → Set α) (h : ι) : ι :=
  (exists_minimal_below L h).choose

theorem minimalBelow_subset (L : ι → Set α) (h : ι) :
    L (minimalBelow L h) ⊆ L h := (exists_minimal_below L h).choose_spec.1

theorem minimalBelow_minimal (L : ι → Set α) (h : ι) :
    MinimalLanguage L (minimalBelow L h) := (exists_minimal_below L h).choose_spec.2

theorem residual_eq_of_first_subset (L : ι → Set α) {j j' i k : ι}
    (hsub : L j' ⊆ L j) (heq : residual L j' i = residual L j' k) :
    residual L j i = residual L j k := by
  ext x
  constructor
  · rintro ⟨hxi, hxj⟩
    have hxj' : x ∉ L j' := fun hx => hxj (hsub hx)
    exact ⟨(residual_eq_mem_iff L j' heq hxj').mp hxi, hxj⟩
  · rintro ⟨hxk, hxj⟩
    have hxj' : x ∉ L j' := fun hx => hxj (hsub hx)
    exact ⟨(residual_eq_mem_iff L j' heq hxj').mpr hxk, hxj⟩

theorem goodFirst_of_subset (L : ι → Set α) {P : Finset ι} {j j' : ι}
    (hgood : GoodFirst L P j) (hsub : L j' ⊆ L j) : GoodFirst L P j' := by
  intro i hi
  obtain ⟨h, hh⟩ := hgood i hi
  refine ⟨h, ?_⟩
  intro k hk
  rcases (mem_group L j' P i k).mp hk with ⟨hkP, heq⟩
  apply hh k
  exact (mem_group L j P i k).mpr ⟨hkP, residual_eq_of_first_subset L hsub heq⟩

noncomputable def minimalFirstChoice (L : ι → Set α) (P : Finset ι) : ι :=
  minimalBelow L (firstChoice L P)

noncomputable def minimalLowerChoice (L : ι → Set α) (E : Finset ι) : ι :=
  minimalBelow L (lowerChoice L E)

theorem minimalFirstChoice_spec (L : ι → Set α) (hc : Criterion L) (x : α)
    (hx : ∃ i, x ∈ L i) :
    GoodFirst L (profile L x) (minimalFirstChoice L (profile L x)) := by
  exact goodFirst_of_subset L (firstChoice_spec L hc x hx) (minimalBelow_subset L _)

theorem minimalLowerChoice_spec (L : ι → Set α) : LowerSpec L (minimalLowerChoice L) := by
  intro E hE k hk
  exact (minimalBelow_subset L _).trans (lowerChoice_spec L E hE k hk)

theorem chosenOutput_minimal (L : ι → Set α) (lower : Finset ι → ι)
    (hlower : ∀ E, MinimalLanguage L (lower E)) {j : ι}
    (hj : MinimalLanguage L j) (C : Finset ι) :
    MinimalLanguage L (chosenOutput L lower j C) := by
  classical
  unfold chosenOutput
  split_ifs
  · exact hlower _
  · exact hj

/-- Every actual (positive-prefix) output is inclusion-minimal, including the first. -/
theorem minimal_generator_outputs (L : ι → Set α) (s : ℕ → α) (n : ℕ) :
    MinimalLanguage L
      (properOutput (generator L (minimalFirstChoice L) (minimalLowerChoice L)) s (n + 1)) := by
  rw [generator_output_succ]
  split_ifs
  · exact minimalBelow_minimal L _
  · exact chosenOutput_minimal L (minimalLowerChoice L)
      (fun _ => minimalBelow_minimal L _) (minimalBelow_minimal L _) _

/-- The semantic correctness theorem with inclusion-minimal outputs. -/
theorem minimal_generator_correct (L : ι → Set α) (hc : Criterion L) :
    IsProperLimitReplayGenerator L
      (generator L (minimalFirstChoice L) (minimalLowerChoice L)) :=
  generator_correct L (minimalFirstChoice L) (minimalLowerChoice L)
    (minimalFirstChoice_spec L hc) (minimalLowerChoice_spec L)

end Section4.Replay
