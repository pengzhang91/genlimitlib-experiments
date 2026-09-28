import Stage3Model
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

def core : Set ℕ := {n | (Nat.unpair n).1 = 0}

def swapStream (n : ℕ) : ℕ :=
  let p := Nat.unpair n
  if p.1 = 0 then
    Nat.pair (Nat.unpair p.2).1.succ (Nat.unpair p.2).2
  else
    Nat.pair 0 (Nat.pair (p.1 - 1) p.2)

lemma mem_core_pair_zero (n : ℕ) : Nat.pair 0 n ∈ core := by
  simp [core]

lemma not_mem_core_pair_succ (a b : ℕ) : Nat.pair a.succ b ∉ core := by
  simp [core]

lemma core_iff_exists_pair_zero {n : ℕ} : n ∈ core ↔ ∃ k, n = Nat.pair 0 k := by
  constructor
  · intro hn
    refine ⟨(Nat.unpair n).2, ?_⟩
    simp [core] at hn
    calc
      n = Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 := (Nat.pair_unpair n).symm
      _ = Nat.pair 0 (Nat.unpair n).2 := by rw [hn]
  · rintro ⟨k, rfl⟩
    exact mem_core_pair_zero k

lemma swap_pair_zero (n : ℕ) :
    swapStream (Nat.pair 0 n) =
      Nat.pair (Nat.unpair n).1.succ (Nat.unpair n).2 := by
  simp [swapStream]

lemma swap_pair_succ (a b : ℕ) :
    swapStream (Nat.pair a.succ b) = Nat.pair 0 (Nat.pair a b) := by
  simp [swapStream]

lemma swap_involutive : Function.Involutive swapStream := by
  intro n
  obtain ⟨a, b, rfl⟩ : ∃ a b, n = Nat.pair a b := by
    exact ⟨(Nat.unpair n).1, (Nat.unpair n).2, (Nat.pair_unpair n).symm⟩
  cases a with
  | zero =>
      rw [swap_pair_zero]
      rw [swap_pair_succ]
      simp
  | succ a =>
      rw [swap_pair_succ]
      rw [swap_pair_zero]
      simp

lemma swap_injective : Function.Injective swapStream := swap_involutive.injective

lemma swap_surjective : Function.Surjective swapStream := swap_involutive.surjective

lemma swap_mem_core_iff {n : ℕ} : swapStream n ∈ core ↔ n ∉ core := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, n = Nat.pair a b := by
    exact ⟨(Nat.unpair n).1, (Nat.unpair n).2, (Nat.pair_unpair n).symm⟩
  cases a with
  | zero => simp [swap_pair_zero, core]
  | succ a => simp [swap_pair_succ, core]

lemma core_infinite : core.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n => Nat.pair 0 n)
  · intro a b h
    exact (Nat.pair_eq_pair.mp h).2
  · exact mem_core_pair_zero

end Case024

namespace Case024

lemma tendsto_sqrt_cast_atTop :
    Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  refine Filter.atTop_basis.tendsto_right_iff.mpr ?_
  intro b _
  rw [Filter.eventually_atTop]
  refine ⟨b * b, ?_⟩
  intro n hn
  exact Nat.le_sqrt.mpr hn

lemma tendsto_sqrt_add_div (C : ℕ) :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + C : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have h₁ : Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.sqrt n : ℝ)) atTop (nhds 0) :=
    tendsto_sqrt_cast_atTop.const_div_atTop 1
  have h₂ : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_div_atTop (C : ℝ)
  have hadd : Tendsto
      (fun n : ℕ => (1 : ℝ) / (Nat.sqrt n : ℝ) + (C : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    simpa using h₁.add h₂
  refine squeeze_zero' ?_ ?_ hadd
  · exact Filter.Eventually.of_forall fun n => div_nonneg (by positivity) (by positivity)
  · rw [Filter.eventually_atTop]
    refine ⟨1, ?_⟩
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hspos : (0 : ℝ) < Nat.sqrt n := by
      exact_mod_cast (Nat.sqrt_pos.2 hn)
    have hsquare : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ (n : ℝ) := by
      exact_mod_cast Nat.sqrt_le n
    calc
      ((Nat.sqrt n + C : ℕ) : ℝ) / (n : ℝ) =
          (Nat.sqrt n : ℝ) / n + (C : ℝ) / n := by
            push_cast
            ring
      _ ≤ (1 : ℝ) / Nat.sqrt n + (C : ℝ) / n := by
        apply add_le_add_right
        rw [div_le_div_iff₀ hnpos hspos]
        simpa using hsquare

lemma prefixCount_core_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n ≤ Nat.sqrt n + 1 := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  have hcard :
      ((Finset.range n).filter (fun x => x ∈ core)).card ≤
        (Finset.range (Nat.sqrt n + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun x => (Nat.unpair x).2)
    · intro x hx
      change x ∈ (Finset.range n).filter (fun x => x ∈ core) at hx
      rw [Finset.mem_filter] at hx
      simp only [Finset.mem_range] at hx
      change (Nat.unpair x).2 ∈ Finset.range (Nat.sqrt n + 1)
      simp only [Finset.mem_range]
      apply Nat.lt_succ_of_le
      apply Nat.le_sqrt.mpr
      have hx0 : (Nat.unpair x).1 = 0 := hx.2
      have hrepr : x = Nat.pair 0 (Nat.unpair x).2 := by
        calc
          x = Nat.pair (Nat.unpair x).1 (Nat.unpair x).2 := (Nat.pair_unpair x).symm
          _ = Nat.pair 0 (Nat.unpair x).2 := by rw [hx0]
      let k := (Nat.unpair x).2
      have hpair : Nat.pair 0 k = k * k := by
        cases k with
        | zero => simp [Nat.pair]
        | succ k => simp [Nat.pair]
      have hxle : Nat.pair 0 k ≤ n := by
        rw [← hrepr]
        exact hx.1.le
      rw [hpair] at hxle
      exact hxle
    · intro x hx y hy heq
      change x ∈ (Finset.range n).filter (fun x => x ∈ core) at hx
      change y ∈ (Finset.range n).filter (fun x => x ∈ core) at hy
      rw [Finset.mem_filter] at hx hy
      simp only [Finset.mem_range] at hx hy
      have hx0 : (Nat.unpair x).1 = 0 := hx.2
      have hy0 : (Nat.unpair y).1 = 0 := hy.2
      dsimp at heq
      calc
        x = Nat.pair (Nat.unpair x).1 (Nat.unpair x).2 := (Nat.pair_unpair x).symm
        _ = Nat.pair 0 (Nat.unpair x).2 := by rw [hx0]
        _ = Nat.pair 0 (Nat.unpair y).2 := by rw [heq]
        _ = Nat.pair (Nat.unpair y).1 (Nat.unpair y).2 := by rw [hy0]
        _ = y := Nat.pair_unpair y
  simpa using hcard

lemma tendsto_core_ratio :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount core n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => div_nonneg (by positivity) (by positivity)) ?_
      (tendsto_sqrt_add_div 1)
  intro n
  exact div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_core_le n) (by positivity)

end Case024

namespace Case024

lemma noiseCount_core (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount swapStream core n =
      GenLimit.PatientScope.prefixCount core n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
    GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  congr 1
  ext t
  simp [swap_mem_core_iff]

lemma vanishingNoise_core :
    GenLimit.InfiniteContamination.VanishingNoise swapStream core := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
    GenLimit.InfiniteContamination.empiricalNoiseRate
  convert tendsto_core_ratio using 1
  funext n
  rw [noiseCount_core]
  by_cases hn : n = 0
  · simp [hn, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]
  · simp [hn]

lemma vanishingNoise_univ :
    GenLimit.InfiniteContamination.VanishingNoise swapStream Set.univ := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
    GenLimit.InfiniteContamination.empiricalNoiseRate
    GenLimit.InfiniteContamination.noiseCount
  simp

lemma noOmissions_of_surjective (K : Set ℕ) :
    GenLimit.InfiniteContamination.NoOmissions swapStream K := by
  intro x hx
  exact swap_surjective x

lemma legal_core : Stage3Case024.Legal swapStream core := by
  refine ⟨core_infinite, swap_injective, noOmissions_of_surjective core, ?_⟩
  exact vanishingNoise_core

lemma legal_univ : Stage3Case024.Legal swapStream Set.univ := by
  refine ⟨Set.infinite_univ, swap_injective, noOmissions_of_surjective Set.univ, ?_⟩
  exact vanishingNoise_univ

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount Set.univ n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

end Case024

namespace Case024

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_subset_core_union (A : Set ℕ) (F : Finset ℕ)
    (hA : A ⊆ core ∪ (F : Set ℕ)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount core n + F.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  calc
    ((Finset.range n).filter (fun x => x ∈ A)).card ≤
        (((Finset.range n).filter (fun x => x ∈ core)) ∪ F).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hx ⊢
      rcases hA hx.2 with hxcore | hxF
      · exact Or.inl ⟨hx.1, hxcore⟩
      · exact Or.inr hxF
    _ ≤ ((Finset.range n).filter (fun x => x ∈ core)).card + F.card :=
      Finset.card_union_le _ _

lemma tendsto_subset_core_union_ratio (A : Set ℕ) (F : Finset ℕ)
    (hA : A ⊆ core ∪ (F : Set ℕ)) :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  refine squeeze_zero (fun n => div_nonneg (by positivity) (by positivity)) ?_
      (tendsto_sqrt_add_div (1 + F.card))
  intro n
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnat := (prefixCount_subset_core_union A F hA n).trans
    (Nat.add_le_add_right (prefixCount_core_le n) F.card)
  have hnat' : GenLimit.PatientScope.prefixCount A n ≤ Nat.sqrt n + (1 + F.card) := by
    omega
  exact_mod_cast hnat'

lemma relativeUpperDensity_univ_eq_zero (A : Set ℕ) (F : Finset ℕ)
    (hA : A ⊆ core ∪ (F : Set ℕ)) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  simpa [prefixCount_univ] using tendsto_subset_core_union_ratio A F hA

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_eventually_le atTop
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (by positivity) (by positivity)))
  exact Filter.Eventually.of_forall fun n => by
    have hcount := prefixCount_mono (A := A ∩ K) (B := K) (Set.inter_subset_right) n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · rw [div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hzero))]
      exact_mod_cast hcount

end Case024
