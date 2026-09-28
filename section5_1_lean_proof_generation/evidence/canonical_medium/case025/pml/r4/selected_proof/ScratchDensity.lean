import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Test

open GenLimit.PatientScope

theorem prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    prefixCount (A ∪ B) n ≤ prefixCount A n + prefixCount B n := by
  classical
  unfold prefixCount
  calc
    (prefixFinset (A ∪ B) n).card ≤
        (prefixFinset A n ∪ prefixFinset B n).card := by
      apply Finset.card_le_card
      intro x hx
      rw [mem_prefixFinset] at hx
      simp only [Finset.mem_union, mem_prefixFinset]
      rcases hx.2 with hxA | hxB
      · exact Or.inl ⟨hx.1, hxA⟩
      · exact Or.inr ⟨hx.1, hxB⟩
    _ ≤ (prefixFinset A n).card + (prefixFinset B n).card :=
      Finset.card_union_le _ _

 theorem prefixCount_le_ncard {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    prefixCount F n ≤ F.ncard := by
  classical
  unfold prefixCount
  rw [Set.ncard_eq_toFinset_card F hF]
  apply Finset.card_le_card
  intro x hx
  exact hF.mem_toFinset.mpr (mem_prefixFinset.mp hx).2

theorem finite_extension_half
    (A K R : Set ℕ) (hK : K.Infinite) (hKR : K ⊆ R)
    (hfin : (R \ K).Finite)
    (hhalf : (1 / 2 : ℝ) ≤ relativeLowerDensity (A ∩ R) R) :
    (1 / 2 : ℝ) ≤ relativeLowerDensity (A ∩ K) K := by
  let f : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ R) n : ℝ) / prefixCount R n
  let g : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / prefixCount K n
  let e : ℕ → ℝ := fun n =>
    (R \ K).ncard / (prefixCount K n : ℝ)
  have hcast : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_prefixCount_atTop hK)
  have he : Tendsto e atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcast
  have hcomp : ∀ᶠ n : ℕ in atTop, f n - e n ≤ g n := by
    have hKpos : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
      (tendsto_prefixCount_atTop hK).eventually (eventually_gt_atTop 0)
    filter_upwards [hKpos] with n hn
    have hnum : prefixCount (A ∩ R) n ≤
        prefixCount (A ∩ K) n + (R \ K).ncard := by
      calc
        prefixCount (A ∩ R) n ≤
            prefixCount ((A ∩ K) ∪ (R \ K)) n :=
          prefixCount_mono (by
            intro x hx
            by_cases hxK : x ∈ K
            · exact Or.inl ⟨hx.1, hxK⟩
            · exact Or.inr ⟨hx.2, hxK⟩) n
        _ ≤ prefixCount (A ∩ K) n + prefixCount (R \ K) n :=
          prefixCount_union_le _ _ _
        _ ≤ prefixCount (A ∩ K) n + (R \ K).ncard :=
          Nat.add_le_add_left (prefixCount_le_ncard hfin n) _
    have hden : prefixCount K n ≤ prefixCount R n := prefixCount_mono hKR n
    have hnR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hdenR : (prefixCount K n : ℝ) ≤ prefixCount R n := by exact_mod_cast hden
    have hnumR : (prefixCount (A ∩ R) n : ℝ) ≤
        prefixCount (A ∩ K) n + (R \ K).ncard := by exact_mod_cast hnum
    dsimp [f, g, e]
    have hrnonneg : (0 : ℝ) ≤ prefixCount (A ∩ R) n := by positivity
    have hdiv : (prefixCount (A ∩ R) n : ℝ) / prefixCount R n ≤
        (prefixCount (A ∩ R) n : ℝ) / prefixCount K n := by
      exact div_le_div_of_nonneg_left hrnonneg hnR hdenR
    calc
      (prefixCount (A ∩ R) n : ℝ) / prefixCount R n -
          (R \ K).ncard / prefixCount K n
          ≤ (prefixCount (A ∩ R) n : ℝ) / prefixCount K n -
              (R \ K).ncard / prefixCount K n := sub_le_sub_right hdiv _
      _ = ((prefixCount (A ∩ R) n : ℝ) - (R \ K).ncard) /
            prefixCount K n := by rw [sub_div]
      _ ≤ (prefixCount (A ∩ K) n : ℝ) / prefixCount K n := by
        apply div_le_div_of_nonneg_right _ hnR.le
        linarith
  have hf_lower : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hf_upper : ∀ n, f n ≤ 1 := by
    intro n
    by_cases hn : prefixCount R n = 0
    · simp [f, hn]
    · change (prefixCount (A ∩ R) n : ℝ) / prefixCount R n ≤ 1
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  have hg_lower : ∀ n, 0 ≤ g n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hg_upper : ∀ n, g n ≤ 1 := by
    intro n
    by_cases hn : prefixCount K n = 0
    · simp [g, hn]
    · change (prefixCount (A ∩ K) n : ℝ) / prefixCount K n ≤ 1
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  rw [relativeLowerDensity] at hhalf ⊢
  change (1 / 2 : ℝ) ≤ liminf g atTop
  change (1 / 2 : ℝ) ≤ liminf f atTop at hhalf
  by_contra hnot
  have hlt : liminf g atTop < (1 / 2 : ℝ) := lt_of_not_ge hnot
  let ε : ℝ := ((1 / 2 : ℝ) - liminf g atTop) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hevent : ∀ᶠ n in atTop, e n < ε := (he.eventually (gt_mem_nhds hε))
  have hcompare : ∀ᶠ n in atTop, f n - ε ≤ g n := by
    filter_upwards [hcomp, hevent] with n hfg heps
    linarith
  have hleftBounded : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => f n - ε) :=
    isBoundedUnder_of ⟨-ε, fun n => by linarith [hf_lower n]⟩
  have hlim := liminf_le_liminf hcompare hleftBounded
    (isCoboundedUnder_ge_of_le atTop hg_upper)
  rw [liminf_sub_const atTop f ε
    (isCoboundedUnder_ge_of_le atTop hf_upper)
    (isBoundedUnder_of ⟨0, hf_lower⟩)] at hlim
  dsimp [ε] at hlim
  linarith

end Test
