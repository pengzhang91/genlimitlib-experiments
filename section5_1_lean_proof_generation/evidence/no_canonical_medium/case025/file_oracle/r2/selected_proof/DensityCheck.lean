import Helpers
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Stage3Case025

set_option maxHeartbeats 800000 in
private theorem relativeLowerDensity_inter_le_of_subset_finite
    (A K E : Set ℕ) (hKE : K ⊆ E) (hfinite : (E \ K).Finite)
    (hK : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let c : ℕ := hfinite.toFinset.card
  let ratioE : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  let ratioK : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let err : ℕ → ℝ := fun n =>
    (c : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcount : ∀ n,
      GenLimit.PatientScope.prefixCount (A ∩ E) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + c := by
    intro n
    classical
    unfold GenLimit.PatientScope.prefixCount
    have hsub :
        GenLimit.PatientScope.prefixFinset (A ∩ E) n ⊆
          GenLimit.PatientScope.prefixFinset (A ∩ K) n ∪ hfinite.toFinset := by
      intro x hx
      rw [Finset.mem_union]
      by_cases hxK : x ∈ K
      · exact Or.inl (GenLimit.PatientScope.mem_prefixFinset.2
          ⟨(GenLimit.PatientScope.mem_prefixFinset.1 hx).1,
            (GenLimit.PatientScope.mem_prefixFinset.1 hx).2.1, hxK⟩)
      · exact Or.inr ((Set.Finite.mem_toFinset hfinite).2
          ⟨(GenLimit.PatientScope.mem_prefixFinset.1 hx).2.2, hxK⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcompare : ∀ᶠ n : ℕ in atTop, ratioE n ≤ ratioK n + err n := by
    have hpos : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hkR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hden := GenLimit.PatientScope.prefixCount_mono hKE n
    have hnum : (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount (A ∩ K) n + c : ℕ) := by
      exact_mod_cast hcount n
    have heR : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n :=
      lt_of_lt_of_le hkR (by exact_mod_cast hden)
    calc
      ratioE n ≤
          (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        dsimp [ratioE]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hkR
          (by exact_mod_cast hden)
      _ ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n + c : ℕ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt hkR)
      _ = ratioK n + err n := by
        simp only [ratioK, err, Nat.cast_add, add_div]
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
    have htR : Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
        atTop atTop := tendsto_natCast_atTop_atTop.comp ht
    exact tendsto_const_nhds.div_atTop htR
  have hratioE_nonneg : ∀ n, 0 ≤ ratioE n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hratioE_le_one : ∀ n, ratioE n ≤ 1 := by
    intro n
    by_cases hz : GenLimit.PatientScope.prefixCount E n = 0
    · simp [ratioE, hz]
    · have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      change (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          (GenLimit.PatientScope.prefixCount E n : ℝ) ≤ 1
      rw [div_le_one hp]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono inter_subset_right n
  have hratioK_le_one : ∀ n, ratioK n ≤ 1 := by
    intro n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratioK, hz]
    · have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      change (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one hp]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono inter_subset_right n
  change liminf ratioE atTop ≤ liminf ratioK atTop
  apply (liminf_le_iff
    (isCoboundedUnder_ge_of_le atTop hratioE_le_one)
    (isBoundedUnder_of ⟨0, hratioE_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hrK, hry⟩ := exists_between hy
  have hfreq : ∃ᶠ n : ℕ in atTop, ratioK n < r :=
    frequently_lt_of_liminf_lt
      (isCoboundedUnder_ge_of_le atTop hratioK_le_one) hrK
  have herrSmall : ∀ᶠ n : ℕ in atTop, err n < y - r :=
    herr.eventually_lt_const (sub_pos.mpr hry)
  exact (hfreq.and_eventually (herrSmall.and hcompare)).mono (by
    intro n hn
    linarith [hn.2.2])


end Stage3Case025
