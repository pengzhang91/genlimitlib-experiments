import output.CountableScratch
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology
open GenLimit

namespace Case019

lemma prefixCount_finite_extension
    {K E : Set ℕ} (hKE : K ⊆ E) (hfin : (E \ K).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount E n ≤
      GenLimit.PatientScope.prefixCount K n + hfin.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply le_trans (Finset.card_le_card ?_)
    (Finset.card_union_le (GenLimit.PatientScope.prefixFinset K n) hfin.toFinset)
  intro x hx
  have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
  by_cases hxK : x ∈ K
  · exact Finset.mem_union_left _
      (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxK⟩)
  · exact Finset.mem_union_right _
      ((Set.Finite.mem_toFinset hfin).mpr ⟨hx'.2, hxK⟩)

lemma relativeLowerDensity_finite_extension
    {K E D : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfin : (E \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (D ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
  classical
  let c := hfin.toFinset.card
  let f : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  let g : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let err : ℕ → ℝ := fun n => -(c : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herr0 : Tendsto err atTop (𝓝 0) := by
    have hdiv := tendsto_const_div_atTop_nhds_zero_nat (-(c : ℝ))
    exact hdiv.comp hcountK
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hf_le_one : ∀ n, f n ≤ 1 := by
    intro n
    by_cases hz : GenLimit.PatientScope.prefixCount E n = 0
    · simp [f, hz]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      dsimp [f]
      rw [div_le_one hpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  have hcompare : ∀ᶠ n : ℕ in atTop, f n + err n ≤ g n := by
    filter_upwards [hcountK.eventually (eventually_gt_atTop 0)] with n hn
    have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hkE : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount E n :=
      GenLimit.PatientScope.prefixCount_mono hKE n
    have hepos : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn hkE
    have hAcNat : GenLimit.PatientScope.prefixCount (D ∩ E) n ≤
        GenLimit.PatientScope.prefixCount (D ∩ K) n + c := by
      unfold GenLimit.PatientScope.prefixCount
      apply le_trans (Finset.card_le_card ?_)
        (Finset.card_union_le
          (GenLimit.PatientScope.prefixFinset (D ∩ K) n) hfin.toFinset)
      intro x hx
      have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
      by_cases hxK : x ∈ K
      · exact Finset.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr
            ⟨hx'.1, hx'.2.1, hxK⟩)
      · exact Finset.mem_union_right _
          ((Set.Finite.mem_toFinset hfin).mpr ⟨hx'.2.2, hxK⟩)
    have hAc : (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) ≤
        GenLimit.PatientScope.prefixCount (D ∩ K) n + c := by
      exact_mod_cast hAcNat
    have hfirst : f n ≤
        (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) := by
      dsimp [f]
      exact div_le_div_of_nonneg_left (by positivity) hkpos (by exact_mod_cast hkE)
    dsimp [err, g]
    rw [show (-(c : ℝ)) / (GenLimit.PatientScope.prefixCount K n : ℝ) =
      -(c / (GenLimit.PatientScope.prefixCount K n : ℝ)) by ring]
    have hsecond :
        (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) -
          c / (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) := by
      rw [div_sub_div_same]
      exact div_le_div_of_nonneg_right (by linarith) hkpos.le
    exact (add_le_add_right hfirst _).trans hsecond
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf f atTop ≤ liminf g atTop
  have hfLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop f :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hf_nonneg)
  have hfUpper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop f :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hf_le_one)
  have hadd : liminf f atTop + liminf err atTop ≤
      liminf (f + err) atTop :=
    le_liminf_add hfLower hfUpper herr0.isBoundedUnder_ge herr0.isCoboundedUnder_ge
  have herrL : liminf err atTop = 0 := herr0.liminf_eq
  rw [herrL, add_zero] at hadd
  exact hadd.trans (liminf_le_liminf hcompare
    (isBoundedUnder_ge_add hfLower herr0.isBoundedUnder_ge)
    (isCoboundedUnder_ge_of_le atTop (fun n => by
      exact (show g n ≤ 1 from by
        by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
        · simp [g, hz]
        · have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
            exact_mod_cast Nat.pos_of_ne_zero hz
          dsimp [g]
          rw [div_le_one hp]
          exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n))))

end Case019
