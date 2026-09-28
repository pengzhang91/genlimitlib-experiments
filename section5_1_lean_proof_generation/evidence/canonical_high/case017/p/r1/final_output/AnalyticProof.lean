import Case017Helpers
import Mathlib

open Set Filter
open scoped Topology

namespace Stage3Case017

noncomputable section

lemma prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => GenLimit.PatientScope.prefixCount K n) atTop atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop
    (R := ℕ) (r := 1) Nat.zero_lt_one] at hK
  simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Set.indicator, Finset.sum_filter] using hK

lemma ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    (0 : ℝ) ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  have hnum : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
      GenLimit.PatientScope.prefixCount K n :=
    Nat.cast_le.mpr (prefixCount_mono hAK n)
  by_cases hzero : (GenLimit.PatientScope.prefixCount K n : ℝ) = 0
  · simp [hzero]
  · exact (div_le_one (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hzero))).2 hnum

lemma half_density_le_of_prefix_bound {A B K : Set ℕ} {C : ℕ}
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hK : K.Infinite)
    (hcount : ∀ n, GenLimit.PatientScope.prefixCount A n ≤
      2 * GenLimit.PatientScope.prefixCount B n + C) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let b : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    ((C : ℝ) / 2) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have ha0 : ∀ n, 0 ≤ a n := fun n => ratio_nonneg A K n
  have ha1 : ∀ n, a n ≤ 1 := fun n => ratio_le_one hAK n
  have hb0 : ∀ n, 0 ≤ b n := fun n => ratio_nonneg B K n
  have hb1 : ∀ n, b n ≤ 1 := fun n => ratio_le_one hBK n
  have he0 : ∀ n, 0 ≤ e n := by
    intro n
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  have heC : ∀ n, e n ≤ (C : ℝ) := by
    intro n
    by_cases hk0 : GenLimit.PatientScope.prefixCount K n = 0
    · simp [e, hk0]
    · have hk1 : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hhalf : (C : ℝ) / 2 ≤ (C : ℝ) := by
        have hC : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
        linarith
      calc
        e n ≤ (C : ℝ) / 2 := (div_le_iff₀ (by positivity :
          (0 : ℝ) < GenLimit.PatientScope.prefixCount K n)).2
            (by simpa [e] using mul_le_mul_of_nonneg_left hk1 (by positivity : (0 : ℝ) ≤ C / 2))
        _ ≤ C := hhalf
  have herr : Tendsto e atTop (𝓝 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat ((C : ℝ) / 2)).comp
      (prefixCount_tendsto_atTop hK)
  have hpoint : ∀ n, (1 / 2 : ℝ) * a n ≤ b n + e n := by
    intro n
    by_cases hk0 : GenLimit.PatientScope.prefixCount K n = 0
    · have haCount0 : GenLimit.PatientScope.prefixCount A n = 0 :=
        Nat.eq_zero_of_le_zero (hk0 ▸ prefixCount_mono hAK n)
      simp [a, b, e, hk0, haCount0]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        positivity
      have hcast : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount B n : ℝ) + C := by
        exact_mod_cast hcount n
      calc
        (1 / 2 : ℝ) * a n =
            (GenLimit.PatientScope.prefixCount A n : ℝ) /
              (2 * GenLimit.PatientScope.prefixCount K n) := by
                simp [a]
                ring
        _ ≤ (2 * (GenLimit.PatientScope.prefixCount B n : ℝ) + C) /
              (2 * GenLimit.PatientScope.prefixCount K n) := by
                exact (div_le_div_iff_of_pos_right (by positivity)).2 hcast
        _ = b n + e n := by
              simp [b, e]
              field_simp
  have hscale :
      (1 / 2 : ℝ) * liminf a atTop ≤
        liminf (fun n => (1 / 2 : ℝ) * a n) atTop := by
    simpa only [liminf_const, Pi.mul_apply] using
      (le_liminf_mul (f := atTop)
        (u := fun _ : ℕ => (1 / 2 : ℝ)) (v := a)
        (Eventually.of_forall fun _ => by norm_num)
        (isBoundedUnder_of_eventually_le (a := (1 / 2 : ℝ))
          (Eventually.of_forall fun _ => le_rfl))
        (Eventually.of_forall ha0)
        ((isBoundedUnder_of_eventually_le (Eventually.of_forall ha1)).isCoboundedUnder_ge))
  have hmono : liminf (fun n => (1 / 2 : ℝ) * a n) atTop ≤
      liminf (fun n => b n + e n) atTop := by
    refine Filter.liminf_le_liminf (Eventually.of_forall hpoint) (hu := ?_) (hv := ?_)
    · exact isBoundedUnder_of_eventually_ge
        (Eventually.of_forall fun n => mul_nonneg (by norm_num) (ha0 n))
    · exact (isBoundedUnder_of_eventually_le
        (Eventually.of_forall fun n => add_le_add (hb1 n) (heC n))).isCoboundedUnder_ge
  have hadd : liminf (fun n => b n + e n) atTop ≤ liminf b atTop := by
    have hle := liminf_add_le (f := atTop) (u := e) (v := b)
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall he0))
      (isBoundedUnder_of_eventually_le (Eventually.of_forall heC))
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hb0))
      ((isBoundedUnder_of_eventually_le (Eventually.of_forall hb1)).isCoboundedUnder_ge)
    rw [herr.limsup_eq, zero_add] at hle
    simpa only [add_comm] using hle
  change (1 / 2 : ℝ) * liminf a atTop ≤ liminf b atTop
  exact hscale.trans (hmono.trans hadd)

end

end Stage3Case017
