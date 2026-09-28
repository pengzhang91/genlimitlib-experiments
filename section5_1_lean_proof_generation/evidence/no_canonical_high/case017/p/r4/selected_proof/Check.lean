import Case017Formalization
import Mathlib

open Set Filter
open scoped Topology
open Stage3Case017
open Stage3Case017Proof

 theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => GenLimit.PatientScope.prefixCount K n) atTop atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) (r := 1) Nat.zero_lt_one] at hK
  convert hK using 1
  funext n
  simp only [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxK : x ∈ K
  · simp [hxK, Set.indicator_of_mem]
  · simp [hxK, Set.indicator_of_notMem]

theorem half_density_of_prefix_bound {A B K : Set ℕ}
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hK : K.Infinite) (C : ℕ)
    (hcount : ∀ n, GenLimit.PatientScope.prefixCount A n ≤
      2 * GenLimit.PatientScope.prefixCount B n + C) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  let a : ℕ → ℝ := fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)
  let b : ℕ → ℝ := fun n => (GenLimit.PatientScope.prefixCount B n : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n => (C : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)
  have ha0 : ∀ n, 0 ≤ a n := fun n => ratio_nonneg A K n
  have hb0 : ∀ n, 0 ≤ b n := fun n => ratio_nonneg B K n
  have he0 : ∀ n, 0 ≤ e n := by intro n; dsimp [e]; positivity
  have ha1 : ∀ n, a n ≤ 1 := fun n => ratio_le_one hAK n
  have hb1 : ∀ n, b n ≤ 1 := fun n => ratio_le_one hBK n
  have heC : ∀ n, e n ≤ (C : ℝ) := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [e, hzero]
    · have hkone : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      dsimp [e]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have herr : Tendsto e atTop (nhds 0) := by
    dsimp [e]
    exact Filter.Tendsto.const_div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (prefixCount_tendsto_atTop hK)) C
  have hpoint : ∀ n, (1 / 2 : ℝ) * a n ≤ e n + b n := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [a, b, e, hzero]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by positivity
      have hc : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount B n : ℝ) + C := by
        exact_mod_cast hcount n
      dsimp [a, b, e]
      rw [← add_div]
      calc
        (1 / 2 : ℝ) * ((GenLimit.PatientScope.prefixCount A n : ℝ) /
            GenLimit.PatientScope.prefixCount K n) =
            ((1 / 2 : ℝ) * GenLimit.PatientScope.prefixCount A n) /
              GenLimit.PatientScope.prefixCount K n := by ring
        _ ≤ (C + GenLimit.PatientScope.prefixCount B n) /
              GenLimit.PatientScope.prefixCount K n := by
          apply (div_le_div_iff₀ hkpos hkpos).2
          nlinarith [show (0 : ℝ) ≤ C by positivity]
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) * liminf a atTop ≤ liminf b atTop
  calc
    (1 / 2 : ℝ) * liminf a atTop ≤
        liminf (fun n => (1 / 2 : ℝ) * a n) atTop := by
      have hconst : liminf (fun _ : ℕ => (1 / 2 : ℝ)) atTop = 1 / 2 :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2))).liminf_eq
      calc
        (1 / 2 : ℝ) * liminf a atTop =
            liminf (fun _ : ℕ => (1 / 2 : ℝ)) atTop * liminf a atTop := by rw [hconst]
        _ ≤ liminf ((fun _ : ℕ => (1 / 2 : ℝ)) * a) atTop := by
          apply le_liminf_mul
          · exact Eventually.of_forall fun _ => by norm_num
          · exact isBoundedUnder_of_eventually_le
              (Eventually.of_forall fun _ => show (1 / 2 : ℝ) ≤ 1 by norm_num)
          · exact Eventually.of_forall ha0
          · exact (isBoundedUnder_of_eventually_le (Eventually.of_forall ha1)).isCobounded_flip
        _ = liminf (fun n => (1 / 2 : ℝ) * a n) atTop := by rfl
    _ ≤ liminf (fun n => e n + b n) atTop := by
      apply Filter.liminf_le_liminf
      · exact Eventually.of_forall hpoint
      · exact isBoundedUnder_of_eventually_ge
          (Eventually.of_forall fun n => mul_nonneg (by norm_num) (ha0 n))
      · exact (isBoundedUnder_of_eventually_le (a := (C : ℝ) + 1)
          (Eventually.of_forall fun n => by nlinarith [heC n, hb1 n])).isCobounded_flip
    _ ≤ limsup e atTop + liminf b atTop := by
      apply liminf_add_le
      · exact isBoundedUnder_of_eventually_ge (Eventually.of_forall he0)
      · exact isBoundedUnder_of_eventually_le (Eventually.of_forall heC)
      · exact isBoundedUnder_of_eventually_ge (Eventually.of_forall hb0)
      · exact (isBoundedUnder_of_eventually_le (Eventually.of_forall hb1)).isCobounded_flip
    _ = liminf b atTop := by rw [herr.limsup_eq]; simp
