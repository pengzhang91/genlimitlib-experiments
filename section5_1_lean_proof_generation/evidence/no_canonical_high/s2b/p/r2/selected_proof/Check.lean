import Stage3Model
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Set Function Filter

example : Tendsto (fun n : ℕ =>
    ((Nat.log2 (12 * n + 9) + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => 12 * (n : ℝ) + 9) atTop atTop := by
    apply tendsto_atTop_add_const_right atTop 9
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
  have hlog : Tendsto (fun n : ℕ =>
      Real.logb 2 (12 * (n : ℝ) + 9) / (n : ℝ)) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b := (2 : ℝ))
      (1 / 12) (-3 / 4) 1 (by norm_num : (1 / 12 : ℝ) ≠ 0)).comp hx
    convert h using 1
    funext n
    simp only [pow_one]
    congr 1
    ring
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hupper : Tendsto (fun n : ℕ =>
      (Real.logb 2 (12 * (n : ℝ) + 9) + 1) / (n : ℝ)) atTop (nhds 0) := by
    have hadd := hlog.add hone
    rw [zero_add] at hadd
    convert hadd using 1
    funext n
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      convert add_le_add_right (Real.log2_le_logb (12 * n + 9)) 1 using 1 <;> norm_num
