import Stage3Model
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Set Filter

example : Tendsto (fun n : ℕ =>
    (Real.logb 2 (3 * n) + 1) / (n : ℝ)) atTop (nhds 0) := by
  have hk : Tendsto (fun n : ℕ => (3 : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hbase := Real.tendsto_pow_logb_div_mul_add_atTop (b := (2 : ℝ)) 1 0 1 one_ne_zero
  have hcomp := hbase.comp hk
  have hlog : Tendsto (fun n : ℕ =>
      Real.logb 2 ((3 : ℝ) * n) / ((3 : ℝ) * n)) atTop (nhds 0) := by
    simpa using hcomp
  have hlog' := hlog.const_mul (3 : ℝ)
  have hone := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hadd := hlog'.add hone
  have hadd0 : Tendsto (fun n : ℕ =>
      3 * (Real.logb 2 ((3 : ℝ) * n) / ((3 : ℝ) * n)) + 1 / (n : ℝ))
      atTop (nhds 0) := by simpa using hadd
  apply hadd0.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, hn0]
  field_simp
