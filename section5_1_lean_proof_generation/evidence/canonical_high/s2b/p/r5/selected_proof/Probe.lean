import Stage3Model
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set Filter

example : Tendsto (fun n : ℕ => (12 : ℝ) * n + 9) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h12 : Tendsto (fun n : ℕ => (12 : ℝ) * n) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  exact Filter.tendsto_atTop_add_const_right atTop (9 : ℝ) h12

example : Tendsto (fun n : ℕ => ((12 : ℝ) * n + 9) / (n : ℝ)) atTop (nhds 12) := by
  have h9 : Tendsto (fun n : ℕ => (9 : ℝ) * (1 / (n : ℝ))) atTop (nhds 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (9 : ℝ)) atTop (nhds 9)).mul
      tendsto_one_div_atTop_nhds_zero_nat using 1 <;> norm_num
  have h : Tendsto (fun n : ℕ => (12 : ℝ) + 9 * (1 / (n : ℝ))) atTop (nhds 12) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (nhds 12)).add h9 using 1 <;> norm_num
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp

example : Tendsto (fun n : ℕ =>
    (Real.logb 2 ((12 : ℝ) * n + 9) + 1) / (n : ℝ)) atTop (nhds 0) := by
  have hu : Tendsto (fun n : ℕ => (12 : ℝ) * n + 9) atTop atTop := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h12 : Tendsto (fun n : ℕ => (12 : ℝ) * n) atTop atTop :=
      hn.const_mul_atTop (by norm_num)
    exact Filter.tendsto_atTop_add_const_right atTop (9 : ℝ) h12
  have hlogdivu : Tendsto (fun n : ℕ =>
      Real.log ((12 : ℝ) * n + 9) / ((12 : ℝ) * n + 9)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hu
  have huratio : Tendsto (fun n : ℕ => ((12 : ℝ) * n + 9) / (n : ℝ))
      atTop (nhds 12) := by
    have h9 : Tendsto (fun n : ℕ => (9 : ℝ) * (1 / (n : ℝ))) atTop (nhds 0) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (9 : ℝ)) atTop (nhds 9)).mul
        tendsto_one_div_atTop_nhds_zero_nat using 1 <;> norm_num
    have h : Tendsto (fun n : ℕ => (12 : ℝ) + 9 * (1 / (n : ℝ))) atTop (nhds 12) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (12 : ℝ)) atTop (nhds 12)).add h9 using 1 <;> norm_num
    apply h.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  have hlogdivn : Tendsto (fun n : ℕ =>
      Real.log ((12 : ℝ) * n + 9) / (n : ℝ)) atTop (nhds 0) := by
    have h := hlogdivu.mul huratio
    norm_num at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hu0 : (12 : ℝ) * n + 9 ≠ 0 := by positivity
    field_simp
  have hlogb : Tendsto (fun n : ℕ =>
      Real.logb 2 ((12 : ℝ) * n + 9) / (n : ℝ)) atTop (nhds 0) := by
    have h := hlogdivn.div_const (Real.log 2)
    norm_num at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [Real.logb]
    field_simp
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h := hlogb.add hone
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  field_simp
