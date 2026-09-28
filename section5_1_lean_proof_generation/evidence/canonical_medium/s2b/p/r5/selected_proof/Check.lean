import Mathlib.Analysis.SpecialFunctions.Log.Base
open Filter
example : Tendsto (fun n : ℕ => (Real.logb 2 (12*n+9) + 1) / (n:ℝ)) atTop (nhds 0) := by
  have hmul : Tendsto (fun n : ℕ => (12 : ℝ) * n) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun n : ℕ => (12 : ℝ) * n + 9) atTop atTop :=
    tendsto_atTop_add_const_right atTop 9 hmul
  have hlog := (Real.tendsto_pow_logb_div_mul_add_atTop (b := (2:ℝ)) (1/12) (-3/4) 1 (by norm_num)).comp harg
  have hlog' : Tendsto (fun n : ℕ => Real.logb 2 (12*n+9) / (n:ℝ)) atTop (nhds 0) := by
    convert hlog using 1
    funext n
    simp only [pow_one]
    congr 2 <;> norm_num <;> ring
  have hadd := hlog'.add (tendsto_const_div_atTop_nhds_zero_nat 1)
  rw [zero_add] at hadd
  convert hadd using 1
  funext n
  rw [add_div]
