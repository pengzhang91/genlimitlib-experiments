import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
open Filter
open scoped Topology
example : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  simpa [Function.comp_def, id] using
    Real.isLittleO_log_id_atTop.natCast_atTop.tendsto_div_nhds_zero

example (c : ℝ) : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

example (c : ℝ) : Tendsto (fun n : ℕ => c * (Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, id] using
      Real.isLittleO_log_id_atTop.natCast_atTop.tendsto_div_nhds_zero
  simpa using h.const_mul c

example : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
example (n:ℕ) (hn:1≤n) : Real.log ((6*n+4:ℕ):ℝ) ≤ Real.log 10 + Real.log (n:ℝ) := by
  rw [← Real.log_mul (by norm_num : (10:ℝ) ≠ 0) (by exact_mod_cast (Nat.ne_of_gt hn))]
  apply Real.log_le_log
  · positivity
  · norm_num at *
    exact_mod_cast (show 6*n+4 ≤ 10*n by omega)
