import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Archimedean.IndicatorCard

open Filter
open scoped Topology
#check div_le_div_of_nonneg_left
#check div_le_div₀
#check div_le_div_of_nonneg_right
#check Set.Infinite.exists_not_mem_finset
#check Filter.Eventually.exists
#check tendsto_natCast_atTop_atTop
#check Filter.Tendsto.comp
#check isBoundedUnder_of_eventually_le
#check isBoundedUnder_of_eventually_ge
#check isCoboundedUnder_le
#check isCoboundedUnder_ge
#check Filter.isCoboundedUnder_le_of_le
#check Filter.isCoboundedUnder_ge_of_ge
#check Filter.isCoboundedUnder_le
#check Filter.isCoboundedUnder_ge

example (a b c d q : ℕ) (ha : a ≤ c + q) (hd : d ≤ b) (hpos : 0 < d) :
    (a : ℝ) / b - (q : ℝ) / d ≤ (c : ℝ) / d := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast lt_of_lt_of_le hpos hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hpos
  have hden : (d : ℝ) ≤ b := by exact_mod_cast hd
  have hfirst : (a : ℝ) / b ≤ (a : ℝ) / d := by
    exact div_le_div_of_nonneg_left (by positivity) hdpos hden
  have hnum : (a : ℝ) ≤ (c : ℝ) + q := by exact_mod_cast ha
  have hsecond : (a : ℝ) / d ≤ ((c : ℝ) + q) / d :=
    (div_le_div_iff_of_pos_right hdpos).2 hnum
  calc
    (a : ℝ) / b - (q : ℝ) / d ≤ ((c : ℝ) + q) / d - (q : ℝ) / d := sub_le_sub_right (hfirst.trans hsecond) _
    _ = (c : ℝ) / d := by ring
