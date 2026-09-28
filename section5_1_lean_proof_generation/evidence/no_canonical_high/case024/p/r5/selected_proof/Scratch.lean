import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter MeasureTheory
open scoped Topology

#check Nat.nth_mem_of_infinite
#check Nat.exists_nth_eq
#check Nat.nth_injective
#check Nat.count_nth_of_infinite
#check Nat.nth_count
#check Nat.count_succ_eq_succ_count
#check Nat.count_eq_card_filter_range
#check Nat.tendsto_cast_atTop_atTop
#check tendsto_natCast_atTop_atTop
#check tendsto_pow_div_pow_atTop_zero
#check tendsto_one_div_atTop_nhds_zero_nat
#check tendsto_const_nhds.div_atTop
#check Filter.Tendsto.limsup_eq
#check limsup_eq_of_tendsto
#check limsup_le
#check limsup_const
#check MeasureTheory.integral_mono_ae
#check MeasureTheory.integral_const
#check MeasureTheory.integral_zero
#check MeasureTheory.Integrable.integral_mono
#check MeasureTheory.Integrable.integral_mono_ae
#check Set.Finite.subset_bddAbove
#check Finset.card_le_card
#check Finset.card_filter_le
#check Finset.card_congr
#check Finset.card_image_lem

namespace Scratch

def squares : Set ℕ := {x | ∃ m, x = m^2}

lemma squares_infinite : squares.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  refine ⟨(a+1)^2, ?_, ⟨a+1, rfl⟩⟩
  nlinarith [Nat.le_mul_self (a+1)]

end Scratch
