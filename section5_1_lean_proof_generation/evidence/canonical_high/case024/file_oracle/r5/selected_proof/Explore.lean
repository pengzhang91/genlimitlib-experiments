import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib

open Filter MeasureTheory
open scoped Topology BigOperators

#check Filter.Tendsto.limsup_eq
#check Filter.limsup_le_of_le
#check Filter.limsup_le_limsup
#check MeasureTheory.integral_congr_ae
#check MeasureTheory.integral_mono_ae
#check MeasureTheory.integral_const
#check MeasureTheory.Integrable.integral_mono
#check Set.Finite.subset
#check Set.finite_range_iff
#check Finset.card_le_card
#check GenLimit.PatientScope.mem_prefixFinset
#check Nat.count_eq_card_filter_range
#check Finset.sum_le_sum_of_subset_of_nonneg
#check Finset.single_le_sum
#check Set.infinite_range_of_injective
#check Nat.mul_self_injective
#check Nat.strictMono_mul_self
#check Set.Finite.image
#check Set.finite_range
#check Set.range_comp
