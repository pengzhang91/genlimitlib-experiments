import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Analysis.SpecificLimits.Basic

open Filter MeasureTheory
open scoped Topology BigOperators

#check Filter.Tendsto.limsup_eq
#check Filter.limsup_le
#check limsup_le_iff
#check le_limsup_iff
#check tendsto_const_nhds
#check tendsto_const_div_atTop_nhds_zero_nat
#check Finset.card_filter_le
#check Finset.card_le_card
#check MeasureTheory.Integrable.mono'
#check MeasureTheory.integral_congr_ae
#check MeasureTheory.integral_zero
#check MeasureTheory.integral_nonneg
#check MeasureTheory.integral_mono_ae
#check MeasureTheory.integral_const
#check Set.Finite.subset
#check Set.Finite.image
#check Set.Finite.union
#check Set.finite_range
#check Set.finite_Iio
#check Finset.sum_le_sum
#check Finset.single_le_sum
#check Finset.sum_range_succ
#check Finset.sum_fin_eq_sum_range
#check Fin.sum_univ_succ
#check Finset.sum_const_zero
#check Finset.sum_add_distrib
#check Nat.pow_two
#check pow_le_pow_left₀
#check sq_le_sq₀
#check GenLimit.InfiniteContamination.sparseMergePresentation_injective
#check GenLimit.InfiniteContamination.range_sparseMergePresentation
#check GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
