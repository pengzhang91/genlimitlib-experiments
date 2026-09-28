import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open Filter Set
open scoped Topology
#check Set.infinite_iff_tendsto_sum_indicator_atTop
#check tendsto_natCast_atTop_atTop
#check tendsto_inv_atTop_zero
#check Filter.Tendsto.inv₀
#check Filter.Tendsto.inv_tendsto_atTop
#check le_liminf_add
#check liminf_add_le
#check liminf_const_mul
#check liminf_mul_const
#check liminf_const
#check Filter.Tendsto.liminf_eq
#check Filter.Tendsto.limsup_eq
#check Filter.Tendsto.isBoundedUnder_le
#check Filter.Tendsto.isBoundedUnder_ge
#check isBoundedUnder_le_of_eventually_le
#check isBoundedUnder_ge_of_eventually_le
