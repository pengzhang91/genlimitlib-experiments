import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic
open Set Filter
open scoped Topology
#check Filter.Tendsto.isBoundedUnder_le
#check Filter.Tendsto.isBoundedUnder_ge
#check Filter.Tendsto.isCoboundedUnder_le
#check Filter.Tendsto.isCoboundedUnder_ge
#check Filter.IsBoundedUnder.isCoboundedUnder_ge
#check Filter.IsBoundedUnder.isCoboundedUnder_le
#check Filter.isBoundedUnder_of_eventually_ge
#check Filter.isBoundedUnder_of_eventually_le
#check Filter.isCoboundedUnder_ge_of_le
#check Filter.isCoboundedUnder_le_of_ge
