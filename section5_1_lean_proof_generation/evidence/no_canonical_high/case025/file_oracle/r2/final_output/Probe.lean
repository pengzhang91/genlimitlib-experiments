import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Logic.Equiv.Finset
open Filter Topology
#synth Encodable (Finset ℕ)
#check GenLimit.sample
#check GenLimit.Generic.sample
#check Set.Finite.coe_toFinset
#check tendsto_natCast_atTop_atTop
#check Filter.Tendsto.natCast_atTop
