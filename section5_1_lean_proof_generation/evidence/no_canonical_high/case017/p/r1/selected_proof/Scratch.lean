import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Scratch

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) : Stage3Case017.Stream :=
  Nat.lt_wfRel.wf.fix (fun t rec =>
    gen t (fun i => input i) (fun i => rec i.1 i.2))

 theorem trajectory_eq (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory, WellFounded.fix_eq]

#check Filter.eventually_all
#check Filter.Eventually.exists_forall_of_atTop
#check Set.Infinite.exists_notMem_finset
#check Nat.sInf_mem
#check Nat.sInf_le
#check Finset.card_le_card
#check Filter.liminf_le_liminf
#check Filter.liminf_congr
#check Filter.Tendsto.liminf_eq
#check tendsto_const_nhds
#check tendsto_natCast_atTop_atTop
#check tendsto_const_nhds.div_atTop
#check tendsto_const_nhds.div
#check tendsto_natCast_atTop_iff

end Scratch
