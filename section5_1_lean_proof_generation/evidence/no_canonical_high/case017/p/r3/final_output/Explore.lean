import Stage3Model

open Set Filter
open scoped Topology

#check Set.Infinite.exists_notMem_finset
#check Filter.Eventually.forall_finset
#check eventually_all_finset
#check Filter.liminf_le_liminf
#check Filter.Tendsto.liminf_eq
#check tendsto_const_nhds
#check tendsto_inv_atTop_zero
#check Set.infinite_iff_tendsto_sum_indicator_atTop
#check Finset.card_image_iff
#check Finset.card_image_of_injective
#check Finset.card_le_card
#check Finset.card_sdiff_add_card_inter
#check Finset.card_sdiff
#check Nat.card_range
#check Set.ncard_le_ncard
#check Finset.range_add_one
#check Nat.Icc
#check Finset.Icc
#check Finset.card_Icc
#check Nat.sub_add_cancel

namespace Test

noncomputable def run (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t

theorem run_follows (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) :
    Stage3Case017.Follows gen input (run gen input) := by
  intro t
  rw [run]

end Test
