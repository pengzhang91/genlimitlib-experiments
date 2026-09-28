import Countable
import Helpers
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import Mathlib.Data.Countable.Defs

open Set Filter
open scoped Topology

#check exists_surjective_nat
#check List.ofFn
#check List.get
#check List.get?_eq_getElem?
#check Finset.max'
#check Finset.max'_mem
#check Finset.lt_max'
#check List.nodup_iff_injective_get
#check List.toFinset_card_of_nodup
#check GenLimit.Generic.sequenceSample
#check GenLimit.Generic.mem_sequenceSample_iff
#check Finset.coe_image
#check Set.preimage_image_eq
#check Function.Injective.injOn
#check Filter.Tendsto.liminf_eq
#check List.ofFn_succ
#check List.ofFn_succ_last
#check List.get_append_left
#check List.get_append_right
#check List.get_append
#check List.get_eq_getElem
#check List.toFinset_cons
#check List.nodup_cons
#check List.nodup_append
#check List.get_ofFn
