import Case017Helpers
import Mathlib
open Set Filter
open scoped Topology
namespace Stage3Case017
lemma test_prefix_tendsto {K : Set ℕ} (hK : K.Infinite) :
    Filter.Tendsto (fun n => GenLimit.PatientScope.prefixCount K n) Filter.atTop Filter.atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) (r := 1) Nat.zero_lt_one] at hK
  simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Set.indicator, Finset.sum_filter] using hK
end Stage3Case017
