import Case017Helpers
open Set Filter
open GenLimit
open Stage3Case017Proof
#check Nat.find_spec
#check dif_pos
#check Set.mem_range
#check isCoboundedUnder_ge_of_le
example {input : Stage3Case017.Stream} {z : ℕ} (h : ∃ t, input t = z) :
    input (if h' : ∃ t, input t = z then Nat.find h' else 0) = z := by
  rw [dif_pos h]
  exact Nat.find_spec h
