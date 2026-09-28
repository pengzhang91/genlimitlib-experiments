import Helpers
open scoped BigOperators

noncomputable def fg : Stage3Case024.OnlineGenerator := fun t inp out =>
  2 ^ (1 + (∑ i, inp i) + ∑ i, out i)

noncomputable def rr (g : Stage3Case024.OnlineGenerator) (inp : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => Nat.strongRec (motive := fun _ => ℕ)
    (fun t ih => g t (fun i => inp i) (fun i => ih i.1 i.2)) t

lemma rr_eq (g : Stage3Case024.OnlineGenerator) (inp : Stage3Case024.Stream) (t : ℕ) :
    rr g inp t = g t (fun i => inp i) (fun i => rr g inp i) := by
  rw [rr]
  rw [Nat.strongRec_eq]
  rfl

#check Finset.single_le_sum
#check Finset.sum_le_sum_of_subset_of_nonneg
#check Finset.le_sum_of_subadditive_on_pred
#check Finset.sum_le_sum
