import Stage3Model
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace X
abbrev Stream := Stage3Case024.Stream

def growingBase (input : Stream) (t : ℕ) : ℕ :=
  t + 1 + ∑ i : Fin (t + 1), input i

def squareOutput (input : Stream) (t : ℕ) : ℕ := (growingBase input t) ^ 2

def squareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ => (t + 1 + ∑ i, input i) ^ 2

example (input : Stream) : Stage3Case024.Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

lemma prefixSum_mono (input : Stream) {s t : ℕ} (hst : s < t) :
    (∑ i : Fin (s + 1), input i) ≤ ∑ i : Fin (t + 1), input i := by
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by omega)
  · intro i hi hnot
    omega

lemma input_le_prefixSum (input : Stream) (t : ℕ) (i : Fin (t + 1)) :
    input i ≤ ∑ j : Fin (t + 1), input j := by
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin (t + 1) => input j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

example (input : Stream) (t : ℕ) : squareOutput input t ∉ GenLimit.sample input (t+1) := by
  intro hmem
  unfold GenLimit.sample at hmem
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hmem
  have hterm := input_le_prefixSum input t ⟨s, Finset.mem_range.mp hs⟩
  have hbasepos : 1 ≤ growingBase input t := by
    unfold growingBase
    omega
  change input s ≤ ∑ j : Fin (t + 1), input j at hterm
  have hslt : input s < growingBase input t := by
    unfold growingBase
    omega
  have hbasele : growingBase input t ≤ squareOutput input t := by
    unfold squareOutput
    nlinarith
  have : input s < squareOutput input t := lt_of_lt_of_le hslt hbasele
  omega

example (input : Stream) {s t : ℕ} (hst : s < t) :
    squareOutput input s ≠ squareOutput input t := by
  have hsum := prefixSum_mono input hst
  have hbase : growingBase input s < growingBase input t := by
    unfold growingBase
    omega
  unfold squareOutput
  nlinarith [show 0 ≤ growingBase input s from Nat.zero_le _]

end X
