import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib

open Filter
open scoped Topology
open Stage3Case019

namespace Case019

open GenLimit.Generic

noncomputable def negativeCandidates {n : ℕ} (xs : Fin n → ℤ) : Finset ℕ :=
  (Finset.range (2 * n)).filter fun k =>
    GenLimit.UnionClosedness.negativeCode k ∉ sequenceSample xs

lemma negativeCandidates_nonempty {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    (negativeCandidates xs).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hsub :
      (Finset.range (2 * n)).image GenLimit.UnionClosedness.negativeCode ⊆
        sequenceSample xs := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    have hknot : k ∉ negativeCandidates xs := by simp [hempty]
    simp only [negativeCandidates, Finset.mem_filter, hk, true_and, not_not] at hknot
    exact hknot
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _
    GenLimit.UnionClosedness.negativeCode_injective, Finset.card_range] at hcard
  have hsample : (sequenceSample xs).card ≤ n := by
    unfold sequenceSample
    simpa using Finset.card_image_le
  omega

noncomputable def freshNegativeIndex {n : ℕ} (xs : Fin n → ℤ) : ℕ :=
  if hn : 0 < n then (negativeCandidates xs).max' (negativeCandidates_nonempty hn xs) else 0

lemma freshNegativeIndex_mem {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    freshNegativeIndex xs ∈ negativeCandidates xs := by
  classical
  simp only [freshNegativeIndex, dif_pos hn]
  exact Finset.max'_mem _ _

lemma freshNegativeIndex_lt {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    freshNegativeIndex xs < 2 * n := by
  have h := freshNegativeIndex_mem hn xs
  exact (Finset.mem_filter.mp h).1 |> Finset.mem_range.mp

lemma freshNegativeIndex_fresh {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    GenLimit.UnionClosedness.negativeCode (freshNegativeIndex xs) ∉ sequenceSample xs := by
  have h := freshNegativeIndex_mem hn xs
  exact (Finset.mem_filter.mp h).2

lemma freshNegativeIndex_strict
    {n : ℕ} (hn : 0 < n) (xs : Fin (n + 1) → ℤ) :
    freshNegativeIndex (fun i : Fin n => xs i.castSucc) < freshNegativeIndex xs := by
  classical
  let oldxs : Fin n → ℤ := fun i => xs i.castSucc
  let a := freshNegativeIndex oldxs
  have ha_lt : a < 2 * n := freshNegativeIndex_lt hn oldxs
  by_cases hnew : xs ⟨n, Nat.lt_succ_self n⟩ =
      GenLimit.UnionClosedness.negativeCode (2 * n)
  · let k := 2 * n + 1
    have hk_lt : k < 2 * (n + 1) := by dsimp [k]; omega
    have hkfresh : GenLimit.UnionClosedness.negativeCode k ∉ sequenceSample xs := by
      intro hmem
      rw [mem_sequenceSample_iff] at hmem
      obtain ⟨i, hi⟩ := hmem
      by_cases hin : i.val < n
      · have hold : GenLimit.UnionClosedness.negativeCode k ∈ sequenceSample oldxs := by
          rw [mem_sequenceSample_iff]
          exact ⟨⟨i, hin⟩, hi⟩
        have holdfresh := freshNegativeIndex_fresh hn oldxs
        have hindex : a < k := by dsimp [a, k]; omega
        have hkmem : k ∈ negativeCandidates oldxs := by
          simp [negativeCandidates, hindex.trans ha_lt, hold]
        have hkle : k ≤ a := by
          dsimp [a]
          rw [freshNegativeIndex, dif_pos hn]
          exact Finset.le_max' _ _ hkmem
        omega
      · have hieq : i.val = n := by omega
        have hix : xs i = xs ⟨n, Nat.lt_succ_self n⟩ := by congr
        have hc := GenLimit.UnionClosedness.negativeCode_injective
          (hi.symm.trans (hix.trans hnew))
        dsimp [k] at hc
        omega
    have hkmem : k ∈ negativeCandidates xs := by
      simp [negativeCandidates, hk_lt, hkfresh]
    have hkle : k ≤ freshNegativeIndex xs := by
      rw [freshNegativeIndex, dif_pos (Nat.succ_pos n)]
      exact Finset.le_max' _ _ hkmem
    dsimp [a, k] at ha_lt ⊢
    omega
  · let k := 2 * n
    have hk_lt : k < 2 * (n + 1) := by dsimp [k]; omega
    have hkfresh : GenLimit.UnionClosedness.negativeCode k ∉ sequenceSample xs := by
      intro hmem
      rw [mem_sequenceSample_iff] at hmem
      obtain ⟨i, hi⟩ := hmem
      by_cases hin : i.val < n
      · have hold : GenLimit.UnionClosedness.negativeCode k ∈ sequenceSample oldxs := by
          rw [mem_sequenceSample_iff]
          exact ⟨⟨i, hin⟩, hi⟩
        have hkmem : k ∈ negativeCandidates oldxs := by
          simp [negativeCandidates, k, hold]
        have hkle : k ≤ a := by
          dsimp [a]
          rw [freshNegativeIndex, dif_pos hn]
          exact Finset.le_max' _ _ hkmem
        dsimp [k] at hkle
        omega
      · have hieq : i.val = n := by omega
        have hix : xs i = xs ⟨n, Nat.lt_succ_self n⟩ := by congr
        exact hnew (hix.symm.trans hi)
    have hkmem : k ∈ negativeCandidates xs := by
      simp [negativeCandidates, hk_lt, hkfresh]
    have hkle : k ≤ freshNegativeIndex xs := by
      rw [freshNegativeIndex, dif_pos (Nat.succ_pos n)]
      exact Finset.le_max' _ _ hkmem
    dsimp [a, k] at ha_lt ⊢
    omega

noncomputable def positiveCandidates {n : ℕ} (xs : Fin n → ℤ) : Finset ℕ :=
  (Finset.range (2 * n)).filter fun k =>
    GenLimit.UnionClosedness.positiveCode k ∉ sequenceSample xs

lemma positiveCandidates_nonempty {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    (positiveCandidates xs).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hsub :
      (Finset.range (2 * n)).image GenLimit.UnionClosedness.positiveCode ⊆
        sequenceSample xs := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    have hknot : k ∉ positiveCandidates xs := by simp [hempty]
    simp only [positiveCandidates, Finset.mem_filter, hk, true_and, not_not] at hknot
    exact hknot
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _
    GenLimit.UnionClosedness.positiveCode_injective, Finset.card_range] at hcard
  have hsample : (sequenceSample xs).card ≤ n := by
    unfold sequenceSample
    simpa using Finset.card_image_le
  omega

noncomputable def freshPositiveIndex {n : ℕ} (xs : Fin n → ℤ) : ℕ :=
  if hn : 0 < n then (positiveCandidates xs).max' (positiveCandidates_nonempty hn xs) else 0

lemma freshPositiveIndex_mem {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    freshPositiveIndex xs ∈ positiveCandidates xs := by
  classical
  simp only [freshPositiveIndex, dif_pos hn]
  exact Finset.max'_mem _ _

lemma freshPositiveIndex_lt {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    freshPositiveIndex xs < 2 * n := by
  have h := freshPositiveIndex_mem hn xs
  exact (Finset.mem_filter.mp h).1 |> Finset.mem_range.mp

lemma freshPositiveIndex_fresh {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    GenLimit.UnionClosedness.positiveCode (freshPositiveIndex xs) ∉ sequenceSample xs := by
  have h := freshPositiveIndex_mem hn xs
  exact (Finset.mem_filter.mp h).2

-- The positive proof is the negative proof transported through negation.
lemma freshPositiveIndex_strict
    {n : ℕ} (hn : 0 < n) (xs : Fin (n + 1) → ℤ) :
    freshPositiveIndex (fun i : Fin n => xs i.castSucc) < freshPositiveIndex xs := by
  classical
  let negxs : Fin (n + 1) → ℤ := fun i => -xs i
  have hcand (m : ℕ) (ys : Fin m → ℤ) :
      positiveCandidates ys = negativeCandidates (fun i => -ys i) := by
    ext k
    simp only [positiveCandidates, negativeCandidates, Finset.mem_filter,
      Finset.mem_range, and_congr_right_iff]
    intro hk
    rw [mem_sequenceSample_iff, mem_sequenceSample_iff]
    constructor <;> intro h
    · obtain ⟨i, hi⟩ := h
      refine ⟨i, ?_⟩
      have : -GenLimit.UnionClosedness.positiveCode k =
          GenLimit.UnionClosedness.negativeCode k := by
        simp [GenLimit.UnionClosedness.positiveCode,
          GenLimit.UnionClosedness.negativeCode]
      simpa [this] using congrArg Neg.neg hi
    · obtain ⟨i, hi⟩ := h
      refine ⟨i, ?_⟩
      have : -GenLimit.UnionClosedness.negativeCode k =
          GenLimit.UnionClosedness.positiveCode k := by
        simp [GenLimit.UnionClosedness.positiveCode,
          GenLimit.UnionClosedness.negativeCode]
      simpa [this] using congrArg Neg.neg hi
  have hidx (m : ℕ) (ys : Fin m → ℤ) :
      freshPositiveIndex ys = freshNegativeIndex (fun i => -ys i) := by
    by_cases hm : 0 < m
    · rw [freshPositiveIndex, freshNegativeIndex, dif_pos hm, dif_pos hm]
      apply Finset.max'_eq_max'
      exact hcand m ys
    · simp [freshPositiveIndex, freshNegativeIndex, hm]
  rw [hidx n, hidx (n + 1)]
  exact freshNegativeIndex_strict hn negxs

noncomputable def denseSweepGenerator (q : ℕ) : GenLimit.Generic.Generator ℤ :=
  fun n xs =>
    if GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆ sequenceSample xs then
      GenLimit.UnionClosedness.positiveCode (freshPositiveIndex xs)
    else GenLimit.UnionClosedness.negativeCode (freshNegativeIndex xs)

end Case019
