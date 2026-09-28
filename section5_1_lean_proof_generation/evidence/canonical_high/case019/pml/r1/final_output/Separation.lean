import Countable
import Helpers
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import Mathlib.Data.Countable.Defs

open Set Filter
open scoped Topology

namespace Stage3Case019

open GenLimit
open GenLimit.Generic
open GenLimit.InfiniteContamination
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

structure VirtualState where
  seen : Finset ℤ
  used : Finset ℕ
  values : List ℕ

noncomputable def freshNat (used : Finset ℕ) : ℕ :=
  if h : used.Nonempty then used.max' h + 1 else 0

lemma freshNat_not_mem (used : Finset ℕ) : freshNat used ∉ used := by
  classical
  unfold freshNat
  split <;> rename_i h
  · intro hmem
    have hle := Finset.le_max' used (used.max' h + 1) hmem
    omega
  · intro hmem
    exact h ⟨0, hmem⟩

def positiveIndex? (z : ℤ) : Option ℕ :=
  if 0 < z then some (z.toNat - 1) else none

def negativeIndex? : ℤ → Option ℕ
  | Int.negSucc n => some n
  | Int.ofNat _ => none

@[simp] lemma positiveIndex?_positiveCode (n : ℕ) :
    positiveIndex? (positiveCode n) = some n := by
  simp [positiveIndex?, positiveCode]

@[simp] lemma negativeIndex?_negativeCode (n : ℕ) :
    negativeIndex? (negativeCode n) = some n := by
  rfl

noncomputable def chooseVirtual (used : Finset ℕ) (candidate : Option ℕ) : ℕ :=
  match candidate with
  | some n => if n ∈ used then freshNat used else n
  | none => freshNat used

lemma chooseVirtual_not_mem (used : Finset ℕ) (candidate : Option ℕ) :
    chooseVirtual used candidate ∉ used := by
  classical
  cases candidate with
  | none => exact freshNat_not_mem used
  | some n =>
      simp only [chooseVirtual]
      split <;> rename_i h
      · exact freshNat_not_mem used
      · exact h

noncomputable def virtualStep (q : ℕ) (state : VirtualState) (z : ℤ) : VirtualState := by
  classical
  let seen' := insert z state.seen
  let candidate :=
    if omissionMarkerFinset q ⊆ seen' then positiveIndex? z else negativeIndex? z
  let value := chooseVirtual state.used candidate
  exact ⟨seen', insert value state.used, state.values ++ [value]⟩

noncomputable def virtualState (q : ℕ) (xs : List ℤ) : VirtualState :=
  xs.foldl (virtualStep q) ⟨∅, ∅, []⟩

noncomputable def virtualValues (q : ℕ) (xs : List ℤ) : List ℕ :=
  (virtualState q xs).values

lemma virtualStep_values (q : ℕ) (state : VirtualState) (z : ℤ) :
    (virtualStep q state z).values =
      state.values ++ [chooseVirtual state.used
        (if omissionMarkerFinset q ⊆ insert z state.seen then
          positiveIndex? z else negativeIndex? z)] := by
  classical
  rfl

lemma virtualState_append (q : ℕ) (xs ys : List ℤ) :
    virtualState q (xs ++ ys) = ys.foldl (virtualStep q) (virtualState q xs) := by
  simp [virtualState, List.foldl_append]

lemma virtualValues_length (q : ℕ) (xs : List ℤ) :
    (virtualValues q xs).length = xs.length := by
  induction xs using List.reverseRecOn with
  | nil => simp [virtualValues, virtualState]
  | append_singleton xs z ih =>
      rw [virtualValues, virtualState_append]
      have hlen : (virtualState q xs).values.length = xs.length := by
        simpa [virtualValues] using ih
      simp only [List.foldl_cons, List.foldl_nil, virtualStep_values,
        List.length_append, List.length_singleton, hlen]

end Stage3Case019

namespace Stage3Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

noncomputable def historyWeight {n : ℕ} (xs : Fin n → ℤ) : ℕ :=
  ∑ i : Fin n, (xs i).natAbs

noncomputable def strictHalfGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    let index := n + historyWeight xs
    if omissionMarkerFinset q ⊆ sequenceSample xs then
      positiveCode index
    else
      negativeCode index

lemma historyWeight_prefix (input : Stream ℤ) (n : ℕ) :
    historyWeight (fun i : Fin n => input i) =
      ∑ k ∈ Finset.range n, (input k).natAbs := by
  classical
  unfold historyWeight
  simpa using (Fin.sum_univ_eq_sum_range (fun k : ℕ => (input k).natAbs) n)

lemma runIndex_strict (input : Stream ℤ) {s t : ℕ} (hst : s < t) :
    s + 1 + historyWeight (fun i : Fin (s + 1) => input i) <
      t + 1 + historyWeight (fun i : Fin (t + 1) => input i) := by
  rw [historyWeight_prefix, historyWeight_prefix]
  have hsum :
      (∑ k ∈ Finset.range (s + 1), (input k).natAbs) ≤
        ∑ k ∈ Finset.range (t + 1), (input k).natAbs := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro i _ _
      omega
  omega

lemma sample_natAbs_le_historyWeight
    {n : ℕ} (xs : Fin n → ℤ) (i : Fin n) :
    (xs i).natAbs ≤ historyWeight xs := by
  classical
  unfold historyWeight
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun j : Fin n => (xs j).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  simpa using h

lemma strictHalfGenerator_sample_fresh
    (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    outputAfterInput (strictHalfGenerator q) input t ∉
      sample input (t + 1) := by
  classical
  intro hmem
  obtain ⟨i, hi, heq⟩ := mem_sample_iff.mp hmem
  let xs : Fin (t + 1) → ℤ := fun k => input k
  have habs := sample_natAbs_le_historyWeight xs ⟨i, hi⟩
  change (input i).natAbs ≤ historyWeight xs at habs
  change input i = strictHalfGenerator q (t + 1) xs at heq
  unfold strictHalfGenerator at heq
  dsimp only at heq
  split at heq
  · have habsEq : (input i).natAbs = t + 1 + historyWeight xs + 1 := by
      rw [heq, positiveCode]
      rfl
    omega
  · have habsEq : (input i).natAbs = t + 1 + historyWeight xs + 1 := by
      rw [heq, negativeCode, Int.natAbs_negSucc]
    omega

lemma strictHalfGenerator_output_ne_of_lt
    (q : ℕ) (input : Stream ℤ) {s t : ℕ} (hst : s < t) :
    outputAfterInput (strictHalfGenerator q) input s ≠
      outputAfterInput (strictHalfGenerator q) input t := by
  classical
  let si := s + 1 + historyWeight (fun i : Fin (s + 1) => input i)
  let ti := t + 1 + historyWeight (fun i : Fin (t + 1) => input i)
  have hindex : si < ti := runIndex_strict input hst
  simp only [outputAfterInput, output, strictHalfGenerator]
  rw [sequenceSample_prefix input (s + 1), sequenceSample_prefix input (t + 1)]
  change (if omissionMarkerFinset q ⊆ sample input (s + 1) then
      positiveCode si else negativeCode si) ≠
    (if omissionMarkerFinset q ⊆ sample input (t + 1) then
      positiveCode ti else negativeCode ti)
  split <;> split
  · exact fun h => Nat.ne_of_lt hindex (positiveCode_injective h)
  · intro h
    have hp := positiveCode_mem si
    have hn := negativeCode_mem ti
    rw [h] at hp
    exact (Int.not_lt_of_ge (Int.le_of_lt hp)) hn
  · intro h
    have hn := negativeCode_mem si
    have hp := positiveCode_mem ti
    rw [h] at hn
    exact (Int.not_lt_of_ge (Int.le_of_lt hp)) hn
  · exact fun h => Nat.ne_of_lt hindex (negativeCode_injective h)

lemma strictHalfGenerator_first_novel
    {q : ℕ} {K : Language ℤ}
    (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input
      (outputAfterInput (strictHalfGenerator q) input) K := by
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Td, hTd⟩ := allMarkers_eventually_observed hinput hmarkers
  refine ⟨max Td j, ?_⟩
  intro t ht
  have hdetect : omissionMarkerFinset q ⊆ sample input (t + 1) :=
    hTd t ((Nat.le_max_left _ _).trans ht)
  have hout : outputAfterInput (strictHalfGenerator q) input t =
      positiveCode (t + 1 + historyWeight (fun i : Fin (t + 1) => input i)) := by
    simp only [outputAfterInput, output, strictHalfGenerator]
    rw [if_pos]
    simpa only [sequenceSample_prefix] using hdetect
  refine ⟨?_, strictHalfGenerator_sample_fresh q input t, ?_⟩
  · rw [hout]
    apply htail
    refine ⟨(t + 1 + historyWeight (fun i : Fin (t + 1) => input i)) - j, ?_⟩
    change positiveCode (j + ((t + 1 + historyWeight (fun i : Fin (t + 1) => input i)) - j)) =
      positiveCode (t + 1 + historyWeight (fun i : Fin (t + 1) => input i))
    exact congrArg positiveCode (by omega)
  · intro s hs
    exact strictHalfGenerator_output_ne_of_lt q input hs

lemma strictHalfGenerator_second_novel
    {q : ℕ} {K : Language ℤ}
    (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input
      (outputAfterInput (strictHalfGenerator q) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  have hnoDetect : ¬omissionMarkerFinset q ⊆ sample input (t + 1) :=
    not_allMarkers_observed_second hK hinput t
  have hout : outputAfterInput (strictHalfGenerator q) input t =
      negativeCode (t + 1 + historyWeight (fun i : Fin (t + 1) => input i)) := by
    simp only [outputAfterInput, output, strictHalfGenerator]
    rw [if_neg]
    simpa only [sequenceSample_prefix] using hnoDetect
  refine ⟨?_, strictHalfGenerator_sample_fresh q input t, ?_⟩
  · rw [hout]
    exact hK.1 (negativeCode_mem _)
  · intro s hs
    exact strictHalfGenerator_output_ne_of_lt q input hs

lemma strictHalfGenerator_novel
    (q : ℕ) {K : Language ℤ} (hK : K ∈ finiteOmissionClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input
      (outputAfterInput (strictHalfGenerator q) input) K := by
  rcases hK with hfirst | hsecond
  · exact strictHalfGenerator_first_novel hfirst hinput
  · exact strictHalfGenerator_second_novel hsecond hinput

end Stage3Case019
