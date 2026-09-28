import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Scratch
open GenLimit GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

private theorem exists_index_not_mem (code : ℕ → ℤ) (hinj : Function.Injective code)
    (F : Finset ℤ) : ∃ k, code k ∉ F := by
  by_contra h
  push_neg at h
  have hrange : Set.range code ⊆ (F : Set ℤ) := by
    rintro z ⟨k, rfl⟩
    exact h k
  exact (Set.infinite_range_of_injective hinj) (F.finite_toSet.subset hrange)

noncomputable def leastFresh (code : ℕ → ℤ) (hinj : Function.Injective code)
    (F : Finset ℤ) : ℕ := Nat.find (exists_index_not_mem code hinj F)

lemma leastFresh_not_mem (code : ℕ → ℤ) (hinj : Function.Injective code)
    (F : Finset ℤ) : code (leastFresh code hinj F) ∉ F :=
  Nat.find_spec (exists_index_not_mem code hinj F)

lemma leastFresh_le_card (code : ℕ → ℤ) (hinj : Function.Injective code)
    (F : Finset ℤ) : leastFresh code hinj F ≤ F.card := by
  by_contra h
  have hlt : F.card < leastFresh code hinj F := Nat.lt_of_not_ge h
  have hall : ∀ k < F.card + 1, code k ∈ F := by
    intro k hk
    by_contra hkF
    exact (Nat.find_min (exists_index_not_mem code hinj F)
      (lt_of_le_of_lt (Nat.le_of_lt_succ hk) hlt)) hkF
  let emb : Fin (F.card + 1) ↪ F :=
    ⟨fun k => ⟨code k, hall k k.isLt⟩, fun a b hab => Fin.ext (hinj (congrArg Subtype.val hab))⟩
  have hc := Fintype.card_le_of_embedding emb
  simp at hc

def restrictAt {n : ℕ} (xs : Fin n → ℤ) (k : {x // x ∈ Finset.range n}) : Fin k.1 → ℤ :=
  fun j => xs ⟨j, lt_trans j.isLt (Finset.mem_range.mp k.2)⟩

noncomputable def denseSweepGenerator (q : ℕ) : GenLimit.Generic.Generator ℤ :=
  fun n xs =>
      let used : Finset ℤ := (Finset.range n).attach.image fun k : {x // x ∈ Finset.range n} =>
        denseSweepGenerator q k.1 (restrictAt xs k)
      let forbidden := GenLimit.Generic.sequenceSample xs ∪ used
      if omissionMarkerFinset q ⊆ GenLimit.Generic.sequenceSample xs then
        positiveCode (leastFresh positiveCode positiveCode_injective forbidden)
      else
        negativeCode (leastFresh negativeCode negativeCode_injective forbidden)
termination_by n xs => n
decreasing_by
  exact Finset.mem_range.mp k.2

lemma denseSweepGenerator_spec (q n : ℕ) (xs : Fin n → ℤ) :
    denseSweepGenerator q n xs ∉ GenLimit.Generic.sequenceSample xs ∧
      (∀ m (hm : m < n), denseSweepGenerator q n xs ≠
        denseSweepGenerator q m (fun j : Fin m => xs ⟨j, by omega⟩)) ∧
      ∃ k ≤ 2 * n,
        denseSweepGenerator q n xs =
          if omissionMarkerFinset q ⊆ GenLimit.Generic.sequenceSample xs then
            positiveCode k else negativeCode k := by
  rw [denseSweepGenerator.eq_1]
  let used : Finset ℤ := (Finset.range n).attach.image fun k : {x // x ∈ Finset.range n} =>
    denseSweepGenerator q k.1 (restrictAt xs k)
  generalize hforbidden : GenLimit.Generic.sequenceSample xs ∪ used = forbidden
  have hsampleCard : (GenLimit.Generic.sequenceSample xs).card ≤ n := by
    letI : DecidableEq ℤ := Classical.decEq ℤ
    unfold GenLimit.Generic.sequenceSample
    exact Finset.card_image_le.trans_eq (Fintype.card_fin n)
  have husedCard : used.card ≤ n := by
    dsimp [used]
    exact Finset.card_image_le.trans (by simp)
  have hforbiddenCard : forbidden.card ≤ 2 * n := by
    rw [← hforbidden]
    exact (Finset.card_union_le _ _).trans (by omega)
  split_ifs with hbranch
  · have hfresh := leastFresh_not_mem positiveCode positiveCode_injective forbidden
    refine ⟨fun hs => hfresh (by
      rw [← hforbidden] at hs ⊢
      exact Finset.mem_union_left _ hs), ?_, ?_⟩
    · intro m hm heq
      apply hfresh
      rw [← hforbidden] at heq ⊢
      apply Finset.mem_union_right
      dsimp [used]
      apply Finset.mem_image.mpr
      let k : {x // x ∈ Finset.range n} := ⟨m, Finset.mem_range.mpr hm⟩
      refine ⟨k, by simp [k], ?_⟩
      simpa only [k, restrictAt] using heq.symm
    · exact ⟨_, (leastFresh_le_card _ _ _).trans hforbiddenCard, rfl⟩
  · have hfresh := leastFresh_not_mem negativeCode negativeCode_injective forbidden
    refine ⟨fun hs => hfresh (by
      rw [← hforbidden] at hs ⊢
      exact Finset.mem_union_left _ hs), ?_, ?_⟩
    · intro m hm heq
      apply hfresh
      rw [← hforbidden] at heq ⊢
      apply Finset.mem_union_right
      dsimp [used]
      apply Finset.mem_image.mpr
      let k : {x // x ∈ Finset.range n} := ⟨m, Finset.mem_range.mpr hm⟩
      refine ⟨k, by simp [k], ?_⟩
      simpa only [k, restrictAt] using heq.symm
    · exact ⟨_, (leastFresh_le_card _ _ _).trans hforbiddenCard, rfl⟩


lemma balanced_negative (k : ℕ) : Stage3Case019.balanced (2 * k + 1) = negativeCode k := by
  simp [Stage3Case019.balanced, negativeCode]
  congr 1 <;> omega

lemma balanced_positive (k : ℕ) : Stage3Case019.balanced (2 * k + 2) = positiveCode k := by
  simp [Stage3Case019.balanced, positiveCode]
  congr 1 <;> omega

lemma balanced_injective : Function.Injective Stage3Case019.balanced := by
  intro m n h
  rcases m with _ | m <;> rcases n with _ | n
  · rfl
  · simp [Stage3Case019.balanced] at h
    split at h <;> omega
  · simp [Stage3Case019.balanced] at h
    split at h <;> omega
  · simp [Stage3Case019.balanced] at h
    split at h <;> split at h <;> omega


noncomputable def denseOutput (q : ℕ) (input : ℕ → ℤ) : ℕ → ℤ :=
  Stage3Case019.outputAfterInput (denseSweepGenerator q) input

lemma denseOutput_spec (q : ℕ) (input : ℕ → ℤ) (t : ℕ) :
    denseOutput q input t ∉ GenLimit.Generic.sample input (t + 1) ∧
      (∀ s, s < t → denseOutput q input s ≠ denseOutput q input t) ∧
      ∃ k ≤ 2 * (t + 1), denseOutput q input t =
        if omissionMarkerFinset q ⊆ observedThrough input t then
          positiveCode k else negativeCode k := by
  have h := denseSweepGenerator_spec q (t + 1) (fun j : Fin (t + 1) => input j)
  have hsamp : GenLimit.Generic.sequenceSample (fun j : Fin (t + 1) => input j) =
      GenLimit.Generic.sample input (t + 1) := by
    exact GenLimit.Generic.sequenceSample_prefix input (t + 1)
  rw [hsamp] at h
  have hobs : GenLimit.Generic.sample input (t + 1) = observedThrough input t := rfl
  rw [hobs] at h
  refine ⟨h.1, ?_, h.2.2⟩
  intro s hs
  exact (h.2.1 (s + 1) (by omega)).symm

lemma denseOutput_injective (q : ℕ) (input : ℕ → ℤ) :
    Function.Injective (denseOutput q input) := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · exact False.elim ((denseOutput_spec q input t).2.1 s hlt hst)
  · rfl
  · exact False.elim ((denseOutput_spec q input s).2.1 t hgt hst.symm)

lemma denseOutput_generatorFirst (q : ℕ) (input : ℕ → ℤ) (t : ℕ) :
    denseOutput q input t ∈ Stage3Case019.GeneratorFirstOn input (denseOutput q input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  exact (denseOutput_spec q input t).1
    (GenLimit.Generic.mem_sample_iff.mpr ⟨s, by omega, heq⟩)

lemma denseOutput_rank (q : ℕ) (input : ℕ → ℤ) (t : ℕ) :
    ∃ r < 4 * t + 7, Stage3Case019.balanced r = denseOutput q input t := by
  obtain ⟨k, hk, hout⟩ := (denseOutput_spec q input t).2.2
  split at hout
  · refine ⟨2 * k + 2, by omega, ?_⟩
    rw [balanced_positive, hout]
  · refine ⟨2 * k + 1, by omega, ?_⟩
    rw [balanced_negative, hout]

end Scratch
