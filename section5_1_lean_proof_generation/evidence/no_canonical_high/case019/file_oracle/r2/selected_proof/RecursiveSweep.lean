import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib

open Stage3Case019
open GenLimit.Generic

namespace Case019

lemma exists_code_not_mem
    (code : ℕ → ℤ) (hinj : Function.Injective code) (S : Finset ℤ) :
    ∃ k ≤ S.card, code k ∉ S := by
  classical
  by_cases hex : ∃ k ≤ S.card, code k ∉ S
  · exact hex
  · have hall : ∀ k, k ≤ S.card → code k ∈ S := by
      intro k hk
      by_contra hnot
      exact hex ⟨k, hk, hnot⟩
    have hsub : (Finset.range (S.card + 1)).image code ⊆ S := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨k, hk, rfl⟩ := hz
      apply hall k
      simp only [Finset.mem_range] at hk
      omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc
    omega

noncomputable def boundedSideGenerator
    (code : ℕ → ℤ) (hinj : Function.Injective code) : GenLimit.Generic.Generator ℤ
  | 0, _ => code 0
  | n + 1, xs =>
      let previous : Finset ℤ := Finset.univ.image fun i : Fin n =>
        boundedSideGenerator code hinj (i + 1) (fun j => xs ⟨j, by omega⟩)
      let blocked := sequenceSample xs ∪ previous
      code (Nat.find (exists_code_not_mem code hinj blocked))
termination_by n _ => n

lemma boundedSideGenerator_mem_previous
    (code : ℕ → ℤ) (hinj : Function.Injective code)
    {n : ℕ} (xs : Fin (n + 1) → ℤ) (i : Fin n) :
    boundedSideGenerator code hinj (i + 1) (fun j => xs ⟨j, by omega⟩) ∈
      (Finset.univ.image fun i : Fin n =>
        boundedSideGenerator code hinj (i + 1) (fun j => xs ⟨j, by omega⟩)) := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_univ _, rfl⟩

lemma boundedSideGenerator_spec
    (code : ℕ → ℤ) (hinj : Function.Injective code)
    {n : ℕ} (hn : 0 < n) (xs : Fin n → ℤ) :
    ∃ k < 2 * n,
      boundedSideGenerator code hinj n xs = code k ∧
      boundedSideGenerator code hinj n xs ∉ sequenceSample xs := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let previous : Finset ℤ := Finset.univ.image fun i : Fin m =>
    boundedSideGenerator code hinj (i + 1) (fun j => xs ⟨j, by omega⟩)
  let blocked := sequenceSample xs ∪ previous
  let k := Nat.find (exists_code_not_mem code hinj blocked)
  have hknot : code k ∉ blocked := (Nat.find_spec (exists_code_not_mem code hinj blocked)).2
  have hk_le : k ≤ blocked.card := (Nat.find_spec (exists_code_not_mem code hinj blocked)).1
  have hsample : (sequenceSample xs).card ≤ m + 1 := by
    letI : DecidableEq ℤ := Classical.decEq ℤ
    change (Finset.univ.image xs).card ≤ m + 1
    exact (Finset.card_image_le).trans_eq (by simp)
  have hprevious : previous.card ≤ m := by
    dsimp [previous]
    exact (Finset.card_image_le).trans_eq (by simp)
  have hblocked : blocked.card ≤ 2 * m + 1 := by
    dsimp [blocked]
    exact le_trans (Finset.card_union_le _ _) (by omega)
  refine ⟨k, by omega, ?_, ?_⟩
  · rw [boundedSideGenerator.eq_2]
  · intro hmem
    rw [boundedSideGenerator.eq_2] at hmem
    apply hknot
    apply Finset.mem_union_left
    simpa only [k, blocked, previous] using hmem

lemma boundedSideGenerator_prior_ne
    (code : ℕ → ℤ) (hinj : Function.Injective code)
    {n : ℕ} (xs : Fin n → ℤ) {s : ℕ} (hs : s + 1 < n) :
    boundedSideGenerator code hinj (s + 1) (fun j => xs ⟨j, by omega⟩) ≠
      boundedSideGenerator code hinj n xs := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let previous : Finset ℤ := Finset.univ.image fun i : Fin m =>
    boundedSideGenerator code hinj (i + 1) (fun j => xs ⟨j, by omega⟩)
  let blocked := sequenceSample xs ∪ previous
  let k := Nat.find (exists_code_not_mem code hinj blocked)
  have hknot : code k ∉ blocked :=
    (Nat.find_spec (exists_code_not_mem code hinj blocked)).2
  have hprev :
      boundedSideGenerator code hinj (s + 1) (fun j => xs ⟨j, by omega⟩) ∈ previous := by
    dsimp [previous]
    apply Finset.mem_image.mpr
    refine ⟨⟨s, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 2
  intro heq
  apply hknot
  apply Finset.mem_union_right
  have hout : boundedSideGenerator code hinj (m + 1) xs = code k := by
    rw [boundedSideGenerator.eq_2]
  rw [heq] at hprev
  rw [hout] at hprev
  exact hprev

noncomputable abbrev boundedNegativeGenerator : GenLimit.Generic.Generator ℤ :=
  boundedSideGenerator GenLimit.UnionClosedness.negativeCode
    GenLimit.UnionClosedness.negativeCode_injective

noncomputable abbrev boundedPositiveGenerator : GenLimit.Generic.Generator ℤ :=
  boundedSideGenerator GenLimit.UnionClosedness.positiveCode
    GenLimit.UnionClosedness.positiveCode_injective

end Case019
