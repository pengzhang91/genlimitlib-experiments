import Stage3Model

open Stage3Case019

namespace Stage3Case019.Partial

noncomputable def chooseFresh {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (used : Finset α) : α :=
  Classical.choose (hK.exists_notMem_finset used)

lemma chooseFresh_mem {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (used : Finset α) :
    chooseFresh K hK used ∈ K :=
  (Classical.choose_spec (hK.exists_notMem_finset used)).1

lemma chooseFresh_not_mem {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (used : Finset α) :
    chooseFresh K hK used ∉ used :=
  (Classical.choose_spec (hK.exists_notMem_finset used)).2

noncomputable def knownTargetGenerator {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) : Generator α :=
  fun t xs =>
    chooseFresh K hK
      (GenLimit.Generic.sequenceSample xs ∪
        Finset.univ.image (fun s : Fin t =>
          knownTargetGenerator K hK s
            (fun j => xs ⟨j, Nat.lt_trans j.isLt s.isLt⟩)))
termination_by t => t

lemma knownTargetGenerator_mem {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (t : ℕ) (xs : Fin t → α) :
    knownTargetGenerator K hK t xs ∈ K := by
  rw [knownTargetGenerator]
  apply chooseFresh_mem

lemma knownTargetGenerator_not_used {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (t : ℕ) (xs : Fin t → α) :
    knownTargetGenerator K hK t xs ∉
      GenLimit.Generic.sequenceSample xs ∪
        Finset.univ.image (fun s : Fin t =>
          knownTargetGenerator K hK s
            (fun j => xs ⟨j, Nat.lt_trans j.isLt s.isLt⟩)) := by
  rw [knownTargetGenerator]
  apply chooseFresh_not_mem

lemma knownTargetGenerator_not_input {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (t : ℕ) (xs : Fin t → α) (j : Fin t) :
    knownTargetGenerator K hK t xs ≠ xs j := by
  intro heq
  have hnot := knownTargetGenerator_not_used K hK t xs
  apply hnot
  apply Finset.mem_union_left
  rw [GenLimit.Generic.sequenceSample]
  simp [heq]

lemma knownTargetGenerator_ne_prior {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (t : ℕ) (xs : Fin t → α) (s : Fin t) :
    knownTargetGenerator K hK s
        (fun j => xs ⟨j, Nat.lt_trans j.isLt s.isLt⟩) ≠
      knownTargetGenerator K hK t xs := by
  intro heq
  have hnot := knownTargetGenerator_not_used K hK t xs
  apply hnot
  apply Finset.mem_union_right
  exact Finset.mem_image.2 ⟨s, Finset.mem_univ s, heq⟩

end Stage3Case019.Partial

namespace Stage3Case019.Partial

lemma knownTarget_output_mem {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (t : ℕ) :
    outputAfterInput (knownTargetGenerator K hK) input t ∈ K := by
  apply knownTargetGenerator_mem

lemma knownTarget_output_not_sample {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) (t : ℕ) :
    outputAfterInput (knownTargetGenerator K hK) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  intro hmem
  rw [GenLimit.Generic.sample] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨j, hj, heq⟩ := hmem
  have hne := knownTargetGenerator_not_input K hK (t + 1)
    (fun i : Fin (t + 1) => input i) ⟨j, hj⟩
  exact hne heq.symm

lemma knownTarget_output_ne_prior {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) {s t : ℕ} (hst : s < t) :
    outputAfterInput (knownTargetGenerator K hK) input s ≠
      outputAfterInput (knownTargetGenerator K hK) input t := by
  have hlt : s + 1 < t + 1 := Nat.add_lt_add_right hst 1
  have hne := knownTargetGenerator_ne_prior K hK (t + 1)
    (fun i : Fin (t + 1) => input i) ⟨s + 1, hlt⟩
  simpa [outputAfterInput, GenLimit.Generic.output] using hne

/-- With the target supplied semantically, freshness and non-repetition hold
from the first paper round, independently of the presentation quality. -/
theorem knownTarget_novel {α : Type*} [DecidableEq α]
    (K : Set α) (hK : K.Infinite) (input : Stream α) :
    NovelGeneratesAfterInput input
      (outputAfterInput (knownTargetGenerator K hK) input) K := by
  refine ⟨0, fun t _ => ?_⟩
  exact ⟨knownTarget_output_mem K hK input t,
    knownTarget_output_not_sample K hK input t,
    fun s hst => knownTarget_output_ne_prior K hK input hst⟩

end Stage3Case019.Partial
