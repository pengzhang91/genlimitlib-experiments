import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3S2B

lemma core_mem_targetClass : core ∈ targetClass := by
  refine ⟨∅, empty_subset _, ?_⟩
  simp

lemma core_subset_of_mem_targetClass {K : Language} (hK : K ∈ targetClass) : core ⊆ K := by
  rcases hK with ⟨A, hA, rfl⟩
  exact subset_union_left

lemma pow_two_injective : Function.Injective (fun k : ℕ => 2 ^ k) := by
  exact Nat.pow_right_injective (by omega)

lemma ordinary_infinite : Infinite (Subtype ordinary) := by
  let embed : ℕ → Subtype ordinary := fun n => ⟨2 * n + 3, by
    intro hcore
    rcases hcore with ⟨k, hk⟩
    change 2 ^ k = 2 * n + 3 at hk
    by_cases hk0 : k = 0
    · subst k
      simp at hk
    · have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨by simp, hk0⟩
      have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
      rw [hk] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven⟩
  exact Infinite.of_injective embed (by
    intro a b hab
    have hval := congrArg Subtype.val hab
    dsimp [embed] at hval
    omega)

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  let encode : Set (Subtype ordinary) → {K // K ∈ targetClass} := fun A =>
    ⟨core ∪ ((fun z : Subtype ordinary => (z : ℕ)) '' A), by
      refine ⟨((fun z : Subtype ordinary => (z : ℕ)) '' A), ?_, rfl⟩
      intro n hn
      rcases hn with ⟨z, hz, rfl⟩
      exact z.property⟩
  have hencode : Function.Injective encode := by
    intro A B hAB
    ext z
    have hord : (z : ℕ) ∉ core := z.property
    have hu : (z : ℕ) ∈ core ∪ ((fun w : Subtype ordinary => (w : ℕ)) '' A) ↔ z ∈ A := by
      constructor
      · intro hz
        rcases hz with hz | hz
        · exact False.elim (hord hz)
        · rcases hz with ⟨w, hw, heq⟩
          have : w = z := Subtype.ext heq
          simpa [this] using hw
      · intro hz
        exact Or.inr ⟨z, hz, rfl⟩
    have hv : (z : ℕ) ∈ core ∪ ((fun w : Subtype ordinary => (w : ℕ)) '' B) ↔ z ∈ B := by
      constructor
      · intro hz
        rcases hz with hz | hz
        · exact False.elim (hord hz)
        · rcases hz with ⟨w, hw, heq⟩
          have : w = z := Subtype.ext heq
          simpa [this] using hw
      · intro hz
        exact Or.inr ⟨z, hz, rfl⟩
    rw [← hu, ← hv]
    have hsets : core ∪ ((fun w : Subtype ordinary => (w : ℕ)) '' A) =
        core ∪ ((fun w : Subtype ordinary => (w : ℕ)) '' B) :=
      congrArg Subtype.val hAB
    rw [hsets]
  letI : Countable {K // K ∈ targetClass} := hcount.to_subtype
  letI : Infinite (Subtype ordinary) := ordinary_infinite
  have : Countable (Set (Subtype ordinary)) := hencode.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable (Subtype ordinary) this

lemma uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨(fun k => 2 ^ k), pow_two_injective, 0, ?_⟩
  intro K hK t ht
  exact core_subset_of_mem_targetClass hK ⟨t, rfl⟩

end Stage3S2B

namespace Stage3S2B

private def snoc {α : Type} {n : ℕ} (f : Fin n → α) (a : α) : Fin (n + 1) → α :=
  Fin.lastCases a f

private structure Hist (n : ℕ) where
  presentation : Fin n → ℕ
  query : Fin n → Option ℕ
  answer : Fin n → Option Bool
  output : Fin n → ℕ

private def Hist.empty : Hist 0 where
  presentation := Fin.elim0
  query := Fin.elim0
  answer := Fin.elim0
  output := Fin.elim0

private def admissible {n : ℕ} (h : Hist n) (z : ℕ) : Prop :=
  (∀ i, h.presentation i < z) ∧
    (z ∈ core ∨ ∀ i, h.query i ≠ some z)

private lemma exists_admissible {n : ℕ} (h : Hist n) : ∃ z, admissible h z := by
  let b := ∑ i : Fin n, h.presentation i
  have hk : b < 2 ^ b := Nat.lt_pow_self (by omega)
  refine ⟨2 ^ b, ?_, Or.inl ⟨b, rfl⟩⟩
  intro i
  exact lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hk

private noncomputable def nextPresentation {n : ℕ} (h : Hist n) : ℕ := by
  classical
  exact Nat.find (exists_admissible h)

private lemma nextPresentation_spec {n : ℕ} (h : Hist n) :
    admissible h (nextPresentation h) := by
  classical
  exact Nat.find_spec (exists_admissible h)

private noncomputable def extend (gen : FeedbackGenerator) {n : ℕ} (h : Hist n) : Hist (n + 1) := by
  let x := nextPresentation h
  let xs := snoc h.presentation x
  let q := gen.query n xs h.answer
  let a := match q with
    | none => none
    | some z => some (membershipAnswer (core ∪ Set.range xs) z)
  let as := snoc h.answer a
  let y := gen.output n xs as
  exact {
    presentation := xs
    query := snoc h.query q
    answer := as
    output := snoc h.output y
  }

private noncomputable def run (gen : FeedbackGenerator) : (n : ℕ) → Hist n
  | 0 => Hist.empty
  | n + 1 => extend gen (run gen n)

private noncomputable def adversarialTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := nextPresentation (run gen t)
  query t := gen.query t
    (snoc (run gen t).presentation (nextPresentation (run gen t)))
    (run gen t).answer
  answer t := match gen.query t
      (snoc (run gen t).presentation (nextPresentation (run gen t)))
      (run gen t).answer with
    | none => none
    | some z => some (membershipAnswer
        (core ∪ Set.range (snoc (run gen t).presentation (nextPresentation (run gen t)))) z)
  output t := gen.output t
    (snoc (run gen t).presentation (nextPresentation (run gen t)))
    (snoc (run gen t).answer (match gen.query t
      (snoc (run gen t).presentation (nextPresentation (run gen t)))
      (run gen t).answer with
      | none => none
      | some z => some (membershipAnswer
          (core ∪ Set.range (snoc (run gen t).presentation (nextPresentation (run gen t)))) z)))

private lemma run_presentation (gen : FeedbackGenerator) (n : ℕ) :
    (run gen n).presentation = fun i : Fin n => (adversarialTranscript gen).presentation (i : ℕ) := by
  funext i
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [run]
      simp only [extend]
      change snoc (run gen n).presentation (nextPresentation (run gen n)) i = _
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [snoc, adversarialTranscript]
      · simpa [snoc, adversarialTranscript] using ih j

private lemma run_query (gen : FeedbackGenerator) (n : ℕ) :
    (run gen n).query = fun i : Fin n => (adversarialTranscript gen).query (i : ℕ) := by
  funext i
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [run]
      simp only [extend]
      change snoc (run gen n).query _ i = _
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [snoc, adversarialTranscript]
      · simpa [snoc, adversarialTranscript] using ih j

private lemma run_answer (gen : FeedbackGenerator) (n : ℕ) :
    (run gen n).answer = fun i : Fin n => (adversarialTranscript gen).answer (i : ℕ) := by
  funext i
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [run]
      simp only [extend]
      change snoc (run gen n).answer _ i = _
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [snoc, adversarialTranscript]
      · simpa [snoc, adversarialTranscript] using ih j

private lemma run_output (gen : FeedbackGenerator) (n : ℕ) :
    (run gen n).output = fun i : Fin n => (adversarialTranscript gen).output (i : ℕ) := by
  funext i
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [run]
      simp only [extend]
      change snoc (run gen n).output _ i = _
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [snoc, adversarialTranscript]
      · simpa [snoc, adversarialTranscript] using ih j

end Stage3S2B

namespace Stage3S2B

end Stage3S2B
