import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Abstract.Density
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

open Set Function Filter
open scoped Topology

namespace Stage3S2B

private structure BuildState where
  presentation : ℕ → ℕ := fun _ => 0
  query : ℕ → Option ℕ := fun _ => none
  answer : ℕ → Option Bool := fun _ => none
  output : ℕ → ℕ := fun _ => 0
  presented : Finset ℕ := ∅
  blocked : Finset ℕ := ∅

private noncomputable def fresh (s : BuildState) : ℕ :=
  Nat.find (Finset.exists_not_mem (s.presented ∪ s.blocked))

private theorem fresh_not_mem (s : BuildState) :
    fresh s ∉ s.presented ∪ s.blocked :=
  Nat.find_spec (Finset.exists_not_mem (s.presented ∪ s.blocked))

private noncomputable def advance (gen : FeedbackGenerator) (t : ℕ)
    (s : BuildState) : BuildState := by
  classical
  let z := fresh s
  let p' := insert z s.presented
  let q := gen.query t (fun i => s.presentation i) (fun i => s.answer i)
  let a := match q with
    | none => none
    | some u => some (decide (u ∈ core ∨ u ∈ p'))
  let r' := match q with
    | some u => if u ∈ core ∨ u ∈ p' then s.blocked else insert u s.blocked
    | none => s.blocked
  let y := gen.output t (fun i => Function.update s.presentation t z i)
    (fun i => Function.update s.answer t a i)
  let r'' := if y ∈ core ∨ y ∈ p' then r' else insert y r'
  exact {
    presentation := Function.update s.presentation t z
    query := Function.update s.query t q
    answer := Function.update s.answer t a
    output := Function.update s.output t y
    presented := p'
    blocked := r'' }

private noncomputable def states (gen : FeedbackGenerator) : ℕ → BuildState
  | 0 => {}
  | t + 1 => advance gen t (states gen t)

private noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation t := (states gen (t + 1)).presentation t
  query t := (states gen (t + 1)).query t
  answer t := (states gen (t + 1)).answer t
  output t := (states gen (t + 1)).output t

private noncomputable def builtTarget (gen : FeedbackGenerator) : Language :=
  core ∪ Set.range (builtTranscript gen).presentation

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro h
  let encode : Set ordinary → Language := fun A => core ∪ Subtype.val '' A
  have hmem : ∀ A : Set ordinary, encode A ∈ targetClass := by
    intro A
    refine ⟨Subtype.val '' A, ?_, rfl⟩
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact a.property
  have hinj : Function.Injective encode := by
    intro A B hab
    ext a
    have ha : (a : ℕ) ∉ core := a.property
    have heq := Set.ext_iff.mp hab (a : ℕ)
    simpa [encode, ha] using heq
  have hcountRange : (Set.range encode).Countable := h.mono (by
    intro K hK
    obtain ⟨A, rfl⟩ := hK
    exact hmem A)
  have hcount : Countable (Set ordinary) := by
    letI : Countable (Set.range encode) := hcountRange.to_subtype
    obtain ⟨code, hcode⟩ := (countable_iff_exists_injective (Set.range encode)).mp inferInstance
    rw [countable_iff_exists_injective]
    exact ⟨fun A => code ⟨encode A, A, rfl⟩, fun A B hab => hinj (Subtype.ext_iff.mp (hcode hab))⟩
  haveI : Infinite ordinary := by
    rw [Set.infinite_coe_iff]
    exact Set.infinite_of_injective_forall_mem
      (f := fun n => 2 * n + 3)
      (fun a b hab => Nat.mul_left_cancel (by omega) (Nat.add_right_cancel hab))
      (fun n => by
        simp only [ordinary, mem_compl_iff, core, mem_range, not_exists]
        intro k hk
        cases k with
        | zero => simp at hk
        | succ k => simp [pow_succ] at hk; omega)
  exact GenLimit.UnionClosedness.powerSet_not_countable ordinary hcount

theorem uniform_generation : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _
  obtain ⟨A, hA, rfl⟩ := hK
  exact Or.inl ⟨t, rfl⟩


private theorem advance_presentation_at (gen : FeedbackGenerator) (t : ℕ) (s : BuildState) :
    (advance gen t s).presentation t = fresh s := by
  classical
  simp [advance]

private theorem advance_query_at (gen : FeedbackGenerator) (t : ℕ) (s : BuildState) :
    (advance gen t s).query t = gen.query t
      (fun i => s.presentation i) (fun i => s.answer i) := by
  classical
  simp [advance]

private theorem advance_answer_at (gen : FeedbackGenerator) (t : ℕ) (s : BuildState) :
    (advance gen t s).answer t = match gen.query t
      (fun i => s.presentation i) (fun i => s.answer i) with
      | none => none
      | some u => some (decide (u ∈ core ∨ u ∈ insert (fresh s) s.presented)) := by
  classical
  simp [advance]

private theorem advance_output_at (gen : FeedbackGenerator) (t : ℕ) (s : BuildState) :
    (advance gen t s).output t = gen.output t
      (fun i => Function.update s.presentation t (fresh s) i)
      (fun i => Function.update s.answer t
        (match gen.query t (fun i => s.presentation i) (fun i => s.answer i) with
         | none => none
         | some u => some (decide (u ∈ core ∨ u ∈ insert (fresh s) s.presented))) i) := by
  classical
  simp [advance]

private theorem advance_old (gen : FeedbackGenerator) (t : ℕ) (s : BuildState)
    {i : ℕ} (hi : i ≠ t) :
    (advance gen t s).presentation i = s.presentation i ∧
    (advance gen t s).query i = s.query i ∧
    (advance gen t s).answer i = s.answer i ∧
    (advance gen t s).output i = s.output i := by
  classical
  simp [advance, Function.update_noteq hi]

private theorem state_history (gen : FeedbackGenerator) (t : ℕ) :
    (∀ i, i < t → (states gen t).presentation i = (builtTranscript gen).presentation i) ∧
    (∀ i, i < t → (states gen t).query i = (builtTranscript gen).query i) ∧
    (∀ i, i < t → (states gen t).answer i = (builtTranscript gen).answer i) ∧
    (∀ i, i < t → (states gen t).output i = (builtTranscript gen).output i) := by
  induction t with
  | zero => simp
  | succ t ih =>
      constructor
      · intro i hi
        by_cases hit : i = t
        · subst i; rfl
        · rw [(advance_old gen t (states gen t) hit).1]
          exact ih.1 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hit)
      constructor
      · intro i hi
        by_cases hit : i = t
        · subst i; rfl
        · rw [(advance_old gen t (states gen t) hit).2.1]
          exact ih.2.1 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hit)
      constructor
      · intro i hi
        by_cases hit : i = t
        · subst i; rfl
        · rw [(advance_old gen t (states gen t) hit).2.2.1]
          exact ih.2.2.1 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hit)
      · intro i hi
        by_cases hit : i = t
        · subst i; rfl
        · rw [(advance_old gen t (states gen t) hit).2.2.2]
          exact ih.2.2.2 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hit)

private theorem state_invariant (gen : FeedbackGenerator) (t : ℕ) :
    (states gen t).presented.card = t ∧
    Disjoint (states gen t).presented (states gen t).blocked ∧
    (∀ z ∈ (states gen t).blocked, z ∉ core) := by

end Stage3S2B
