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



theorem negative_claim : NegativeClaim := by
  intro gen hgen
  sorry

end Stage3S2B
