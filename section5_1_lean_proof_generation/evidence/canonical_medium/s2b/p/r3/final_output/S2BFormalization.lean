import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3Proof

open Stage3S2B

lemma odd_not_core (n : ℕ) : 2 * n + 3 ∈ ordinary := by
  intro h
  rcases h with ⟨k, hk⟩
  have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
  have hkpos : 0 < k := by
    by_contra hz
    have : k = 0 := Nat.eq_zero_of_not_pos hz
    subst k
    simp at hk
  change 2 ^ k = 2 * n + 3 at hk
  have heven : Even (2 ^ k) := (Nat.even_pow).2 ⟨even_two, by omega⟩
  rw [hk] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

lemma ordinary_infinite : ordinary.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 3)
  · intro a b h
    dsimp at h
    omega
  · exact odd_not_core

noncomputable def freshOrd (s : Finset ℕ) : ℕ :=
  by classical exact Nat.find (ordinary_infinite.exists_notMem_finset s)

lemma freshOrd_spec (s : Finset ℕ) : freshOrd s ∈ ordinary ∧ freshOrd s ∉ s :=
  by classical exact Nat.find_spec (ordinary_infinite.exists_notMem_finset s)

structure SimState where
  admitted : Finset ℕ
  rejected : Finset ℕ
  presentation : ℕ → ℕ
  query : ℕ → Option ℕ
  answer : ℕ → Option Bool
  output : ℕ → ℕ

noncomputable def step (gen : FeedbackGenerator) (t : ℕ) (s : SimState) : SimState := by
  classical
  let isOdd := t % 2 = 1
  let x := if isOdd then freshOrd (s.admitted ∪ s.rejected) else 2 ^ (t / 2)
  let admitted' := if isOdd then insert x s.admitted else s.admitted
  let q := gen.query t (fun i => Function.update s.presentation t x i) (fun i => s.answer i)
  let answerValue : Option Bool := match q with
    | none => none
    | some z => some (decide (z ∈ core ∨ z ∈ admitted'))
  let rejectedQ := match q with
    | some z => if z ∈ ordinary ∧ z ∉ admitted' ∧ z ∉ s.rejected then insert z s.rejected else s.rejected
    | none => s.rejected
  let y := gen.output t (fun i => Function.update s.presentation t x i)
    (fun i => Function.update s.answer t answerValue i)
  let rejected' := if y ∈ ordinary ∧ y ∉ admitted' ∧ y ∉ rejectedQ then insert y rejectedQ else rejectedQ
  exact {
    admitted := admitted'
    rejected := rejected'
    presentation := Function.update s.presentation t x
    query := Function.update s.query t q
    answer := Function.update s.answer t answerValue
    output := Function.update s.output t y
  }

noncomputable def states (gen : FeedbackGenerator) : ℕ → SimState
  | 0 => ⟨∅, ∅, 0, fun _ => none, fun _ => none, 0⟩
  | t + 1 => step gen t (states gen t)

noncomputable def simPresentation (gen : FeedbackGenerator) (t : ℕ) := (states gen (t+1)).presentation t
noncomputable def simQuery (gen : FeedbackGenerator) (t : ℕ) := (states gen (t+1)).query t
noncomputable def simAnswer (gen : FeedbackGenerator) (t : ℕ) := (states gen (t+1)).answer t
noncomputable def simOutput (gen : FeedbackGenerator) (t : ℕ) := (states gen (t+1)).output t
noncomputable def admittedLimit (gen : FeedbackGenerator) : Set ℕ := {z | ∃ t, z ∈ (states gen t).admitted}
noncomputable def diagonalTarget (gen : FeedbackGenerator) : Set ℕ := core ∪ admittedLimit gen

-- Values written at a round are never changed later.
lemma states_stable (gen : FeedbackGenerator) {i t : ℕ} (h : i < t) :
    (states gen t).presentation i = simPresentation gen i ∧
    (states gen t).query i = simQuery gen i ∧
    (states gen t).answer i = simAnswer gen i ∧
    (states gen t).output i = simOutput gen i := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases hit : i = t
    · subst i
      simp [simPresentation, simQuery, simAnswer, simOutput, states, step]
    · have hil : i < t := by omega
      have hrec := ih hil
      simpa [states, step, Function.update, hit] using hrec

lemma targetClass_diagonal (gen : FeedbackGenerator) : diagonalTarget gen ∈ targetClass := by
  refine ⟨admittedLimit gen, ?_, rfl⟩
  rintro z ⟨t, hz⟩
  induction t with
  | zero => simp [states] at hz
  | succ t ih =>
    simp only [states] at hz
    simp only [step] at hz
    split at hz
    · simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact (freshOrd_spec _).1
      · exact ih hz
    · exact ih hz


lemma targetClass_nonempty : targetClass.Nonempty := by
  refine ⟨core, ?_⟩
  exact ⟨∅, Set.empty_subset _, by simp⟩

lemma targetClass_uncountable : ¬ targetClass.Countable := by
  intro hc
  obtain ⟨f, hf⟩ := hc.exists_surjective targetClass_nonempty
  let marker : ℕ → ℕ := fun n => 2 * n + 3
  let A : Set ℕ := {z | ∃ n, z = marker n ∧ marker n ∉ (f n : Set ℕ)}
  let K : Set ℕ := core ∪ A
  have hA : A ⊆ ordinary := by
    rintro z ⟨n, rfl, _⟩
    exact odd_not_core n
  have hK : K ∈ targetClass := ⟨A, hA, rfl⟩
  obtain ⟨n, hn⟩ := hf ⟨K, hK⟩
  have hsets : (f n : Set ℕ) = K := congrArg Subtype.val hn
  have hmord : marker n ∈ ordinary := odd_not_core n
  have hmcore : marker n ∉ core := hmord
  have hdiag : marker n ∈ A ↔ marker n ∉ (f n : Set ℕ) := by
    constructor
    · rintro ⟨j, hj, hnot⟩
      have hmn : marker j = marker n := hj.symm
      have hnj : j = n := by
        dsimp [marker] at hmn
        omega
      simpa [hnj] using hnot
    · intro hnot
      exact ⟨n, rfl, hnot⟩
  have hmem : marker n ∈ (f n : Set ℕ) ↔ marker n ∈ A := by
    rw [hsets]
    simp [K, hmcore]
  by_cases h : marker n ∈ (f n : Set ℕ)
  · exact (hdiag.mp (hmem.mp h)) h
  · exact h (hmem.mpr (hdiag.mpr h))

lemma uniform_positive : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

end Stage3Proof

open Stage3S2B
open Stage3Proof

theorem stage3_positive :
    ¬ Stage3S2B.targetClass.Countable ∧ Stage3S2B.UniformlyGeneratableWithoutSamples := by
  exact ⟨targetClass_uncountable, uniform_positive⟩
