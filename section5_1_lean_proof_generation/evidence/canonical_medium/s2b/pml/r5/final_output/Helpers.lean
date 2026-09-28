import Stage3Model
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open GenLimit.KleinbergWei

namespace Stage3Proof

open Stage3S2B

lemma oddThree_not_core (n : ℕ) : 2 * n + 3 ∉ core := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      have heven : Even (2 ^ (Nat.succ k)) := by
        rw [Nat.even_pow]
        simp
      have hodd : ¬ Even (2 * n + 3) := Nat.not_even_iff_odd.mpr ⟨n + 1, by omega⟩
      exact hodd (hk ▸ heven)

lemma ordinary_infinite : ordinary.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 3) := by
    intro a b h
    have hmul : 2 * a = 2 * b := Nat.add_right_cancel h
    exact Nat.mul_left_cancel (by decide) hmul
  have hrange : (Set.range fun n : ℕ => 2 * n + 3).Infinite :=
    Set.infinite_range_of_injective hinj
  exact hrange.mono (by
    rintro z ⟨n, rfl⟩
    exact oddThree_not_core n)

lemma targetClass_not_countable : ¬ targetClass.Countable := by
  intro hcount
  letI : Infinite ordinary := ordinary_infinite.to_subtype
  have hpowers : ¬ Countable (Set ordinary) :=
    GenLimit.UnionClosedness.powerSet_not_countable ordinary
  apply hpowers
  let encode : Set ordinary → Language := fun A => core ∪ ((↑) '' A)
  have henc_mem : ∀ A, encode A ∈ targetClass := by
    intro A
    exact ⟨(↑) '' A, by
      rintro z ⟨a, ha, rfl⟩
      exact a.property, rfl⟩
  have hinj : Function.Injective encode := by
    intro A B hab
    ext a
    have haOrd : (a : ℕ) ∉ core := a.property
    have hmemA : (a : ℕ) ∈ encode A ↔ a ∈ A := by
      simp [encode, haOrd]
    have hmemB : (a : ℕ) ∈ encode B ↔ a ∈ B := by
      simp [encode, haOrd]
    rw [← hmemA, hab, hmemB]
  have hrange : (Set.range encode).Countable :=
    hcount.mono (by rintro K ⟨A, rfl⟩; exact henc_mem A)
  letI : Countable (Set.range encode) := hrange.to_subtype
  let lift : Set ordinary → Set.range encode := fun A => ⟨encode A, ⟨A, rfl⟩⟩
  exact (show Function.Injective lift from
    fun _ _ h => hinj (Subtype.ext_iff.mp h)).countable

lemma core_generator_injective : Function.Injective (fun t : ℕ => 2 ^ t) := by
  exact (strictMono_nat_of_lt_succ (fun n => by simp [pow_succ])).injective

lemma uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, core_generator_injective, 0, ?_⟩
  intro K hK t _
  obtain ⟨A, hA, rfl⟩ := hK
  exact Or.inl ⟨t, rfl⟩

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

noncomputable def freshOrdinary (I R : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ z, z ∈ ordinary ∧ z ∉ I ∧ z ∉ R by
    obtain ⟨z, hzO, hz⟩ := ordinary_infinite.exists_notMem_finset (I ∪ R)
    refine ⟨z, hzO, ?_, ?_⟩
    · intro hzI
      exact hz (by simp [hzI])
    · intro hzR
      exact hz (by simp [hzR]))

lemma freshOrdinary_spec (I R : Finset ℕ) :
    freshOrdinary I R ∈ ordinary ∧ freshOrdinary I R ∉ I ∧ freshOrdinary I R ∉ R := by
  classical
  exact Nat.find_spec (show ∃ z, z ∈ ordinary ∧ z ∉ I ∧ z ∉ R by
    obtain ⟨z, hzO, hz⟩ := ordinary_infinite.exists_notMem_finset (I ∪ R)
    refine ⟨z, hzO, ?_, ?_⟩
    · intro hzI
      exact hz (by simp [hzI])
    · intro hzR
      exact hz (by simp [hzR]))

structure RunState where
  admitted : Finset ℕ
  rejected : Finset ℕ
  presentation : Stream
  query : ℕ → Option ℕ
  answer : ℕ → Option Bool
  output : Stream

noncomputable def initialState : RunState where
  admitted := ∅
  rejected := ∅
  presentation := fun _ => 0
  query := fun _ => none
  answer := fun _ => none
  output := fun _ => 0

noncomputable def step (gen : FeedbackGenerator) (t : ℕ) (s : RunState) : RunState := by
  classical
  let x := if Even t then 2 ^ (t / 2) else freshOrdinary s.admitted s.rejected
  let I := if Even t then s.admitted else insert x s.admitted
  let presentation := Function.update s.presentation t x
  let q := gen.query t (fun i => presentation i) (fun i => s.answer i)
  let positive (z : ℕ) := z ∈ core ∨ z ∈ I
  let a := q.map (fun z => positive z)
  let Rq := match q with
    | none => s.rejected
    | some z => if positive z then s.rejected else insert z s.rejected
  let query := Function.update s.query t q
  let answer := Function.update s.answer t a
  let y := gen.output t (fun i => presentation i) (fun i => answer i)
  let output := Function.update s.output t y
  let R := if y ∈ ordinary ∧ y ∉ I then insert y Rq else Rq
  exact ⟨I, R, presentation, query, answer, output⟩

noncomputable def run (gen : FeedbackGenerator) : ℕ → RunState
  | 0 => initialState
  | t + 1 => step gen t (run gen t)

noncomputable def builtPresentation (gen : FeedbackGenerator) : Stream :=
  fun t => (run gen (t + 1)).presentation t

noncomputable def builtQuery (gen : FeedbackGenerator) : ℕ → Option ℕ :=
  fun t => (run gen (t + 1)).query t

noncomputable def builtAnswer (gen : FeedbackGenerator) : ℕ → Option Bool :=
  fun t => (run gen (t + 1)).answer t

noncomputable def builtOutput (gen : FeedbackGenerator) : Stream :=
  fun t => (run gen (t + 1)).output t

noncomputable def admittedLimit (gen : FeedbackGenerator) : Language :=
  {z | ∃ t, z ∈ (run gen t).admitted}

noncomputable def builtTarget (gen : FeedbackGenerator) : Language :=
  core ∪ admittedLimit gen

noncomputable def builtTranscript (gen : FeedbackGenerator) : Transcript where
  presentation := builtPresentation gen
  query := builtQuery gen
  answer := builtAnswer gen
  output := builtOutput gen

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

lemma step_presentation_current (gen : FeedbackGenerator) (t : ℕ) (s : RunState) :
    (step gen t s).presentation t =
      (if Even t then 2 ^ (t / 2) else freshOrdinary s.admitted s.rejected) := by
  classical
  simp [step]

lemma step_presentation_prior (gen : FeedbackGenerator) (t i : ℕ) (s : RunState)
    (hi : i ≠ t) :
    (step gen t s).presentation i = s.presentation i := by
  classical
  simp [step, hi]

lemma step_query_current (gen : FeedbackGenerator) (t : ℕ) (s : RunState) :
    (step gen t s).query t = gen.query t
      (fun i => (step gen t s).presentation i) (fun i => s.answer i) := by
  classical
  simp [step]

lemma step_answer_current (gen : FeedbackGenerator) (t : ℕ) (s : RunState) :
    (step gen t s).answer t =
      ((step gen t s).query t).map (fun z =>
        membershipAnswer (core ∪ (step gen t s).admitted) z) := by
  classical
  unfold step
  dsimp
  generalize gen.query t
      (fun i => Function.update s.presentation t
        (if Even t then 2 ^ (t / 2) else freshOrdinary s.admitted s.rejected) i)
      (fun i => s.answer i) = q
  cases q <;> simp [membershipAnswer, Bool.decide_or]

lemma step_output_current (gen : FeedbackGenerator) (t : ℕ) (s : RunState) :
    (step gen t s).output t = gen.output t
      (fun i => (step gen t s).presentation i)
      (fun i => (step gen t s).answer i) := by
  classical
  simp [step]

lemma step_answer_prior (gen : FeedbackGenerator) (t i : ℕ) (s : RunState)
    (hi : i ≠ t) :
    (step gen t s).answer i = s.answer i := by
  classical
  simp [step, hi]

lemma step_query_prior (gen : FeedbackGenerator) (t i : ℕ) (s : RunState)
    (hi : i ≠ t) :
    (step gen t s).query i = s.query i := by
  classical
  simp [step, hi]

lemma step_output_prior (gen : FeedbackGenerator) (t i : ℕ) (s : RunState)
    (hi : i ≠ t) :
    (step gen t s).output i = s.output i := by
  classical
  simp [step, hi]

lemma run_presentation_stable (gen : FeedbackGenerator) {i n : ℕ} (h : i < n) :
    (run gen n).presentation i = builtPresentation gen i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hin : i = n
      · subst i
        rfl
      · rw [run, step_presentation_prior gen n i _ hin]
        exact ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hin)

lemma run_query_stable (gen : FeedbackGenerator) {i n : ℕ} (h : i < n) :
    (run gen n).query i = builtQuery gen i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hin : i = n
      · subst i
        rfl
      · rw [run, step_query_prior gen n i _ hin]
        exact ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hin)

lemma run_answer_stable (gen : FeedbackGenerator) {i n : ℕ} (h : i < n) :
    (run gen n).answer i = builtAnswer gen i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hin : i = n
      · subst i
        rfl
      · rw [run, step_answer_prior gen n i _ hin]
        exact ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hin)

lemma run_output_stable (gen : FeedbackGenerator) {i n : ℕ} (h : i < n) :
    (run gen n).output i = builtOutput gen i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hin : i = n
      · subst i
        rfl
      · rw [run, step_output_prior gen n i _ hin]
        exact ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hin)

end Stage3Proof

namespace Stage3Proof

open Stage3S2B

structure StateInv (s : RunState) : Prop where
  admitted_ordinary : ∀ z ∈ s.admitted, z ∈ ordinary
  rejected_ordinary : ∀ z ∈ s.rejected, z ∈ ordinary
  disjoint : Disjoint s.admitted s.rejected

lemma initial_inv : StateInv initialState := by
  constructor <;> simp [initialState]

lemma step_admitted_mono (gen : FeedbackGenerator) (t : ℕ) (s : RunState) :
    s.admitted ⊆ (step gen t s).admitted := by
  classical
  simp [step]
  split <;> simp


end Stage3Proof
