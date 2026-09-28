import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main

open Stage3Case025

namespace Case025

open GenLimit

noncomputable def oracleOfFamily (family : ℕ → GenLimit.Language)
    (hinf : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by simp

lemma sample_eq_of_prefix_eq {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    sample a t = sample b t := by
  ext x
  simp only [mem_sample_iff]
  constructor <;> rintro ⟨s, hs, rfl⟩
  · exact ⟨s, hs, (h s hs).symm⟩
  · exact ⟨s, hs, h s hs⟩

lemma consistent_eq_of_sample_eq (C : LanguageFamily) {a b : ℕ → ℕ} {t i : ℕ}
    (h : sample a t = sample b t) :
    Consistent C a t i ↔ Consistent C b t i := by
  simp only [Consistent]
  rw [h]

lemma recursiveCritical_eq_of_sample_eq (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : sample a t = sample b t) (i : ℕ) :
    RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [RecursiveCritical] using consistent_eq_of_sample_eq C h (i := 0)
      | succ i =>
          rw [RecursiveCritical, RecursiveCritical]
          rw [consistent_eq_of_sample_eq C h]
          constructor
          · rintro ⟨hcon, hcrit⟩
            exact ⟨hcon, fun j hj hjcrit => hcrit j hj ((ih j (by omega)).2 hjcrit)⟩
          · rintro ⟨hcon, hcrit⟩
            exact ⟨hcon, fun j hj hjcrit => hcrit j hj ((ih j (by omega)).1 hjcrit)⟩

lemma patient_run_congr (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ s, s < t → a s = b s) :
    PatientMachine.run O a t = PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hp : ∀ s, s < t → a s = b s := fun s hs => h s (Nat.lt.step hs)
      have hrun := ih hp
      have hsamp : ∀ k, k ≤ t + 1 → sample a k = sample b k := by
        intro k hk
        apply sample_eq_of_prefix_eq
        intro s hs
        exact h s (lt_of_lt_of_le hs hk)
      rw [PatientMachine.run_succ, PatientMachine.run_succ, hrun]
      simp only [PatientMachine.processRound]
      have hcon_t : Consistent O.language a t = Consistent O.language b t := by
        funext i
        exact propext (consistent_eq_of_sample_eq O.language (hsamp t (by omega)))
      have hcon_succ : Consistent O.language a (t + 1) =
          Consistent O.language b (t + 1) := by
        funext i
        exact propext (consistent_eq_of_sample_eq O.language (hsamp (t + 1) (by omega)))
      have hcrit_t : RecursiveCritical O.language a t =
          RecursiveCritical O.language b t := by
        funext i
        exact propext (recursiveCritical_eq_of_sample_eq O.language (hsamp t (by omega)) i)
      have hcrit_succ : RecursiveCritical O.language a (t + 1) =
          RecursiveCritical O.language b (t + 1) := by
        funext i
        exact propext (recursiveCritical_eq_of_sample_eq O.language (hsamp (t + 1) (by omega)) i)
      have hdec : PatientMachine.decide O.language a t (PatientMachine.run O b t) =
          PatientMachine.decide O.language b t (PatientMachine.run O b t) := by
        unfold PatientMachine.decide PatientMachine.stableDecision
          PatientMachine.backtrackDecision
          PatientMachine.highestCritical PatientMachine.highestSurvivor
          PatientMachine.lowestConsistentInScope PatientMachine.lowestConsistent
          PatientMachine.consistentIndices PatientMachine.criticalIndices
          PatientMachine.survivingCriticalIndices
        rw [hcon_succ, hcrit_t, hcrit_succ]
      rw [hdec]
      have havail : ∀ x,
          PatientMachine.Available O.language a (t + 1)
              (PatientMachine.run O b t).used
              (PatientMachine.decide O.language b t (PatientMachine.run O b t)).focus x ↔
          PatientMachine.Available O.language b (t + 1)
              (PatientMachine.run O b t).used
              (PatientMachine.decide O.language b t (PatientMachine.run O b t)).focus x := by
        intro x
        simp only [PatientMachine.Available]
        rw [hsamp (t + 1) (by omega)]
      have hleast :
          PatientMachine.leastAvailable O.language O.infinite' a (t + 1)
              (PatientMachine.run O b t).used
              (PatientMachine.decide O.language b t (PatientMachine.run O b t)).focus =
          PatientMachine.leastAvailable O.language O.infinite' b (t + 1)
              (PatientMachine.run O b t).used
              (PatientMachine.decide O.language b t (PatientMachine.run O b t)).focus := by
        unfold PatientMachine.leastAvailable PatientMachine.available_exists
        congr 1
        funext x
        exact propext (havail x)
      rw [hleast]

noncomputable def prefixStream (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

noncomputable def patientOnline (O : OracleFamily) : OnlineGenerator :=
  fun t xs _ => PatientMachine.output O (prefixStream t xs) t

lemma patientOnline_follows (O : OracleFamily) (input : Stream) :
    Follows (patientOnline O) input (PatientMachine.output O input) := by
  intro t
  unfold patientOnline PatientMachine.output
  exact congrArg (fun s => s.lastOutput.getD 0) (patient_run_congr O (t + 1) (by
    intro s hs
    change input s = (if h : s < t + 1 then input (↑(⟨s, h⟩ : Fin (t + 1))) else 0)
    simp [hs]))

theorem positive : PositivePresentationHalfDensity := by
  intro family hinf
  let O := oracleOfFamily family hinf
  refine ⟨patientOnline O, ?_⟩
  intro i input hP
  refine ⟨PatientMachine.output O input, patientOnline_follows O input, ?_⟩
  have hP' : Presents input (O.language i) := by exact hP
  have hmain := PatientMachine.patientScope_generation_and_lowerDensity O input hP'
  constructor
  · obtain ⟨T, hT⟩ := hmain.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hinput, hout⟩ := hT t ht
    refine ⟨hmem, ?_, hout⟩
    intro hx
    rw [mem_sample_iff] at hx
    obtain ⟨s, hs, heq⟩ := hx
    exact hinput s (by omega) heq
  · exact hmain.2

end Case025
