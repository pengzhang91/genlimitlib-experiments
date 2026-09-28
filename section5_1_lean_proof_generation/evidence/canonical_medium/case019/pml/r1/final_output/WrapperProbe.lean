import GenLimit.Paper39_DenseGeneration.Patient.Main

namespace GenLimit.PatientMachine

open GenLimit

private theorem sample_eq_of_prefix_eq
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ i, i < t → a i = b i) :
    sample a t = sample b t := by
  ext x
  simp only [mem_sample_iff]
  constructor <;> rintro ⟨i, hi, rfl⟩
  · exact ⟨i, hi, (h i hi).symm⟩
  · exact ⟨i, hi, h i hi⟩

private theorem consistent_eq_of_prefix_eq
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ i, i < t → a i = b i) :
    Consistent C a t = Consistent C b t := by
  unfold Consistent
  rw [sample_eq_of_prefix_eq h]

private theorem recursiveCritical_eq_of_prefix_eq
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ i, i < t → a i = b i) (n : ℕ) :
    RecursiveCritical C a t n = RecursiveCritical C b t n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp only [RecursiveCritical, consistent_eq_of_prefix_eq C h]
      | succ n =>
          simp only [RecursiveCritical, consistent_eq_of_prefix_eq C h]
          congr 1
          apply propext
          constructor
          · intro ha j hj hb
            exact ha j hj ((ih j (by omega)).mpr hb)
          · intro hb j hj ha
            exact hb j hj ((ih j (by omega)).mp ha)

private theorem processRound_eq_of_prefix_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ) (old : State)
    (h : ∀ i, i < t + 1 → a i = b i) :
    processRound O a t old = processRound O b t old := by
  have hs (s : ℕ) (hs : s ≤ t + 1) : sample a s = sample b s :=
    sample_eq_of_prefix_eq (fun i hi => h i (lt_of_lt_of_le hi hs))
  have hc (s : ℕ) (hs : s ≤ t + 1) :
      Consistent O.language a s = Consistent O.language b s := by
    funext n
    exact congrFun (consistent_eq_of_prefix_eq O.language
      (fun i hi => h i (lt_of_lt_of_le hi hs))) n
  have hr (s : ℕ) (hs : s ≤ t + 1) :
      RecursiveCritical O.language a s =
        RecursiveCritical O.language b s := by
    funext n
    exact recursiveCritical_eq_of_prefix_eq O.language
      (fun i hi => h i (lt_of_lt_of_le hi hs)) n
  unfold processRound decide stableDecision backtrackDecision leastAvailable
    available_exists Available highestCritical highestSurvivor
    lowestConsistentInScope lowestConsistent consistentIndices
    criticalIndices survivingCriticalIndices
  rw [hs (t + 1) le_rfl, hc (t + 1) le_rfl,
    hr (t + 1) le_rfl, hr t (Nat.le_succ t)]

private theorem run_eq_of_prefix_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ i, i < t → a i = b i) :
    run O a t = run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ, ih (fun i hi => h i (Nat.lt.step hi))]
      exact processRound_eq_of_prefix_eq O t _ h

end GenLimit.PatientMachine

namespace Case019Probe

open GenLimit
open GenLimit.Generic
open GenLimit.PatientMachine

noncomputable def patientGenerator (O : OracleFamily) : Generator ℕ :=
  fun n xs =>
    if h : n = 0 then 0
    else
      PatientMachine.output O
        (historyThenFallback (List.ofFn xs) 0)
        (n - 1)

private theorem historyThenFallback_ofFn_eq
    (stream : Stream ℕ) (n i : ℕ) (hi : i < n) :
    historyThenFallback (List.ofFn (fun j : Fin n => stream j)) 0 i = stream i := by
  simp [historyThenFallback, hi]

theorem patientGenerator_output_succ
    (O : OracleFamily) (stream : Stream ℕ) (t : ℕ) :
    output (patientGenerator O) stream (t + 1) =
      PatientMachine.output O stream t := by
  unfold GenLimit.Generic.output patientGenerator
  simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
  unfold PatientMachine.output
  rw [run_eq_of_prefix_eq O (t + 1) (fun i hi =>
    historyThenFallback_ofFn_eq stream (t + 1) i hi)]

end Case019Probe
