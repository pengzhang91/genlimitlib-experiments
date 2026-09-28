import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3Case019

def AgreeBelow (a b : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k, k < n → a k = b k

theorem sample_eq_of_agreeBelow {a b : ℕ → ℕ} {n : ℕ}
    (h : AgreeBelow a b n) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

theorem consistent_iff_of_agreeBelow
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {n i : ℕ}
    (h : AgreeBelow a b n) :
    GenLimit.Consistent C a n i ↔ GenLimit.Consistent C b n i := by
  unfold GenLimit.Consistent
  rw [sample_eq_of_agreeBelow h]

theorem recursiveCritical_iff_of_agreeBelow
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {n i : ℕ}
    (h : AgreeBelow a b n) :
    GenLimit.RecursiveCritical C a n i ↔
      GenLimit.RecursiveCritical C b n i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using
            consistent_iff_of_agreeBelow C h (i := 0)
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_iff_of_agreeBelow C h]
          constructor
          · rintro ⟨hc, hs⟩
            refine ⟨hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjc)
          · rintro ⟨hc, hs⟩
            refine ⟨hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjc)


theorem consistent_fun_eq_of_agreeBelow
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {n : ℕ}
    (h : AgreeBelow a b n) :
    GenLimit.Consistent C a n = GenLimit.Consistent C b n := by
  funext i
  exact propext (consistent_iff_of_agreeBelow C h)

theorem recursiveCritical_fun_eq_of_agreeBelow
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {n : ℕ}
    (h : AgreeBelow a b n) :
    GenLimit.RecursiveCritical C a n =
      GenLimit.RecursiveCritical C b n := by
  funext i
  exact propext (recursiveCritical_iff_of_agreeBelow C h)

theorem decide_eq_of_agreeBelow
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : AgreeBelow a b (t + 1)) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  have ht : AgreeBelow a b t := by
    intro k hk
    exact h k (Nat.lt_succ_of_lt hk)
  have hconNow := consistent_fun_eq_of_agreeBelow C h
  have hcritNow := recursiveCritical_fun_eq_of_agreeBelow C h
  have hcritPrev := recursiveCritical_fun_eq_of_agreeBelow C ht
  unfold GenLimit.PatientMachine.decide
  unfold GenLimit.PatientMachine.stableDecision
  unfold GenLimit.PatientMachine.backtrackDecision
  unfold GenLimit.PatientMachine.highestCritical
  unfold GenLimit.PatientMachine.highestSurvivor
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  unfold GenLimit.PatientMachine.lowestConsistent
  unfold GenLimit.PatientMachine.consistentIndices
  unfold GenLimit.PatientMachine.criticalIndices
  unfold GenLimit.PatientMachine.survivingCriticalIndices
  simp only [hconNow, hcritNow, hcritPrev]

theorem leastAvailable_eq_of_agreeBelow
    (C : GenLimit.LanguageFamily) (hinf : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {n : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : AgreeBelow a b n) :
    GenLimit.PatientMachine.leastAvailable C hinf a n used focus =
      GenLimit.PatientMachine.leastAvailable C hinf b n used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr'
  intro x
  unfold GenLimit.PatientMachine.Available
  rw [sample_eq_of_agreeBelow h]

theorem processRound_eq_of_agreeBelow
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : AgreeBelow a b (t + 1)) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  unfold GenLimit.PatientMachine.processRound
  rw [decide_eq_of_agreeBelow O.language old h]
  simp only [leastAvailable_eq_of_agreeBelow O.language O.infinite' old.used
    (GenLimit.PatientMachine.decide O.language b t old).focus h]

theorem patient_run_eq_of_agreeBelow
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {n : ℕ}
    (h : AgreeBelow a b n) :
    GenLimit.PatientMachine.run O a n =
      GenLimit.PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn : AgreeBelow a b n := by
        intro k hk
        exact h k (Nat.lt_succ_of_lt hk)
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, ih hn]
      exact processRound_eq_of_agreeBelow O
        (GenLimit.PatientMachine.run O b n) h

theorem patient_output_eq_of_agreeBelow
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : AgreeBelow a b (t + 1)) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [patient_run_eq_of_agreeBelow O h]

end Stage3Case019
