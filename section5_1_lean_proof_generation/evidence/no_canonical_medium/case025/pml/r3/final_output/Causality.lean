import GenLimit.Paper39_DenseGeneration.Patient.Main

open GenLimit

namespace Case025Helpers

private def PrefixEq (a b : ℕ → ℕ) (t : ℕ) : Prop :=
  ∀ n, n < t → a n = b n

private theorem sample_congr {a b : ℕ → ℕ} {t : ℕ}
    (h : PrefixEq a b t) : sample a t = sample b t := by
  unfold sample
  apply Finset.image_congr
  intro n hn
  exact h n (Finset.mem_range.mp hn)

private theorem consistent_fun_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : PrefixEq a b t) : Consistent C a t = Consistent C b t := by
  funext i
  apply propext
  unfold Consistent
  rw [sample_congr h]

private theorem recursiveCritical_fun_congr (C : LanguageFamily)
    {a b : ℕ → ℕ} {t : ℕ} (h : PrefixEq a b t) :
    RecursiveCritical C a t = RecursiveCritical C b t := by
  funext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simp only [RecursiveCritical]
          rw [consistent_fun_congr C h]
      | succ i =>
          simp only [RecursiveCritical]
          rw [consistent_fun_congr C h]
          apply congrArg (fun p => Consistent C b t (i + 1) ∧ p)
          apply propext
          constructor
          · intro hp j hj hcrit
            exact hp j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hcrit)
          · intro hp j hj hcrit
            exact hp j hj ((ih j (Nat.lt_succ_of_le hj)).mp hcrit)

private theorem machineAux_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : PrefixEq a b t) :
    (PatientMachine.consistentIndices C a t = PatientMachine.consistentIndices C b t) ∧
    (PatientMachine.criticalIndices C a t = PatientMachine.criticalIndices C b t) := by
  constructor
  · unfold PatientMachine.consistentIndices
    rw [consistent_fun_congr C h]
  · unfold PatientMachine.criticalIndices
    rw [recursiveCritical_fun_congr C h]

private theorem surviving_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : PrefixEq a b (t + 1)) :
    PatientMachine.survivingCriticalIndices C a t =
      PatientMachine.survivingCriticalIndices C b t := by
  unfold PatientMachine.survivingCriticalIndices
  rw [recursiveCritical_fun_congr C (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t)))]
  rw [recursiveCritical_fun_congr C h]

private theorem decision_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : PrefixEq a b (t + 1)) (old : PatientMachine.State) :
    PatientMachine.decide C a t old = PatientMachine.decide C b t old := by
  have ht : PrefixEq a b t := fun n hn => h n (lt_trans hn (Nat.lt_succ_self t))
  have hConT := consistent_fun_congr C ht
  have hConS := consistent_fun_congr C h
  have hCritT := recursiveCritical_fun_congr C ht
  have hCritS := recursiveCritical_fun_congr C h
  unfold PatientMachine.decide PatientMachine.stableDecision
    PatientMachine.backtrackDecision PatientMachine.highestCritical
    PatientMachine.highestSurvivor PatientMachine.lowestConsistentInScope
    PatientMachine.lowestConsistent PatientMachine.consistentIndices
    PatientMachine.criticalIndices PatientMachine.survivingCriticalIndices
  rw [hConS, hCritS, hCritT]

private theorem leastAvailable_congr (C : LanguageFamily) (hInf : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t : ℕ} (h : PrefixEq a b t)
    (used : Finset ℕ) (focus : ℕ) :
    PatientMachine.leastAvailable C hInf a t used focus =
      PatientMachine.leastAvailable C hInf b t used focus := by
  unfold PatientMachine.leastAvailable
  have hs := sample_congr h
  congr 1
  funext x
  apply propext
  unfold PatientMachine.Available
  rw [hs]

private theorem processRound_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : PrefixEq a b (t + 1)) (old : PatientMachine.State) :
    PatientMachine.processRound O a t old = PatientMachine.processRound O b t old := by
  unfold PatientMachine.processRound
  rw [decision_congr O.language h old]
  let d := PatientMachine.decide O.language b t old
  have hx := leastAvailable_congr O.language O.infinite' h old.used d.focus
  change PatientMachine.leastAvailable O.language O.infinite' a (t + 1) old.used d.focus =
    PatientMachine.leastAvailable O.language O.infinite' b (t + 1) old.used d.focus at hx
  simp only [d, hx]

 theorem run_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : PrefixEq a b t) : PatientMachine.run O a t = PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      rw [ih (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t)))]
      exact processRound_congr O h _

 theorem output_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : PrefixEq a b (t + 1)) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  unfold PatientMachine.output
  rw [run_congr O h]

end Case025Helpers
