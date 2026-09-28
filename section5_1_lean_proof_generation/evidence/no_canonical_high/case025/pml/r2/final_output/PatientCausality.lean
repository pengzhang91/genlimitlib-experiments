import GenLimit.Paper39_DenseGeneration.Patient.Main

namespace Stage3Case025

open GenLimit
open GenLimit.PatientMachine

private theorem sample_eq_of_prefix
    {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    sample a t = sample b t := by
  ext x
  simp only [mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

private theorem consistent_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    Consistent C a t i ↔ Consistent C b t i := by
  unfold Consistent
  rw [sample_eq_of_prefix h]

private theorem recursiveCritical_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    ∀ i, RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa [RecursiveCritical] using consistent_congr C h (i := 0)
    | succ i =>
      simp only [RecursiveCritical]
      constructor
      · rintro ⟨hcon, hsub⟩
        refine ⟨(consistent_congr C h).1 hcon, ?_⟩
        intro j hj hjcrit
        exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjcrit)
      · rintro ⟨hcon, hsub⟩
        refine ⟨(consistent_congr C h).2 hcon, ?_⟩
        intro j hj hjcrit
        exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjcrit)

private theorem consistentIndices_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    consistentIndices C a t scope = consistentIndices C b t scope := by
  ext i
  simp only [mem_consistentIndices]
  rw [consistent_congr C h]

private theorem criticalIndices_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    criticalIndices C a t scope = criticalIndices C b t scope := by
  ext i
  simp only [mem_criticalIndices]
  rw [recursiveCritical_congr C h i]

private theorem survivingCriticalIndices_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    survivingCriticalIndices C a t scope =
      survivingCriticalIndices C b t scope := by
  ext i
  simp only [mem_survivingCriticalIndices]
  rw [recursiveCritical_congr C (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t))) i,
    recursiveCritical_congr C h i]

private theorem highestCritical_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    highestCritical C a t scope fallback =
      highestCritical C b t scope fallback := by
  unfold highestCritical
  rw [criticalIndices_congr C h]

private theorem highestSurvivor_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    highestSurvivor C a t scope fallback =
      highestSurvivor C b t scope fallback := by
  unfold highestSurvivor
  rw [survivingCriticalIndices_congr C h]

private theorem lowestConsistentInScope_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    lowestConsistentInScope C a t scope fallback =
      lowestConsistentInScope C b t scope fallback := by
  unfold lowestConsistentInScope
  rw [consistentIndices_congr C h]

private theorem lowestConsistent_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    lowestConsistent C a t fallback = lowestConsistent C b t fallback := by
  classical
  unfold lowestConsistent
  have hall : (∃ i, Consistent C a t i) ↔ ∃ i, Consistent C b t i := by
    constructor <;> rintro ⟨i, hi⟩
    · exact ⟨i, (consistent_congr C h).1 hi⟩
    · exact ⟨i, (consistent_congr C h).2 hi⟩
  by_cases ha : ∃ i, Consistent C a t i
  · have hb := hall.1 ha
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr (Nat.find_spec ha)
      (fun n _ => consistent_congr C h)
  · have hb : ¬ ∃ i, Consistent C b t i := fun hb => ha (hall.2 hb)
    simp [ha, hb]

private theorem backtrackDecision_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} (t : ℕ) (old : State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    backtrackDecision C a t old = backtrackDecision C b t old := by
  unfold backtrackDecision
  rw [consistentIndices_congr C h,
    survivingCriticalIndices_congr C h,
    highestSurvivor_congr C h,
    lowestConsistentInScope_congr C h,
    lowestConsistent_congr C h]
  have hall : (∃ j, Consistent C a (t + 1) j) ↔
      ∃ j, Consistent C b (t + 1) j := by
    constructor <;> rintro ⟨j, hj⟩
    · exact ⟨j, (consistent_congr C h).1 hj⟩
    · exact ⟨j, (consistent_congr C h).2 hj⟩
  rw [propext hall]

private theorem stableDecision_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} (t : ℕ) (old : State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    stableDecision C a t old = stableDecision C b t old := by
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp only [stableDecision, hwait, ↓reduceDIte]
    rw [highestCritical_congr C h]
  · simp [stableDecision, hwait]

private theorem decide_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} (t : ℕ) (old : State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.decide C a t old = PatientMachine.decide C b t old := by
  unfold PatientMachine.decide
  rw [propext (consistent_congr C h),
    stableDecision_congr C t old h,
    backtrackDecision_congr C t old h]

private theorem leastAvailable_congr
    (C : LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    leastAvailable C hInfinite a t used focus =
      leastAvailable C hInfinite b t used focus := by
  classical
  unfold leastAvailable
  have hav : ∀ x, Available C a t used focus x ↔
      Available C b t used focus x := by
    intro x
    unfold Available
    rw [sample_eq_of_prefix h]
  let ha := available_exists C hInfinite a t used focus
  exact Nat.find_congr (Nat.find_spec ha) (fun n _ => hav n)

private theorem processRound_congr
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ) (old : State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    processRound O a t old = processRound O b t old := by
  unfold processRound
  have hd := decide_congr O.language t old h
  simp only
  rw [hd]
  rw [leastAvailable_congr O.language O.infinite' old.used
    (PatientMachine.decide O.language b t old).focus h]

/-- The patient machine state after `t` rounds depends only on the first `t`
input values. -/
theorem patient_run_congr
    (O : OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ n, n < t → a n = b n) → run O a t = run O b t := by
  intro t h
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ]
      rw [ih (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t)))]
      exact processRound_congr O t (run O b t) h

/-- The round-`t` patient output depends only on the presenter moves through
round `t`. -/
theorem patient_output_congr
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    output O a t = output O b t := by
  unfold output
  rw [patient_run_congr O (t + 1) h]

end Stage3Case025
