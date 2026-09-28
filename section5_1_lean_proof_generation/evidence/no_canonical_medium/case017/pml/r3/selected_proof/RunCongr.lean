import GenLimit.Paper39_DenseGeneration.Partial.Main

open GenLimit

namespace Test

theorem sample_congr {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) : sample a t = sample b t := by
  ext x
  simp only [mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

theorem consistent_congr {C : LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    Consistent C a t i ↔ Consistent C b t i := by
  unfold Consistent
  rw [sample_congr h]

theorem recursiveCritical_congr {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) : ∀ i,
    RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa only [RecursiveCritical] using (consistent_congr (C := C) (i := 0) h)
    | succ i =>
      simp only [RecursiveCritical]
      constructor
      · rintro ⟨hc, hs⟩
        refine ⟨(consistent_congr h).1 hc, ?_⟩
        intro j hj hjc
        exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjc)
      · rintro ⟨hc, hs⟩
        refine ⟨(consistent_congr h).2 hc, ?_⟩
        intro j hj hjc
        exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjc)

theorem consistentIndices_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t → a n = b n) :
    PatientMachine.consistentIndices C a t scope =
      PatientMachine.consistentIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_consistentIndices]
  exact and_congr_right (fun _ => consistent_congr h)

theorem criticalIndices_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t → a n = b n) :
    PatientMachine.criticalIndices C a t scope =
      PatientMachine.criticalIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_criticalIndices]
  exact and_congr_right (fun _ => recursiveCritical_congr h i)

theorem survivingIndices_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.survivingCriticalIndices C a t scope =
      PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t))) i]
  rw [recursiveCritical_congr h i]

theorem highestCritical_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ n, n < t → a n = b n) :
    PatientMachine.highestCritical C a t scope fallback =
      PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold PatientMachine.highestCritical
  rw [criticalIndices_congr h]

theorem highestSurvivor_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.highestSurvivor C a t scope fallback =
      PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold PatientMachine.highestSurvivor
  rw [survivingIndices_congr h]

theorem lowestInScope_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ n, n < t → a n = b n) :
    PatientMachine.lowestConsistentInScope C a t scope fallback =
      PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr h]

theorem lowestConsistent_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t fallback : ℕ} (h : ∀ n, n < t → a n = b n) :
    PatientMachine.lowestConsistent C a t fallback =
      PatientMachine.lowestConsistent C b t fallback := by
  classical
  have hc : (∃ i, Consistent C a t i) ↔ ∃ i, Consistent C b t i :=
    exists_congr (fun i => consistent_congr h)
  by_cases ha : ∃ i, Consistent C a t i
  · have hb := hc.mp ha
    simp only [PatientMachine.lowestConsistent, dif_pos ha, dif_pos hb]
    exact Nat.find_congr (Nat.find_spec ha) (fun n _ => consistent_congr h)
  · have hb : ¬ ∃ i, Consistent C b t i := fun hb => ha (hc.mpr hb)
    simp [PatientMachine.lowestConsistent, ha, hb]

theorem leastAvailable_congr (C : LanguageFamily) (hinf : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ n, n < t → a n = b n)
    (used : Finset ℕ) (focus : ℕ) :
    PatientMachine.leastAvailable C hinf a t used focus =
      PatientMachine.leastAvailable C hinf b t used focus := by
  classical
  unfold PatientMachine.leastAvailable PatientMachine.available_exists
  unfold PatientMachine.Available
  rw [sample_congr h]

theorem stableDecision_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t : ℕ} (h : ∀ n, n < t + 1 → a n = b n)
    (old : PatientMachine.State) :
    PatientMachine.stableDecision C a t old =
      PatientMachine.stableDecision C b t old := by
  classical
  simp only [PatientMachine.stableDecision]
  split
  · simp only [highestCritical_congr h]
  · rfl

theorem backtrackDecision_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t : ℕ} (h : ∀ n, n < t + 1 → a n = b n)
    (old : PatientMachine.State) :
    PatientMachine.backtrackDecision C a t old =
      PatientMachine.backtrackDecision C b t old := by
  classical
  have hc : (∃ j, Consistent C a (t + 1) j) ↔
      ∃ j, Consistent C b (t + 1) j :=
    exists_congr (fun i => consistent_congr h)
  simp only [PatientMachine.backtrackDecision, consistentIndices_congr h,
    survivingIndices_congr h, highestSurvivor_congr h,
    lowestInScope_congr h, lowestConsistent_congr h, hc]

theorem decide_congr {C : LanguageFamily} {a b : ℕ → ℕ}
    {t : ℕ} (h : ∀ n, n < t + 1 → a n = b n)
    (old : PatientMachine.State) :
    PatientMachine.decide C a t old = PatientMachine.decide C b t old := by
  classical
  unfold PatientMachine.decide
  rw [show Consistent C a (t + 1) old.focus = Consistent C b (t + 1) old.focus from
    propext (consistent_congr h)]
  split
  · exact stableDecision_congr h old
  · exact backtrackDecision_congr h old

theorem processRound_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n)
    (old : PatientMachine.State) :
    PatientMachine.processRound O a t old =
      PatientMachine.processRound O b t old := by
  classical
  simp only [PatientMachine.processRound, decide_congr h old,
    leastAvailable_congr O.language O.infinite' h]

theorem run_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.run O a t = PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      rw [ih (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t)))]
      exact processRound_congr O h _

theorem output_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  unfold PatientMachine.output
  rw [run_congr O h]

end Test
