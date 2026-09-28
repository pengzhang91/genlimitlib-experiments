import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main

open Set Filter

namespace Stage3Case019Proof

private theorem patient_sample_eq
    {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem patient_consistent_iff
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  unfold GenLimit.Consistent
  rw [patient_sample_eq h]

private theorem patient_recursiveCritical_iff
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using patient_consistent_iff C h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [patient_consistent_iff C h]
          constructor
          · rintro ⟨hcon, hsub⟩
            exact ⟨hcon, fun j hj hjcrit =>
              hsub j hj ((ih j (by omega)).mpr hjcrit)⟩
          · rintro ⟨hcon, hsub⟩
            exact ⟨hcon, fun j hj hjcrit =>
              hsub j hj ((ih j (by omega)).mp hjcrit)⟩

private theorem patient_consistentIndices_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) (scope : ℕ) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [patient_consistent_iff C h]

private theorem patient_criticalIndices_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) (scope : ℕ) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [patient_recursiveCritical_iff C h i]


private theorem patient_highestCritical_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) (scope fallback : ℕ) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [patient_criticalIndices_eq C h]

private theorem patient_survivingIndices_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k < t + 1 → a k = b k) (scope : ℕ) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  have hp : ∀ k, k < t → a k = b k := fun k hk => h k (by omega)
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [patient_recursiveCritical_iff C hp i,
    patient_recursiveCritical_iff C h i]

private theorem patient_stableDecision_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  split
  · dsimp only
    rw [patient_highestCritical_eq C h]
  · rfl

private theorem patient_highestSurvivor_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k < t + 1 → a k = b k) (scope fallback : ℕ) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [patient_survivingIndices_eq C t h]

private theorem patient_lowestConsistentInScope_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) (scope fallback : ℕ) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [patient_consistentIndices_eq C h]

private theorem patient_lowestConsistent_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i :=
      (exists_congr (fun i => patient_consistent_iff C h)).mp ha
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr' (fun {i} => patient_consistent_iff C h)
  · have hb : ¬ ∃ i, GenLimit.Consistent C b t i := by
      intro hb
      exact ha ((exists_congr (fun i => patient_consistent_iff C h)).mpr hb)
    rw [dif_neg ha, dif_neg hb]

private theorem patient_backtrackDecision_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  have hcon := patient_consistentIndices_eq C h old.scope
  have hsurv := patient_survivingIndices_eq C t h old.scope
  have hhigh := patient_highestSurvivor_eq C t h old.scope old.focus
  have hscope := patient_lowestConsistentInScope_eq C h old.scope old.focus
  have hlow := patient_lowestConsistent_eq C h (fallback := old.focus)
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [hcon, hsurv, hhigh, hscope, hlow]
  rw [exists_congr (fun j => patient_consistent_iff C h)]

private theorem patient_decide_eq
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [patient_consistent_iff C h]
  split <;>
    simp only [patient_stableDecision_eq C t old h,
      patient_backtrackDecision_eq C t old h]

private theorem patient_leastAvailable_eq
    (C : GenLimit.LanguageFamily) (hinfinite : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} (t : ℕ) (used : Finset ℕ) (focus : ℕ)
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.leastAvailable C hinfinite a t used focus =
      GenLimit.PatientMachine.leastAvailable C hinfinite b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  unfold GenLimit.PatientMachine.Available
  rw [patient_sample_eq h]

private theorem patient_processRound_eq
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hd := patient_decide_eq O.language t old h
  unfold GenLimit.PatientMachine.processRound
  simp only [hd]
  let d := GenLimit.PatientMachine.decide O.language b t old
  have hx := patient_leastAvailable_eq O.language O.infinite'
    (t + 1) old.used d.focus h
  rw [hx]

private theorem patient_run_eq
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.PatientMachine.run O a n =
      GenLimit.PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      have hp : ∀ k, k < n → a k = b k := fun k hk => h k (by omega)
      rw [ih hp]
      exact patient_processRound_eq O n _ h

noncomputable def testGenerator (O : GenLimit.OracleFamily) : GenLimit.Generic.Generator ℕ :=
  fun n xs => GenLimit.PatientMachine.output O
    (fun t => if h : t < n then xs ⟨t, h⟩ else 0) (n - 1)

theorem testGenerator_output
    (O : GenLimit.OracleFamily) (input : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (testGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output testGenerator
  change (GenLimit.PatientMachine.run O _ (t + 1)).lastOutput.getD 0 = _
  unfold GenLimit.PatientMachine.output
  apply congrArg (fun s : GenLimit.PatientMachine.State => s.lastOutput.getD 0)
  apply patient_run_eq
  intro k hk
  simp
  omega

end Stage3Case019Proof
