import GenLimit.Paper39_DenseGeneration.Patient.Main

namespace Stage3Case019Proof

open GenLimit
open GenLimit.PatientMachine

private def prefixStream (n : ℕ) (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if h : k < n then xs ⟨k, h⟩ else 0

private theorem coreSample_eq_of_eq_on_prefix
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem consistent_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) (i : ℕ) :
    Consistent C stream₁ t i ↔ Consistent C stream₂ t i := by
  unfold Consistent
  rw [coreSample_eq_of_eq_on_prefix h]

private theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) :
    ∀ i, RecursiveCritical C stream₁ t i ↔
      RecursiveCritical C stream₂ t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa [RecursiveCritical] using consistent_congr C h 0
    | succ i =>
      simp only [RecursiveCritical]
      constructor
      · rintro ⟨hcon, hcrit⟩
        refine ⟨(consistent_congr C h (i + 1)).mp hcon, ?_⟩
        intro j hj hjcrit
        exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
      · rintro ⟨hcon, hcrit⟩
        refine ⟨(consistent_congr C h (i + 1)).mpr hcon, ?_⟩
        intro j hj hjcrit
        exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

private theorem consistentIndices_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) (scope : ℕ) :
    consistentIndices C stream₁ t scope =
      consistentIndices C stream₂ t scope := by
  ext i
  simp only [mem_consistentIndices]
  rw [consistent_congr C h i]

private theorem criticalIndices_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) (scope : ℕ) :
    criticalIndices C stream₁ t scope =
      criticalIndices C stream₂ t scope := by
  ext i
  simp only [mem_criticalIndices]
  rw [recursiveCritical_congr C h i]

private theorem survivingCriticalIndices_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t + 1 → stream₁ k = stream₂ k) (scope : ℕ) :
    survivingCriticalIndices C stream₁ t scope =
      survivingCriticalIndices C stream₂ t scope := by
  ext i
  simp only [mem_survivingCriticalIndices]
  have ht : ∀ k, k < t → stream₁ k = stream₂ k :=
    fun k hk => h k (lt_trans hk (Nat.lt_succ_self t))
  rw [recursiveCritical_congr C ht i, recursiveCritical_congr C h i]

private theorem highestCritical_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k)
    (scope fallback : ℕ) :
    highestCritical C stream₁ t scope fallback =
      highestCritical C stream₂ t scope fallback := by
  unfold highestCritical
  rw [criticalIndices_congr C h scope]

private theorem highestSurvivor_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t + 1 → stream₁ k = stream₂ k)
    (scope fallback : ℕ) :
    highestSurvivor C stream₁ t scope fallback =
      highestSurvivor C stream₂ t scope fallback := by
  unfold highestSurvivor
  rw [survivingCriticalIndices_congr C h scope]

private theorem lowestConsistentInScope_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k)
    (scope fallback : ℕ) :
    lowestConsistentInScope C stream₁ t scope fallback =
      lowestConsistentInScope C stream₂ t scope fallback := by
  unfold lowestConsistentInScope
  rw [consistentIndices_congr C h scope]

private theorem lowestConsistent_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) (fallback : ℕ) :
    lowestConsistent C stream₁ t fallback =
      lowestConsistent C stream₂ t fallback := by
  classical
  unfold lowestConsistent
  have hp : (∃ i, Consistent C stream₁ t i) ↔
      ∃ i, Consistent C stream₂ t i := by
    apply exists_congr
    intro i
    exact consistent_congr C h i
  split <;> rename_i hex
  · rw [dif_pos (hp.mp hex)]
    apply Nat.find_congr (Classical.choose_spec hex)
    intro i hi
    exact consistent_congr C h i
  · rw [dif_neg (fun hex' => hex (hp.mpr hex'))]

private theorem backtrackDecision_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k < t + 1 → stream₁ k = stream₂ k) (old : State) :
    backtrackDecision C stream₁ t old =
      backtrackDecision C stream₂ t old := by
  classical
  have hci := consistentIndices_congr C h old.scope
  have hsi := survivingCriticalIndices_congr C h old.scope
  have hhs := highestSurvivor_congr C h old.scope old.focus
  have hlis := lowestConsistentInScope_congr C h old.scope old.focus
  have hlc := lowestConsistent_congr C h old.focus
  have hp : (∃ j, Consistent C stream₁ (t + 1) j) ↔
      ∃ j, Consistent C stream₂ (t + 1) j := by
    apply exists_congr
    intro j
    exact consistent_congr C h j
  simp only [backtrackDecision]
  rw [hci, hsi, hhs, hlis, hlc, propext hp]

private theorem stableDecision_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k < t + 1 → stream₁ k = stream₂ k) (old : State) :
    stableDecision C stream₁ t old = stableDecision C stream₂ t old := by
  classical
  simp only [stableDecision]
  split
  · have hhc := highestCritical_congr C h (old.scope + 1) old.focus
    rw [hhc]
  · rfl

private theorem decide_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k < t + 1 → stream₁ k = stream₂ k) (old : State) :
    PatientMachine.decide C stream₁ t old =
      PatientMachine.decide C stream₂ t old := by
  unfold PatientMachine.decide
  have hc := consistent_congr C h old.focus
  split <;> rename_i hcon
  · rw [if_pos (hc.mp hcon)]
    exact stableDecision_congr C t h old
  · rw [if_neg (fun hcon' => hcon (hc.mpr hcon'))]
    exact backtrackDecision_congr C t h old

private theorem leastAvailable_congr
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k)
    (used : Finset ℕ) (focus : ℕ) :
    leastAvailable C hInfinite stream₁ t used focus =
      leastAvailable C hInfinite stream₂ t used focus := by
  classical
  unfold leastAvailable
  let hex := available_exists C hInfinite stream₁ t used focus
  apply Nat.find_congr (Classical.choose_spec hex)
  intro x hx
  unfold Available
  rw [coreSample_eq_of_eq_on_prefix h]

private theorem processRound_congr
    (O : OracleFamily) {stream₁ stream₂ : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k < t + 1 → stream₁ k = stream₂ k) (old : State) :
    processRound O stream₁ t old = processRound O stream₂ t old := by
  classical
  have hd := decide_congr O.language t h old
  have hl := leastAvailable_congr O.language O.infinite' h old.used
    (PatientMachine.decide O.language stream₂ t old).focus
  simp only [processRound]
  rw [hd, hl]

private theorem run_congr
    (O : OracleFamily) {stream₁ stream₂ : ℕ → ℕ} :
    ∀ t, (∀ k, k < t → stream₁ k = stream₂ k) →
      run O stream₁ t = run O stream₂ t := by
  intro t h
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ]
      have ht : ∀ k, k < t → stream₁ k = stream₂ k :=
        fun k hk => h k (lt_trans hk (Nat.lt_succ_self t))
      rw [ih ht]
      exact processRound_congr O t h (run O stream₂ t)

theorem patient_output_congr
    (O : OracleFamily) {stream₁ stream₂ : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k < t + 1 → stream₁ k = stream₂ k) :
    PatientMachine.output O stream₁ t = PatientMachine.output O stream₂ t := by
  unfold PatientMachine.output
  rw [run_congr O (t + 1) h]

noncomputable def patientGenerator (O : OracleFamily) :
    GenLimit.Generic.Generator ℕ :=
  fun n xs =>
    match n with
    | 0 => 0
    | t + 1 => PatientMachine.output O (prefixStream (t + 1) xs) t

theorem output_patientGenerator
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    GenLimit.Generic.output (patientGenerator O) stream (t + 1) =
      PatientMachine.output O stream t := by
  change PatientMachine.output O
      (prefixStream (t + 1) (fun i : Fin (t + 1) => stream i)) t = _
  apply patient_output_congr O t
  intro k hk
  simp [prefixStream, hk]

end Stage3Case019Proof
