import GenLimit.Paper39_DenseGeneration.Patient.Main

namespace Case019

open GenLimit
open GenLimit.PatientMachine

private theorem sample_eq_of_prefixEq {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) : sample a n = sample b n := by
  ext x
  simp only [mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

private theorem consistent_iff_of_prefixEq (C : LanguageFamily)
    {a b : ℕ → ℕ} {n i : ℕ} (h : ∀ k, k < n → a k = b k) :
    Consistent C a n i ↔ Consistent C b n i := by
  unfold Consistent
  rw [sample_eq_of_prefixEq h]

private theorem recursiveCritical_iff_of_prefixEq (C : LanguageFamily)
    {a b : ℕ → ℕ} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    ∀ i, RecursiveCritical C a n i ↔ RecursiveCritical C b n i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [RecursiveCritical] using consistent_iff_of_prefixEq C h (i := 0)
      | succ i =>
          simp only [RecursiveCritical]
          constructor
          · rintro ⟨hc, hsub⟩
            refine ⟨(consistent_iff_of_prefixEq C h).mp hc, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hc, hsub⟩
            refine ⟨(consistent_iff_of_prefixEq C h).mpr hc, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

private theorem processRound_congr (O : OracleFamily) {a b : ℕ → ℕ}
    {t : ℕ} {old : State} (h : ∀ k, k < t + 1 → a k = b k) :
    processRound O a t old = processRound O b t old := by
  classical
  have hs : sample a (t + 1) = sample b (t + 1) := sample_eq_of_prefixEq h
  have hc : ∀ i, Consistent O.language a (t + 1) i ↔
      Consistent O.language b (t + 1) i := fun i => consistent_iff_of_prefixEq O.language h
  have hold : ∀ k, k < t → a k = b k := fun k hk => h k (Nat.lt.step hk)
  have hco : ∀ i, Consistent O.language a t i ↔
      Consistent O.language b t i := fun i => consistent_iff_of_prefixEq O.language hold
  have hr : ∀ i, RecursiveCritical O.language a (t + 1) i ↔
      RecursiveCritical O.language b (t + 1) i := fun i => recursiveCritical_iff_of_prefixEq O.language h i
  have hro : ∀ i, RecursiveCritical O.language a t i ↔
      RecursiveCritical O.language b t i := fun i => recursiveCritical_iff_of_prefixEq O.language hold i
  have hci : ∀ scope, consistentIndices O.language a (t + 1) scope =
      consistentIndices O.language b (t + 1) scope := by
    intro scope; ext i; simp [hc]
  have hcri : ∀ scope, criticalIndices O.language a (t + 1) scope =
      criticalIndices O.language b (t + 1) scope := by
    intro scope; ext i; simp [hr]
  have hsci : ∀ scope, survivingCriticalIndices O.language a t scope =
      survivingCriticalIndices O.language b t scope := by
    intro scope; ext i; simp [hro, hr]
  have hhighest : ∀ scope fallback,
      highestCritical O.language a (t + 1) scope fallback =
      highestCritical O.language b (t + 1) scope fallback := by
    intro scope fallback
    unfold highestCritical
    rw [hcri]
  have hsurvivor : ∀ scope fallback,
      highestSurvivor O.language a t scope fallback =
      highestSurvivor O.language b t scope fallback := by
    intro scope fallback
    unfold highestSurvivor
    rw [hsci]
  have hlowestScope : ∀ scope fallback,
      lowestConsistentInScope O.language a (t + 1) scope fallback =
      lowestConsistentInScope O.language b (t + 1) scope fallback := by
    intro scope fallback
    unfold lowestConsistentInScope
    rw [hci]
  have hlowest : ∀ fallback,
      lowestConsistent O.language a (t + 1) fallback =
      lowestConsistent O.language b (t + 1) fallback := by
    intro fallback
    by_cases ha : ∃ i, Consistent O.language a (t + 1) i
    · have hb : ∃ i, Consistent O.language b (t + 1) i := by
        obtain ⟨i, hi⟩ := ha
        exact ⟨i, (hc i).mp hi⟩
      unfold lowestConsistent
      rw [dif_pos ha, dif_pos hb]
      exact Nat.find_congr (Nat.find_spec ha) (fun n _ => hc n)
    · have hb : ¬∃ i, Consistent O.language b (t + 1) i := by
        intro hb
        obtain ⟨i, hi⟩ := hb
        exact ha ⟨i, (hc i).mpr hi⟩
      simp [lowestConsistent, ha, hb]
  have hdecision : PatientMachine.decide O.language a t old =
      PatientMachine.decide O.language b t old := by
    unfold PatientMachine.decide stableDecision backtrackDecision
    simp only [hc, hci, hsci, hhighest, hsurvivor, hlowestScope, hlowest]
  let d := PatientMachine.decide O.language b t old
  have hleast :
      leastAvailable O.language O.infinite' a (t + 1) old.used d.focus =
      leastAvailable O.language O.infinite' b (t + 1) old.used d.focus := by
    unfold leastAvailable
    apply Nat.find_congr (Nat.find_spec (available_exists O.language O.infinite' a (t + 1) old.used d.focus))
    intro x _
    simp only [Available, hs]
  simp only [processRound, hdecision]
  have hleast' :
      leastAvailable O.language O.infinite' a (t + 1) old.used
          (PatientMachine.decide O.language b t old).focus =
      leastAvailable O.language O.infinite' b (t + 1) old.used
          (PatientMachine.decide O.language b t old).focus := by
    simpa [d] using hleast
  rw [hleast']

private theorem run_congr (O : OracleFamily) {a b : ℕ → ℕ} :
    ∀ n, (∀ k, k < n → a k = b k) → run O a n = run O b n := by
  intro n
  induction n with
  | zero => intro; rfl
  | succ n ih =>
      intro h
      rw [run_succ, run_succ, ih (fun k hk => h k (Nat.lt.step hk))]
      exact processRound_congr O h

theorem patient_output_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    output O a t = output O b t := by
  unfold output
  rw [run_congr O (t + 1) h]

noncomputable def patientPrefixGenerator (O : OracleFamily) :
    GenLimit.Generic.Generator ℕ := fun n xs =>
  match n with
  | 0 => 0
  | t + 1 => output O (fun k => if hk : k < t + 1 then xs ⟨k, hk⟩ else 0) t

theorem patientPrefixGenerator_output (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    GenLimit.Generic.output (patientPrefixGenerator O) stream (t + 1) =
      output O stream t := by
  apply patient_output_congr O
  intro k hk
  simp [GenLimit.Generic.output, patientPrefixGenerator, hk]

end Case019
