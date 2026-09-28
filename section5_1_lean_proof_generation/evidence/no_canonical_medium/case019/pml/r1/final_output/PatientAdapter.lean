import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main

open Set Filter
open GenLimit.Generic
open Stage3Case019

namespace Stage3Case019

open GenLimit
open GenLimit.PatientMachine

private theorem patientSample_eq_of_eq_on_prefix
    (s₁ s₂ : Stream ℕ) (u : ℕ)
    (h : ∀ n, n < u → s₁ n = s₂ n) :
    GenLimit.sample s₁ u = GenLimit.sample s₂ u := by
  classical
  unfold GenLimit.sample
  apply Finset.image_congr
  intro n hn
  exact h n (Finset.mem_range.mp hn)

private theorem recursiveCritical_congr_stream
    (C : LanguageFamily ℕ) (s₁ s₂ : Stream ℕ) (u : ℕ)
    (hs : GenLimit.sample s₁ u = GenLimit.sample s₂ u) :
    ∀ i, RecursiveCritical C s₁ u i ↔ RecursiveCritical C s₂ u i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp only [RecursiveCritical, Consistent]; rw [hs]
      | succ i =>
          simp only [RecursiveCritical]
          constructor
          · rintro ⟨hc, hsub⟩
            refine ⟨?_, ?_⟩
            · simpa only [Consistent, hs] using hc
            · intro j hj hjc
              exact hsub j hj ((ih j (by omega)).2 hjc)
          · rintro ⟨hc, hsub⟩
            refine ⟨?_, ?_⟩
            · simpa only [Consistent, hs] using hc
            · intro j hj hjc
              exact hsub j hj ((ih j (by omega)).1 hjc)

private theorem processRound_congr_stream
    (O : OracleFamily) (s₁ s₂ : Stream ℕ) (t : ℕ)
    (old : PatientMachine.State)
    (hprefix : ∀ n, n < t + 1 → s₁ n = s₂ n) :
    processRound O s₁ t old = processRound O s₂ t old := by
  classical
  have hs0 : GenLimit.sample s₁ t = GenLimit.sample s₂ t :=
    patientSample_eq_of_eq_on_prefix s₁ s₂ t (fun n hn => hprefix n (by omega))
  have hs1 : GenLimit.sample s₁ (t + 1) = GenLimit.sample s₂ (t + 1) :=
    patientSample_eq_of_eq_on_prefix s₁ s₂ (t + 1) hprefix
  have hc1 (i : ℕ) : Consistent O.language s₁ (t + 1) i ↔
      Consistent O.language s₂ (t + 1) i := by
    simp only [Consistent]
    rw [hs1]
  have hr0 (i : ℕ) : RecursiveCritical O.language s₁ t i ↔
      RecursiveCritical O.language s₂ t i :=
    recursiveCritical_congr_stream O.language s₁ s₂ t hs0 i
  have hr1 (i : ℕ) : RecursiveCritical O.language s₁ (t + 1) i ↔
      RecursiveCritical O.language s₂ (t + 1) i :=
    recursiveCritical_congr_stream O.language s₁ s₂ (t + 1) hs1 i
  have hconsistent (scope : ℕ) :
      consistentIndices O.language s₁ (t + 1) scope =
        consistentIndices O.language s₂ (t + 1) scope := by
    ext i
    simp only [mem_consistentIndices, hc1]
  have hcritical (scope : ℕ) :
      criticalIndices O.language s₁ (t + 1) scope =
        criticalIndices O.language s₂ (t + 1) scope := by
    ext i
    simp only [mem_criticalIndices, hr1]
  have hsurviving (scope : ℕ) :
      survivingCriticalIndices O.language s₁ t scope =
        survivingCriticalIndices O.language s₂ t scope := by
    ext i
    simp only [mem_survivingCriticalIndices, hr0, hr1]
  have hhighest (scope fallback : ℕ) :
      highestCritical O.language s₁ (t + 1) scope fallback =
        highestCritical O.language s₂ (t + 1) scope fallback := by
    unfold highestCritical
    rw [hcritical]
  have hsurvivor (scope fallback : ℕ) :
      highestSurvivor O.language s₁ t scope fallback =
        highestSurvivor O.language s₂ t scope fallback := by
    unfold highestSurvivor
    rw [hsurviving]
  have hlowestScope (scope fallback : ℕ) :
      lowestConsistentInScope O.language s₁ (t + 1) scope fallback =
        lowestConsistentInScope O.language s₂ (t + 1) scope fallback := by
    unfold lowestConsistentInScope
    rw [hconsistent]
  have hlowest (fallback : ℕ) :
      lowestConsistent O.language s₁ (t + 1) fallback =
        lowestConsistent O.language s₂ (t + 1) fallback := by
    unfold lowestConsistent
    by_cases h₁ : ∃ i, Consistent O.language s₁ (t + 1) i
    · have h₂ : ∃ i, Consistent O.language s₂ (t + 1) i := by
        obtain ⟨i, hi⟩ := h₁
        exact ⟨i, (hc1 i).1 hi⟩
      rw [dif_pos h₁, dif_pos h₂]
      exact Nat.find_congr' (fun {n} => hc1 n)
    · have h₂ : ¬∃ i, Consistent O.language s₂ (t + 1) i := by
        intro h
        obtain ⟨i, hi⟩ := h
        exact h₁ ⟨i, (hc1 i).2 hi⟩
      rw [dif_neg h₁, dif_neg h₂]
  have hdecision :
      PatientMachine.decide O.language s₁ t old =
        PatientMachine.decide O.language s₂ t old := by
    unfold PatientMachine.decide
    by_cases hf₁ : Consistent O.language s₁ (t + 1) old.focus
    · have hf₂ := (hc1 old.focus).1 hf₁
      rw [if_pos hf₁, if_pos hf₂]
      unfold stableDecision
      by_cases hw : 2 ^ old.tau ≤ old.age
      · simp only [dif_pos hw]
        rw [hhighest]
      · simp only [dif_neg hw]
    · have hf₂ : ¬Consistent O.language s₂ (t + 1) old.focus :=
        fun h => hf₁ ((hc1 old.focus).2 h)
      rw [if_neg hf₁, if_neg hf₂]
      unfold backtrackDecision
      rw [hconsistent]
      by_cases hcon : (consistentIndices O.language s₂ (t + 1) old.scope).Nonempty
      · simp only [dif_pos hcon]
        rw [hsurviving]
        by_cases hsurv : (survivingCriticalIndices O.language s₂ t old.scope).Nonempty
        · simp only [if_pos hsurv]
          rw [hsurvivor]
        · simp only [if_neg hsurv]
          rw [hlowestScope]
      · simp only [dif_neg hcon]
        rw [hlowest]
        by_cases hall₁ : ∃ j, Consistent O.language s₁ (t + 1) j
        · have hall₂ : ∃ j, Consistent O.language s₂ (t + 1) j := by
            obtain ⟨j, hj⟩ := hall₁
            exact ⟨j, (hc1 j).1 hj⟩
          simp only [dif_pos hall₁, dif_pos hall₂]
        · have hall₂ : ¬∃ j, Consistent O.language s₂ (t + 1) j := by
            intro h
            obtain ⟨j, hj⟩ := h
            exact hall₁ ⟨j, (hc1 j).2 hj⟩
          simp only [dif_neg hall₁, dif_neg hall₂]
  have hleast (used : Finset ℕ) (focus : ℕ) :
      leastAvailable O.language O.infinite' s₁ (t + 1) used focus =
        leastAvailable O.language O.infinite' s₂ (t + 1) used focus := by
    unfold leastAvailable
    apply Nat.find_congr'
    intro x
    unfold Available
    rw [hs1]
  rw [processRound, processRound]
  rw [hdecision]
  simp only [hleast]

private def extendHistory {n : ℕ} (xs : Fin n → ℕ) : Stream ℕ :=
  fun k => if h : k < n then xs ⟨k, h⟩ else 0

noncomputable def patientGenerator (O : OracleFamily) : Generator ℕ :=
  fun n xs =>
    match n with
    | 0 => 0
    | t + 1 => PatientMachine.output O (extendHistory xs) t

private theorem run_congr_stream
    (O : OracleFamily) (s₁ s₂ : Stream ℕ) :
    ∀ t, (∀ n, n < t → s₁ n = s₂ n) →
      PatientMachine.run O s₁ t = PatientMachine.run O s₂ t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro hprefix
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      rw [ih (fun n hn => hprefix n (by omega))]
      exact processRound_congr_stream O s₁ s₂ t _ hprefix

private theorem output_congr_stream
    (O : OracleFamily) (s₁ s₂ : Stream ℕ) (t : ℕ)
    (hprefix : ∀ n, n < t + 1 → s₁ n = s₂ n) :
    PatientMachine.output O s₁ t = PatientMachine.output O s₂ t := by
  unfold PatientMachine.output
  rw [run_congr_stream O s₁ s₂ (t + 1) hprefix]

 theorem outputAfterInput_patientGenerator
    (O : OracleFamily) (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (patientGenerator O) input t =
      PatientMachine.output O input t := by
  unfold outputAfterInput GenLimit.Generic.output patientGenerator
  simp only
  apply output_congr_stream
  intro n hn
  simp [extendHistory, hn]

end Stage3Case019
