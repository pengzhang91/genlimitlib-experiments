import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import Mathlib

open Stage3Case019
open GenLimit
open GenLimit.Generic

namespace Case019

lemma recursiveCritical_congr_sample
    (C : GenLimit.LanguageFamily) (a b : ℕ → ℕ) (t i : ℕ)
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.RecursiveCritical C a t i ↔ GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [GenLimit.RecursiveCritical, GenLimit.Consistent, hs]
    | succ i =>
      simp only [GenLimit.RecursiveCritical]
      constructor
      · rintro ⟨hcon, hrec⟩
        refine ⟨?_, ?_⟩
        · simpa [GenLimit.Consistent, hs] using hcon
        · intro j hj hjcrit
          exact hrec j hj ((ih j (by omega)).mpr hjcrit)
      · rintro ⟨hcon, hrec⟩
        refine ⟨?_, ?_⟩
        · simpa [GenLimit.Consistent, hs] using hcon
        · intro j hj hjcrit
          exact hrec j hj ((ih j (by omega)).mp hjcrit)

lemma patient_processRound_congr
    (O : GenLimit.OracleFamily) (a b : ℕ → ℕ) (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (hprefix : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hs_t : GenLimit.sample a t = GenLimit.sample b t := by
    ext x
    simp only [GenLimit.mem_sample_iff]
    constructor <;> rintro ⟨k, hk, rfl⟩
    · exact ⟨k, hk, (hprefix k (by omega)).symm⟩
    · exact ⟨k, hk, hprefix k (by omega)⟩
  have hs_succ : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) := by
    ext x
    simp only [GenLimit.mem_sample_iff]
    constructor <;> rintro ⟨k, hk, rfl⟩
    · exact ⟨k, hk, (hprefix k hk).symm⟩
    · exact ⟨k, hk, hprefix k hk⟩
  have hcon_t : ∀ i, GenLimit.Consistent O.language a t i ↔
      GenLimit.Consistent O.language b t i := by
    intro i
    simp [GenLimit.Consistent, hs_t]
  have hcon_succ : ∀ i, GenLimit.Consistent O.language a (t + 1) i ↔
      GenLimit.Consistent O.language b (t + 1) i := by
    intro i
    simp [GenLimit.Consistent, hs_succ]
  have hcrit_t : ∀ i, GenLimit.RecursiveCritical O.language a t i ↔
      GenLimit.RecursiveCritical O.language b t i := by
    intro i
    exact recursiveCritical_congr_sample O.language a b t i hs_t
  have hcrit_succ : ∀ i, GenLimit.RecursiveCritical O.language a (t + 1) i ↔
      GenLimit.RecursiveCritical O.language b (t + 1) i := by
    intro i
    exact recursiveCritical_congr_sample O.language a b (t + 1) i hs_succ
  have hconsistentIndices : ∀ scope,
      GenLimit.PatientMachine.consistentIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.consistentIndices O.language b (t + 1) scope := by
    intro scope
    ext i
    simp [hcon_succ i]
  have hcriticalIndices : ∀ scope,
      GenLimit.PatientMachine.criticalIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices O.language b (t + 1) scope := by
    intro scope
    ext i
    simp [hcrit_succ i]
  have hsurvivingIndices : ∀ scope,
      GenLimit.PatientMachine.survivingCriticalIndices O.language a t scope =
        GenLimit.PatientMachine.survivingCriticalIndices O.language b t scope := by
    intro scope
    ext i
    simp [hcrit_t i, hcrit_succ i]
  have hhighestCritical : ∀ scope fallback,
      GenLimit.PatientMachine.highestCritical O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical O.language b (t + 1) scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.highestCritical]
    rw [hcriticalIndices scope]
  have hhighestSurvivor : ∀ scope fallback,
      GenLimit.PatientMachine.highestSurvivor O.language a t scope fallback =
        GenLimit.PatientMachine.highestSurvivor O.language b t scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.highestSurvivor]
    rw [hsurvivingIndices scope]
  have hlowestScope : ∀ scope fallback,
      GenLimit.PatientMachine.lowestConsistentInScope O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope O.language b (t + 1) scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.lowestConsistentInScope]
    rw [hconsistentIndices scope]
  have hlowest : ∀ fallback,
      GenLimit.PatientMachine.lowestConsistent O.language a (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent O.language b (t + 1) fallback := by
    intro fallback
    simp only [GenLimit.PatientMachine.lowestConsistent]
    have hex : (∃ i, GenLimit.Consistent O.language a (t + 1) i) ↔
        ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (hcon_succ i).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (hcon_succ i).mpr hi⟩
    split <;> rename_i h
    · rw [dif_pos (hex.mp h)]
      congr 1
      funext i
      exact propext (hcon_succ i)
    · rw [dif_neg (fun hb => h (hex.mpr hb))]
  have hbacktrack :
      GenLimit.PatientMachine.backtrackDecision O.language a t old =
        GenLimit.PatientMachine.backtrackDecision O.language b t old := by
    have hex : (∃ j, GenLimit.Consistent O.language a (t + 1) j) ↔
        ∃ j, GenLimit.Consistent O.language b (t + 1) j := by
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (hcon_succ i).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (hcon_succ i).mpr hi⟩
    simp only [GenLimit.PatientMachine.backtrackDecision]
    rw [hconsistentIndices old.scope, hsurvivingIndices old.scope,
      hhighestSurvivor old.scope old.focus, hlowestScope old.scope old.focus,
      hlowest old.focus, propext hex]
  have hstable :
      GenLimit.PatientMachine.stableDecision O.language a t old =
        GenLimit.PatientMachine.stableDecision O.language b t old := by
    simp only [GenLimit.PatientMachine.stableDecision]
    split
    · rw [hhighestCritical (old.scope + 1) old.focus]
    · rfl
  have hdecide :
      GenLimit.PatientMachine.decide O.language a t old =
        GenLimit.PatientMachine.decide O.language b t old := by
    simp only [GenLimit.PatientMachine.decide]
    by_cases h : GenLimit.Consistent O.language a (t + 1) old.focus
    · rw [if_pos h, if_pos ((hcon_succ old.focus).mp h), hstable]
    · rw [if_neg h, if_neg (fun hb => h ((hcon_succ old.focus).mpr hb)), hbacktrack]
  have hleast : ∀ used focus,
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a (t + 1) used focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b (t + 1) used focus := by
    intro used focus
    simp only [GenLimit.PatientMachine.leastAvailable]
    congr 1
    funext x
    apply propext
    simp [GenLimit.PatientMachine.Available, hs_succ]
  simp only [GenLimit.PatientMachine.processRound]
  rw [hdecide]
  rw [hleast]

lemma patient_run_congr
    (O : GenLimit.OracleFamily) (a b : ℕ → ℕ) (n : ℕ)
    (hprefix : ∀ k, k < n → a k = b k) :
    GenLimit.PatientMachine.run O a n = GenLimit.PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun k hk => hprefix k (by omega))]
      exact patient_processRound_congr O a b n _ hprefix

lemma patient_output_congr
    (O : GenLimit.OracleFamily) (a b : ℕ → ℕ) (t : ℕ)
    (hprefix : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.output O a t = GenLimit.PatientMachine.output O b t := by
  simp only [GenLimit.PatientMachine.output]
  rw [patient_run_congr O a b (t + 1) hprefix]

noncomputable def prefixCompletion {n : ℕ} (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if h : k < n then xs ⟨k, h⟩ else 0

noncomputable def patientPrefixGenerator (O : GenLimit.OracleFamily) : GenLimit.Generic.Generator ℕ
  | 0, _ => 0
  | n + 1, xs => GenLimit.PatientMachine.output O (prefixCompletion xs) n

lemma patientPrefixGenerator_output
    (O : GenLimit.OracleFamily) (input : ℕ → ℕ) (t : ℕ) :
    outputAfterInput (patientPrefixGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  apply patient_output_congr O (prefixCompletion (fun i : Fin (t + 1) => input i)) input t
  intro k hk
  simp [prefixCompletion, hk]

end Case019
