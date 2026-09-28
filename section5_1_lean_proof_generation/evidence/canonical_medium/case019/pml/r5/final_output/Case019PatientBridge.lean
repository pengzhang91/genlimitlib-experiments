import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set

namespace Stage3Case019

open GenLimit
open GenLimit.Generic
open GenLimit.PatientMachine
open GenLimit.InfiniteContamination

private theorem core_sample_eq_of_prefix
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

private theorem consistent_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) (i : ℕ) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  unfold GenLimit.Consistent
  rw [core_sample_eq_of_prefix h]

private theorem recursiveCritical_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) : ∀ i,
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using
            consistent_congr_prefix C h 0
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_congr_prefix C h (i + 1)]
          constructor
          · rintro ⟨hc, hall⟩
            refine ⟨hc, ?_⟩
            intro j hj hjcrit
            exact hall j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hc, hall⟩
            refine ⟨hc, ?_⟩
            intro j hj hjcrit
            exact hall j hj ((ih j (by omega)).mp hjcrit)

private theorem consistentIndices_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    consistentIndices C a t scope = consistentIndices C b t scope := by
  classical
  ext i
  simp only [mem_consistentIndices]
  rw [consistent_congr_prefix C h i]

private theorem criticalIndices_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    criticalIndices C a t scope = criticalIndices C b t scope := by
  classical
  ext i
  simp only [mem_criticalIndices]
  rw [recursiveCritical_congr_prefix C h i]

private theorem survivingCriticalIndices_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    survivingCriticalIndices C a t scope =
      survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [mem_survivingCriticalIndices]
  have ht : ∀ n, n < t → a n = b n := fun n hn => h n (lt_trans hn (Nat.lt_succ_self t))
  rw [recursiveCritical_congr_prefix C ht i,
    recursiveCritical_congr_prefix C h i]

private theorem highestCritical_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    highestCritical C a t scope fallback =
      highestCritical C b t scope fallback := by
  simp [highestCritical, criticalIndices_congr_prefix C h]

private theorem highestSurvivor_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    highestSurvivor C a t scope fallback =
      highestSurvivor C b t scope fallback := by
  simp [highestSurvivor, survivingCriticalIndices_congr_prefix C h]

private theorem lowestConsistentInScope_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    lowestConsistentInScope C a t scope fallback =
      lowestConsistentInScope C b t scope fallback := by
  simp [lowestConsistentInScope, consistentIndices_congr_prefix C h]

private theorem lowestConsistent_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    lowestConsistent C a t fallback = lowestConsistent C b t fallback := by
  classical
  have hc : ∀ i, GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i :=
    fun i => consistent_congr_prefix C h i
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (hc i).mp hi⟩
    simp only [lowestConsistent, dif_pos ha, dif_pos hb]
    exact Nat.find_congr (Nat.find_spec ha) (fun n _ => hc n)
  · have hb : ¬∃ i, GenLimit.Consistent C b t i := by
      rintro ⟨i, hi⟩
      exact ha ⟨i, (hc i).mpr hi⟩
    simp [lowestConsistent, ha, hb]

private theorem stableDecision_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) (old : State) :
    stableDecision C a t old = stableDecision C b t old := by
  classical
  unfold stableDecision
  split <;> rename_i hw
  · dsimp only
    rw [highestCritical_congr_prefix C h]
  · rfl

private theorem backtrackDecision_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) (old : State) :
    backtrackDecision C a t old = backtrackDecision C b t old := by
  classical
  have hci := consistentIndices_congr_prefix
    (C := C) (a := a) (b := b) (t := t + 1) (scope := old.scope) h
  have hsi := survivingCriticalIndices_congr_prefix
    (C := C) (a := a) (b := b) (t := t) (scope := old.scope) h
  unfold backtrackDecision
  rw [hci]
  dsimp only
  by_cases hc : (consistentIndices C b (t + 1) old.scope).Nonempty
  · simp only [dif_pos hc]
    rw [hsi]
    by_cases hs : (survivingCriticalIndices C b t old.scope).Nonempty
    · simp only [if_pos hs]
      rw [highestSurvivor_congr_prefix C h]
    · simp only [if_neg hs]
      rw [lowestConsistentInScope_congr_prefix C h]
  · simp only [dif_neg hc]
    rw [lowestConsistent_congr_prefix C h]
    have hall : (∃ j, GenLimit.Consistent C a (t + 1) j) ↔
        ∃ j, GenLimit.Consistent C b (t + 1) j := by
      constructor <;> rintro ⟨j, hj⟩ <;> refine ⟨j, ?_⟩
      · exact (consistent_congr_prefix C h j).mp hj
      · exact (consistent_congr_prefix C h j).mpr hj
    by_cases hb : ∃ j, GenLimit.Consistent C b (t + 1) j
    · have ha := hall.mpr hb
      simp only [dif_pos ha, dif_pos hb]
    · have ha : ¬∃ j, GenLimit.Consistent C a (t + 1) j :=
        fun ha => hb (hall.mp ha)
      simp only [dif_neg ha, dif_neg hb]

private theorem decide_congr_prefix
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) (old : State) :
    PatientMachine.decide C a t old = PatientMachine.decide C b t old := by
  classical
  have hcon : GenLimit.Consistent C a (t + 1) old.focus ↔
      GenLimit.Consistent C b (t + 1) old.focus :=
    consistent_congr_prefix C h old.focus
  by_cases ha : GenLimit.Consistent C a (t + 1) old.focus
  · have hb := hcon.mp ha
    simp [PatientMachine.decide, ha, hb,
      stableDecision_congr_prefix C h old]
  · have hb : ¬GenLimit.Consistent C b (t + 1) old.focus :=
      fun hb => ha (hcon.mpr hb)
    simp [PatientMachine.decide, ha, hb,
      backtrackDecision_congr_prefix C h old]

private theorem leastAvailable_congr_prefix
    (C : GenLimit.LanguageFamily) (hInf : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ n, n < t → a n = b n)
    (used : Finset ℕ) (focus : ℕ) :
    leastAvailable C hInf a t used focus =
      leastAvailable C hInf b t used focus := by
  have hs : GenLimit.sample a t = GenLimit.sample b t := core_sample_eq_of_prefix h
  simp only [leastAvailable]
  congr 1
  funext x
  apply propext
  simp [Available, hs]

private theorem processRound_congr_prefix
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) (old : State) :
    processRound O a t old = processRound O b t old := by
  classical
  have hd := decide_congr_prefix O.language h old
  let d := PatientMachine.decide O.language b t old
  have hx : leastAvailable O.language O.infinite' a (t + 1) old.used d.focus =
      leastAvailable O.language O.infinite' b (t + 1) old.used d.focus :=
    leastAvailable_congr_prefix O.language O.infinite' h old.used d.focus
  simp only [processRound]
  rw [hd]
  change (let x := leastAvailable O.language O.infinite' a (t + 1) old.used d.focus
    State.mk d.scope d.tau (if d.focus = old.focus then old.age + 1 else 1)
      d.focus (insert x old.used) (some x) d.move) = _
  rw [hx]

private theorem run_congr_prefix
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} : ∀ t,
    (∀ n, n < t → a n = b n) → run O a t = run O b t := by
  intro t
  induction t with
  | zero => intro; rfl
  | succ t ih =>
      intro h
      rw [run_succ, run_succ, ih (fun n hn => h n (Nat.lt.step hn))]
      exact processRound_congr_prefix O h _

private theorem patient_output_congr_prefix
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  unfold PatientMachine.output
  rw [run_congr_prefix O (t + 1) h]

private def patientPrefixCompletion {t : ℕ} (history : Fin t → ℕ) : ℕ → ℕ :=
  GenLimit.Generic.historyThenFallback (List.ofFn history) 0

private theorem patientPrefixCompletion_eq
    {t : ℕ} (history : Fin t → ℕ) {i : ℕ} (hi : i < t) :
    patientPrefixCompletion history i = history ⟨i, hi⟩ := by
  simp [patientPrefixCompletion, GenLimit.Generic.historyThenFallback, hi]

noncomputable def patientGenerator (O : GenLimit.OracleFamily) : Generator ℕ :=
  fun t history =>
    if h : t = 0 then 0
    else PatientMachine.output O (patientPrefixCompletion history) (t - 1)

theorem outputAfterInput_patientGenerator
    (O : GenLimit.OracleFamily) (stream : Stream ℕ) (t : ℕ) :
    outputAfterInput (patientGenerator O) stream t =
      PatientMachine.output O stream t := by
  have hne : t + 1 ≠ 0 := by omega
  simp only [outputAfterInput, GenLimit.Generic.output, patientGenerator, dif_neg hne]
  have hp : ∀ n, n < t + 1 →
      patientPrefixCompletion (fun i : Fin (t + 1) => stream i) n = stream n := by
    intro n hn
    exact patientPrefixCompletion_eq _ hn
  simpa using patient_output_congr_prefix O t hp

end Stage3Case019
