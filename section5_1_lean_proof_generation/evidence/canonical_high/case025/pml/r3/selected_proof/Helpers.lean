import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter

namespace Stage3Case025

open GenLimit

def prefixExtension {t : ℕ} (input : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then input ⟨n, h⟩ else 0

theorem prefixExtension_eq {t : ℕ} (input : Stream) (n : ℕ) (hn : n < t + 1) :
    prefixExtension (fun i : Fin (t + 1) => input i) n = input n := by
  simp [prefixExtension, hn]

theorem sample_eq_of_eq_below
    {a b : Stream} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    sample a t = sample b t := by
  ext x
  simp only [mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem consistent_iff_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    Consistent C a t i ↔ Consistent C b t i := by
  simp only [Consistent, sample_eq_of_eq_below h]

theorem recursiveCritical_iff_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [RecursiveCritical] using consistent_iff_of_eq_below (i := 0) h
      | succ i =>
          simp only [RecursiveCritical]
          rw [consistent_iff_of_eq_below h]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjrec
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjrec)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjrec
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjrec)

theorem consistentIndices_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.consistentIndices C a t scope =
      PatientMachine.consistentIndices C b t scope := by
  classical
  apply Finset.ext
  intro i
  simp only [PatientMachine.mem_consistentIndices]
  rw [consistent_iff_of_eq_below h]

theorem criticalIndices_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.criticalIndices C a t scope =
      PatientMachine.criticalIndices C b t scope := by
  classical
  apply Finset.ext
  intro i
  simp only [PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_iff_of_eq_below h]

theorem survivingCriticalIndices_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.survivingCriticalIndices C a t scope =
      PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  apply Finset.ext
  intro i
  simp only [PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_iff_of_eq_below h]
  rw [recursiveCritical_iff_of_eq_below
    (fun n hn => h n (Nat.lt.step hn))]

theorem highestCritical_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.highestCritical C a t scope fallback =
      PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold PatientMachine.highestCritical
  rw [criticalIndices_eq_of_eq_below h]

theorem highestSurvivor_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.highestSurvivor C a t scope fallback =
      PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_eq_below h]

theorem lowestConsistentInScope_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.lowestConsistentInScope C a t scope fallback =
      PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_eq_below h]

theorem lowestConsistent_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.lowestConsistent C a t fallback =
      PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold PatientMachine.lowestConsistent
  have hall : (∃ i, Consistent C a t i) ↔ ∃ i, Consistent C b t i := by
    constructor <;> rintro ⟨i, hi⟩
    · exact ⟨i, (consistent_iff_of_eq_below h).1 hi⟩
    · exact ⟨i, (consistent_iff_of_eq_below h).2 hi⟩
  by_cases ha : ∃ i, Consistent C a t i
  · have hb := hall.1 ha
    simp only [ha, hb, ↓reduceDIte]
    apply Nat.find_congr (Nat.find_spec ha)
    intro n hn
    exact consistent_iff_of_eq_below h
  · have hb : ¬ ∃ i, Consistent C b t i := fun hb => ha (hall.2 hb)
    simp [ha, hb]

theorem stableDecision_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t : ℕ}
    (old : PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.stableDecision C a t old =
      PatientMachine.stableDecision C b t old := by
  classical
  unfold PatientMachine.stableDecision
  split <;> simp only
  rw [highestCritical_eq_of_eq_below h]

theorem backtrackDecision_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t : ℕ}
    (old : PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.backtrackDecision C a t old =
      PatientMachine.backtrackDecision C b t old := by
  classical
  unfold PatientMachine.backtrackDecision
  rw [consistentIndices_eq_of_eq_below h]
  rw [survivingCriticalIndices_eq_of_eq_below h]
  rw [highestSurvivor_eq_of_eq_below h]
  rw [lowestConsistentInScope_eq_of_eq_below h]
  rw [lowestConsistent_eq_of_eq_below h]
  have hall : (∃ j, Consistent C a (t + 1) j) ↔
      ∃ j, Consistent C b (t + 1) j := by
    constructor <;> rintro ⟨j, hj⟩
    · exact ⟨j, (consistent_iff_of_eq_below h).1 hj⟩
    · exact ⟨j, (consistent_iff_of_eq_below h).2 hj⟩
  rw [propext hall]

theorem decide_eq_of_eq_below
    {C : LanguageFamily} {a b : Stream} {t : ℕ}
    (old : PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.decide C a t old = PatientMachine.decide C b t old := by
  classical
  unfold PatientMachine.decide
  rw [show Consistent C a (t + 1) old.focus =
    Consistent C b (t + 1) old.focus from
      propext (consistent_iff_of_eq_below h)]
  rw [stableDecision_eq_of_eq_below old h]
  rw [backtrackDecision_eq_of_eq_below old h]

theorem leastAvailable_eq_of_eq_below
    {C : LanguageFamily} (hInfinite : ∀ i, (C i).Infinite)
    {a b : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.leastAvailable C hInfinite a t used focus =
      PatientMachine.leastAvailable C hInfinite b t used focus := by
  classical
  unfold PatientMachine.leastAvailable
  let ha := PatientMachine.available_exists C hInfinite a t used focus
  apply Nat.find_congr (Nat.find_spec ha)
  intro n hn
  unfold PatientMachine.Available
  rw [sample_eq_of_eq_below h]

theorem processRound_eq_of_eq_below
    (O : OracleFamily) {a b : Stream} {t : ℕ} (old : PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.processRound O a t old =
      PatientMachine.processRound O b t old := by
  classical
  unfold PatientMachine.processRound
  rw [decide_eq_of_eq_below old h]
  simp only
  rw [leastAvailable_eq_of_eq_below O.infinite' old.used _ h]

theorem run_eq_of_eq_below
    (O : OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.run O a t = PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      rw [ih (fun n hn => h n (Nat.lt.step hn))]
      exact processRound_eq_of_eq_below O _ h

theorem patient_output_eq_of_eq_below
    (O : OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  simp only [PatientMachine.output, run_eq_of_eq_below O h]

noncomputable def semanticOracleFamily
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) : OracleFamily := by
  classical
  exact
    { language := family
      infinite' := hInfinite
      query i x := if x ∈ family i then true else false
      query_spec i x := by simp }

noncomputable def patientOnlineGenerator (O : OracleFamily) : OnlineGenerator :=
  fun t input _ => PatientMachine.output O (prefixExtension input) t

theorem patientOnlineGenerator_follows
    (O : OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input (PatientMachine.output O input) := by
  intro t
  change PatientMachine.output O input t =
    PatientMachine.output O (prefixExtension fun i : Fin (t + 1) => input i) t
  symm
  apply patient_output_eq_of_eq_below
  intro n hn
  exact prefixExtension_eq input n hn

theorem positivePresentationHalfDensity : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := semanticOracleFamily family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hP
  refine ⟨PatientMachine.output O input, patientOnlineGenerator_follows O input, ?_, ?_⟩
  · obtain ⟨hgen, _⟩ := PatientMachine.patientScope_generation_and_lowerDensity O input hP
    obtain ⟨T, hT⟩ := hgen
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hin, hout⟩ := hT t ht
    refine ⟨hmem, ?_, fun s hs => hout s hs⟩
    rw [mem_sample_iff]
    rintro ⟨s, hs, heq⟩
    exact hin s (Nat.lt_succ_iff.mp hs) heq
  · exact (PatientMachine.patientScope_generation_and_lowerDensity O input hP).2

end Stage3Case025
