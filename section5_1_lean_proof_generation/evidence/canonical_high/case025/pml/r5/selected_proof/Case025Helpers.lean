import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Combinatorics.Colex

open Filter

namespace Stage3Case025

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

def prefixExtension (t : ℕ) (hist : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then hist ⟨n, h⟩ else 0

@[simp] theorem prefixExtension_apply
    (t : ℕ) (hist : Fin (t + 1) → ℕ) (n : ℕ) (h : n < t + 1) :
    prefixExtension t hist n = hist ⟨n, h⟩ := by
  simp [prefixExtension, h]

theorem sample_eq_of_eqOn_lt
    {a b : Stream} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem consistent_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) (i : ℕ) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_eq_of_eqOn_lt h]

theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) (i : ℕ) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using consistent_congr C h 0
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_congr C h _).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hprev j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_congr C h _).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hprev j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)


theorem consistentIndices_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_congr C h i]

theorem criticalIndices_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_congr C h i]

theorem survivingCriticalIndices_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr C (fun n hn => h n (Nat.lt.step hn)) i]
  rw [recursiveCritical_congr C h i]

theorem highestCritical_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr C h]

theorem highestSurvivor_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr C h]

theorem lowestConsistentInScope_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr C h]

theorem lowestConsistent_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  have hall : (∃ i, GenLimit.Consistent C a t i) ↔
      ∃ i, GenLimit.Consistent C b t i := by
    constructor <;> rintro ⟨i, hi⟩
    · exact ⟨i, (consistent_congr C h i).mp hi⟩
    · exact ⟨i, (consistent_congr C h i).mpr hi⟩
  split <;> rename_i ha
  · rw [dif_pos (hall.mp ha)]
    congr 1
    funext i
    exact propext (consistent_congr C h i)
  · rw [dif_neg (fun hb => ha (hall.mpr hb))]

theorem backtrackDecision_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  have hCI :
      GenLimit.PatientMachine.consistentIndices C a (t + 1) old.scope =
        GenLimit.PatientMachine.consistentIndices C b (t + 1) old.scope :=
    consistentIndices_congr C h
  have hSI :
      GenLimit.PatientMachine.survivingCriticalIndices C a t old.scope =
        GenLimit.PatientMachine.survivingCriticalIndices C b t old.scope :=
    survivingCriticalIndices_congr C h
  have hHS :
      GenLimit.PatientMachine.highestSurvivor C a t old.scope old.focus =
        GenLimit.PatientMachine.highestSurvivor C b t old.scope old.focus :=
    highestSurvivor_congr C h
  have hLCIS :
      GenLimit.PatientMachine.lowestConsistentInScope C a (t + 1)
          old.scope old.focus =
        GenLimit.PatientMachine.lowestConsistentInScope C b (t + 1)
          old.scope old.focus :=
    lowestConsistentInScope_congr C h
  have hLC :
      GenLimit.PatientMachine.lowestConsistent C a (t + 1) old.focus =
        GenLimit.PatientMachine.lowestConsistent C b (t + 1) old.focus :=
    lowestConsistent_congr C h
  have hall : (∃ i, GenLimit.Consistent C a (t + 1) i) ↔
      ∃ i, GenLimit.Consistent C b (t + 1) i := by
    constructor <;> rintro ⟨i, hi⟩
    · exact ⟨i, (consistent_congr C h i).mp hi⟩
    · exact ⟨i, (consistent_congr C h i).mpr hi⟩
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [hCI, hSI, hHS, hLCIS, hLC, hall]

theorem stableDecision_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp [GenLimit.PatientMachine.stableDecision, hwait,
      highestCritical_congr C h]
  · simp [GenLimit.PatientMachine.stableDecision, hwait]

theorem decide_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  have hcon := consistent_congr C h old.focus
  split <;> rename_i ha
  · rw [if_pos (hcon.mp ha)]
    exact stableDecision_congr C old h
  · rw [if_neg (fun hb => ha (hcon.mpr hb))]
    exact backtrackDecision_congr C old h


theorem available_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (used : Finset ℕ) (focus x : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.Available C a t used focus x ↔
      GenLimit.PatientMachine.Available C b t used focus x := by
  simp only [GenLimit.PatientMachine.Available, sample_eq_of_eqOn_lt h]

theorem leastAvailable_congr
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {a b : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.leastAvailable C hInfinite a t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  exact propext (available_congr C used focus x h)

theorem processRound_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hd := decide_congr O.language old h
  have hl :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a
          (t + 1) old.used
          (GenLimit.PatientMachine.decide O.language b t old).focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b
          (t + 1) old.used
          (GenLimit.PatientMachine.decide O.language b t old).focus :=
    leastAvailable_congr O.language O.infinite' old.used _ h
  simp [GenLimit.PatientMachine.processRound, hd, hl]

theorem run_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.run O a t =
      GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      have hold : GenLimit.PatientMachine.run O a t =
          GenLimit.PatientMachine.run O b t :=
        ih (fun n hn => h n (Nat.lt.step hn))
      rw [hold]
      exact processRound_congr O
        (GenLimit.PatientMachine.run O b t) h

theorem patientOutput_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr O h]

noncomputable def patientOnlineGenerator
    (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t inputHistory _ =>
    GenLimit.PatientMachine.output O (prefixExtension t inputHistory) t

theorem patientOnlineGenerator_follows
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  symm
  apply patientOutput_congr O
  intro n hn
  simp [prefixExtension, hn]

theorem positivePresentationHalfDensity : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, patientOnlineGenerator_follows O input, ?_⟩
  have hresult :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input (z := i) hP
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT⟩ := hresult.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfreshInput, hfreshOutput⟩ := hT t ht
    refine ⟨hmem, ?_, hfreshOutput⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, hvalue⟩ := hsample
    exact hfreshInput s (Nat.lt_succ_iff.mp hs) hvalue
  · simpa [output, O, GenLimit.PatientMachine.patientLowerDensity] using hresult.2

end Stage3Case025
