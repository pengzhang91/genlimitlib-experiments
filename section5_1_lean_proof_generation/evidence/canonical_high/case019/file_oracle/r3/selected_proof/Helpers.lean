import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter

namespace Case019Helpers

open GenLimit
open GenLimit.Generic
open GenLimit.PatientMachine
open GenLimit.InfiniteContamination

theorem basic_sample_congr
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem consistent_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    Consistent C a t i ↔ Consistent C b t i := by
  unfold Consistent
  rw [basic_sample_congr h]

theorem recursiveCritical_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    ∀ i, RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [RecursiveCritical] using consistent_congr_prefix C h (i := 0)
      | succ i =>
          simp only [RecursiveCritical]
          rw [consistent_congr_prefix C h]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjb
            exact hcrit j hj ((ih j (by omega)).mpr hjb)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, ?_⟩
            intro j hj hja
            exact hcrit j hj ((ih j (by omega)).mp hja)

theorem consistentIndices_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    consistentIndices C a t scope = consistentIndices C b t scope := by
  classical
  ext i
  simp [consistent_congr_prefix C h]

theorem criticalIndices_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    criticalIndices C a t scope = criticalIndices C b t scope := by
  classical
  ext i
  simp [recursiveCritical_congr_prefix C h]

theorem survivingCriticalIndices_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    survivingCriticalIndices C a t scope =
      survivingCriticalIndices C b t scope := by
  classical
  ext i
  have ht : ∀ n, n < t → a n = b n :=
    fun n hn => h n (lt_trans hn (Nat.lt_succ_self t))
  simp [recursiveCritical_congr_prefix C ht,
    recursiveCritical_congr_prefix C h]

theorem highestCritical_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    highestCritical C a t scope fallback = highestCritical C b t scope fallback := by
  classical
  unfold highestCritical
  rw [criticalIndices_congr_prefix C h]

 theorem highestSurvivor_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    highestSurvivor C a t scope fallback = highestSurvivor C b t scope fallback := by
  classical
  unfold highestSurvivor
  rw [survivingCriticalIndices_congr_prefix C h]

 theorem lowestConsistentInScope_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    lowestConsistentInScope C a t scope fallback =
      lowestConsistentInScope C b t scope fallback := by
  classical
  unfold lowestConsistentInScope
  rw [consistentIndices_congr_prefix C h]

 theorem lowestConsistent_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    lowestConsistent C a t fallback = lowestConsistent C b t fallback := by
  classical
  unfold lowestConsistent
  by_cases ha : ∃ i, Consistent C a t i
  · have hb : ∃ i, Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_congr_prefix C h).mp hi⟩
    rw [dif_pos ha, dif_pos hb]
    apply Nat.find_congr (Nat.find_spec ha)
    intro n _hn
    exact consistent_congr_prefix C h
  · have hb : ¬ ∃ i, Consistent C b t i := by
      rintro ⟨i, hi⟩
      exact ha ⟨i, (consistent_congr_prefix C h).mpr hi⟩
    rw [dif_neg ha, dif_neg hb]

 theorem stableDecision_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t : ℕ} (old : State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    stableDecision C a t old = stableDecision C b t old := by
  classical
  have hf : ∀ scope fallback,
      highestCritical C a (t + 1) scope fallback =
        highestCritical C b (t + 1) scope fallback :=
    fun _ _ => highestCritical_congr_prefix C h
  unfold stableDecision
  simp only [hf]

 theorem backtrackDecision_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t : ℕ} (old : State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    backtrackDecision C a t old = backtrackDecision C b t old := by
  classical
  have hc : ∀ scope,
      consistentIndices C a (t + 1) scope = consistentIndices C b (t + 1) scope :=
    fun _ => consistentIndices_congr_prefix C h
  have hs : ∀ scope,
      survivingCriticalIndices C a t scope = survivingCriticalIndices C b t scope :=
    fun _ => survivingCriticalIndices_congr_prefix C h
  have hh : ∀ scope fallback,
      highestSurvivor C a t scope fallback = highestSurvivor C b t scope fallback :=
    fun _ _ => highestSurvivor_congr_prefix C h
  have hl : ∀ scope fallback,
      lowestConsistentInScope C a (t + 1) scope fallback =
        lowestConsistentInScope C b (t + 1) scope fallback :=
    fun _ _ => lowestConsistentInScope_congr_prefix C h
  have hg : ∀ fallback,
      lowestConsistent C a (t + 1) fallback = lowestConsistent C b (t + 1) fallback :=
    fun _ => lowestConsistent_congr_prefix C h
  have hp : (∃ j, Consistent C a (t + 1) j) =
      (∃ j, Consistent C b (t + 1) j) := by
    apply propext
    constructor <;> rintro ⟨j, hj⟩
    · exact ⟨j, (consistent_congr_prefix C h).mp hj⟩
    · exact ⟨j, (consistent_congr_prefix C h).mpr hj⟩
  unfold backtrackDecision
  simp only [hc, hs, hh, hl, hg, hp]

 theorem decide_congr_prefix
    (C : LanguageFamily) {a b : Stream ℕ} {t : ℕ} (old : State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.decide C a t old = PatientMachine.decide C b t old := by
  classical
  unfold PatientMachine.decide
  rw [propext (consistent_congr_prefix C h)]
  split
  · exact stableDecision_congr_prefix C old h
  · exact backtrackDecision_congr_prefix C old h

theorem leastAvailable_congr_prefix
    (C : LanguageFamily) (hinf : ∀ i, (C i).Infinite)
    {a b : Stream ℕ} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    leastAvailable C hinf a t used focus =
      leastAvailable C hinf b t used focus := by
  classical
  unfold leastAvailable
  let exa := available_exists C hinf a t used focus
  have hxa := Nat.find_spec exa
  apply Nat.find_congr hxa
  intro n _hn
  unfold Available
  rw [basic_sample_congr h]

theorem processRound_congr_prefix
    (O : OracleFamily) {a b : Stream ℕ} {t : ℕ} (old : State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    processRound O a t old = processRound O b t old := by
  classical
  have hd := decide_congr_prefix O.language old h
  unfold processRound
  simp only [hd]
  rw [leastAvailable_congr_prefix O.language O.infinite' old.used _ h]

theorem run_congr_prefix
    (O : OracleFamily) {a b : Stream ℕ} :
    ∀ t, (∀ n, n < t → a n = b n) → run O a t = run O b t := by
  intro t h
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ]
      rw [ih (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t)))]
      exact processRound_congr_prefix O _ h

theorem output_congr_prefix
    (O : OracleFamily) {a b : Stream ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  unfold PatientMachine.output
  rw [run_congr_prefix O (t + 1) h]

noncomputable def prefixExtension {α : Type*} [Inhabited α]
    {n : ℕ} (xs : Fin n → α) : Stream α :=
  fun k => if hk : k < n then xs ⟨k, hk⟩ else default

noncomputable def patientGenerator (O : OracleFamily) : Generator ℕ :=
  fun n xs =>
    if _h : 0 < n then
      PatientMachine.output O (prefixExtension xs) (n - 1)
    else 0

theorem outputAfterInput_patientGenerator
    (O : OracleFamily) (stream : Stream ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) stream t =
      PatientMachine.output O stream t := by
  unfold Stage3Case019.outputAfterInput Generic.output patientGenerator
  simp only [Nat.zero_lt_succ, ↓reduceDIte, Nat.add_sub_cancel]
  apply output_congr_prefix O
  intro n hn
  simp [prefixExtension, hn]

noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite) :
    OracleFamily where
  language := family
  infinite' := hinf
  query i x := by classical exact decide (x ∈ family i)
  query_spec i x := by classical simp

end Case019Helpers
