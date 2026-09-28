import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set
open GenLimit
open GenLimit.Generic

namespace Test

noncomputable def extend {n : ℕ} (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if h : k < n then xs ⟨k,h⟩ else 0

noncomputable def patientGen (O : OracleFamily) : Generator ℕ :=
  fun n xs => match n with
  | 0 => 0
  | t+1 => PatientMachine.output O (extend xs) t

lemma sample_extend {n m : ℕ} (xs : Fin n → ℕ) (h : m ≤ n) :
    Generic.sample (extend xs) m = Generic.sequenceSample (fun i : Fin m => xs ⟨i, lt_of_lt_of_le i.isLt h⟩) := by
  classical
  ext x
  simp only [Generic.mem_sample_iff, Generic.mem_sequenceSample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k,hk⟩, ?_⟩
    simp [extend, lt_of_lt_of_le hk h]
  · rintro ⟨k, rfl⟩
    refine ⟨k, k.isLt, ?_⟩
    simp [extend, lt_of_lt_of_le k.isLt h]

lemma sample_eq_of_eq_lt {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k,hk,ha⟩
    exact ⟨k,hk,(h k hk).symm.trans ha⟩
  · rintro ⟨k,hk,hb⟩
    exact ⟨k,hk,(h k hk).trans hb⟩

lemma consistent_iff_of_sample_eq (C : LanguageFamily) {a b : ℕ → ℕ} {n i : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    Consistent C a n i ↔ Consistent C b n i := by
  unfold Consistent
  rw [h]

lemma recursiveCritical_iff_of_sample_eq (C : LanguageFamily)
    {a b : ℕ → ℕ} {n : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    ∀ i, RecursiveCritical C a n i ↔ RecursiveCritical C b n i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [RecursiveCritical] using consistent_iff_of_sample_eq C h
      | succ i =>
          simp only [RecursiveCritical]
          rw [consistent_iff_of_sample_eq C h]
          constructor <;> rintro ⟨hc, hr⟩ <;> refine ⟨hc, ?_⟩
          · intro j hj hjc
            exact hr j hj ((ih j (by omega)).mpr hjc)
          · intro j hj hjc
            exact hr j hj ((ih j (by omega)).mp hjc)

lemma decide_eq_of_samples
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : PatientMachine.State)
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t+1) = GenLimit.sample b (t+1)) :
    PatientMachine.decide O.language a t old = PatientMachine.decide O.language b t old := by
  classical
  have hc1 : ∀ i, Consistent O.language a (t+1) i ↔ Consistent O.language b (t+1) i :=
    fun i => consistent_iff_of_sample_eq O.language h1
  have hr0 := recursiveCritical_iff_of_sample_eq O.language h0
  have hr1 := recursiveCritical_iff_of_sample_eq O.language h1
  have hcon : PatientMachine.consistentIndices O.language a (t+1) old.scope =
      PatientMachine.consistentIndices O.language b (t+1) old.scope := by
    ext i
    simp only [PatientMachine.mem_consistentIndices, hc1]
  have hcrit : PatientMachine.criticalIndices O.language a (t+1) (old.scope+1) =
      PatientMachine.criticalIndices O.language b (t+1) (old.scope+1) := by
    ext i
    simp only [PatientMachine.mem_criticalIndices, hr1]
  have hsurv : PatientMachine.survivingCriticalIndices O.language a t old.scope =
      PatientMachine.survivingCriticalIndices O.language b t old.scope := by
    ext i
    simp only [PatientMachine.mem_survivingCriticalIndices, hr0, hr1]
  have hhigh : PatientMachine.highestCritical O.language a (t+1) (old.scope+1) old.focus =
      PatientMachine.highestCritical O.language b (t+1) (old.scope+1) old.focus := by
    unfold PatientMachine.highestCritical
    rw [hcrit]
  have hsurvHigh : PatientMachine.highestSurvivor O.language a t old.scope old.focus =
      PatientMachine.highestSurvivor O.language b t old.scope old.focus := by
    unfold PatientMachine.highestSurvivor
    rw [hsurv]
  have hlowScope : PatientMachine.lowestConsistentInScope O.language a (t+1) old.scope old.focus =
      PatientMachine.lowestConsistentInScope O.language b (t+1) old.scope old.focus := by
    unfold PatientMachine.lowestConsistentInScope
    rw [hcon]
  have hlow : PatientMachine.lowestConsistent O.language a (t+1) old.focus =
      PatientMachine.lowestConsistent O.language b (t+1) old.focus := by
    by_cases ha : ∃ i, Consistent O.language a (t+1) i
    · have hb : ∃ i, Consistent O.language b (t+1) i := by
        rcases ha with ⟨i, hi⟩
        exact ⟨i, (hc1 i).mp hi⟩
      simp only [PatientMachine.lowestConsistent, ha, hb, ↓reduceDIte]
      apply Nat.find_congr (Nat.find_spec ha)
      intro n _hn
      exact hc1 n
    · have hb : ¬ ∃ i, Consistent O.language b (t+1) i := by
        intro hb
        rcases hb with ⟨i, hi⟩
        exact ha ⟨i, (hc1 i).mpr hi⟩
      simp [PatientMachine.lowestConsistent, ha, hb]
  unfold PatientMachine.decide PatientMachine.stableDecision PatientMachine.backtrackDecision
  rw [hc1 old.focus]
  split
  · simp only [hhigh]
  · simp only [hcon, hsurv, hsurvHigh, hlowScope, hlow, hc1]

lemma leastAvailable_eq_of_sample_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (n : ℕ) (used : Finset ℕ) (focus : ℕ)
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    PatientMachine.leastAvailable O.language O.infinite' a n used focus =
      PatientMachine.leastAvailable O.language O.infinite' b n used focus := by
  classical
  let ha := PatientMachine.available_exists O.language O.infinite' a n used focus
  let hb := PatientMachine.available_exists O.language O.infinite' b n used focus
  change Nat.find ha = Nat.find hb
  apply Nat.find_congr (Nat.find_spec ha)
  intro x _hx
  unfold PatientMachine.Available
  rw [h]

lemma processRound_eq_of_samples
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : PatientMachine.State)
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t+1) = GenLimit.sample b (t+1)) :
    PatientMachine.processRound O a t old = PatientMachine.processRound O b t old := by
  classical
  have hd := decide_eq_of_samples O t old h0 h1
  have hx := leastAvailable_eq_of_sample_eq O (t+1) old.used
    (PatientMachine.decide O.language b t old).focus h1
  simp only [PatientMachine.processRound]
  rw [hd, hx]

lemma run_eq_of_eq_lt (O : OracleFamily) {a b : ℕ → ℕ} (n : ℕ)
    (h : ∀ k, k < n → a k = b k) :
    PatientMachine.run O a n = PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      have hr := ih (fun k hk => h k (Nat.lt.step hk))
      rw [hr]
      apply processRound_eq_of_samples O
      · apply sample_eq_of_eq_lt
        exact fun k hk => h k (Nat.lt.step hk)
      · apply sample_eq_of_eq_lt
        exact h

lemma patientGen_output (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Generic.output (patientGen O) stream (t+1) =
      PatientMachine.output O stream t := by
  unfold Generic.output patientGen
  simp only
  unfold PatientMachine.output
  rw [run_eq_of_eq_lt O (n := t+1)]
  intro k hk
  simp [extend, hk]

end Test
