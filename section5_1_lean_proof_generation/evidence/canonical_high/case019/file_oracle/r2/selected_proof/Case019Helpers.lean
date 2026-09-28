import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open scoped Topology

namespace Stage3Case019

noncomputable section

def prefixStream {α : Type*} {n : ℕ} (xs : Fin n → α) (fallback : α) : ℕ → α :=
  fun k => if h : k < n then xs ⟨k, h⟩ else fallback

@[simp] theorem prefixStream_apply {α : Type*} {n : ℕ}
    (xs : Fin n → α) (fallback : α) {k : ℕ} (hk : k < n) :
    prefixStream xs fallback k = xs ⟨k, hk⟩ := by
  simp [prefixStream, hk]

theorem basic_sample_congr {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

theorem consistent_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n i : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.Consistent C a n i ↔ GenLimit.Consistent C b n i := by
  simp [GenLimit.Consistent, h]

theorem recursiveCritical_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n i : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.RecursiveCritical C a n i ↔
      GenLimit.RecursiveCritical C b n i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [GenLimit.RecursiveCritical, consistent_congr h]
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_congr h).mp hcon, ?_⟩
            intro j hj hjcrit
            apply hcrit j hj
            exact (ih j (by omega)).mpr hjcrit
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_congr h).mpr hcon, ?_⟩
            intro j hj hjcrit
            apply hcrit j hj
            exact (ih j (by omega)).mp hjcrit

theorem consistent_fun_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    (fun i => GenLimit.Consistent C a n i) =
      fun i => GenLimit.Consistent C b n i := by
  funext i
  exact propext (consistent_congr h)

theorem recursiveCritical_fun_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.RecursiveCritical C a n =
      GenLimit.RecursiveCritical C b n := by
  funext i
  exact propext (recursiveCritical_congr h)

theorem consistentIndices_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n scope : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.PatientMachine.consistentIndices C a n scope =
      GenLimit.PatientMachine.consistentIndices C b n scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_congr h]

theorem criticalIndices_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n scope : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.PatientMachine.criticalIndices C a n scope =
      GenLimit.PatientMachine.criticalIndices C b n scope := by
  unfold GenLimit.PatientMachine.criticalIndices
  rw [recursiveCritical_fun_eq h]

theorem survivingCriticalIndices_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n scope : ℕ}
    (h0 : GenLimit.sample a n = GenLimit.sample b n)
    (h1 : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1)) :
    GenLimit.PatientMachine.survivingCriticalIndices C a n scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b n scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr h0, recursiveCritical_congr h1]

theorem highestCritical_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n scope fallback : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.PatientMachine.highestCritical C a n scope fallback =
      GenLimit.PatientMachine.highestCritical C b n scope fallback := by
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr h]

theorem highestSurvivor_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n scope fallback : ℕ}
    (h0 : GenLimit.sample a n = GenLimit.sample b n)
    (h1 : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1)) :
    GenLimit.PatientMachine.highestSurvivor C a n scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b n scope fallback := by
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr h0 h1]

theorem lowestConsistentInScope_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n scope fallback : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.PatientMachine.lowestConsistentInScope C a n scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b n scope fallback := by
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr h]

theorem lowestConsistent_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n fallback : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.PatientMachine.lowestConsistent C a n fallback =
      GenLimit.PatientMachine.lowestConsistent C b n fallback := by
  classical
  have hi (i : ℕ) :
      GenLimit.Consistent C a n i ↔ GenLimit.Consistent C b n i :=
    consistent_congr h
  have hex : (∃ i, GenLimit.Consistent C a n i) ↔
      ∃ i, GenLimit.Consistent C b n i := exists_congr hi
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a n i
  · have hb := hex.mp ha
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr' (fun {i} => hi i)
  · have hb : ¬ ∃ i, GenLimit.Consistent C b n i :=
      fun hb => ha (hex.mpr hb)
    rw [dif_neg ha, dif_neg hb]

theorem stableDecision_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n : ℕ} (old : GenLimit.PatientMachine.State)
    (h1 : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1)) :
    GenLimit.PatientMachine.stableDecision C a n old =
      GenLimit.PatientMachine.stableDecision C b n old := by
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp only [GenLimit.PatientMachine.stableDecision, dif_pos hwait]
    rw [highestCritical_congr h1]
  · simp [GenLimit.PatientMachine.stableDecision, hwait]

theorem backtrackDecision_congr {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {n : ℕ} (old : GenLimit.PatientMachine.State)
    (h0 : GenLimit.sample a n = GenLimit.sample b n)
    (h1 : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1)) :
    GenLimit.PatientMachine.backtrackDecision C a n old =
      GenLimit.PatientMachine.backtrackDecision C b n old := by
  unfold GenLimit.PatientMachine.backtrackDecision
  rw [consistentIndices_congr h1]
  rw [survivingCriticalIndices_congr h0 h1]
  rw [highestSurvivor_congr h0 h1]
  rw [lowestConsistentInScope_congr h1]
  rw [lowestConsistent_congr h1]
  have hex : (∃ j, GenLimit.Consistent C a (n + 1) j) ↔
      ∃ j, GenLimit.Consistent C b (n + 1) j :=
    exists_congr (fun j => consistent_congr h1)
  rw [propext hex]

theorem patient_decide_congr (O : GenLimit.OracleFamily)
    {a b : ℕ → ℕ} {n : ℕ} (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a n = GenLimit.sample b n)
    (hs1 : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1)) :
    GenLimit.PatientMachine.decide O.language a n old =
      GenLimit.PatientMachine.decide O.language b n old := by
  unfold GenLimit.PatientMachine.decide
  have hc : GenLimit.Consistent O.language a (n + 1) old.focus ↔
      GenLimit.Consistent O.language b (n + 1) old.focus :=
    consistent_congr hs1
  rw [propext hc]
  rw [stableDecision_congr old hs1, backtrackDecision_congr old hs0 hs1]

theorem patient_leastAvailable_congr (O : GenLimit.OracleFamily)
    {a b : ℕ → ℕ} {n : ℕ} (used : Finset ℕ) (focus : ℕ)
    (hs : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite'
        a n used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite'
        b n used focus := by
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  apply propext
  simp [GenLimit.PatientMachine.Available, hs]

theorem patient_run_congr {O : GenLimit.OracleFamily} {a b : ℕ → ℕ} :
    ∀ n, (∀ k, k < n → a k = b k) →
      GenLimit.PatientMachine.run O a n =
        GenLimit.PatientMachine.run O b n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hab
      have habn : ∀ k, k < n → a k = b k :=
        fun k hk => hab k (Nat.lt.step hk)
      have hr := ih habn
      have hs1 : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1) :=
        basic_sample_congr hab
      have hs0 : GenLimit.sample a n = GenLimit.sample b n :=
        basic_sample_congr habn
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, hr]
      have hd := patient_decide_congr O (GenLimit.PatientMachine.run O b n) hs0 hs1
      unfold GenLimit.PatientMachine.processRound
      rw [hd]
      let d := GenLimit.PatientMachine.decide O.language b n
        (GenLimit.PatientMachine.run O b n)
      have hx := patient_leastAvailable_congr O
        (GenLimit.PatientMachine.run O b n).used d.focus hs1
      simp only [d] at hx ⊢
      rw [hx]

def patientGenerator (O : GenLimit.OracleFamily) : Generator ℕ :=
  fun n xs =>
    match n with
    | 0 => 0
    | t + 1 =>
        GenLimit.PatientMachine.output O (prefixStream xs 0) t

theorem patientGenerator_output (O : GenLimit.OracleFamily)
    (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (patientGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  change GenLimit.PatientMachine.output O
      (prefixStream (fun i : Fin (t + 1) => input i) 0) t =
    GenLimit.PatientMachine.output O input t
  unfold GenLimit.PatientMachine.output
  have hr := patient_run_congr (O := O)
    (a := prefixStream (fun i : Fin (t + 1) => input i) 0)
    (b := input) (t + 1) (by
      intro k hk
      simp [prefixStream, hk])
  rw [hr]
end

end Stage3Case019
