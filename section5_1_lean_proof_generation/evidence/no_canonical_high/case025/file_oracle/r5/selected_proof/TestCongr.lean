import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

private theorem sample_eq_of_eq_below
    {a b : ℕ → ℕ} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {n i : ℕ}
    (hsample : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.RecursiveCritical C a n i ↔ GenLimit.RecursiveCritical C b n i := by
  have hconsistent : ∀ j,
      GenLimit.Consistent C a n j ↔ GenLimit.Consistent C b n j := by
    intro j
    simp only [GenLimit.Consistent, hsample]
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa only [GenLimit.RecursiveCritical] using hconsistent 0
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hchain⟩
            refine ⟨(hconsistent _).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hchain j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hchain⟩
            refine ⟨(hconsistent _).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hchain j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

private theorem processRound_congr
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hs : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
    sample_eq_of_eq_below h
  have hs0 : GenLimit.sample a t = GenLimit.sample b t :=
    sample_eq_of_eq_below (fun k hk => h k (lt_trans hk (Nat.lt_succ_self t)))
  have hcon1 (i : ℕ) :
      GenLimit.Consistent O.language a (t + 1) i ↔
        GenLimit.Consistent O.language b (t + 1) i := by
    simp only [GenLimit.Consistent, hs]
  have hcrit0 (i : ℕ) :
      GenLimit.RecursiveCritical O.language a t i ↔
        GenLimit.RecursiveCritical O.language b t i :=
    recursiveCritical_congr O.language hs0
  have hcrit1 (i : ℕ) :
      GenLimit.RecursiveCritical O.language a (t + 1) i ↔
        GenLimit.RecursiveCritical O.language b (t + 1) i :=
    recursiveCritical_congr O.language hs
  simp only [GenLimit.PatientMachine.processRound,
    GenLimit.PatientMachine.decide, GenLimit.PatientMachine.stableDecision,
    GenLimit.PatientMachine.backtrackDecision,
    GenLimit.PatientMachine.highestCritical,
    GenLimit.PatientMachine.highestSurvivor,
    GenLimit.PatientMachine.lowestConsistentInScope,
    GenLimit.PatientMachine.lowestConsistent,
    GenLimit.PatientMachine.criticalIndices,
    GenLimit.PatientMachine.survivingCriticalIndices,
    GenLimit.PatientMachine.consistentIndices,
    GenLimit.PatientMachine.leastAvailable,
    GenLimit.PatientMachine.available_exists,
    GenLimit.PatientMachine.Available,
    hs, hs0, hcon1, hcrit0, hcrit1]
