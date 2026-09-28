import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main

open Set
open Stage3Case019

namespace Probe

private theorem sample_congr
    {a b : Stream ℕ} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem consistent_congr
    (C : GenLimit.LanguageFamily) {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) (i : ℕ) :
    GenLimit.Consistent C a n i ↔ GenLimit.Consistent C b n i := by
  unfold GenLimit.Consistent
  rw [sample_congr h]

private theorem critical_congr
    (C : GenLimit.LanguageFamily) {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) (i : ℕ) :
    GenLimit.RecursiveCritical C a n i ↔
      GenLimit.RecursiveCritical C b n i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using consistent_congr C h 0
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hc, hs⟩
            refine ⟨(consistent_congr C h _).1 hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjc)
          · rintro ⟨hc, hs⟩
            refine ⟨(consistent_congr C h _).2 hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjc)

private theorem decide_congr
    (C : GenLimit.LanguageFamily) {a b : Stream ℕ} {t : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  have hc : ∀ i, GenLimit.Consistent C a (t + 1) i ↔
      GenLimit.Consistent C b (t + 1) i := consistent_congr C h
  have hr : ∀ i, GenLimit.RecursiveCritical C a (t + 1) i ↔
      GenLimit.RecursiveCritical C b (t + 1) i := critical_congr C h
  have hold : ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i :=
    critical_congr C (fun k hk => h k (Nat.lt.step hk))
  have hci : GenLimit.PatientMachine.consistentIndices C a (t + 1) old.scope =
      GenLimit.PatientMachine.consistentIndices C b (t + 1) old.scope := by
    ext i
    simp [hc i]
  have hcri : GenLimit.PatientMachine.criticalIndices C a (t + 1) (old.scope + 1) =
      GenLimit.PatientMachine.criticalIndices C b (t + 1) (old.scope + 1) := by
    ext i
    simp [hr i]
  have hsurv : GenLimit.PatientMachine.survivingCriticalIndices C a t old.scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t old.scope := by
    ext i
    simp [hold i, hr i]
  have hlcis : GenLimit.PatientMachine.lowestConsistentInScope C a (t + 1) old.scope old.focus =
      GenLimit.PatientMachine.lowestConsistentInScope C b (t + 1) old.scope old.focus := by
    unfold GenLimit.PatientMachine.lowestConsistentInScope
    simp only [hci]
  have he : (∃ i, GenLimit.Consistent C a (t + 1) i) ↔
      ∃ i, GenLimit.Consistent C b (t + 1) i := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hc i).1 hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hc i).2 hi⟩
  have hlc : GenLimit.PatientMachine.lowestConsistent C a (t + 1) old.focus =
      GenLimit.PatientMachine.lowestConsistent C b (t + 1) old.focus := by
    unfold GenLimit.PatientMachine.lowestConsistent
    by_cases ha : ∃ i, GenLimit.Consistent C a (t + 1) i
    · have hb : ∃ i, GenLimit.Consistent C b (t + 1) i := he.1 ha
      simp only [dif_pos ha, dif_pos hb]
      exact Nat.find_congr' (fun {i} => hc i)
    · have hb : ¬ ∃ i, GenLimit.Consistent C b (t + 1) i := fun hb => ha (he.2 hb)
      simp [ha, hb]
  unfold GenLimit.PatientMachine.decide
  rw [propext (hc old.focus)]
  unfold GenLimit.PatientMachine.stableDecision
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [hci, hcri, hsurv, hlcis, hlc, propext he]
  congr 1
  · unfold GenLimit.PatientMachine.highestCritical
    simp only [hcri]
  · unfold GenLimit.PatientMachine.highestSurvivor
    simp only [hsurv]

end Probe

namespace Probe

private theorem leastAvailable_congr
    (C : GenLimit.LanguageFamily) (hI : ∀ i, (C i).Infinite)
    {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k)
    (used : Finset ℕ) (focus : ℕ) :
    GenLimit.PatientMachine.leastAvailable C hI a n used focus =
      GenLimit.PatientMachine.leastAvailable C hI b n used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr'
  intro x
  unfold GenLimit.PatientMachine.Available
  rw [sample_congr h]

private theorem run_congr
    (O : GenLimit.OracleFamily) {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.PatientMachine.run O a n =
      GenLimit.PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      have ih' := ih (fun k hk => h k (Nat.lt.step hk))
      rw [ih']
      have hd := decide_congr O.language h (GenLimit.PatientMachine.run O b n)
      unfold GenLimit.PatientMachine.processRound
      simp only [hd]
      rw [leastAvailable_congr O.language O.infinite' h]

end Probe
