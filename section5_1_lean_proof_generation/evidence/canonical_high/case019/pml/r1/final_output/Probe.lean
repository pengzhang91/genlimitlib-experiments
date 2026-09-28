import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set

namespace Stage3Case019

open GenLimit
open GenLimit.Generic

lemma basicSample_eq_of_prefix_eq {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, hax⟩
    exact ⟨k, hk, (h k hk).symm.trans hax⟩
  · rintro ⟨k, hk, hbx⟩
    exact ⟨k, hk, (h k hk).trans hbx⟩

lemma consistent_iff_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t i : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  rw [GenLimit.Consistent, GenLimit.Consistent, basicSample_eq_of_prefix_eq h]

lemma recursiveCritical_iff_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t i : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero =>
        simpa only [GenLimit.RecursiveCritical] using
          (consistent_iff_of_prefix_eq (C := C) (i := 0) h)
    | succ i =>
        simp only [GenLimit.RecursiveCritical]
        constructor
        · rintro ⟨hc, hr⟩
          refine ⟨(consistent_iff_of_prefix_eq h).mp hc, ?_⟩
          intro j hj hjc
          exact hr j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjc)
        · rintro ⟨hc, hr⟩
          refine ⟨(consistent_iff_of_prefix_eq h).mpr hc, ?_⟩
          intro j hj hjc
          exact hr j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjc)

lemma consistentIndices_eq_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  exact and_congr_right fun _ => consistent_iff_of_prefix_eq h

lemma criticalIndices_eq_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  exact and_congr_right fun _ => recursiveCritical_iff_of_prefix_eq h

lemma survivingCriticalIndices_eq_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope : ℕ} (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  have ht : ∀ k, k < t → a k = b k := fun k hk => h k (Nat.lt.step hk)
  exact and_congr_right fun _ => and_congr
    (recursiveCritical_iff_of_prefix_eq ht)
    (recursiveCritical_iff_of_prefix_eq h)

lemma highestCritical_eq_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope fallback : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq_of_prefix_eq h]

lemma highestSurvivor_eq_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope fallback : ℕ} (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_prefix_eq h]

lemma lowestConsistentInScope_eq_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t scope fallback : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_prefix_eq h]

lemma lowestConsistent_eq_of_prefix_eq {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t fallback : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      simpa only [consistent_iff_of_prefix_eq h] using ha
    rw [dif_pos ha, dif_pos hb]
    apply Nat.find_congr (Nat.find_spec ha)
    intro n _hn
    exact consistent_iff_of_prefix_eq h
  · have hb : ¬∃ i, GenLimit.Consistent C b t i := by
      simpa only [consistent_iff_of_prefix_eq h] using ha
    rw [dif_neg ha, dif_neg hb]

lemma stableDecision_eq_of_prefix_eq
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  split <;> rename_i hw
  · have heq := highestCritical_eq_of_prefix_eq
      (C := C) (a := a) (b := b) (t := t + 1)
      (scope := old.scope + 1) (fallback := old.focus) h
    simp only [heq]
  · rfl

lemma backtrackDecision_eq_of_prefix_eq
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  have hci := consistentIndices_eq_of_prefix_eq
    (C := C) (a := a) (b := b) (t := t + 1) (scope := old.scope) h
  have hsi := survivingCriticalIndices_eq_of_prefix_eq
    (C := C) (a := a) (b := b) (t := t) (scope := old.scope) h
  have hhs := highestSurvivor_eq_of_prefix_eq
    (C := C) (a := a) (b := b) (t := t)
    (scope := old.scope) (fallback := old.focus) h
  have hlc := lowestConsistentInScope_eq_of_prefix_eq
    (C := C) (a := a) (b := b) (t := t + 1)
    (scope := old.scope) (fallback := old.focus) h
  have hlg := lowestConsistent_eq_of_prefix_eq
    (C := C) (a := a) (b := b) (t := t + 1)
    (fallback := old.focus) h
  have hall : (∃ j, GenLimit.Consistent C a (t + 1) j) ↔
      ∃ j, GenLimit.Consistent C b (t + 1) j :=
    exists_congr fun _ => consistent_iff_of_prefix_eq h
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [hci, hsi, hhs, hlc, hlg, hall]

lemma decide_eq_of_prefix_eq
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [consistent_iff_of_prefix_eq h]
  split <;> rename_i hc
  · exact stableDecision_eq_of_prefix_eq old h
  · exact backtrackDecision_eq_of_prefix_eq old h

lemma leastAvailable_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.leastAvailable C hInfinite a t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  have hs := basicSample_eq_of_prefix_eq h
  congr 1
  funext x
  apply propext
  simp only [GenLimit.PatientMachine.Available, hs]

lemma processRound_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  unfold GenLimit.PatientMachine.processRound
  have hd := decide_eq_of_prefix_eq
    (C := O.language) (a := a) (b := b) old h
  have hl := leastAvailable_eq_of_prefix_eq O.language O.infinite'
    (a := a) (b := b) (t := t + 1) old.used
    (GenLimit.PatientMachine.decide O.language b t old).focus h
  simp only [hd, hl]

lemma run_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.run O a t =
      GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, ih (fun k hk => h k (Nat.lt.step hk))]
      exact processRound_eq_of_prefix_eq O _ h

lemma patientOutput_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_prefix_eq O h]

end Stage3Case019
