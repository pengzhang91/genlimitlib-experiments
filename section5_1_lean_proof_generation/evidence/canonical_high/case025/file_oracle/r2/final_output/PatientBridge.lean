import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main

open Set

namespace Stage3Case025
namespace PatientBridge

open GenLimit
open GenLimit.PatientMachine

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by classical exact decide (x ∈ family i)
  query_spec := by
    classical
    intro i x
    simp

noncomputable def extendPrefix (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

@[simp] theorem extendPrefix_apply
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (n : ℕ) (hn : n < t + 1) :
    extendPrefix t xs n = xs ⟨n, hn⟩ := by
  simp [extendPrefix, hn]

theorem sample_eq_of_prefix_eq
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    sample a t = sample b t := by
  classical
  unfold sample
  ext x
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem consistent_iff_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    Consistent C a t i ↔ Consistent C b t i := by
  unfold Consistent
  rw [sample_eq_of_prefix_eq h]

theorem recursiveCritical_iff_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    ∀ i, RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [RecursiveCritical] using
            (consistent_iff_of_prefix_eq (C := C) (i := 0) h)
      | succ i =>
          simp only [RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_iff_of_prefix_eq h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_iff_of_prefix_eq h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

theorem consistentIndices_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    consistentIndices C a t scope = consistentIndices C b t scope := by
  classical
  ext i
  simp only [mem_consistentIndices]
  rw [consistent_iff_of_prefix_eq h]

theorem criticalIndices_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    criticalIndices C a t scope = criticalIndices C b t scope := by
  classical
  ext i
  simp only [mem_criticalIndices]
  rw [recursiveCritical_iff_of_prefix_eq h i]

theorem survivingCriticalIndices_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    survivingCriticalIndices C a t scope =
      survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [mem_survivingCriticalIndices]
  rw [recursiveCritical_iff_of_prefix_eq (fun n hn => h n (hn.trans_le (Nat.le_succ t))) i]
  rw [recursiveCritical_iff_of_prefix_eq h i]

theorem highestCritical_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    highestCritical C a t scope fallback = highestCritical C b t scope fallback := by
  classical
  unfold highestCritical
  rw [criticalIndices_eq_of_prefix_eq h]

theorem highestSurvivor_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    highestSurvivor C a t scope fallback = highestSurvivor C b t scope fallback := by
  classical
  unfold highestSurvivor
  rw [survivingCriticalIndices_eq_of_prefix_eq h]

theorem lowestConsistentInScope_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    lowestConsistentInScope C a t scope fallback =
      lowestConsistentInScope C b t scope fallback := by
  classical
  unfold lowestConsistentInScope
  rw [consistentIndices_eq_of_prefix_eq h]

theorem lowestConsistent_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    lowestConsistent C a t fallback = lowestConsistent C b t fallback := by
  classical
  have hp : (∃ i, Consistent C a t i) ↔ ∃ i, Consistent C b t i := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (consistent_iff_of_prefix_eq h).mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (consistent_iff_of_prefix_eq h).mpr hi⟩
  by_cases ha : ∃ i, Consistent C a t i
  · have hb := hp.mp ha
    have hsa := lowestConsistent_spec (fallback := fallback) ha
    have hsb := lowestConsistent_spec (fallback := fallback) hb
    apply le_antisymm
    · apply Nat.le_of_not_gt
      intro hlt
      exact hsa.2 _ hlt ((consistent_iff_of_prefix_eq h).mpr hsb.1)
    · apply Nat.le_of_not_gt
      intro hlt
      exact hsb.2 _ hlt ((consistent_iff_of_prefix_eq h).mp hsa.1)
  · have hb : ¬ ∃ i, Consistent C b t i := fun hex => ha (hp.mpr hex)
    simp [lowestConsistent, ha, hb]

theorem backtrackDecision_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ n, n < t + 1 → a n = b n) :
    backtrackDecision C a t old = backtrackDecision C b t old := by
  classical
  unfold backtrackDecision
  rw [consistentIndices_eq_of_prefix_eq h]
  rw [survivingCriticalIndices_eq_of_prefix_eq h]
  rw [highestSurvivor_eq_of_prefix_eq h]
  rw [lowestConsistentInScope_eq_of_prefix_eq h]
  rw [lowestConsistent_eq_of_prefix_eq h]
  have hp : (∃ j, Consistent C a (t + 1) j) ↔
      ∃ j, Consistent C b (t + 1) j := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (consistent_iff_of_prefix_eq h).mp hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (consistent_iff_of_prefix_eq h).mpr hj⟩
  rw [propext hp]

 theorem stableDecision_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ n, n < t + 1 → a n = b n) :
    stableDecision C a t old = stableDecision C b t old := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp [stableDecision, hwait, highestCritical_eq_of_prefix_eq h]
  · simp [stableDecision, hwait]

 theorem decide_eq_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ n, n < t + 1 → a n = b n) :
    decide C a t old = decide C b t old := by
  classical
  by_cases hcon : Consistent C a (t + 1) old.focus
  · have hcon' : Consistent C b (t + 1) old.focus :=
      (consistent_iff_of_prefix_eq h).mp hcon
    simp [PatientMachine.decide, hcon, hcon', stableDecision_eq_of_prefix_eq h]
  · have hcon' : ¬ Consistent C b (t + 1) old.focus := fun hb =>
      hcon ((consistent_iff_of_prefix_eq h).mpr hb)
    simp [PatientMachine.decide, hcon, hcon', backtrackDecision_eq_of_prefix_eq h]

theorem available_iff_of_prefix_eq
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    {used : Finset ℕ} {focus x : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    Available C a t used focus x ↔ Available C b t used focus x := by
  unfold Available
  rw [sample_eq_of_prefix_eq h]

theorem leastAvailable_eq_of_prefix_eq
    {C : LanguageFamily} (hInfinite : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t : ℕ} {used : Finset ℕ} {focus : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    leastAvailable C hInfinite a t used focus =
      leastAvailable C hInfinite b t used focus := by
  classical
  apply le_antisymm
  · exact leastAvailable_minimal C hInfinite a t used focus
      (leastAvailable C hInfinite b t used focus)
      ((available_iff_of_prefix_eq h).mpr
        (leastAvailable_spec C hInfinite b t used focus))
  · exact leastAvailable_minimal C hInfinite b t used focus
      (leastAvailable C hInfinite a t used focus)
      ((available_iff_of_prefix_eq h).mp
        (leastAvailable_spec C hInfinite a t used focus))

theorem processRound_eq_of_prefix_eq
    {O : OracleFamily} {a b : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ n, n < t + 1 → a n = b n) :
    processRound O a t old = processRound O b t old := by
  classical
  have hd : PatientMachine.decide O.language a t old =
      PatientMachine.decide O.language b t old := decide_eq_of_prefix_eq h
  simp only [processRound]
  rw [hd]
  rw [leastAvailable_eq_of_prefix_eq O.infinite' h]

theorem run_eq_of_prefix_eq
    {O : OracleFamily} {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    run O a t = run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ]
      rw [ih (fun n hn => h n (hn.trans (Nat.lt_succ_self t)))]
      exact processRound_eq_of_prefix_eq h

theorem output_eq_of_prefix_eq
    {O : OracleFamily} {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    output O a t = output O b t := by
  unfold output
  rw [run_eq_of_prefix_eq h]

noncomputable def onlineGenerator (O : OracleFamily) : OnlineGenerator :=
  fun t xs _ => output O (extendPrefix t xs) t

theorem follows_onlineGenerator (O : OracleFamily) (input : Stream) :
    Follows (onlineGenerator O) input (output O input) := by
  intro t
  apply output_eq_of_prefix_eq
  intro n hn
  simp [onlineGenerator, extendPrefix, hn]

end PatientBridge
end Stage3Case025
