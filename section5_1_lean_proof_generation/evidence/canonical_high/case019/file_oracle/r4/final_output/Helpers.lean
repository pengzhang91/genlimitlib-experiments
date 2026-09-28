import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set

namespace Stage3Case019Proof

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

noncomputable def richFirstLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  (↑(omissionMarkerFinset q) : Set ℤ) ∪
    positiveIntegers ∪ negativeCode '' S

theorem richFirstLanguage_mem (q : ℕ) (S : Set ℕ) :
    richFirstLanguage q S ∈ finiteOmissionClass q := by
  left
  constructor
  · exact fun z hz => Or.inl (Or.inl hz)
  · refine ⟨0, ?_⟩
    intro z hz
    left
    right
    have hzRange : z ∈ Set.range positiveCode := by
      simpa [positiveTail] using hz
    rw [range_positiveCode] at hzRange
    exact hzRange

theorem richFirstLanguage_injective (q : ℕ) :
    Function.Injective (richFirstLanguage q) := by
  intro S T hST
  ext n
  have hneg : negativeCode n < 0 := negativeCode_mem n
  have hnotMarker : negativeCode n ∉ omissionMarkerFinset q :=
    negativeCode_not_marker q n
  have hnotPositive : negativeCode n ∉ positiveIntegers := by
    exact Int.not_lt_of_ge (Int.le_of_lt hneg)
  have hS : negativeCode n ∈ richFirstLanguage q S ↔ n ∈ S := by
    change negativeCode n ∈
      ((↑(omissionMarkerFinset q) : Set ℤ) ∪ positiveIntegers) ∪
        negativeCode '' S ↔ n ∈ S
    constructor
    · rintro ((hm | hp) | ⟨m, hm, heq⟩)
      · exact False.elim (hnotMarker hm)
      · exact False.elim (hnotPositive hp)
      · exact (negativeCode_injective heq).symm ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hT : negativeCode n ∈ richFirstLanguage q T ↔ n ∈ T := by
    change negativeCode n ∈
      ((↑(omissionMarkerFinset q) : Set ℤ) ∪ positiveIntegers) ∪
        negativeCode '' T ↔ n ∈ T
    constructor
    · rintro ((hm | hp) | ⟨m, hm, heq⟩)
      · exact False.elim (hnotMarker hm)
      · exact False.elim (hnotPositive hp)
      · exact (negativeCode_injective heq).symm ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hS, hST, hT]

theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  letI : Countable {K // K ∈ finiteOmissionClass q} := hcount.to_subtype
  let f : Set ℕ → {K // K ∈ finiteOmissionClass q} :=
    fun S => ⟨richFirstLanguage q S, richFirstLanguage_mem q S⟩
  have hf : Function.Injective f := by
    intro S T h
    exact richFirstLanguage_injective q (congrArg Subtype.val h)
  haveI : Countable (Set ℕ) := hf.countable
  exact powerSet_not_countable ℕ inferInstance

theorem finiteOmissionClass_negative (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬Stage3Case019.SampleFreshGeneratesAfterInput
            input (Stage3Case019.outputAfterInput gen input) K := by
  intro gen
  by_contra hnone
  push_neg at hnone
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  exact hnone K hK input hinput

end Stage3Case019Proof

namespace Stage3Case019Proof

open GenLimit

open GenLimit
open GenLimit.PatientMachine

private theorem basicSample_eq_of_eq_on_lt
    {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem consistent_iff_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    Consistent C a t i ↔ Consistent C b t i := by
  rw [Consistent, Consistent, basicSample_eq_of_eq_on_lt h]

private theorem recursiveCritical_iff_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    ∀ i, RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [RecursiveCritical] using
            consistent_iff_of_eq_on_lt C h (i := 0)
      | succ i =>
          simp only [RecursiveCritical]
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨(consistent_iff_of_eq_on_lt C h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hcon, hsub⟩
            refine ⟨(consistent_iff_of_eq_on_lt C h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (by omega)).mp hjcrit)

end Stage3Case019Proof

namespace Stage3Case019Proof

open GenLimit
open GenLimit.PatientMachine

private theorem consistentIndices_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    consistentIndices C a t scope = consistentIndices C b t scope := by
  classical
  ext i
  simp only [mem_consistentIndices]
  exact and_congr_right fun _ => consistent_iff_of_eq_on_lt C h

private theorem criticalIndices_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    criticalIndices C a t scope = criticalIndices C b t scope := by
  classical
  ext i
  simp only [mem_criticalIndices]
  exact and_congr_right fun _ => recursiveCritical_iff_of_eq_on_lt C h i

private theorem survivingCriticalIndices_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    survivingCriticalIndices C a t scope =
      survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [mem_survivingCriticalIndices]
  have ht : ∀ k, k < t → a k = b k := fun k hk => h k (by omega)
  exact and_congr_right fun _ =>
    and_congr (recursiveCritical_iff_of_eq_on_lt C ht i)
      (recursiveCritical_iff_of_eq_on_lt C h i)

private theorem highestCritical_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    highestCritical C a t scope fallback =
      highestCritical C b t scope fallback := by
  classical
  rw [highestCritical, highestCritical,
    criticalIndices_eq_of_eq_on_lt C h]

private theorem highestSurvivor_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    highestSurvivor C a t scope fallback =
      highestSurvivor C b t scope fallback := by
  classical
  rw [highestSurvivor, highestSurvivor,
    survivingCriticalIndices_eq_of_eq_on_lt C h]

private theorem lowestConsistentInScope_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    lowestConsistentInScope C a t scope fallback =
      lowestConsistentInScope C b t scope fallback := by
  classical
  rw [lowestConsistentInScope, lowestConsistentInScope,
    consistentIndices_eq_of_eq_on_lt C h]

private theorem lowestConsistent_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    lowestConsistent C a t fallback =
      lowestConsistent C b t fallback := by
  classical
  have hall : (∃ i, Consistent C a t i) ↔ ∃ i, Consistent C b t i := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (consistent_iff_of_eq_on_lt C h).mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (consistent_iff_of_eq_on_lt C h).mpr hi⟩
  unfold lowestConsistent
  by_cases ha : ∃ i, Consistent C a t i
  · have hb := hall.mp ha
    rw [dif_pos ha, dif_pos hb]
    apply Nat.le_antisymm
    · exact Nat.find_min' ha
        ((consistent_iff_of_eq_on_lt C h).mpr (Nat.find_spec hb))
    · exact Nat.find_min' hb
        ((consistent_iff_of_eq_on_lt C h).mp (Nat.find_spec ha))
  · have hb : ¬∃ i, Consistent C b t i := fun hb => ha (hall.mpr hb)
    rw [dif_neg ha, dif_neg hb]

private theorem stableDecision_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : State) (h : ∀ k, k < t + 1 → a k = b k) :
    stableDecision C a t old = stableDecision C b t old := by
  classical
  unfold stableDecision
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp only [dif_pos hwait]
    rw [highestCritical_eq_of_eq_on_lt C h]
  · simp only [dif_neg hwait]

private theorem backtrackDecision_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : State) (h : ∀ k, k < t + 1 → a k = b k) :
    backtrackDecision C a t old = backtrackDecision C b t old := by
  classical
  have hc := consistentIndices_eq_of_eq_on_lt C h (scope := old.scope)
  have hs := survivingCriticalIndices_eq_of_eq_on_lt C h (scope := old.scope)
  have hhigh := highestSurvivor_eq_of_eq_on_lt C h
    (scope := old.scope) (fallback := old.focus)
  have hlow := lowestConsistentInScope_eq_of_eq_on_lt C h
    (scope := old.scope) (fallback := old.focus)
  have hglobal := lowestConsistent_eq_of_eq_on_lt C h (fallback := old.focus)
  have hall : (∃ j, Consistent C a (t + 1) j) ↔
      ∃ j, Consistent C b (t + 1) j := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (consistent_iff_of_eq_on_lt C h).mp hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (consistent_iff_of_eq_on_lt C h).mpr hj⟩
  unfold backtrackDecision
  by_cases hscope : (consistentIndices C a (t + 1) old.scope).Nonempty
  · have hscope' : (consistentIndices C b (t + 1) old.scope).Nonempty := by
      rwa [← hc]
    simp only [dif_pos hscope, dif_pos hscope']
    by_cases hsurv : (survivingCriticalIndices C a t old.scope).Nonempty
    · have hsurv' : (survivingCriticalIndices C b t old.scope).Nonempty := by
        rwa [← hs]
      simp only [if_pos hsurv, if_pos hsurv']
      rw [hhigh]
    · have hsurv' : ¬(survivingCriticalIndices C b t old.scope).Nonempty := by
        rwa [← hs]
      simp only [if_neg hsurv, if_neg hsurv']
      rw [hlow]
  · have hscope' : ¬(consistentIndices C b (t + 1) old.scope).Nonempty := by
      rwa [← hc]
    simp only [dif_neg hscope, dif_neg hscope']
    rw [hglobal]
    by_cases ha : ∃ j, Consistent C a (t + 1) j
    · simp only [dif_pos ha, dif_pos (hall.mp ha)]
    · simp only [dif_neg ha, dif_neg (fun hb => ha (hall.mpr hb))]

private theorem decide_eq_of_eq_on_lt
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : State) (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.decide C a t old = PatientMachine.decide C b t old := by
  classical
  have hcon := consistent_iff_of_eq_on_lt C h (i := old.focus)
  unfold PatientMachine.decide
  by_cases ha : Consistent C a (t + 1) old.focus
  · rw [if_pos ha, if_pos (hcon.mp ha)]
    exact stableDecision_eq_of_eq_on_lt C old h
  · rw [if_neg ha, if_neg (fun hb => ha (hcon.mpr hb))]
    exact backtrackDecision_eq_of_eq_on_lt C old h

end Stage3Case019Proof

namespace Stage3Case019Proof

open GenLimit
open GenLimit.Generic
open GenLimit.PatientMachine

private theorem leastAvailable_eq_of_eq_on_lt
    (O : OracleFamily) {a b : ℕ → ℕ} {t focus : ℕ} {used : Finset ℕ}
    (h : ∀ k, k < t → a k = b k) :
    leastAvailable O.language O.infinite' a t used focus =
      leastAvailable O.language O.infinite' b t used focus := by
  classical
  have hs := basicSample_eq_of_eq_on_lt h
  apply Nat.le_antisymm
  · apply leastAvailable_minimal
    have hb := leastAvailable_spec O.language O.infinite' b t used focus
    unfold Available at hb ⊢
    rwa [hs]
  · apply leastAvailable_minimal
    have ha := leastAvailable_spec O.language O.infinite' a t used focus
    unfold Available at ha ⊢
    rwa [hs] at ha

private theorem processRound_eq_of_eq_on_lt
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : State) (h : ∀ k, k < t + 1 → a k = b k) :
    processRound O a t old = processRound O b t old := by
  classical
  have hd := decide_eq_of_eq_on_lt O.language old h
  have hx := leastAvailable_eq_of_eq_on_lt O
    (used := old.used) (focus := (decide O.language a t old).focus) h
  unfold processRound
  simp only
  rw [hd] at hx ⊢
  rw [hx]

private theorem run_eq_of_eq_on_lt
    (O : OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ k, k < t → a k = b k) → run O a t = run O b t := by
  intro t
  induction t with
  | zero =>
      intro _
      rfl
  | succ t ih =>
      intro h
      rw [run_succ, run_succ, ih (fun k hk => h k (by omega))]
      exact processRound_eq_of_eq_on_lt O _ h

private theorem patientOutput_eq_of_eq_on_lt
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  unfold PatientMachine.output
  rw [run_eq_of_eq_on_lt O (t + 1) h]

noncomputable def semanticPatientGenerator
    (O : OracleFamily) : Generator ℕ
  | 0, _ => 0
  | t + 1, history =>
      PatientMachine.output O
        (fun k => if hk : k < t + 1 then history ⟨k, hk⟩ else 0) t

theorem semanticPatientGenerator_outputAfterInput
    (O : OracleFamily) (input : Stream ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (semanticPatientGenerator O) input t =
      PatientMachine.output O input t := by
  apply patientOutput_eq_of_eq_on_lt O
  intro k hk
  simp [Stage3Case019.outputAfterInput, semanticPatientGenerator, hk]

end Stage3Case019Proof
