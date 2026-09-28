import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set
open Stage3Case019

namespace Case019

open GenLimit

noncomputable def oracleOfFamily
    (family : GenLimit.Generic.LanguageFamily ℕ)
    (hInfinite : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by classical exact if x ∈ family i then true else false
  query_spec i x := by classical simp

private theorem sample_congr {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext z
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

private theorem consistent_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_congr h]

private theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using consistent_congr C h (i := 0)
      | succ n =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_congr C h]
          constructor <;> rintro ⟨hc, hall⟩ <;> refine ⟨hc, ?_⟩
          · intro j hj hjc
            exact hall j hj ((ih j (by omega)).mpr hjc)
          · intro j hj hjc
            exact hall j hj ((ih j (by omega)).mp hjc)

private theorem consistentIndices_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t scope : ℕ)
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_congr C h]

private theorem criticalIndices_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t scope : ℕ)
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_congr C h i]

private theorem survivingCriticalIndices_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t scope : ℕ)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr C (fun k hk => h k (Nat.lt.step hk)) i,
    recursiveCritical_congr C h i]

private theorem highestCritical_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t scope fallback : ℕ)
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr C t scope h]

private theorem highestSurvivor_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t scope fallback : ℕ)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr C t scope h]

private theorem lowestConsistentInScope_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t scope fallback : ℕ)
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr C t scope h]

private theorem lowestConsistent_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t fallback : ℕ)
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  have he : (∃ i, GenLimit.Consistent C a t i) ↔
      ∃ i, GenLimit.Consistent C b t i := by
    apply exists_congr
    intro i
    exact consistent_congr C h
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb := he.mp ha
    simp only [ha, hb, dif_pos]
    congr 1
    funext i
    apply propext
    exact consistent_congr C h
  · have hb : ¬ ∃ i, GenLimit.Consistent C b t i := fun hb => ha (he.mpr hb)
    simp [ha, hb]

private theorem backtrackDecision_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.backtrackDecision
  rw [consistentIndices_congr C (t + 1) old.scope h]
  by_cases hcon : (GenLimit.PatientMachine.consistentIndices C b (t + 1) old.scope).Nonempty
  · simp only [hcon, dif_pos]
    rw [survivingCriticalIndices_congr C t old.scope h]
    by_cases hsurv : (GenLimit.PatientMachine.survivingCriticalIndices C b t old.scope).Nonempty
    · simp only [hsurv, if_pos]
      rw [highestSurvivor_congr C t old.scope old.focus h]
    · rw [lowestConsistentInScope_congr C (t + 1) old.scope old.focus h]
      simp [hsurv]
  · simp only [hcon, dif_neg]
    rw [lowestConsistent_congr C (t + 1) old.focus h]
    have he : (∃ j, GenLimit.Consistent C a (t + 1) j) ↔
        ∃ j, GenLimit.Consistent C b (t + 1) j := by
      apply exists_congr
      intro j
      exact consistent_congr C h
    by_cases hb : ∃ j, GenLimit.Consistent C b (t + 1) j
    · have ha := he.mpr hb
      simp [ha, hb]
    · have ha : ¬ ∃ j, GenLimit.Consistent C a (t + 1) j := fun ha => hb (he.mp ha)
      simp [ha, hb]

private theorem stableDecision_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  unfold GenLimit.PatientMachine.stableDecision
  split
  · dsimp
    rw [highestCritical_congr C (t + 1) (old.scope + 1) old.focus h]
  · rfl

private theorem decide_congr
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.decide O.language a t old =
      GenLimit.PatientMachine.decide O.language b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  have hc := consistent_congr O.language h (i := old.focus)
  by_cases ha : GenLimit.Consistent O.language a (t + 1) old.focus
  · have hb := hc.mp ha
    simp only [ha, hb, if_pos]
    exact stableDecision_congr O.language t old h
  · have hb : ¬ GenLimit.Consistent O.language b (t + 1) old.focus :=
      fun hb => ha (hc.mpr hb)
    simp only [ha, hb, if_neg]
    exact backtrackDecision_congr O.language t old h

private theorem leastAvailable_congr
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (used : Finset ℕ) (focus : ℕ)
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  simp only [GenLimit.PatientMachine.Available]
  rw [sample_congr h]

private theorem patient_run_congr
    (O : OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ k, k < t → a k = b k) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      have hr := ih (fun k hk => h k (Nat.lt.step hk))
      rw [hr]
      have hd := decide_congr O t (GenLimit.PatientMachine.run O b t) h
      have hl (focus : ℕ) := leastAvailable_congr O (t + 1)
        (GenLimit.PatientMachine.run O b t).used focus h
      simp only [GenLimit.PatientMachine.processRound]
      rw [hd]
      simp_rw [hl]

private theorem patient_output_congr
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k ≤ t → a k = b k) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  rw [GenLimit.PatientMachine.output_eq_leastAvailable,
      GenLimit.PatientMachine.output_eq_leastAvailable]
  have hr := patient_run_congr O t (fun k hk => h k (Nat.le_of_lt hk))
  rw [hr]
  have hd := decide_congr O t (GenLimit.PatientMachine.run O b t)
    (fun k hk => h k (Nat.le_of_lt_succ hk))
  rw [hd]
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  simp only [GenLimit.PatientMachine.Available]
  rw [sample_congr (fun k hk => h k (Nat.le_of_lt_succ hk))]

noncomputable def patientGenerator (O : OracleFamily) : Generator ℕ :=
  fun n xs =>
    match n with
    | 0 => 0
    | t + 1 =>
        GenLimit.PatientMachine.output O
          (GenLimit.Generic.historyThenFallback (List.ofFn xs) 0) t

private theorem outputAfterInput_patientGenerator
    (O : OracleFamily) (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (patientGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  apply patient_output_congr O t
  intro k hk
  change GenLimit.Generic.historyThenFallback
      (List.ofFn (fun i : Fin (t + 1) => input i)) 0 k = input k
  unfold GenLimit.Generic.historyThenFallback
  rw [dif_pos]
  · rw [List.get_ofFn]
    rfl
  · simpa only [List.length_ofFn] using Nat.lt_succ_iff.mpr hk


end Case019

namespace Case019

private theorem contamination_of_levelPresentation
    {input : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration input K := by
  refine ⟨h.1, ?_, ?_⟩
  · exact (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective h.1).mpr
      ((GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le _ _ q).mp h.2.2).1
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty

theorem stage3_countable_eventual_novel
    (q : ℕ) (family : LanguageFamily ℕ)
    (hInfinite : ∀ i, (family i).Infinite) :
    ∃ gen : Generator ℕ,
      ∀ i (input : Stream ℕ),
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input (family i) q →
          GenLimit.NovelGeneratesInLimit input (outputAfterInput gen input) (family i) := by
  let O := oracleOfFamily family hInfinite
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hpresentation
  have hcontam := contamination_of_levelPresentation hpresentation
  obtain ⟨j, hjbase, hjpresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  obtain ⟨⟨Tgen, hTgen⟩, _hdensity⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity E input hjpresents
  have hextra : (E.language j \ family i).Finite := by
    change (GenLimit.InfiniteContamination.finiteExpansionLanguage O j \ family i).Finite
    rw [← hjbase]
    exact (GenLimit.InfiniteContamination.finiteExpansion_symmetricDifference_finite
      (O.language (GenLimit.InfiniteContamination.finiteExpansionBaseIndex j))
      (Finset.equivBitIndices (GenLimit.InfiniteContamination.finiteExpansionCode j).2.1)
      (Finset.equivBitIndices (GenLimit.InfiniteContamination.finiteExpansionCode j).2.2)).1
  have hextraRange : (E.language j \ family i) ⊆ Set.range input := by
    rw [hjpresents]
    exact fun x hx => hx.1
  obtain ⟨Tseen, hTseen⟩ := GenLimit.Generic.finset_eventually_subset_sample
    (GenLimit.InfiniteContamination.stream_presents_range input)
    hextra.toFinset (by
      intro x hx
      exact hextraRange ((Set.Finite.mem_toFinset hextra).mp hx))
  refine ⟨max Tgen Tseen, ?_⟩
  intro t ht
  have hgen := hTgen t ((Nat.le_max_left _ _).trans ht)
  have hseen := hTseen
  rw [outputAfterInput_patientGenerator E input t]
  refine ⟨?_, ?_, ?_⟩
  · by_contra hnot
    have hbad : GenLimit.PatientMachine.output E input t ∈ hextra.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hgen.1, hnot⟩
    have hmem := GenLimit.Generic.sample_mono
      ((Nat.le_max_right _ _).trans ht) (hseen hbad)
    rw [GenLimit.Generic.mem_sample_iff] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact hgen.2.1 s (Nat.le_of_lt hs) heq
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact hgen.2.1 s (Nat.le_of_lt_succ hs) heq
  · intro s hs
    rw [outputAfterInput_patientGenerator E input s]
    exact hgen.2.2 s hs

end Case019

namespace Case019

theorem stage3_adjacent_level_impossibility (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput input (outputAfterInput gen input) K := by
  intro gen
  by_contra hcounter
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hpresentation
  have hsuccess : SampleFreshGeneratesAfterInput
      input (outputAfterInput gen input) K := by
    by_contra hfail
    exact hcounter ⟨K, hK, input, hpresentation, hfail⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt,
    GenLimit.NoiseLossFeedback.observedThrough] using hsuccess

end Case019
