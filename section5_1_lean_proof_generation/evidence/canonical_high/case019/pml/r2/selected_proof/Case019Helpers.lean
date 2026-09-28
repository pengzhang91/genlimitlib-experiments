import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open GenLimit GenLimit.Generic

namespace Case019Helpers

theorem sample_eq_of_prefix {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

theorem consistent_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    Consistent C a t i ↔ Consistent C b t i := by
  rw [Consistent, Consistent]
  rw [sample_eq_of_prefix h]

theorem recursiveCritical_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [RecursiveCritical] using
            consistent_eq_of_prefix (C := C) (i := 0) h
      | succ i =>
          simp only [RecursiveCritical]
          rw [consistent_eq_of_prefix (C := C) (i := i + 1) h]
          constructor
          · rintro ⟨hc, hsub⟩
            exact ⟨hc, fun j hj hjc =>
              hsub j hj ((ih j (by omega)).mpr hjc)⟩
          · rintro ⟨hc, hsub⟩
            exact ⟨hc, fun j hj hjc =>
              hsub j hj ((ih j (by omega)).mp hjc)⟩


theorem consistentIndices_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    PatientMachine.consistentIndices C a t scope =
      PatientMachine.consistentIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_consistentIndices]
  rw [consistent_eq_of_prefix (C := C) (i := i) h]

theorem criticalIndices_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    PatientMachine.criticalIndices C a t scope =
      PatientMachine.criticalIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_eq_of_prefix (C := C) (i := i) h]

theorem survivingCriticalIndices_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.survivingCriticalIndices C a t scope =
      PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_eq_of_prefix (C := C) (i := i)
      (fun k hk => h k (lt_trans hk (Nat.lt_succ_self t)))]
  rw [recursiveCritical_eq_of_prefix (C := C) (i := i) h]

theorem highestCritical_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    PatientMachine.highestCritical C a t scope fallback =
      PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold PatientMachine.highestCritical
  rw [criticalIndices_eq_of_prefix h]

theorem highestSurvivor_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.highestSurvivor C a t scope fallback =
      PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_prefix h]

theorem lowestConsistentInScope_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    PatientMachine.lowestConsistentInScope C a t scope fallback =
      PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_prefix h]

theorem lowestConsistent_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    PatientMachine.lowestConsistent C a t fallback =
      PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold PatientMachine.lowestConsistent
  have hp : (∃ i, Consistent C a t i) ↔ ∃ i, Consistent C b t i := by
    constructor <;> rintro ⟨i, hi⟩
    · exact ⟨i, (consistent_eq_of_prefix h).mp hi⟩
    · exact ⟨i, (consistent_eq_of_prefix h).mpr hi⟩
  split
  · rename_i ha
    rw [dif_pos (hp.mp ha)]
    apply Nat.find_congr'
    intro i
    exact consistent_eq_of_prefix h
  · rename_i ha
    rw [dif_neg (fun hb => ha (hp.mpr hb))]

theorem exists_consistent_iff_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    (∃ i, Consistent C a t i) ↔ ∃ i, Consistent C b t i := by
  constructor <;> rintro ⟨i, hi⟩
  · exact ⟨i, (consistent_eq_of_prefix h).mp hi⟩
  · exact ⟨i, (consistent_eq_of_prefix h).mpr hi⟩

theorem backtrackDecision_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.backtrackDecision C a t old =
      PatientMachine.backtrackDecision C b t old := by

  classical
  simp only [PatientMachine.backtrackDecision,
    consistentIndices_eq_of_prefix h,
    survivingCriticalIndices_eq_of_prefix h,
    highestSurvivor_eq_of_prefix h,
    lowestConsistentInScope_eq_of_prefix h,
    lowestConsistent_eq_of_prefix h,
    exists_consistent_iff_of_prefix h]

theorem stableDecision_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.stableDecision C a t old =
      PatientMachine.stableDecision C b t old := by

  classical
  simp only [PatientMachine.stableDecision,
    highestCritical_eq_of_prefix h]

theorem decide_eq_of_prefix
    {C : LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.decide C a t old =
      PatientMachine.decide C b t old := by
  classical
  unfold PatientMachine.decide
  rw [consistent_eq_of_prefix (C := C) (i := old.focus) h]
  split
  · exact stableDecision_eq_of_prefix old h
  · exact backtrackDecision_eq_of_prefix old h

theorem leastAvailable_eq_of_prefix
    {C : LanguageFamily} (hInfinite : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t used focus}
    (h : ∀ k, k < t → a k = b k) :
    PatientMachine.leastAvailable C hInfinite a t used focus =
      PatientMachine.leastAvailable C hInfinite b t used focus := by
  classical
  unfold PatientMachine.leastAvailable
  have hs := sample_eq_of_prefix h
  congr 1
  funext x
  simp only [PatientMachine.Available]
  rw [hs]

theorem processRound_eq_of_prefix
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.processRound O a t old =
      PatientMachine.processRound O b t old := by

  classical
  simp only [PatientMachine.processRound,
    decide_eq_of_prefix old h,
    leastAvailable_eq_of_prefix O.infinite' h]

theorem run_eq_of_prefix
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    PatientMachine.run O a t = PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      rw [ih (fun k hk => h k (lt_trans hk (Nat.lt_succ_self t)))]
      exact processRound_eq_of_prefix O _ h

theorem patient_output_eq_of_prefix
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  unfold PatientMachine.output
  rw [run_eq_of_prefix O h]


noncomputable def extendHistory {n : ℕ} (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if hk : k < n then xs ⟨k, hk⟩ else 0

noncomputable def patientGenerator (O : OracleFamily) : Generic.Generator ℕ :=
  fun n xs =>
    match n with
    | 0 => 0
    | t + 1 => PatientMachine.output O (extendHistory xs) t

theorem extendHistory_prefix {n : ℕ} (xs : Fin n → ℕ) {k : ℕ}
    (hk : k < n) :
    extendHistory xs k = xs ⟨k, hk⟩ := by
  simp [extendHistory, hk]

theorem output_patientGenerator
    (O : OracleFamily) (input : ℕ → ℕ) (t : ℕ) :
    Generic.output (patientGenerator O) input (t + 1) =
      PatientMachine.output O input t := by
  change PatientMachine.output O
      (extendHistory (fun i : Fin (t + 1) => input i)) t = _
  apply patient_output_eq_of_prefix O
  intro k hk
  simp [extendHistory, hk]

theorem outputAfterInput_patientGenerator
    (O : OracleFamily) (input : ℕ → ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) input =
      PatientMachine.output O input := by
  funext t
  exact output_patientGenerator O input t

noncomputable def oracleOfFamily
    (family : Generic.LanguageFamily ℕ)
    (hInfinite : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

theorem finiteNoiseFiniteOmission_of_injectiveValueContaminated
    {input : Generic.Stream ℕ} {K : Set ℕ} {q : ℕ}
    (h : Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration input K := by
  refine ⟨h.1, ?_, ?_⟩
  · exact
      (InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
        h.1).2
        ((Generic.setDifferenceAtMost_iff_finite_ncard_le
          (Set.range input) K q).1 h.2.2).1
  · rw [InfiniteContamination.FiniteOmissions]
    exact Set.finite_empty.subset fun x hx =>
      hx.2 (h.2.1 hx.1)


end Case019Helpers

namespace Case019Helpers

open scoped Topology

noncomputable def relativeRatio (A K : Set ℕ) (n : ℕ) : ℝ :=
  (PatientScope.prefixCount A n : ℝ) /
    (PatientScope.prefixCount K n : ℝ)

theorem relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ relativeRatio A K n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem relativeRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    relativeRatio A K n ≤ 1 := by
  by_cases hzero : PatientScope.prefixCount K n = 0
  · simp [relativeRatio, hzero]
  · have hpos : (0 : ℝ) < PatientScope.prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [relativeRatio, div_le_one hpos]
    exact_mod_cast PatientScope.prefixCount_mono hAK n

theorem liminf_le_of_eventually_le_add_tendsto_zero
    (source output error : ℕ → ℝ)
    (hsourceNonneg : ∀ n, 0 ≤ source n)
    (hsourceLe : ∀ n, source n ≤ 1)
    (houtputNonneg : ∀ n, 0 ≤ output n)
    (houtputLe : ∀ n, output n ≤ 1)
    (herror : Tendsto error atTop (nhds 0))
    (hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n) :
    liminf source atTop ≤ liminf output atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop houtputLe)
    (isBoundedUnder_of ⟨0, houtputNonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrsource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrsource
      (isBoundedUnder_of ⟨0, hsourceNonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hcompare] with n hr he hc
  linarith

theorem relativeLowerDensity_transfer_finite
    {source output sourceTarget outputTarget : Set ℕ}
    (hsourceSub : source ⊆ sourceTarget)
    (houtputSub : output ⊆ outputTarget)
    (hTargetSub : outputTarget ⊆ sourceTarget)
    (hSourceDiff : (source \ output).Finite)
    (hOutputTargetInfinite : outputTarget.Infinite) :
    PatientScope.relativeLowerDensity source sourceTarget ≤
      PatientScope.relativeLowerDensity output outputTarget := by
  let c := hSourceDiff.toFinset.card
  let error : ℕ → ℝ := fun n =>
    (c : ℝ) / (PatientScope.prefixCount outputTarget n : ℝ)
  have hdenom : Tendsto
      (fun n => (PatientScope.prefixCount outputTarget n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (PatientScope.tendsto_prefixCount_atTop hOutputTargetInfinite)
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hdenom
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < PatientScope.prefixCount outputTarget n :=
    (PatientScope.tendsto_prefixCount_atTop hOutputTargetInfinite).eventually
      (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      relativeRatio source sourceTarget n ≤
        relativeRatio output outputTarget n + error n := by
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < PatientScope.prefixCount outputTarget n := by
      exact_mod_cast hn
    have hsourceCount :
        PatientScope.prefixCount source n ≤
          PatientScope.prefixCount output n + c := by
      classical
      let sourceOnly := PatientScope.prefixFinset source n \ PatientScope.prefixFinset output n
      have hsub : PatientScope.prefixFinset source n ⊆
          PatientScope.prefixFinset output n ∪ sourceOnly := by
        intro x hx
        by_cases ho : x ∈ PatientScope.prefixFinset output n
        · exact Finset.mem_union_left _ ho
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, ho⟩)
      have hcard := (Finset.card_le_card hsub).trans
        (Finset.card_union_le (PatientScope.prefixFinset output n) sourceOnly)
      have hdiffCard : sourceOnly.card ≤ c := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Set.Finite.mem_toFinset]
        exact ⟨(PatientScope.mem_prefixFinset.mp hx.1).2,
          fun hxo => hx.2 (PatientScope.mem_prefixFinset.mpr
            ⟨(PatientScope.mem_prefixFinset.mp hx.1).1, hxo⟩)⟩
      exact hcard.trans (Nat.add_le_add_left hdiffCard _)
    have htargetCount :
        PatientScope.prefixCount outputTarget n ≤
          PatientScope.prefixCount sourceTarget n :=
      PatientScope.prefixCount_mono hTargetSub n
    have hsourceR :
        (PatientScope.prefixCount source n : ℝ) ≤
          PatientScope.prefixCount output n + c := by exact_mod_cast hsourceCount
    have htargetR :
        (PatientScope.prefixCount outputTarget n : ℝ) ≤
          PatientScope.prefixCount sourceTarget n := by exact_mod_cast htargetCount
    dsimp [relativeRatio, error]
    have hsourceDenom : (0 : ℝ) < PatientScope.prefixCount sourceTarget n :=
      lt_of_lt_of_le hnR htargetR
    calc
      (PatientScope.prefixCount source n : ℝ) /
          PatientScope.prefixCount sourceTarget n
          ≤ (PatientScope.prefixCount source n : ℝ) /
              PatientScope.prefixCount outputTarget n := by
              rw [div_le_div_iff₀ hsourceDenom hnR]
              have hnum : (0 : ℝ) ≤
                  PatientScope.prefixCount source n := Nat.cast_nonneg _
              nlinarith
      _ ≤ ((PatientScope.prefixCount output n : ℝ) + (c : ℝ)) /
              (PatientScope.prefixCount outputTarget n : ℝ) := by
              exact div_le_div_of_nonneg_right hsourceR hnR.le
      _ = (PatientScope.prefixCount output n : ℝ) /
              PatientScope.prefixCount outputTarget n +
            (c : ℝ) / PatientScope.prefixCount outputTarget n := by
              push_cast
              rw [add_div]
  unfold PatientScope.relativeLowerDensity
  exact liminf_le_of_eventually_le_add_tendsto_zero
    (relativeRatio source sourceTarget)
    (relativeRatio output outputTarget) error
    (relativeRatio_nonneg source sourceTarget)
    (relativeRatio_le_one hsourceSub)
    (relativeRatio_nonneg output outputTarget)
    (relativeRatio_le_one houtputSub)
    herror hcompare

theorem patientOutput_injective (O : OracleFamily) (input : ℕ → ℕ) :
    Function.Injective (PatientMachine.output O input) := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact False.elim ((PatientMachine.output_ne_of_lt O input hlt) hst)
  · exact heq
  · exact False.elim ((PatientMachine.output_ne_of_lt O input hgt) hst.symm)

theorem eventually_patientOutput_not_mem_finite
    (O : OracleFamily) (input : ℕ → ℕ) {F : Set ℕ} (hF : F.Finite) :
    ∃ T, ∀ t, T ≤ t → PatientMachine.output O input t ∉ F := by
  have hpre : ((PatientMachine.output O input) ⁻¹' F).Finite :=
    hF.preimage (Set.injOn_of_injective (patientOutput_injective O input))
  obtain ⟨T, hT⟩ := Finset.exists_nat_subset_range hpre.toFinset
  refine ⟨T, ?_⟩
  intro t ht hmem
  have htmem : t ∈ hpre.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hmem
  have : t < T := by simpa using hT htmem
  omega

theorem finiteExpansion_diff_base_finite
    (O : OracleFamily) (j : ℕ) :
    ((InfiniteContamination.finiteExpansionOracleFamily O).language j \
      O.language (InfiniteContamination.finiteExpansionBaseIndex j)).Finite := by
  let data := InfiniteContamination.finiteExpansionCode j
  have h := (InfiniteContamination.finiteExpansion_symmetricDifference_finite
    (O.language data.1)
    (Finset.equivBitIndices data.2.1)
    (Finset.equivBitIndices data.2.2)).1
  simpa [InfiniteContamination.finiteExpansionOracleFamily_language,
    InfiniteContamination.finiteExpansionLanguage,
    InfiniteContamination.finiteExpansionBaseIndex, data] using h

end Case019Helpers

namespace Case019Helpers

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

noncomputable def sweepCode (positive : Bool) (k : ℕ) : ℤ :=
  if positive then positiveCode k else negativeCode k

theorem sweepCode_injective (positive : Bool) :
    Function.Injective (sweepCode positive) := by
  intro a b hab
  cases positive
  · exact negativeCode_injective (by simpa [sweepCode] using hab)
  · exact positiveCode_injective (by simpa [sweepCode] using hab)

private theorem exists_freshSweep_index
    (positive : Bool) {n : ℕ} (xs : Fin n → ℤ)
    (previous : Finset ℤ) (hprevious : previous.card ≤ n) :
    ∃ k < 2 * n + 1,
      sweepCode positive k ∉ Generic.sequenceSample xs ∪ previous := by
  classical
  let forbidden := Generic.sequenceSample xs ∪ previous
  let candidates := Finset.range (2 * n + 1)
  let blocked := candidates.filter fun k => sweepCode positive k ∈ forbidden
  have hsample : (Generic.sequenceSample xs).card ≤ n := by
    letI : DecidableEq ℤ := Classical.decEq ℤ
    rw [Generic.sequenceSample]
    calc
      (Finset.univ.image xs).card ≤ Finset.univ.card := Finset.card_image_le
      _ = n := Finset.card_fin n
  have hforbidden : forbidden.card ≤ 2 * n := by
    exact (Finset.card_union_le _ _).trans (by omega)
  have hblocked : blocked.card ≤ forbidden.card := by
    let image := blocked.image (sweepCode positive)
    have himage : image.card = blocked.card :=
      Finset.card_image_iff.mpr fun a _ b _ h => sweepCode_injective positive h
    rw [← himage]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hk).2
  have hcard : blocked.card < candidates.card := by
    have hcand : candidates.card = 2 * n + 1 := by simp [candidates]
    rw [hcand]
    omega
  obtain ⟨k, hkCand, hkNotBlocked⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨k, by simpa [candidates] using hkCand, ?_⟩
  intro hkForbidden
  exact hkNotBlocked (Finset.mem_filter.mpr ⟨hkCand, hkForbidden⟩)

noncomputable def freshSweepOutput
    (q : ℕ) (n : ℕ) (xs : Fin n → ℤ) : ℤ := by
  classical
  let previous : Finset ℤ := Finset.univ.image fun s : Fin n =>
    freshSweepOutput q s
      (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)
  let positive : Bool := decide
    (NoiseLossFeedback.omissionMarkerFinset q ⊆ Generic.sequenceSample xs)
  have hprevious : previous.card ≤ n := by
    dsimp [previous]
    calc
      (Finset.univ.image fun s : Fin n =>
        freshSweepOutput q s
          (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)).card
          ≤ Finset.univ.card := Finset.card_image_le
      _ = n := Finset.card_fin n
  let hexists := exists_freshSweep_index positive xs previous hprevious
  exact sweepCode positive (Nat.find hexists)
termination_by n
decreasing_by all_goals omega

noncomputable def freshSweepGenerator (q : ℕ) : Generic.Generator ℤ :=
  freshSweepOutput q

theorem freshSweepOutput_spec
    (q : ℕ) {n : ℕ} (xs : Fin n → ℤ) :
    let positive : Bool := decide
      (NoiseLossFeedback.omissionMarkerFinset q ⊆ Generic.sequenceSample xs)
    ∃ k < 2 * n + 1,
      freshSweepOutput q n xs = sweepCode positive k ∧
      freshSweepOutput q n xs ∉ Generic.sequenceSample xs ∧
      ∀ s : Fin n,
        freshSweepOutput q n xs ≠
          freshSweepOutput q s
            (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩) := by
  classical
  let previous : Finset ℤ := Finset.univ.image fun s : Fin n =>
    freshSweepOutput q s
      (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)
  let positive : Bool := decide
    (NoiseLossFeedback.omissionMarkerFinset q ⊆ Generic.sequenceSample xs)
  have hprevious : previous.card ≤ n := by
    dsimp [previous]
    calc
      (Finset.univ.image fun s : Fin n =>
        freshSweepOutput q s
          (fun j : Fin s => xs ⟨j, j.isLt.trans s.isLt⟩)).card
          ≤ Finset.univ.card := Finset.card_image_le
      _ = n := Finset.card_fin n
  let hexists := exists_freshSweep_index positive xs previous hprevious
  have hspec := Nat.find_spec hexists
  have hout : freshSweepOutput q n xs =
      sweepCode positive (Nat.find hexists) := by
    rw [freshSweepOutput]
  refine ⟨Nat.find hexists, hspec.1, hout, ?_, ?_⟩
  · rw [hout]
    exact fun h => hspec.2 (Finset.mem_union_left _ h)
  · intro s heq
    apply hspec.2
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, by
      rw [← hout]
      exact heq.symm⟩

end Case019Helpers

namespace Case019Helpers

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

@[simp] theorem balanced_negativeCode (k : ℕ) :
    Stage3Case019.balanced (2 * k + 1) = negativeCode k := by
  simp [Stage3Case019.balanced, negativeCode, Int.negSucc_eq]

@[simp] theorem balanced_positiveCode (k : ℕ) :
    Stage3Case019.balanced (2 * k + 2) = positiveCode k := by
  simp [Stage3Case019.balanced, positiveCode]
  omega

theorem freshSweep_run_spec
    (q : ℕ) (input : ℕ → ℤ) (t : ℕ) :
    ∃ k < 2 * (t + 1) + 1,
      Stage3Case019.outputAfterInput (freshSweepGenerator q) input t =
        sweepCode
          (decide (omissionMarkerFinset q ⊆ Generic.sample input (t + 1))) k ∧
      Stage3Case019.outputAfterInput (freshSweepGenerator q) input t ∉
        Generic.sample input (t + 1) ∧
      ∀ s < t,
        Stage3Case019.outputAfterInput (freshSweepGenerator q) input s ≠
          Stage3Case019.outputAfterInput (freshSweepGenerator q) input t := by
  obtain ⟨k, hk, hout, hfresh, hnew⟩ :=
    freshSweepOutput_spec q (fun j : Fin (t + 1) => input j)
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · simpa [Stage3Case019.outputAfterInput, freshSweepGenerator,
      Generic.sequenceSample_prefix] using hout
  · simpa [Stage3Case019.outputAfterInput, freshSweepGenerator,
      Generic.sequenceSample_prefix] using hfresh
  · intro s hs
    have h := hnew ⟨s + 1, by omega⟩
    simpa [Stage3Case019.outputAfterInput, freshSweepGenerator] using h.symm

theorem freshSweep_output_injective (q : ℕ) (input : ℕ → ℤ) :
    Function.Injective
      (Stage3Case019.outputAfterInput (freshSweepGenerator q) input) := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | heq | hgt
  · obtain ⟨_, _, _, _, hnew⟩ := freshSweep_run_spec q input t
    exact False.elim ((hnew s hlt) hst)
  · exact heq
  · obtain ⟨_, _, _, _, hnew⟩ := freshSweep_run_spec q input s
    exact False.elim ((hnew t hgt) hst.symm)

theorem freshSweep_rank_bound (q : ℕ) (input : ℕ → ℤ) (t : ℕ) :
    ∃ r < 4 * t + 7,
      Stage3Case019.balanced r =
        Stage3Case019.outputAfterInput (freshSweepGenerator q) input t := by
  obtain ⟨k, hk, hout, _, _⟩ := freshSweep_run_spec q input t
  by_cases hpositive :
      omissionMarkerFinset q ⊆ Generic.sample input (t + 1)
  · refine ⟨2 * k + 2, by omega, ?_⟩
    rw [balanced_positiveCode]
    simpa [sweepCode, hpositive] using hout.symm
  · refine ⟨2 * k + 1, by omega, ?_⟩
    rw [balanced_negativeCode]
    simpa [sweepCode, hpositive] using hout.symm

theorem ambient_prefix_counting_of_ranked_outputs
    (output : ℕ → ℤ) (D : Set ℤ) (T : ℕ)
    (hinjective : Function.Injective output)
    (hD : ∀ t, T ≤ t → output t ∈ D)
    (hrank : ∀ t, ∃ r < 4 * t + 7,
      Stage3Case019.balanced r = output t) :
    ∀ n, n ≤ 4 * PatientScope.prefixCount
      (Stage3Case019.balancedRanks D) n + (4 * T + 10) := by
  classical
  let rank : ℕ → ℕ := fun t => Classical.choose (hrank t)
  have hrank_lt : ∀ t, rank t < 4 * t + 7 := fun t =>
    (Classical.choose_spec (hrank t)).1
  have hrank_eq : ∀ t, Stage3Case019.balanced (rank t) = output t := fun t =>
    (Classical.choose_spec (hrank t)).2
  have hrank_injective : Function.Injective rank := by
    intro s t hst
    apply hinjective
    rw [← hrank_eq s, ← hrank_eq t, hst]
  intro n
  let r := (n - 7) / 4
  let times := Finset.Ico T r
  have himageSub : times.image rank ⊆
      PatientScope.prefixFinset (Stage3Case019.balancedRanks D) n := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have htIco := Finset.mem_Ico.mp ht
    apply PatientScope.mem_prefixFinset.mpr
    constructor
    · have hlt := hrank_lt t
      dsimp [r] at htIco
      omega
    · change Stage3Case019.balanced (rank t) ∈ D
      rw [hrank_eq]
      exact hD t htIco.1
  have hcount : r - T ≤ PatientScope.prefixCount
      (Stage3Case019.balancedRanks D) n := by
    have hcard := Finset.card_le_card himageSub
    have himageCard : (times.image rank).card = times.card := by
      exact Finset.card_image_iff.mpr fun a _ b _ hab => hrank_injective hab
    rw [himageCard] at hcard
    simpa [times] using hcard
  dsimp [r] at hcount
  omega

theorem relativeLowerDensity_quarter_of_ambient_counting
    {D K : Set ℕ} (hDK : D ⊆ K) (hK : K.Infinite) (C : ℕ)
    (hcount : ∀ n, n ≤ 4 * PatientScope.prefixCount D n + C) :
    (1 / 4 : ℝ) ≤ PatientScope.relativeLowerDensity D K := by
  let error : ℕ → ℝ := fun n =>
    (C : ℝ) / (4 * (n : ℝ))
  have herror : Tendsto error atTop (nhds 0) := by
    have hdenom : Tendsto (fun n : ℕ => 4 * (n : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num)
        tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hdenom
  have hpositiveK : ∀ᶠ n : ℕ in atTop,
      0 < PatientScope.prefixCount K n :=
    (PatientScope.tendsto_prefixCount_atTop hK).eventually
      (eventually_gt_atTop 0)
  have hnpositive : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hcompare : ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) ≤
        (PatientScope.prefixCount D n : ℝ) /
          (PatientScope.prefixCount K n : ℝ) + error n := by
    filter_upwards [hpositiveK, hnpositive] with n hnK hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hnKR : (0 : ℝ) < PatientScope.prefixCount K n := by exact_mod_cast hnK
    have hKle : PatientScope.prefixCount K n ≤ n := by
      classical
      unfold PatientScope.prefixCount
      calc
        (PatientScope.prefixFinset K n).card ≤ (Finset.range n).card := by
          apply Finset.card_le_card
          intro x hx
          exact Finset.mem_range.mpr (PatientScope.mem_prefixFinset.mp hx).1
        _ = n := Finset.card_range n
    have hDleK := PatientScope.prefixCount_mono hDK n
    have hcountR : (n : ℝ) ≤
        4 * (PatientScope.prefixCount D n : ℝ) + C := by
      exact_mod_cast hcount n
    have hratio : (PatientScope.prefixCount D n : ℝ) / (n : ℝ) ≤
        (PatientScope.prefixCount D n : ℝ) /
          (PatientScope.prefixCount K n : ℝ) := by
      rw [div_le_div_iff₀ hnR hnKR]
      have hDnonneg : (0 : ℝ) ≤ PatientScope.prefixCount D n := Nat.cast_nonneg _
      have hKleR : (PatientScope.prefixCount K n : ℝ) ≤ n := by exact_mod_cast hKle
      nlinarith
    dsimp [error]
    calc
      (1 / 4 : ℝ) ≤
          (PatientScope.prefixCount D n : ℝ) / (n : ℝ) +
            (C : ℝ) / (4 * (n : ℝ)) := by
              field_simp [hnR.ne']
              nlinarith
      _ ≤ (PatientScope.prefixCount D n : ℝ) /
            (PatientScope.prefixCount K n : ℝ) +
              (C : ℝ) / (4 * (n : ℝ)) := add_le_add_right hratio _
  unfold PatientScope.relativeLowerDensity
  have hlim := liminf_le_of_eventually_le_add_tendsto_zero
    (fun _ : ℕ => (1 / 4 : ℝ))
    (fun n => (PatientScope.prefixCount D n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)) error
    (by intro n; norm_num)
    (by intro n; norm_num)
    (by intro n; positivity)
    (by
      intro n
      by_cases hn : PatientScope.prefixCount K n = 0
      · simp [hn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast PatientScope.prefixCount_mono hDK n)
    herror hcompare
  simpa using hlim

end Case019Helpers

namespace Case019Helpers

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

private def finiteOmissionEncoding (q : ℕ)
    (A : Set negativeIntegers) : Set ℤ :=
  (↑(omissionMarkerFinset q) : Set ℤ) ∪ positiveIntegers ∪
    (fun z : negativeIntegers => z.1) '' A

private theorem finiteOmissionEncoding_mem (q : ℕ)
    (A : Set negativeIntegers) :
    finiteOmissionEncoding q A ∈ finiteOmissionClass q := by
  apply Or.inl
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · refine ⟨0, ?_⟩
    intro z hz
    obtain ⟨k, rfl⟩ := hz
    exact Or.inl (Or.inr (by simpa using positiveCode_mem k))

private theorem finiteOmissionEncoding_injective (q : ℕ) :
    Function.Injective (finiteOmissionEncoding q) := by
  intro A B hAB
  apply Set.ext
  intro p
  have hpNotMarker : p.1 ∉ omissionMarkerFinset q := by
    intro hp
    exact (Int.not_lt_of_ge (omissionMarker_nonnegative hp)) p.2
  have hpNotPositive : p.1 ∉ positiveIntegers := by
    exact Int.not_lt_of_ge (Int.le_of_lt p.2)
  have hpImage (C : Set negativeIntegers) :
      p.1 ∈ (fun z : negativeIntegers => z.1) '' C ↔ p ∈ C := by
    constructor
    · rintro ⟨z, hz, hzp⟩
      simpa [Subtype.ext hzp] using hz
    · intro hp
      exact ⟨p, hp, rfl⟩
  have hmem := Set.ext_iff.mp hAB p.1
  change
    p.1 ∈ (↑(omissionMarkerFinset q) : Set ℤ) ∪ positiveIntegers ∪
        (fun z : negativeIntegers => z.1) '' A ↔
      p.1 ∈ (↑(omissionMarkerFinset q) : Set ℤ) ∪ positiveIntegers ∪
        (fun z : negativeIntegers => z.1) '' B at hmem
  simp only [Set.mem_union, hpImage] at hmem
  simpa [hpNotMarker, hpNotPositive] using hmem

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  letI : Infinite negativeIntegers := negativeIntegers_infinite.to_subtype
  intro hcountable
  let f : Set negativeIntegers → finiteOmissionClass q := fun A =>
    ⟨finiteOmissionEncoding q A, finiteOmissionEncoding_mem q A⟩
  have hf : Function.Injective f := by
    intro A B hAB
    apply finiteOmissionEncoding_injective q
    exact congrArg Subtype.val hAB
  letI : Countable (finiteOmissionClass q) := hcountable.to_subtype
  have hpower : Countable (Set negativeIntegers) := hf.countable
  exact powerSet_not_countable negativeIntegers hpower

end Case019Helpers

namespace Case019Helpers

open GenLimit.UnionClosedness

 theorem eventually_injective_not_mem_finite
    {α : Type*} (output : ℕ → α) (hinjective : Function.Injective output)
    {F : Set α} (hF : F.Finite) :
    ∃ T, ∀ t, T ≤ t → output t ∉ F := by
  have hpre : (output ⁻¹' F).Finite :=
    hF.preimage (Set.injOn_of_injective hinjective)
  obtain ⟨T, hT⟩ := Finset.exists_nat_subset_range hpre.toFinset
  refine ⟨T, ?_⟩
  intro t ht hmem
  have htmem : t ∈ hpre.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hmem
  have : t < T := by simpa using hT htmem
  omega

theorem balanced_surjective : Function.Surjective Stage3Case019.balanced := by
  intro z
  rcases z with k | k
  · cases k with
    | zero => exact ⟨0, rfl⟩
    | succ k => exact ⟨2 * k + 2, balanced_positiveCode k⟩
  · exact ⟨2 * k + 1, balanced_negativeCode k⟩

theorem balancedRanks_infinite {K : Set ℤ} (hK : K.Infinite) :
    (Stage3Case019.balancedRanks K).Infinite := by
  intro hfinite
  apply hK
  have himage : Stage3Case019.balanced ''
      Stage3Case019.balancedRanks K = K := by
    apply Set.Subset.antisymm
    · rintro z ⟨n, hn, rfl⟩
      exact hn
    · intro z hz
      obtain ⟨n, hn⟩ := balanced_surjective z
      exact ⟨n, by simpa [Stage3Case019.balancedRanks, hn] using hz, hn⟩
  rw [← himage]
  exact hfinite.image Stage3Case019.balanced

end Case019Helpers
