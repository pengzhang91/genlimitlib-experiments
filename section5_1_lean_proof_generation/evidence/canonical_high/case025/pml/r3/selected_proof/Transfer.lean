import Helpers
import GenLimit.Bridges.BasicToGeneric

namespace Stage3Case025

open Filter
open scoped Topology
open GenLimit
open GenLimit.InfiniteContamination

noncomputable def relativeRatio (A K : Language) (n : ℕ) : ℝ :=
  (PatientScope.prefixCount A n : ℝ) / (PatientScope.prefixCount K n : ℝ)

theorem relativeRatio_nonneg (A K : Language) (n : ℕ) :
    0 ≤ relativeRatio A K n := by
  exact div_nonneg (by positivity) (by positivity)

theorem relativeRatio_le_one {A K : Language} (hAK : A ⊆ K) (n : ℕ) :
    relativeRatio A K n ≤ 1 := by
  by_cases hzero : PatientScope.prefixCount K n = 0
  · simp [relativeRatio, hzero]
  · rw [relativeRatio, div_le_one]
    · exact_mod_cast PatientScope.prefixCount_mono hAK n
    · exact_mod_cast Nat.pos_of_ne_zero hzero

theorem relativeLowerDensity_le_of_eventually_ratio_le
    {A K B R : Language} (hAK : A ⊆ K) (hBR : B ⊆ R)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hprefix : ∀ᶠ n : ℕ in atTop,
      relativeRatio A K n ≤ relativeRatio B R n + error n) :
    PatientScope.relativeLowerDensity A K ≤
      PatientScope.relativeLowerDensity B R := by
  unfold PatientScope.relativeLowerDensity
  change liminf (relativeRatio A K) atTop ≤ liminf (relativeRatio B R) atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (relativeRatio_le_one hBR))
    (isBoundedUnder_of ⟨0, relativeRatio_nonneg B R⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrDensity⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < relativeRatio A K n :=
    eventually_lt_of_lt_liminf hrDensity
      (isBoundedUnder_of ⟨0, relativeRatio_nonneg A K⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr hsmall hcount
  linarith

theorem prefixCount_le_add_finite_diff
    {A B : Language} (hfinite : (A \ B).Finite) (n : ℕ) :
    PatientScope.prefixCount A n ≤
      PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := PatientScope.prefixFinset A n
  let bPrefix := PatientScope.prefixFinset B n
  let diffPrefix := PatientScope.prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    have hx' := PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ (PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _
        (PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2
      (PatientScope.mem_prefixFinset.mp hx).2
  calc
    PatientScope.prefixCount A n = aPrefix.card := rfl
    _ ≤ (bPrefix ∪ diffPrefix).card := Finset.card_le_card hsub
    _ ≤ bPrefix.card + diffPrefix.card := Finset.card_union_le _ _
    _ ≤ bPrefix.card + hfinite.toFinset.card := Nat.add_le_add_left hdiff _
    _ = PatientScope.prefixCount B n + hfinite.toFinset.card := rfl

theorem relativeRatio_le_add_finite_error
    {A B K R : Language}
    (hKInfinite : K.Infinite)
    (hAK : A ⊆ R) (hBK : B ⊆ K) (hKR : K ⊆ R)
    (hfinite : (A \ B).Finite) :
    ∀ᶠ n : ℕ in atTop,
      relativeRatio A R n ≤ relativeRatio B K n +
        (hfinite.toFinset.card : ℝ) / PatientScope.prefixCount R n := by
  have hRInfinite : R.Infinite := hKInfinite.mono hKR
  have hRpos : ∀ᶠ n : ℕ in atTop, 0 < PatientScope.prefixCount R n :=
    (PatientScope.tendsto_prefixCount_atTop hRInfinite).eventually
      (eventually_gt_atTop 0)
  have hKpos : ∀ᶠ n : ℕ in atTop, 0 < PatientScope.prefixCount K n :=
    (PatientScope.tendsto_prefixCount_atTop hKInfinite).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hRpos, hKpos] with n hRn hKn
  have hcount := prefixCount_le_add_finite_diff hfinite n
  have hdenom := PatientScope.prefixCount_mono hKR n
  rw [relativeRatio, relativeRatio]
  have hRnR : (0 : ℝ) < PatientScope.prefixCount R n := by exact_mod_cast hRn
  have hKnR : (0 : ℝ) < PatientScope.prefixCount K n := by exact_mod_cast hKn
  have hcountR : (PatientScope.prefixCount A n : ℝ) ≤
      PatientScope.prefixCount B n + hfinite.toFinset.card := by
    exact_mod_cast hcount
  have hdenomR : (PatientScope.prefixCount K n : ℝ) ≤
      PatientScope.prefixCount R n := by exact_mod_cast hdenom
  calc
    (PatientScope.prefixCount A n : ℝ) / PatientScope.prefixCount R n ≤
        (PatientScope.prefixCount B n + hfinite.toFinset.card : ℝ) /
          PatientScope.prefixCount R n :=
      div_le_div_of_nonneg_right hcountR hRnR.le
    _ = (PatientScope.prefixCount B n : ℝ) / PatientScope.prefixCount R n +
        (hfinite.toFinset.card : ℝ) / PatientScope.prefixCount R n := by rw [add_div]
    _ ≤ (PatientScope.prefixCount B n : ℝ) / PatientScope.prefixCount K n +
        (hfinite.toFinset.card : ℝ) / PatientScope.prefixCount R n := by
      apply add_le_add_right
      rw [div_le_div_iff₀ hRnR hKnR]
      exact mul_le_mul_of_nonneg_left hdenomR (by positivity)

theorem relativeLowerDensity_finite_numerator_transfer
    {A B K R : Language}
    (hKInfinite : K.Infinite) (hAK : A ⊆ R) (hBK : B ⊆ K)
    (hKR : K ⊆ R) (hfinite : (A \ B).Finite) :
    PatientScope.relativeLowerDensity A R ≤
      PatientScope.relativeLowerDensity B K := by
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) / PatientScope.prefixCount R n
  have hRInfinite : R.Infinite := hKInfinite.mono hKR
  have hcount := PatientScope.tendsto_prefixCount_atTop hRInfinite
  have hcast : Tendsto (fun n => (PatientScope.prefixCount R n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hcount
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcast
  exact relativeLowerDensity_le_of_eventually_ratio_le hAK hBK error herror
    (relativeRatio_le_add_finite_error hKInfinite hAK hBK hKR hfinite)

theorem finite_range_noise_of_occurrence_noise
    {input : Stream} {K : Language}
    (hnoise : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
  exact hnoise.image input

theorem exists_expansion_index_for_complete_occurrence
    (O : OracleFamily) {z : ℕ} {input : Stream}
    (hcomplete : CompleteFiniteOccurrencePresentation input (O.language z)) :
    ∃ j, GenLimit.Presents input
      ((finiteExpansionOracleFamily O).language j) := by
  let noiseFinite := finite_range_noise_of_occurrence_noise hcomplete.2
  let data : FiniteExpansionCode :=
    (z, Finset.equivBitIndices.symm noiseFinite.toFinset,
      Finset.equivBitIndices.symm (∅ : Finset ℕ))
  let j := encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  change Set.range input = finiteExpansionLanguage O j
  have hnoise : (↑noiseFinite.toFinset : Set ℕ) = Set.range input \ O.language z :=
    Set.Finite.coe_toFinset noiseFinite
  rw [finiteExpansionLanguage]
  simp only [j, data, finiteExpansionCode_encode, Equiv.apply_symm_apply]
  rw [hnoise]
  ext x
  simp only [finiteExpansion, Set.mem_diff, Set.mem_union, Set.mem_empty_iff_false,
    not_false_eq_true, and_true, Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    by_cases hx : input t ∈ O.language z
    · exact ⟨Or.inl hx, by simp⟩
    · exact ⟨Or.inr ⟨⟨t, rfl⟩, hx⟩, by simp⟩
  · rintro (hx | ⟨hx, _⟩)
    · exact hcomplete.1 hx
    · exact hx

theorem novelGeneratesInLimit_of_finite_extraneous
    {input output : Stream} {K R : Language}
    (hP : Presents input R) (hfinite : (R \ K).Finite)
    (hgen : NovelGeneratesInLimit input output R) :
    NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgen, hTgen⟩ := hgen
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hP hfinite.toFinset (by
      intro x hx
      exact (Set.Finite.mem_toFinset hfinite).mp hx |>.1)
  refine ⟨max Tgen Tseen, ?_⟩
  intro t ht
  have hcorrect := hTgen t ((Nat.le_max_left _ _).trans ht)
  have hseen : hfinite.toFinset ⊆ sample input (t + 1) := by
    intro x hx
    exact sample_mono
      ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t))
      (by simpa using hTseen hx)
  refine ⟨?_, hcorrect.2.1, hcorrect.2.2⟩
  by_contra hxK
  have hxBad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hcorrect.1, hxK⟩
  exact hcorrect.2.1 (hseen hxBad)

end Stage3Case025

namespace Stage3Case025

open Filter
open scoped Topology
open GenLimit
open GenLimit.InfiniteContamination

theorem finiteNoiseTransferPrinciple : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let O := semanticOracleFamily family hInfinite
  let expanded := finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hpositive expanded.language expanded.infinite'
  refine ⟨gen, ?_⟩
  intro i input hcomplete
  have hcompleteO :
      CompleteFiniteOccurrencePresentation input (O.language i) := by
    simpa [O, semanticOracleFamily] using hcomplete
  obtain ⟨j, hP⟩ := exists_expansion_index_for_complete_occurrence O hcompleteO
  obtain ⟨output, hfollows, hnovelExpanded, hdensityExpanded⟩ :=
    hgen j input hP
  let R := expanded.language j
  let K := O.language i
  have hP' : Presents input R := hP
  have hKR : K ⊆ R := by
    intro x hx
    rw [← hP']
    exact hcompleteO.1 hx
  have hnoise : (R \ K).Finite := by
    rw [← hP']
    exact finite_range_noise_of_occurrence_noise hcompleteO.2
  have hnovelK : NovelGeneratesInLimit input output K :=
    novelGeneratesInLimit_of_finite_extraneous hP' hnoise hnovelExpanded
  let A := GeneratorFirst input output ∩ R
  let B := GeneratorFirst input output ∩ K
  have hABfinite : (A \ B).Finite := by
    apply hnoise.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  have hdensityTransfer :
      PatientScope.relativeLowerDensity A R ≤
        PatientScope.relativeLowerDensity B K := by
    apply relativeLowerDensity_finite_numerator_transfer
      (hInfinite i) Set.inter_subset_right Set.inter_subset_right hKR hABfinite
  refine ⟨output, hfollows, ?_, ?_⟩
  · simpa [K, O, semanticOracleFamily] using hnovelK
  · have hdensityK : (1 / 2 : ℝ) ≤
        PatientScope.relativeLowerDensity B K :=
      hdensityExpanded.trans hdensityTransfer
    simpa [B, K, O, semanticOracleFamily] using hdensityK

end Stage3Case025
