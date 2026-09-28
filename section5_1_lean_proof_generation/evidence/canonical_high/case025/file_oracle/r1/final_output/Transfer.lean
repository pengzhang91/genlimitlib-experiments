import Positive
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter
open scoped Topology

namespace Stage3Case025Formalization

noncomputable section

private theorem relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

private theorem relativeRatio_le_one
    {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · have hA : GenLimit.PatientScope.prefixCount A n = 0 := by
      exact Nat.eq_zero_of_le_zero
        ((GenLimit.PatientScope.prefixCount_mono hAK n).trans_eq hzero)
    simp [hzero, hA]
  · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n

theorem relativeLowerDensity_le_of_eventually_ratio_le
    {A K B L : Set ℕ}
    (hBL : B ⊆ L)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hprefix : ∀ᶠ n : ℕ in atTop,
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount L n : ℝ) + error n) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B L := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => relativeRatio_le_one hBL n))
    (isBoundedUnder_of
      ⟨0, fun n => relativeRatio_nonneg B L n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop,
      r < (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of
        ⟨0, fun n => relativeRatio_nonneg A K n⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with
      n hrn herr hcount
  linarith

theorem prefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  have hsub :
      GenLimit.PatientScope.prefixFinset A n ⊆
        GenLimit.PatientScope.prefixFinset B n ∪ hfinite.toFinset := by
    intro x hx
    have hxparts := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxparts.1, hxB⟩)
    · exact Finset.mem_union_right _
        ((Set.Finite.mem_toFinset hfinite).mpr ⟨hxparts.2, hxB⟩)
  change (GenLimit.PatientScope.prefixFinset A n).card ≤
    (GenLimit.PatientScope.prefixFinset B n).card + hfinite.toFinset.card
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _)

theorem relativeRatio_le_add_finiteError
    {A B K R : Set ℕ}
    (hKR : K ⊆ R) (hfinite : (A \ B).Finite)
    {n : ℕ} (hKpos : 0 < GenLimit.PatientScope.prefixCount K n) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount R n : ℝ) ≤
      (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) +
        (hfinite.toFinset.card : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  have hRposNat : 0 < GenLimit.PatientScope.prefixCount R n :=
    lt_of_lt_of_le hKpos (GenLimit.PatientScope.prefixCount_mono hKR n)
  have hKposReal : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
    exact_mod_cast hKpos
  have hRposReal : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n := by
    exact_mod_cast hRposNat
  have hdenom :
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        GenLimit.PatientScope.prefixCount R n := by
    exact_mod_cast GenLimit.PatientScope.prefixCount_mono hKR n
  have hcount :
      (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
        GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
    exact_mod_cast prefixCount_le_add_ncard_diff hfinite n
  rw [← add_div]
  rw [div_le_div_iff₀ hRposReal hKposReal]
  have hAnonneg : (0 : ℝ) ≤ GenLimit.PatientScope.prefixCount A n := by positivity
  have hsumNonneg : (0 : ℝ) ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by positivity
  nlinarith

set_option maxHeartbeats 800000 in
theorem relativeLowerDensity_of_finite_extension
    {Q K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  have hdifference : ((Q ∩ R) \ (Q ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  let error : ℕ → ℝ := fun n =>
    (hdifference.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountTendsto : Tendsto
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcountTendsto
  apply relativeLowerDensity_le_of_eventually_ratio_le
    (A := Q ∩ R) (K := R) (B := Q ∩ K) (L := K)
    inter_subset_right error herror
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hpositive] with n hn
  dsimp only [error]
  exact relativeRatio_le_add_finiteError hKR hdifference hn

theorem novelGeneratesInLimit_of_finite_extraneous
    {input output : ℕ → ℕ} {K R : Set ℕ}
    (hfinite : (R \ K).Finite)
    (hseen : R \ K ⊆ Set.range input)
    (hNovel : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hNovel
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      (L := Set.range input) rfl hfinite.toFinset (by
        intro x hx
        exact hseen ((Set.Finite.mem_toFinset hfinite).mp hx))
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have htGenerate : Tgenerate ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  have hAt := hTgenerate t htGenerate
  refine ⟨?_, hAt.2.1, hAt.2.2⟩
  by_contra houtside
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hAt.1, houtside⟩
  apply hAt.2.1
  simpa [Nat.succ_eq_add_one] using
    (GenLimit.Generic.sample_mono (htSeen.trans (Nat.le_succ t)) (hTseen hbad))

theorem exists_expansion_index_for_occurrence_presentation
    (O : GenLimit.OracleFamily) {z : ℕ}
    {input : GenLimit.Generic.Stream ℕ}
    (hcover : O.language z ⊆ Set.range input)
    (hnoise : GenLimit.Generic.FinitelyManyViolations input
      (fun x => x ∈ O.language z)) :
    ∃ j, GenLimit.Presents input
      ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) := by
  classical
  let addFinite :=
    GenLimit.InfiniteContamination.displayedNoise_finite hnoise
  have hremoveFinite :
      (GenLimit.InfiniteContamination.displayedOmissions
        input (O.language z)).Finite := by
    rw [GenLimit.InfiniteContamination.displayedOmissions,
      Set.diff_eq_empty.mpr hcover]
    exact Set.finite_empty
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (z, Finset.equivBitIndices.symm addFinite.toFinset,
      Finset.equivBitIndices.symm hremoveFinite.toFinset)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  change Set.range input =
    GenLimit.InfiniteContamination.finiteExpansionLanguage O j
  have hadd :
      (↑addFinite.toFinset : Set ℕ) =
        GenLimit.InfiniteContamination.displayedNoise input (O.language z) :=
    Set.Finite.coe_toFinset addFinite
  have hremove :
      (↑hremoveFinite.toFinset : Set ℕ) =
        GenLimit.InfiniteContamination.displayedOmissions input (O.language z) :=
    Set.Finite.coe_toFinset hremoveFinite
  rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
  simp only [j, data,
    GenLimit.InfiniteContamination.finiteExpansionCode_encode]
  simp only [Equiv.apply_symm_apply]
  rw [hadd, hremove]
  exact
    (GenLimit.InfiniteContamination.finiteExpansion_displayedNoise_displayedOmissions
      input (O.language z)).symm

end

end Stage3Case025Formalization
