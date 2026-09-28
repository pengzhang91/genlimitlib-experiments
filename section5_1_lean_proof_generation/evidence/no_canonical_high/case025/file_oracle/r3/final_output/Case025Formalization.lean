import output.Helpers

open Filter
open scoped Topology
open Stage3Case025

namespace Stage3Case025

lemma exists_expansion_index_for_complete_occurrence
    (O : GenLimit.OracleFamily) {i : ℕ} {input : Stream}
    (hcomplete : CompleteFiniteOccurrencePresentation input (O.language i)) :
    ∃ j,
      GenLimit.InfiniteContamination.finiteExpansionBaseIndex j = i ∧
      GenLimit.Presents input
        ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) ∧
      (((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j \ O.language i).Finite) ∧
      O.language i ⊆
        (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j := by
  classical
  let noise : Set ℕ := Set.range input \ O.language i
  have hnoise : noise.Finite := by
    change (Set.range input \ O.language i).Finite
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hcomplete.2.image input
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm hnoise.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  have hexpansion :
      (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j =
        Set.range input := by
    change GenLimit.InfiniteContamination.finiteExpansionLanguage O j = _
    rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
    simp only [j, data,
      GenLimit.InfiniteContamination.finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    rw [Set.Finite.coe_toFinset hnoise]
    ext x
    simp only [GenLimit.InfiniteContamination.finiteExpansion, noise,
      Set.mem_diff, Set.mem_union, Set.mem_range, Finset.coe_empty,
      Set.mem_empty_iff_false, not_false_eq_true, and_true]
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact hcomplete.1 hx
      · exact hx
    · intro hx
      by_cases hxi : x ∈ O.language i
      · exact Or.inl hxi
      · exact Or.inr ⟨hx, hxi⟩
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · simp [j, data, GenLimit.InfiniteContamination.finiteExpansionBaseIndex]
  · exact hexpansion.symm
  · rw [hexpansion]
    exact hnoise
  · rw [hexpansion]
    exact hcomplete.1

lemma relativeRatio_nonneg (A K : Language) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

lemma relativeRatio_le_one {A K : Language} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · have hAzero : GenLimit.PatientScope.prefixCount A n = 0 :=
      Nat.eq_zero_of_le_zero
        ((GenLimit.PatientScope.prefixCount_mono hAK n).trans_eq hzero)
    simp [hzero, hAzero]
  · rw [div_le_one]
    · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n
    · exact_mod_cast Nat.pos_of_ne_zero hzero

lemma prefixCount_le_add_finite_diff {A B : Language}
    (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := GenLimit.PatientScope.prefixFinset A n
  let bPrefix := GenLimit.PatientScope.prefixFinset B n
  let dPrefix := GenLimit.PatientScope.prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ dPrefix := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hcard : aPrefix.card ≤ bPrefix.card + dPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : dPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2
      (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
  simpa [GenLimit.PatientScope.prefixCount, aPrefix, bPrefix, dPrefix] using
    hcard.trans (Nat.add_le_add_left hdiff _)

lemma liminf_le_of_eventually_le_add_vanishing
    (source output error : ℕ → ℝ)
    (hsourceNonneg : ∀ n, 0 ≤ source n)
    (houtputNonneg : ∀ n, 0 ≤ output n)
    (houtputLeOne : ∀ n, output n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n) :
    liminf source atTop ≤ liminf output atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop houtputLeOne)
    (isBoundedUnder_of ⟨0, houtputNonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrSource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrSource
      (isBoundedUnder_of ⟨0, hsourceNonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr he hp
  linarith

lemma relativeLowerDensity_le_of_finite_extension
    {A K E : Language} (hK : K.Infinite) (hKE : K ⊆ E)
    (hdiff : (E \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  let output : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hdiff.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hden : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
  have herror : Tendsto error atTop (𝓝 0) := by
    exact hden.const_div_atTop (hdiff.toFinset.card : ℝ)
  have hprefix : ∀ᶠ n : ℕ in atTop,
      source n ≤ output n + error n := by
    filter_upwards
      [(GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
        (eventually_gt_atTop 0)] with n hKn
    have hKpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hKn
    have hEpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hKn
        (GenLimit.PatientScope.prefixCount_mono hKE n)
    have hsmall : ((A ∩ E) \ (A ∩ K)).Finite := by
      apply hdiff.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hsmallCard : hsmall.toFinset.card ≤ hdiff.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      exact Set.Finite.mem_toFinset hdiff |>.2
        (by
          have hx' := Set.Finite.mem_toFinset hsmall |>.1 hx
          exact ⟨hx'.1.2, fun hxK => hx'.2 ⟨hx'.1.1, hxK⟩⟩)
    have hnum :
        GenLimit.PatientScope.prefixCount (A ∩ E) n ≤
          GenLimit.PatientScope.prefixCount (A ∩ K) n +
            hdiff.toFinset.card := by
      exact (prefixCount_le_add_finite_diff hsmall n).trans
        (Nat.add_le_add_left hsmallCard _)
    have hdenom :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount E n := by
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hKE n
    dsimp [source, output, error]
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          GenLimit.PatientScope.prefixCount E n
        ≤ (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by
          exact div_le_div_of_nonneg_left (by positivity) hKpos hdenom
      _ ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) +
            hdiff.toFinset.card) /
            GenLimit.PatientScope.prefixCount K n := by
          apply div_le_div_of_nonneg_right
          · exact_mod_cast hnum
          · positivity
      _ = (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n +
          (hdiff.toFinset.card : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by
          rw [add_div]
  unfold GenLimit.PatientScope.relativeLowerDensity
  simpa [source, output] using
    (liminf_le_of_eventually_le_add_vanishing source output error
      (fun n => relativeRatio_nonneg _ _ n)
      (fun n => relativeRatio_nonneg _ _ n)
      (fun n => relativeRatio_le_one Set.inter_subset_right n)
      herror hprefix)

lemma novelGenerates_transfer_finite_expansion
    {input output : Stream} {K E : Language}
    (hP : GenLimit.Presents input E) (hdiff : (E \ K).Finite)
    (hgen : GenLimit.NovelGeneratesInLimit input output E) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgen, hTgen⟩ := hgen
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hP hdiff.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hdiff).mp hx).1)
  refine ⟨max Tgen Tseen, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ :=
    hTgen t ((Nat.le_max_left _ _).trans ht)
  refine ⟨?_, hfresh, hnovel⟩
  by_contra hnot
  have hex : output t ∈ hdiff.toFinset :=
    (Set.Finite.mem_toFinset hdiff).2 ⟨hmem, hnot⟩
  have hsampleSeen : output t ∈ GenLimit.sample input Tseen := by
    simpa [GenLimit.Generic.sample, GenLimit.sample] using hTseen hex
  exact hfresh (GenLimit.sample_mono
    ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)) hsampleSeen)

 theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, patientOnlineGenerator_follows O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ :=
      (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input hP).1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨hmem, ?_, hnovel⟩
    intro hsamp
    rw [GenLimit.mem_sample_iff] at hsamp
    obtain ⟨s, hs, heq⟩ := hsamp
    exact (hfresh s (by omega)) heq
  · exact (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input hP).2


theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let O := oracleOfFamily family hInfinite
  let Oexp := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hpositive Oexp.language Oexp.infinite'
  refine ⟨gen, ?_⟩
  intro i input hcomplete
  have hcompleteO : CompleteFiniteOccurrencePresentation input (O.language i) := by
    simpa [O, oracleOfFamily] using hcomplete
  obtain ⟨j, hjBase, hjPresents, hjDiff, hjSub⟩ :=
    exists_expansion_index_for_complete_occurrence O hcompleteO
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hjPresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply novelGenerates_transfer_finite_expansion hjPresents hjDiff hnovel
  · have htransfer := relativeLowerDensity_le_of_finite_extension
      (A := GenLimit.GeneratorFirst input output)
      (O.infinite' i) hjSub hjDiff
    exact hdensity.trans htransfer

end Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025.stage3_finite_noise_transfer
    Stage3Case025.stage3_positive_engine
