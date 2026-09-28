import output.Case025Helpers

open Filter
open scoped Topology

namespace Stage3Case025

open GenLimit.PatientScope

noncomputable def finiteAdditionLanguage
    (family : ℕ → Language) (n : ℕ) : Language :=
  family (Nat.unpair n).1 ∪
    (Finset.equivBitIndices (Nat.unpair n).2 : Set ℕ)

theorem finiteAdditionLanguage_infinite
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) (n : ℕ) :
    (finiteAdditionLanguage family n).Infinite := by
  exact (hInfinite (Nat.unpair n).1).mono Set.subset_union_left

theorem finite_range_diff
    {input : Stream} {K : Language}
    (hviol : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
  exact hviol.image input

theorem exists_finiteAddition_index
    (family : ℕ → Language) {i : ℕ} {input : Stream}
    (hpres : CompleteFiniteOccurrencePresentation input (family i)) :
    ∃ j, GenLimit.Presents input (finiteAdditionLanguage family j) := by
  let hdiff : (Set.range input \ family i).Finite := finite_range_diff hpres.2
  let code := Finset.equivBitIndices.symm hdiff.toFinset
  refine ⟨Nat.pair i code, ?_⟩
  change Set.range input = finiteAdditionLanguage family (Nat.pair i code)
  rw [finiteAdditionLanguage]
  simp only [Nat.unpair_pair, code, Equiv.apply_symm_apply]
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ family i
    · exact Or.inl hxK
    · exact Or.inr (Set.Finite.mem_toFinset hdiff |>.2 ⟨hx, hxK⟩)
  · rintro (hxK | hxF)
    · exact hpres.1 hxK
    · exact (Set.Finite.mem_toFinset hdiff |>.1 hxF).1

theorem prefixCount_inter_le
    (A B : Set ℕ) (n : ℕ) :
    prefixCount (A ∩ B) n ≤ prefixCount B n :=
  prefixCount_mono Set.inter_subset_right n

theorem prefixCount_union_le
    (A B : Set ℕ) (n : ℕ) :
    prefixCount (A ∪ B) n ≤ prefixCount A n + prefixCount B n := by
  classical
  unfold prefixCount
  calc
    (prefixFinset (A ∪ B) n).card ≤
        (prefixFinset A n ∪ prefixFinset B n).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := mem_prefixFinset.mp hx
      rcases hx'.2 with hxA | hxB
      · exact Finset.mem_union_left _ (mem_prefixFinset.mpr ⟨hx'.1, hxA⟩)
      · exact Finset.mem_union_right _ (mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    _ ≤ (prefixFinset A n).card + (prefixFinset B n).card :=
      Finset.card_union_le _ _

theorem prefixCount_le_ncard_of_finite
    {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold prefixCount
  apply Finset.card_le_card
  intro x hx
  exact Set.Finite.mem_toFinset hF |>.2 (Finset.mem_filter.mp hx).2

theorem prefixCount_inter_expansion_le
    {Q K R : Set ℕ} (hfinite : (R \ K).Finite) (n : ℕ) :
    prefixCount (Q ∩ R) n ≤
      prefixCount (Q ∩ K) n + hfinite.toFinset.card := by
  have hsub : Q ∩ R ⊆ (Q ∩ K) ∪ (R \ K) := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx.1, hxK⟩
    · exact Or.inr ⟨hx.2, hxK⟩
  calc
    prefixCount (Q ∩ R) n ≤ prefixCount ((Q ∩ K) ∪ (R \ K)) n :=
      prefixCount_mono hsub n
    _ ≤ prefixCount (Q ∩ K) n + prefixCount (R \ K) n :=
      prefixCount_union_le _ _ n
    _ ≤ prefixCount (Q ∩ K) n + hfinite.toFinset.card :=
      Nat.add_le_add_left (prefixCount_le_ncard_of_finite hfinite n) _

theorem relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (prefixCount A n : ℝ) / (prefixCount K n : ℝ) := by positivity

theorem relativeRatio_le_one
    {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
  by_cases hk : prefixCount K n = 0
  · simp [hk]
  · rw [div_le_one]
    · exact_mod_cast prefixCount_mono hAK n
    · exact_mod_cast Nat.pos_of_ne_zero hk

theorem liminf_le_of_le_add_tendsto_zero
    (source target error : ℕ → ℝ)
    (hsourceNonneg : ∀ n, 0 ≤ source n)
    (htargetNonneg : ∀ n, 0 ≤ target n)
    (htargetLe : ∀ n, target n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n) :
    liminf source atTop ≤ liminf target atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htargetLe)
    (isBoundedUnder_of ⟨0, htargetNonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrSource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrSource
      (isBoundedUnder_of ⟨0, hsourceNonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hcompare] with n hrs herr hcomp
  linarith

theorem relativeLowerDensity_mono_finiteExpansion
    {Q K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite) :
    relativeLowerDensity (Q ∩ R) R ≤ relativeLowerDensity (Q ∩ K) K := by
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) / (prefixCount K n : ℝ)
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop.comp (tendsto_prefixCount_atTop hK)))
  unfold relativeLowerDensity
  apply liminf_le_of_le_add_tendsto_zero
      (fun n => (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ))
      (fun n => (prefixCount (Q ∩ K) n : ℝ) / (prefixCount K n : ℝ))
      error
  · exact fun n => relativeRatio_nonneg _ _ n
  · exact fun n => relativeRatio_nonneg _ _ n
  · exact fun n => relativeRatio_le_one Set.inter_subset_right n
  · exact herror
  · have hpositive : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
      (tendsto_prefixCount_atTop hK).eventually (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hk
    have hRpos : (0 : ℝ) < prefixCount R n := by
      exact_mod_cast lt_of_lt_of_le hk (prefixCount_mono hKR n)
    have hKpos : (0 : ℝ) < prefixCount K n := by exact_mod_cast hk
    have hnum :
        (prefixCount (Q ∩ R) n : ℝ) ≤
          prefixCount (Q ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast prefixCount_inter_expansion_le hfinite n
    have hden : (prefixCount K n : ℝ) ≤ prefixCount R n := by
      exact_mod_cast prefixCount_mono hKR n
    dsimp [error]
    calc
      (prefixCount (Q ∩ R) n : ℝ) / prefixCount R n ≤
          (prefixCount (Q ∩ R) n : ℝ) / prefixCount K n := by
        exact div_le_div_of_nonneg_left (by positivity) hKpos hden
      _ ≤ ((prefixCount (Q ∩ K) n : ℝ) + hfinite.toFinset.card) /
          (prefixCount K n : ℝ) := by
        rw [div_le_div_iff_of_pos_right hKpos]
        exact hnum
      _ = (prefixCount (Q ∩ K) n : ℝ) / prefixCount K n +
          (hfinite.toFinset.card : ℝ) / prefixCount K n := by
        exact add_div _ _ _

end Stage3Case025

namespace Stage3Case025

open GenLimit.PatientScope

theorem presentationDependentHalfDensity : PresentationDependentHalfDensity := by
  intro family hInfinite
  let expanded : ℕ → Language := finiteAdditionLanguage family
  have hExpandedInfinite : ∀ j, (expanded j).Infinite := by
    intro j
    exact finiteAdditionLanguage_infinite family hInfinite j
  let O := oracleOfFamily expanded hExpandedInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hpres
  obtain ⟨j, hjPresents⟩ := exists_finiteAddition_index family hpres
  have hjPresentsO : GenLimit.Presents input (O.language j) := by
    simpa [O, expanded] using hjPresents
  let output := GenLimit.PatientMachine.output O input
  obtain ⟨hgeneration, hdensity⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input hjPresentsO
  refine ⟨output, patientOnlineGenerator_follows O input, ?_, ?_⟩
  · obtain ⟨TR, hTR⟩ := hgeneration
    have hbad : (Set.range input \ family i).Finite :=
      finite_range_diff hpres.2
    have hinjective : Function.Injective output := by
      simpa [output] using GenLimit.PatientMachine.output_injective O input
    have hbadTimes : (output ⁻¹' (Set.range input \ family i)).Finite :=
      hbad.preimage hinjective.injOn
    obtain ⟨B, hB⟩ := hbadTimes.bddAbove
    refine ⟨max TR (B + 1), ?_⟩
    intro t ht
    have htTR : TR ≤ t := (le_max_left TR (B + 1)).trans ht
    obtain ⟨htRange, htFreshInput, htFreshOutput⟩ := hTR t htTR
    have htargetEq : O.language j = Set.range input := hjPresentsO.symm
    have htInRange : output t ∈ Set.range input := by
      rw [← htargetEq]
      exact htRange
    have htTarget : output t ∈ family i := by
      by_contra htNotTarget
      have htBad : t ∈ output ⁻¹' (Set.range input \ family i) :=
        ⟨htInRange, htNotTarget⟩
      have htB : t ≤ B := hB htBad
      have hBt : B + 1 ≤ t := (le_max_right TR (B + 1)).trans ht
      omega
    refine ⟨htTarget, ?_, htFreshOutput⟩
    intro htSample
    rw [GenLimit.mem_sample_iff] at htSample
    obtain ⟨s, hs, hvalue⟩ := htSample
    exact htFreshInput s (Nat.lt_succ_iff.mp hs) hvalue
  · have htargetEq : O.language j = Set.range input := hjPresentsO.symm
    have hbad : (Set.range input \ family i).Finite :=
      finite_range_diff hpres.2
    have htransfer := relativeLowerDensity_mono_finiteExpansion
      (Q := GenLimit.GeneratorFirst input output)
      (K := family i) (R := Set.range input)
      (hInfinite i) hpres.1 hbad
    have hhalf :
        (1 / 2 : ℝ) ≤
          relativeLowerDensity
            (GenLimit.GeneratorFirst input output ∩ Set.range input)
            (Set.range input) := by
      simpa [GenLimit.PatientMachine.patientLowerDensity, output, htargetEq] using hdensity
    exact hhalf.trans htransfer

end Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025.presentationDependentHalfDensity
