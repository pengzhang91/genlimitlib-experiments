import Helpers
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open Stage3Case025

namespace Stage3Case025Local

open GenLimit
open GenLimit.PatientScope
open GenLimit.InfiniteContamination

private theorem prefixCount_le_add_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold prefixCount
  let a := (Finset.range n).filter fun x => x ∈ A
  let b := (Finset.range n).filter fun x => x ∈ B
  let d := hfinite.toFinset
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    simp only [a, b, Finset.mem_filter, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ((Set.Finite.mem_toFinset hfinite).mpr ⟨hx.2, hxB⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le b d)

private theorem relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (prefixCount A n : ℝ) / (prefixCount K n : ℝ) := by
  positivity

private theorem relativeRatio_le_one
    {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : prefixCount K n = 0
  · simp [hzero]
  · rw [div_le_one]
    · exact_mod_cast prefixCount_mono hAK n
    · exact_mod_cast Nat.pos_of_ne_zero hzero

private theorem relativeLowerDensity_le_of_finite_extension
    {A B K R : Set ℕ}
    (hAR : A ⊆ R) (hBK : B ⊆ K)
    (hfinite : (A \ B).Finite)
    (hK : K.Infinite)
    (hKR : K ⊆ R)
    (hcount : ∀ n, prefixCount A n ≤ prefixCount B n + hfinite.toFinset.card) :
    relativeLowerDensity A R ≤ relativeLowerDensity B K := by
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) / (prefixCount K n : ℝ)
  have hdenom : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_prefixCount_atTop hK)
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hdenom
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
    (tendsto_prefixCount_atTop hK).eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      (prefixCount A n : ℝ) / (prefixCount R n : ℝ) ≤
        (prefixCount B n : ℝ) / (prefixCount K n : ℝ) + error n := by
    filter_upwards [hpositive] with n hn
    have hnK : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hnR : (0 : ℝ) < prefixCount R n := by
      exact_mod_cast (lt_of_lt_of_le hn (prefixCount_mono hKR n))
    have hnum : (prefixCount A n : ℝ) ≤
        prefixCount B n + hfinite.toFinset.card := by
      exact_mod_cast hcount n
    calc
      (prefixCount A n : ℝ) / (prefixCount R n : ℝ)
          ≤ (prefixCount A n : ℝ) / (prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_left (by positivity) hnK
              (by exact_mod_cast prefixCount_mono hKR n)
      _ ≤ ((prefixCount B n : ℝ) + hfinite.toFinset.card) /
            (prefixCount K n : ℝ) :=
          div_le_div_of_nonneg_right hnum hnK.le
      _ = (prefixCount B n : ℝ) / (prefixCount K n : ℝ) + error n := by
          rw [add_div]
  unfold relativeLowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => relativeRatio_le_one hBK n))
    (isBoundedUnder_of
      ⟨0, fun n => relativeRatio_nonneg B K n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop,
      r < (prefixCount A n : ℝ) / (prefixCount R n : ℝ) :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, fun n => relativeRatio_nonneg A R n⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hcompare] with n hrn hen hcmp
  linarith

private theorem density_transfer
    (input output : Stream) (K R : Set ℕ)
    (hK : K.Infinite) (hKR : K ⊆ R) (hfinite : (R \ K).Finite) :
    relativeLowerDensity (GeneratorFirst input output ∩ R) R ≤
      relativeLowerDensity (GeneratorFirst input output ∩ K) K := by
  have hnumerator :
      ((GeneratorFirst input output ∩ R) \
        (GeneratorFirst input output ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  exact relativeLowerDensity_le_of_finite_extension
    (A := GeneratorFirst input output ∩ R)
    (B := GeneratorFirst input output ∩ K)
    (K := K) (R := R)
    Set.inter_subset_right Set.inter_subset_right hnumerator hK hKR
    (fun n => prefixCount_le_add_finite hnumerator n)

private theorem novel_transfer
    {input output : Stream} {K R : Set ℕ}
    (hpresents : GenLimit.Presents input R)
    (hfinite : (R \ K).Finite)
    (hnovel : NovelGeneratesInLimit input output R) :
    NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨T, hT⟩ := hnovel
  obtain ⟨Tseen, hseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hpresents hfinite.toFinset (by
        intro x hx
        exact (Set.Finite.mem_toFinset hfinite).mp hx |>.1)
  refine ⟨max T Tseen, ?_⟩
  intro t ht
  have htT : T ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨hR, hfresh, hnovelEarlier⟩ := hT t htT
  refine ⟨?_, hfresh, hnovelEarlier⟩
  by_contra hnotK
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hR, hnotK⟩
  have hsampleGeneric : output t ∈ GenLimit.Generic.sample input t :=
    GenLimit.Generic.sample_mono htSeen (hseen hbad)
  have hsampleT : output t ∈ GenLimit.sample input t := by
    rw [GenLimit.mem_sample_iff]
    rw [GenLimit.Generic.mem_sample_iff] at hsampleGeneric
    exact hsampleGeneric
  exact hfresh (GenLimit.sample_mono (Nat.le_succ t) hsampleT)

 theorem finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let O : GenLimit.OracleFamily := oracleFamily family hInfinite
  let expanded : ℕ → Stage3Case025.Language := finiteExpansionLanguage O
  have hExpandedInfinite : ∀ j, (expanded j).Infinite :=
    finiteExpansionLanguage_infinite O
  obtain ⟨gen, hgen⟩ := hpositive expanded hExpandedInfinite
  refine ⟨gen, ?_⟩
  intro i input hPresentation
  have hnoiseValues : (Set.range input \ family i).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hPresentation.2.image input
  let noise : Finset ℕ := hnoiseValues.toFinset
  let data : FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm noise, Finset.equivBitIndices.symm ∅)
  let j := encodeFiniteExpansionCode data
  have hnoiseSet : (noise : Set ℕ) = Set.range input \ family i := by
    exact Set.Finite.coe_toFinset hnoiseValues
  have hExpandedEq : expanded j = Set.range input := by
    change finiteExpansionLanguage O j = Set.range input
    rw [finiteExpansionLanguage]
    simp only [j, data, finiteExpansionCode_encode, Equiv.apply_symm_apply]
    rw [show O.language i = family i by rfl]
    simp only [Finset.coe_empty]
    rw [hnoiseSet]
    ext x
    simp only [finiteExpansion, Set.mem_diff, Set.mem_union,
      Set.mem_empty_iff_false, not_false_eq_true, and_true, Set.mem_range]
    constructor
    · rintro (hxK | ⟨hxRange, -⟩)
      · exact hPresentation.1 hxK
      · exact hxRange
    · intro hxRange
      by_cases hxK : x ∈ family i
      · exact Or.inl hxK
      · exact Or.inr ⟨hxRange, hxK⟩
  have hpresentsExpanded : GenLimit.Presents input (expanded j) := by
    change Set.range input = expanded j
    exact hExpandedEq.symm
  obtain ⟨output, hfollows, hnovelExpanded, hdensityExpanded⟩ :=
    hgen j input hpresentsExpanded
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply novel_transfer (R := expanded j) hpresentsExpanded
      (K := family i) ?_ hnovelExpanded
    rw [hExpandedEq]
    exact hnoiseValues
  · exact hdensityExpanded.trans
      (density_transfer input output (family i) (expanded j)
        (hInfinite i) (by
          rw [hExpandedEq]
          exact hPresentation.1)
        (by simpa [hExpandedEq] using hnoiseValues))

end Stage3Case025Local
