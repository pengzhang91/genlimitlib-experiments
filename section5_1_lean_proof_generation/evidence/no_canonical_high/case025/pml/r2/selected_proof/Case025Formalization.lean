import Stage3Model
import output.PatientCausality
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Combinatorics.Colex

open Stage3Case025
open GenLimit

noncomputable section

private def oracleOfFamily (family : ℕ → GenLimit.Language)
    (hInfinite : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private def patientOnlineGenerator (O : OracleFamily) : OnlineGenerator :=
  fun t input _ =>
    GenLimit.PatientMachine.output O
      (fun n => if h : n < t + 1 then input ⟨n, h⟩ else 0) t

private theorem follows_patientOnlineGenerator
    (O : OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply Stage3Case025.patient_output_congr
  intro n hn
  simp [patientOnlineGenerator, hn]

private theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  have hP' : GenLimit.Presents input (O.language i) := by
    simpa [O, oracleOfFamily] using hP
  have hRun := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    O input (z := i) hP'
  refine ⟨output, follows_patientOnlineGenerator O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hRun.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hinj⟩ := hT t ht
    refine ⟨?_, ?_, hinj⟩
    · simpa [O, oracleOfFamily] using hmem
    intro hs
    rw [GenLimit.mem_sample_iff] at hs
    obtain ⟨s, hst, hs⟩ := hs
    exact hfresh s (Nat.le_of_lt_succ hst) hs
  · simpa [output, GenLimit.PatientMachine.patientLowerDensity,
      O, oracleOfFamily] using hRun.2


open Filter

private theorem prefixCount_le_ncard_of_finite
    {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  exact Set.Finite.mem_toFinset hF |>.2
    (GenLimit.PatientScope.mem_prefixFinset.mp hx).2

private theorem prefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let a := GenLimit.PatientScope.prefixFinset A n
  let b := GenLimit.PatientScope.prefixFinset B n
  let d := GenLimit.PatientScope.prefixFinset (A \ B) n
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    simp only [a, b, d, Finset.mem_union,
      GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hcard : a.card ≤ b.card + d.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le b d)
  have hd : d.card ≤ hfinite.toFinset.card := by
    simpa [d, GenLimit.PatientScope.prefixCount] using
      prefixCount_le_ncard_of_finite hfinite n
  simpa [a, b, d, GenLimit.PatientScope.prefixCount] using
    hcard.trans (Nat.add_le_add_left hd _)

private theorem relativeLowerDensity_le_of_finite_diff
    {A B K : Set ℕ} (hK : K.Infinite)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hfinite : (A \ B).Finite) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  let ratio : Set ℕ → ℕ → ℝ := fun S n =>
    (GenLimit.PatientScope.prefixCount S n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have herror : Tendsto error atTop (nhds 0) := by
    have hden : Tendsto
        (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
    exact tendsto_const_nhds.div_atTop hden
  have hratio_nonneg : ∀ S n, 0 ≤ ratio S n := by
    intro S n
    exact div_nonneg (by positivity) (by positivity)
  have hratio_le_one : ∀ {S}, S ⊆ K → ∀ n, ratio S n ≤ 1 := by
    intro S hS n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratio, hn]
    · have hnpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      change (GenLimit.PatientScope.prefixCount S n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one hnpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hS n
  have hprefix : ∀ n, ratio A n ≤ ratio B n + error n := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratio, error, hn]
    · have hnnonneg : (0 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
        positivity
      have hcount :
          (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
            GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
        exact_mod_cast prefixCount_le_add_ncard_diff hfinite n
      simp only [ratio, error]
      rw [← add_div]
      exact div_le_div_of_nonneg_right hcount hnnonneg
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf (ratio A) atTop ≤ liminf (ratio B) atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (hratio_le_one hBK))
    (isBoundedUnder_of ⟨0, hratio_nonneg B⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < ratio A n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, hratio_nonneg A⟩)
  have herrEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrEventually] with n hrn hen
  have hp := hprefix n
  linarith

private theorem relativeLowerDensity_anti_right
    {A K E : Set ℕ} (hAK : A ⊆ K) (hKE : K ⊆ E) :
    GenLimit.PatientScope.relativeLowerDensity A E ≤
      GenLimit.PatientScope.relativeLowerDensity A K := by
  let ratio : Set ℕ → ℕ → ℝ := fun S n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount S n : ℝ)
  have hnonneg : ∀ S n, 0 ≤ ratio S n := by
    intro S n
    exact div_nonneg (by positivity) (by positivity)
  have hright_le_one : ∀ n, ratio K n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratio, hn]
    · have hnpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      change (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one hnpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n
  have hpoint : ∀ n, ratio E n ≤ ratio K n := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · have ha : GenLimit.PatientScope.prefixCount A n = 0 :=
        Nat.eq_zero_of_le_zero
          ((GenLimit.PatientScope.prefixCount_mono hAK n).trans_eq hn)
      simp [ratio, ha]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      exact div_le_div_of_nonneg_left (by positivity) hkpos
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hKE n)
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf (ratio E) atTop ≤ liminf (ratio K) atTop
  exact liminf_le_liminf (Eventually.of_forall hpoint)
    (isBoundedUnder_of ⟨0, hnonneg E⟩)
    (isCoboundedUnder_ge_of_le atTop hright_le_one)

private def expansionData (n : ℕ) : ℕ × ℕ := Nat.unpair n

private noncomputable def expandedFamily
    (family : ℕ → Set ℕ) (n : ℕ) : Set ℕ :=
  family (expansionData n).1 ∪
    (Finset.equivBitIndices (expansionData n).2 : Set ℕ)

private theorem expandedFamily_infinite
    (family : ℕ → Set ℕ) (hInfinite : ∀ i, (family i).Infinite) (n : ℕ) :
    (expandedFamily family n).Infinite :=
  (hInfinite (expansionData n).1).mono Set.subset_union_left

private theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hPositive family hInfinite
  have hExpandedInfinite : ∀ n, (expandedFamily family n).Infinite :=
    expandedFamily_infinite family hInfinite
  obtain ⟨gen, hgen⟩ := hPositive (expandedFamily family) hExpandedInfinite
  refine ⟨gen, ?_⟩
  intro i input hComplete
  let K := family i
  have hNoise : (Set.range input \ K).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hComplete.2.image input
  let noiseCode := Finset.equivBitIndices.symm hNoise.toFinset
  let j := Nat.pair i noiseCode
  have hjData : expansionData j = (i, noiseCode) := by
    simp [expansionData, j]
  have hNoiseCode :
      (Finset.equivBitIndices noiseCode : Set ℕ) = Set.range input \ K := by
    have hfinset : Finset.equivBitIndices noiseCode = hNoise.toFinset := by
      exact Equiv.apply_symm_apply Finset.equivBitIndices hNoise.toFinset
    rw [hfinset]
    exact Set.Finite.coe_toFinset hNoise
  have hExpanded : expandedFamily family j = Set.range input := by
    rw [expandedFamily, hjData, hNoiseCode]
    ext x
    constructor
    · rintro (hxK | ⟨hx, -⟩)
      · exact hComplete.1 hxK
      · exact hx
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  have hP : GenLimit.Presents input (expandedFamily family j) := hExpanded.symm
  obtain ⟨output, hFollows, hNovel, hDensity⟩ := hgen j input hP
  refine ⟨output, hFollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hNovel
    let badTimes : Set ℕ := {t | T ≤ t ∧ output t ∉ K}
    have hExtra : (expandedFamily family j \ K).Finite := by
      rw [expandedFamily, hjData, hNoiseCode]
      apply hNoise.subset
      intro x hx
      rcases hx.1 with hxK | hxNoise
      · exact False.elim (hx.2 hxK)
      · exact hxNoise
    have hbadFinite : badTimes.Finite := by
      apply Set.Finite.of_injOn
        (f := output) (t := expandedFamily family j \ K)
      · intro t ht
        exact ⟨(hT t ht.1).1, ht.2⟩
      · intro s hs t ht hEq
        by_cases hst : s < t
        · exact False.elim ((hT t ht.1).2.2 s hst hEq)
        · by_cases hts : t < s
          · exact False.elim ((hT s hs.1).2.2 t hts hEq.symm)
          · omega
      · exact hExtra
    obtain ⟨B, hB⟩ := bddAbove_def.mp hbadFinite.bddAbove
    refine ⟨max T (B + 1), ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    obtain ⟨hmemExpanded, hfresh, hinj⟩ := hT t htT
    refine ⟨?_, hfresh, hinj⟩
    by_contra htK
    have htBad : t ∈ badTimes := ⟨htT, htK⟩
    have htB := hB t htBad
    have hBt : B + 1 ≤ t := le_trans (le_max_right _ _) ht
    omega
  · let A := GenLimit.GeneratorFirst input output ∩ family i
    let E := expandedFamily family j
    have hKE : family i ⊆ E := by
      intro x hx
      simp [E, expandedFamily, hjData, hx]
    have hAE : A ⊆ E := fun x hx => hKE hx.2
    have hBigSub : GenLimit.GeneratorFirst input output ∩ E ⊆ E := Set.inter_subset_right
    have hdiff :
        ((GenLimit.GeneratorFirst input output ∩ E) \ A).Finite := by
      apply hNoise.subset
      intro x hx
      have hxE := hx.1.2
      have hxNotK : x ∉ family i := by
        intro hxK
        exact hx.2 ⟨hx.1.1, hxK⟩
      change x ∈ expandedFamily family j at hxE
      rw [hExpanded] at hxE
      exact ⟨hxE, hxNotK⟩
    have hremove := relativeLowerDensity_le_of_finite_diff
      (hExpandedInfinite j) hBigSub hAE hdiff
    have hdenom := relativeLowerDensity_anti_right
      (A := A) (K := family i) (E := E) (fun x hx => hx.2) hKE
    exact hDensity.trans (hremove.trans hdenom)


/-- Primary endpoint: presentation-dependent half density under finite
occurrence-counted contamination. -/
theorem stage3_result : Stage3Case025.MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
