import Positive
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

open Stage3Case025

namespace Case025

open GenLimit

namespace Transfer

noncomputable def prefixRatio (A K : Set ℕ) (n : ℕ) : ℝ :=
  (PatientScope.prefixCount A n : ℝ) / (PatientScope.prefixCount K n : ℝ)

lemma prefixRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ prefixRatio A K n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma prefixRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    prefixRatio A K n ≤ 1 := by
  by_cases hn : PatientScope.prefixCount K n = 0
  · simp [prefixRatio, hn]
  · rw [prefixRatio, div_le_one]
    · exact_mod_cast PatientScope.prefixCount_mono hAK n
    · exact_mod_cast Nat.pos_of_ne_zero hn

lemma relativeLowerDensity_le_of_eventually_ratio_le
    {source output : ℕ → ℝ}
    (hsource_nonneg : ∀ n, 0 ≤ source n)
    (houtput_nonneg : ∀ n, 0 ≤ output n)
    (houtput_le_one : ∀ n, output n ≤ 1)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n) :
    liminf source atTop ≤ liminf output atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop houtput_le_one)
    (isBoundedUnder_of ⟨0, houtput_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrDensity⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrDensity
      (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr hsmall hcount
  linarith

lemma prefixCount_le_add_finite {A B : Set ℕ}
    (hfinite : (A \ B).Finite) (n : ℕ) :
    PatientScope.prefixCount A n ≤
      PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := PatientScope.prefixFinset A n
  let bPrefix := PatientScope.prefixFinset B n
  let diffPrefix := PatientScope.prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    simp only [aPrefix, bPrefix, diffPrefix, PatientScope.mem_prefixFinset,
      Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hcard : aPrefix.card ≤ bPrefix.card + diffPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2
      ((PatientScope.mem_prefixFinset.mp hx).2)
  exact hcard.trans (Nat.add_le_add_left hdiff _)

lemma relativeLowerDensity_mono_finite_extension
    {A K R : Set ℕ} (hKR : K ⊆ R) (hK : K.Infinite)
    (hfinite : (R \ K).Finite) :
    PatientScope.relativeLowerDensity (A ∩ R) R ≤
      PatientScope.relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := prefixRatio (A ∩ R) R
  let output : ℕ → ℝ := prefixRatio (A ∩ K) K
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) / (PatientScope.prefixCount K n : ℝ)
  have hcountK := PatientScope.tendsto_prefixCount_atTop hK
  have hdenom : Tendsto (fun n => (PatientScope.prefixCount K n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hdenom
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < PatientScope.prefixCount K n :=
    hcountK.eventually (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n := by
    filter_upwards [hpositive] with n hn
    have hkR : (0 : ℝ) < PatientScope.prefixCount K n := by exact_mod_cast hn
    have hdiffSubset : (A ∩ R) \ (A ∩ K) ⊆ R \ K := by
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hdiffFinite : ((A ∩ R) \ (A ∩ K)).Finite :=
      hfinite.subset hdiffSubset
    have hdiffCard : hdiffFinite.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      rw [Set.Finite.mem_toFinset] at hx ⊢
      exact hdiffSubset hx
    have hnum0 := prefixCount_le_add_finite hdiffFinite n
    have hnum : PatientScope.prefixCount (A ∩ R) n ≤
        PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card :=
      hnum0.trans (Nat.add_le_add_left hdiffCard _)
    have hcast : (PatientScope.prefixCount (A ∩ R) n : ℝ) ≤
        PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hnum
    calc
      source n = (PatientScope.prefixCount (A ∩ R) n : ℝ) /
          PatientScope.prefixCount R n := rfl
      _ ≤ (PatientScope.prefixCount (A ∩ R) n : ℝ) /
          PatientScope.prefixCount K n := by
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hkR
          (by exact_mod_cast PatientScope.prefixCount_mono hKR n)
      _ ≤ (PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card : ℝ) /
          PatientScope.prefixCount K n :=
        div_le_div_of_nonneg_right hcast hkR.le
      _ = output n + error n := by rw [add_div]; rfl
  change liminf source atTop ≤ liminf output atTop
  exact relativeLowerDensity_le_of_eventually_ratio_le
    (fun n => prefixRatio_nonneg _ _ n)
    (fun n => prefixRatio_nonneg _ _ n)
    (fun n => prefixRatio_le_one Set.inter_subset_right n)
    error herror hprefix

end Transfer

end Case025

namespace Case025

open GenLimit

namespace Transfer

noncomputable def additionFamily (family : ℕ → Stage3Case025.Language) (n : ℕ) : Stage3Case025.Language :=
  family (Nat.unpair n).1 ∪ (Finset.equivBitIndices (Nat.unpair n).2 : Set ℕ)

lemma additionFamily_infinite {family : ℕ → Stage3Case025.Language}
    (hinf : ∀ i, (family i).Infinite) (n : ℕ) :
    (additionFamily family n).Infinite :=
  (hinf (Nat.unpair n).1).mono Set.subset_union_left

lemma exists_addition_index {family : ℕ → Stage3Case025.Language} {i : ℕ} {R : Set ℕ}
    (hsub : family i ⊆ R) (hfinite : (R \ family i).Finite) :
    ∃ j, additionFamily family j = R := by
  classical
  let F : Finset ℕ := hfinite.toFinset
  let j := Nat.pair i (Finset.equivBitIndices.symm F)
  refine ⟨j, ?_⟩
  have hR : R = family i ∪ (R \ family i) := by
    ext x
    constructor <;> intro hx
    · by_cases hxK : x ∈ family i
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    · exact Or.elim hx (fun h => hsub h) (fun h => h.1)
  rw [hR]
  simp [additionFamily, j, F]

lemma range_diff_finite {input : Stream} {K : Stage3Case025.Language}
    (hviol : Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  change (InfiniteContamination.displayedNoise input K).Finite
  rw [InfiniteContamination.displayedNoise_eq_image_badTimes]
  change ({t | input t ∉ K}).Finite at hviol
  exact hviol.image input

lemma novel_of_finite_extension {input output : Stream} {K R : Stage3Case025.Language}
    (hfinite : (R \ K).Finite)
    (hnovel : NovelGeneratesInLimit input output R) :
    NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨T, hT⟩ := hnovel
  let badTimes : Set ℕ := {t | T ≤ t ∧ output t ∈ R \ K}
  have hinj : Set.InjOn output badTimes := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hablt | hbalt
    · exact (hT b hb.1).2.2 a hablt hab
    · exact (hT a ha.1).2.2 b hbalt hab.symm
  have himage : (output '' badTimes).Finite :=
    hfinite.subset (by
      rintro x ⟨t, ht, rfl⟩
      exact ht.2)
  have hbadFinite : badTimes.Finite := himage.of_finite_image hinj
  have heventual : ∀ᶠ t : ℕ in atTop, t ∉ badTimes := by
    have h := hbadFinite.eventually_cofinite_notMem
    rw [Nat.cofinite_eq_atTop] at h
    exact h
  obtain ⟨T', hT'⟩ := Filter.eventually_atTop.mp heventual
  refine ⟨max T T', ?_⟩
  intro t ht
  have htT : T ≤ t := (Nat.le_max_left _ _).trans ht
  have htT' : T' ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨hR, hfresh, hinjective⟩ := hT t htT
  refine ⟨?_, hfresh, hinjective⟩
  by_contra hnotK
  exact hT' t htT' ⟨htT, hR, hnotK⟩

lemma finiteNoiseTransfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinf
  have hexpInf : ∀ j, (additionFamily family j).Infinite :=
    additionFamily_infinite hinf
  obtain ⟨gen, hgen⟩ := hpositive (additionFamily family) hexpInf
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  let K := family i
  let R : Stage3Case025.Language := Set.range input
  have hKR : K ⊆ R := hpresentation.1
  have hfinite : (R \ K).Finite := range_diff_finite hpresentation.2
  obtain ⟨j, hj⟩ := exists_addition_index hKR hfinite
  have hpresents : Presents input (additionFamily family j) := by
    change Set.range input = additionFamily family j
    exact hj.symm
  obtain ⟨output, hfollows, hnovelR, hdensityR⟩ := hgen j input hpresents
  rw [hj] at hnovelR hdensityR
  refine ⟨output, hfollows, novel_of_finite_extension hfinite hnovelR, ?_⟩
  exact hdensityR.trans
    (relativeLowerDensity_mono_finite_extension hKR (hinf i) hfinite)

end Transfer

end Case025
