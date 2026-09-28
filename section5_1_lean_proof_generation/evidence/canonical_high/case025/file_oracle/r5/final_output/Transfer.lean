import Helpers

open Set Filter
open scoped Topology

namespace Stage3Case025

private theorem prefixCount_le_add_finite_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let a := GenLimit.PatientScope.prefixFinset A n
  let b := GenLimit.PatientScope.prefixFinset B n
  let d := GenLimit.PatientScope.prefixFinset (A \ B) n
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hcard : a.card ≤ b.card + d.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le b d)
  have hd : d.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2
      (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
  exact hcard.trans (Nat.add_le_add_left hd _)

private theorem relativeLowerDensity_le_of_finite_extension
    {Q K R : Set ℕ} (hKR : K ⊆ R) (hK : K.Infinite)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hKcount := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.comp hKcount
  have hKpos : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hKcount.eventually (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hKpos] with n hn
    have hnK : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdenNat : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hden : (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        GenLimit.PatientScope.prefixCount R n := by
      exact_mod_cast hdenNat
    have hbad : ((Q ∩ R) \ (Q ∩ K)).Finite := by
      apply hfinite.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hbadCard : hbad.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := (Set.Finite.mem_toFinset hbad).1 hx
      exact Set.Finite.mem_toFinset hfinite |>.2
        ⟨hx'.1.2, fun hxK => hx'.2 ⟨hx'.1.1, hxK⟩⟩
    have hnumNat : GenLimit.PatientScope.prefixCount (Q ∩ R) n ≤
        GenLimit.PatientScope.prefixCount (Q ∩ K) n +
          hfinite.toFinset.card := by
      exact (prefixCount_le_add_finite_diff hbad n).trans
        (Nat.add_le_add_left hbadCard _)
    have hnum : (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) ≤
        GenLimit.PatientScope.prefixCount (Q ∩ K) n +
          hfinite.toFinset.card := by
      exact_mod_cast hnumNat
    dsimp [source, target, error]
    calc
      (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
          GenLimit.PatientScope.prefixCount R n
          ≤ (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
              GenLimit.PatientScope.prefixCount K n :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnK hden
      _ ≤ ((GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) +
              hfinite.toFinset.card) /
              GenLimit.PatientScope.prefixCount K n :=
        (div_le_div_iff_of_pos_right hnK).2 hnum
      _ = (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
              GenLimit.PatientScope.prefixCount K n +
            (hfinite.toFinset.card : ℝ) /
              GenLimit.PatientScope.prefixCount K n := by rw [add_div]
  have hsource_nonneg : ∀ n, 0 ≤ source n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsource_le_one : ∀ n, source n ≤ 1 := by
    intro n
    dsimp [source]
    by_cases hn : GenLimit.PatientScope.prefixCount R n = 0
    · simp [hn]
    · have hnpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (show Q ∩ R ⊆ R from inter_subset_right) n
  have htarget_nonneg : ∀ n, 0 ≤ target n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htarget_le_one : ∀ n, target n ≤ 1 := by
    intro n
    dsimp [target]
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · have hnpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (show Q ∩ K ⊆ K from inter_subset_right) n
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hrs herr hp
  linarith

end Stage3Case025

namespace Stage3Case025

private theorem novelGeneratesInLimit_of_finite_extension
    {input output : Stream} {K R : Language}
    (hpresents : GenLimit.Presents input R)
    (hfinite : (R \ K).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨T, hT⟩ := hnovel
  obtain ⟨S, hS⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hpresents
      hfinite.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hfinite).1 hx).1)
  refine ⟨max T S, ?_⟩
  intro t ht
  have htT : T ≤ t := (Nat.le_max_left _ _).trans ht
  have htS : S ≤ t + 1 :=
    (Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)
  obtain ⟨hR, hfresh, hdistinct⟩ := hT t htT
  refine ⟨?_, hfresh, hdistinct⟩
  by_contra hK
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).2 ⟨hR, hK⟩
  apply hfresh
  simpa [GenLimit.Generic.sample, GenLimit.sample] using
    GenLimit.Generic.sample_mono htS (hS hbad)

end Stage3Case025

namespace Stage3Case025

private theorem exists_finiteExpansion_index_for_occurrence_stream
    (O : GenLimit.OracleFamily) {i : ℕ} {input : Stream}
    (hcover : O.language i ⊆ Set.range input)
    (hnoise : GenLimit.Generic.FinitelyManyViolations input
      (fun x => x ∈ O.language i)) :
    ∃ j, GenLimit.Presents input
      ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) := by
  classical
  let addFinite :=
    GenLimit.InfiniteContamination.displayedNoise_finite hnoise
  have removeFinite :
      (GenLimit.InfiniteContamination.displayedOmissions input
        (O.language i)).Finite := by
    rw [GenLimit.InfiniteContamination.displayedOmissions,
      Set.diff_eq_empty.mpr hcover]
    exact Set.finite_empty
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm addFinite.toFinset,
      Finset.equivBitIndices.symm removeFinite.toFinset)
  let j :=
    GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  change Set.range input =
    GenLimit.InfiniteContamination.finiteExpansionLanguage O j
  have hadd :
      (↑addFinite.toFinset : Set ℕ) =
        GenLimit.InfiniteContamination.displayedNoise input
          (O.language i) :=
    Set.Finite.coe_toFinset addFinite
  have hremove :
      (↑removeFinite.toFinset : Set ℕ) =
        GenLimit.InfiniteContamination.displayedOmissions input
          (O.language i) :=
    Set.Finite.coe_toFinset removeFinite
  rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
  simp only [j, data,
    GenLimit.InfiniteContamination.finiteExpansionCode_encode]
  simp only [Equiv.apply_symm_apply]
  rw [hadd, hremove]
  exact (GenLimit.InfiniteContamination.finiteExpansion_displayedNoise_displayedOmissions
    input (O.language i)).symm

end Stage3Case025

namespace Stage3Case025

/-- Finite occurrence noise transfers the exact-presentation engine through
an explicitly enumerated family of finite expansions. -/
theorem finiteNoiseTransfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinf
  let O := oracleOfFamily family hinf
  let expandedO :=
    GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ :=
    hpositive expandedO.language expandedO.infinite'
  refine ⟨gen, ?_⟩
  intro i input hinput
  have hcover : O.language i ⊆ Set.range input := by
    simpa [O, oracleOfFamily] using hinput.1
  have hnoise : GenLimit.Generic.FinitelyManyViolations input
      (fun x => x ∈ O.language i) := by
    simpa [O, oracleOfFamily] using hinput.2
  obtain ⟨j, hpresents⟩ :=
    exists_finiteExpansion_index_for_occurrence_stream O hcover hnoise
  obtain ⟨output, hfollows, hnovel, hdensity⟩ :=
    hgen j input hpresents
  have htarget : family i ⊆ expandedO.language j := by
    intro x hx
    rw [← hpresents]
    exact hinput.1 hx
  have hextraneous : (expandedO.language j \ family i).Finite := by
    rw [← hpresents]
    exact GenLimit.InfiniteContamination.displayedNoise_finite hinput.2
  refine ⟨output, hfollows, ?_, ?_⟩
  · exact novelGeneratesInLimit_of_finite_extension
      hpresents hextraneous hnovel
  · exact hdensity.trans
      (relativeLowerDensity_le_of_finite_extension
        htarget (hinf i) hextraneous)

end Stage3Case025
