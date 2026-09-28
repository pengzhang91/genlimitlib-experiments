import Case019PatientBridge
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set Filter
open scoped Topology

namespace Stage3Case019

open GenLimit.Generic

private noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem prefixCount_le_add_of_diff_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let a := (Finset.range n).filter fun x => x ∈ A
  let b := (Finset.range n).filter fun x => x ∈ B
  let d := (Finset.range n).filter fun x => x ∈ A \ B
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    simp only [a, b, d, Finset.mem_filter, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hd : d.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [d, Finset.mem_filter] at hx
    exact Set.Finite.mem_toFinset hfinite |>.2 hx.2
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le b d).trans (Nat.add_le_add_left hd _))

private theorem liminf_le_of_ratio_finite_error
    (source target error : ℕ → ℝ)
    (hsourceLower : ∀ n, 0 ≤ source n)
    (hsourceUpper : ∀ n, source n ≤ 1)
    (htargetLower : ∀ n, 0 ≤ target n)
    (htargetUpper : ∀ n, target n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hle : ∀ᶠ n in atTop, source n ≤ target n + error n) :
    liminf source atTop ≤ liminf target atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htargetUpper)
    (isBoundedUnder_of ⟨0, htargetLower⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n in atTop, r < source n := by
    exact eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, hsourceLower⟩)
  have heEventually : ∀ᶠ n in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, heEventually, hle] with n hrs he hs
  linarith

private theorem relativeLowerDensity_transfer_finite_expansion
    {A B K E : Set ℕ}
    (hK : K.Infinite) (hBK : B ⊆ K) (hAE : A \ B ⊆ E)
    (hE : E.Finite) (hAExpanded : A ⊆ E ∪ K) :
    GenLimit.PatientScope.relativeLowerDensity A (E ∪ K) ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  have hdiff : (A \ B).Finite := hE.subset hAE
  let c := hdiff.toFinset.card
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      GenLimit.PatientScope.prefixCount (E ∪ K) n
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  let error : ℕ → ℝ := fun n =>
    (c : ℝ) / GenLimit.PatientScope.prefixCount K n
  have hcountAB := prefixCount_le_add_of_diff_finite hdiff
  have hdenom : ∀ n,
      GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount (E ∪ K) n :=
    fun n => GenLimit.PatientScope.prefixCount_mono (by intro x hx; exact Or.inr hx) n
  have hsourceLower : ∀ n, 0 ≤ source n := fun n => div_nonneg (by positivity) (by positivity)
  have hsourceUpper : ∀ n, source n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount (E ∪ K) n = 0
    · simp [source, hn]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAExpanded n
  have htargetLower : ∀ n, 0 ≤ target n := fun n => div_nonneg (by positivity) (by positivity)
  have htargetUpper : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [target, hn]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp
        (GenLimit.PatientScope.tendsto_prefixCount_atTop hK))
  have hle : ∀ᶠ n in atTop, source n ≤ target n + error n := by
    have hpos : ∀ᶠ n in atTop, 0 < GenLimit.PatientScope.prefixCount K n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hkR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hn
    have heR : (0 : ℝ) < GenLimit.PatientScope.prefixCount (E ∪ K) n := by
      exact lt_of_lt_of_le hkR (by exact_mod_cast hdenom n)
    have hc :
        (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
          GenLimit.PatientScope.prefixCount B n + c := by
      exact_mod_cast hcountAB n
    dsimp [source, target, error]
    calc
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
          GenLimit.PatientScope.prefixCount (E ∪ K) n
          ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
              GenLimit.PatientScope.prefixCount K n := by
              exact div_le_div_of_nonneg_left (by positivity) hkR
                (by exact_mod_cast hdenom n)
      _ ≤ ((GenLimit.PatientScope.prefixCount B n : ℝ) + c) /
              GenLimit.PatientScope.prefixCount K n :=
            div_le_div_of_nonneg_right hc hkR.le
      _ = _ := by rw [add_div]
  unfold GenLimit.PatientScope.relativeLowerDensity
  exact liminf_le_of_ratio_finite_error source target error
    hsourceLower hsourceUpper htargetLower htargetUpper herror hle

private theorem countableHalfDensity (q : ℕ) : CountableHalfDensity q := by
  intro family hinf
  let O := oracleOfFamily family hinf
  let EO := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator EO, ?_⟩
  intro i input hinput
  have hnoise : (Set.range input \ family i).Finite :=
    (GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le _ _ q).mp hinput.2.2 |>.1
  have homit : (family i \ Set.range input).Finite := by
    simpa [Set.diff_eq_empty.mpr hinput.2.1]
  have hp17noise : GenLimit.InfiniteContamination.FiniteNoise input (O.language i) :=
    (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
      hinput.1).mpr hnoise
  have hcontam : GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
      input (O.language i) := ⟨hinput.1, hp17noise, homit⟩
  obtain ⟨j, hj, hpresent⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hrun := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity EO input hpresent
  have hout := outputAfterInput_patientGenerator EO input
  constructor
  · obtain ⟨T, hT⟩ := hrun.1
    have hnoiseSeen : ∃ N, ∀ x ∈ Set.range input \ family i, ∃ s ≤ N, input s = x := by
      classical
      let witness : ℕ → ℕ := fun x =>
        if hx : x ∈ Set.range input then Nat.find hx else 0
      refine ⟨hnoise.toFinset.sup witness, ?_⟩
      intro x hx
      have hxF : x ∈ hnoise.toFinset := Set.Finite.mem_toFinset hnoise |>.2 hx
      have hxrange : x ∈ Set.range input := hx.1
      refine ⟨witness x, Finset.le_sup hxF, ?_⟩
      simp only [witness, dif_pos hxrange]
      exact Nat.find_spec hxrange
    obtain ⟨N, hN⟩ := hnoiseSeen
    refine ⟨max T N, ?_⟩
    intro t ht
    have hv := hT t (le_trans (le_max_left _ _) ht)
    rw [← hout t] at hv
    refine ⟨?_, ?_, ?_⟩
    · have hrange : outputAfterInput (patientGenerator EO) input t ∈ Set.range input := by
        rw [hpresent]
        exact hv.1
      by_contra hnot
      obtain ⟨s, hsN, hs⟩ := hN _ ⟨hrange, hnot⟩
      exact hv.2.1 s (by omega) hs
    · intro hsample
      rw [GenLimit.mem_sample_iff] at hsample
      obtain ⟨s, hslt, hs⟩ := hsample
      exact hv.2.1 s (by omega) hs
    · intro s hs
      rw [hout s]
      exact hv.2.2 s hs
  · have hdensity : (1 / 2 : ℝ) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input (outputAfterInput (patientGenerator EO) input) ∩ EO.language j)
          (EO.language j) := by
      have houtfun : outputAfterInput (patientGenerator EO) input =
          GenLimit.PatientMachine.output EO input := funext hout
      rw [houtfun]
      exact hrun.2
    have hrange : EO.language j = Set.range input := hpresent.symm
    have hEK : Set.range input = (Set.range input \ family i) ∪ family i := by
      ext x
      constructor
      · intro hx
        by_cases hxi : x ∈ family i
        · exact Or.inr hxi
        · exact Or.inl ⟨hx, hxi⟩
      · rintro (hx | hx)
        · exact hx.1
        · exact hinput.2.1 hx
    have htransfer := relativeLowerDensity_transfer_finite_expansion
      (A := GenLimit.GeneratorFirst input (outputAfterInput (patientGenerator EO) input) ∩ EO.language j)
      (B := GenLimit.GeneratorFirst input (outputAfterInput (patientGenerator EO) input) ∩ family i)
      (K := family i) (E := Set.range input \ family i)
      (hinf i) Set.inter_subset_right (by
        intro x hx
        refine ⟨?_, ?_⟩
        · simpa [hrange] using hx.1.2
        · intro hxi
          exact hx.2 ⟨hx.1.1, hxi⟩)
      hnoise (by
        intro x hx
        rw [hrange] at hx
        rw [hEK] at hx
        exact hx.2)
    rw [← hEK, ← hrange] at htransfer
    exact hdensity.trans htransfer

theorem countableClause_checked : CountableClause := by
  intro q
  exact countableHalfDensity q

end Stage3Case019
