import Probe
import GenLimit.Paper17_InfiniteContamination.Definitions

open Set Filter
open scoped Topology

namespace Stage3Case019

open GenLimit
open GenLimit.Generic
open GenLimit.InfiniteContamination

noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily := by
  classical
  exact {
    language := family
    infinite' := hInfinite
    query := fun i x => if x ∈ family i then true else false
    query_spec := by intro i x; simp }

def completeHistory {n : ℕ} (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if h : k < n then xs ⟨k, h⟩ else 0

noncomputable def patientPrefixGenerator (O : GenLimit.OracleFamily) :
    Generator ℕ :=
  fun n xs => GenLimit.PatientMachine.output O (completeHistory xs) n.pred

lemma outputAfterInput_patientPrefixGenerator
    (O : GenLimit.OracleFamily) (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (patientPrefixGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  change GenLimit.PatientMachine.output O
      (completeHistory (fun i : Fin (t + 1) => input i)) t = _
  apply patientOutput_eq_of_prefix_eq
  intro k hk
  simp [completeHistory, hk]

lemma finiteNoiseFiniteOmission_of_core
    {input : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    FiniteNoiseFiniteOmissionEnumeration input K := by
  refine ⟨hinput.1, ?_, ?_⟩
  · apply (finiteNoise_iff_valuesOutside_finite_of_injective hinput.1).mpr
    exact (setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp hinput.2.2 |>.1
  · unfold FiniteOmissions
    rw [Set.diff_eq_empty.mpr hinput.2.1]
    exact Set.finite_empty

lemma prefixCount_le_add_finite_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
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
  calc
    a.card ≤ (b ∪ d).card := Finset.card_le_card hsub
    _ ≤ b.card + d.card := Finset.card_union_le _ _
    _ ≤ b.card + hfinite.toFinset.card := Nat.add_le_add_left hd _

lemma relativeLowerDensity_le_of_eventually_ratio_le
    {A K B L : Set ℕ} (hAK : A ⊆ K) (hBL : B ⊆ L)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hratio : ∀ᶠ n : ℕ in atTop,
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount L n : ℝ) + error n) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B L := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (fun n => by
      show (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount L n : ℝ) ≤ 1
      have hcount := GenLimit.PatientScope.prefixCount_mono hBL n
      by_cases hzero : GenLimit.PatientScope.prefixCount L n = 0
      · have hbzero : GenLimit.PatientScope.prefixCount B n = 0 :=
          Nat.eq_zero_of_le_zero (hcount.trans_eq hzero)
        simp [hzero, hbzero]
      · rw [div_le_one (by positivity)]
        exact_mod_cast hcount))
    (isBoundedUnder_of ⟨0, fun n => by positivity⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrDensity⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop,
      r < (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) :=
    eventually_lt_of_lt_liminf hrDensity
      (isBoundedUnder_of ⟨0, fun n => by positivity⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hratio] with n hr he hratio
  linarith

lemma relativeLowerDensity_transfer_finite_expansion
    {D K D' E : Set ℕ}
    (hK : K.Infinite) (hDK : D ⊆ K) (hD'E : D' ⊆ E)
    (hKE : K ⊆ E) (hDD' : (D' \ D).Finite) :
    GenLimit.PatientScope.relativeLowerDensity D' E ≤
      GenLimit.PatientScope.relativeLowerDensity D K := by
  let c := hDD'.toFinset.card
  let error : ℕ → ℝ := fun n =>
    (c : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hden : Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hden
  apply relativeLowerDensity_le_of_eventually_ratio_le hD'E hDK error herror
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < GenLimit.PatientScope.prefixCount K n :=
    (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hpos] with n hn
  have hnum := prefixCount_le_add_finite_diff hDD' n
  have hdenom := GenLimit.PatientScope.prefixCount_mono hKE n
  have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hn
  have heR : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n :=
    lt_of_lt_of_le hnR (by exact_mod_cast hdenom)
  have hnumR :
      (GenLimit.PatientScope.prefixCount D' n : ℝ) ≤
        GenLimit.PatientScope.prefixCount D n + c := by exact_mod_cast hnum
  dsimp [error, c]
  calc
    (GenLimit.PatientScope.prefixCount D' n : ℝ) /
        GenLimit.PatientScope.prefixCount E n
        ≤ ((GenLimit.PatientScope.prefixCount D n : ℝ) + hDD'.toFinset.card) /
            GenLimit.PatientScope.prefixCount E n :=
          div_le_div_of_nonneg_right hnumR heR.le
    _ ≤ ((GenLimit.PatientScope.prefixCount D n : ℝ) + hDD'.toFinset.card) /
            GenLimit.PatientScope.prefixCount K n := by
          apply div_le_div_of_nonneg_left
          · positivity
          · exact hnR
          · exact_mod_cast hdenom
    _ = (GenLimit.PatientScope.prefixCount D n : ℝ) /
            GenLimit.PatientScope.prefixCount K n +
          (hDD'.toFinset.card : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by rw [add_div]

lemma countable_half_density : CountableClause := by
  intro q family hInfinite
  let O := oracleOfFamily family hInfinite
  let expanded := finiteExpansionOracleFamily O
  refine ⟨patientPrefixGenerator expanded, ?_⟩
  intro i input hinput
  have hcontam : FiniteNoiseFiniteOmissionEnumeration input (O.language i) :=
    finiteNoiseFiniteOmission_of_core hinput
  obtain ⟨j, hjBase, hjPresents⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  have hpatient :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      expanded input hjPresents
  have hExpandedRange : expanded.language j = Set.range input :=
    hjPresents.symm
  have houtput :
      outputAfterInput (patientPrefixGenerator expanded) input =
        GenLimit.PatientMachine.output expanded input := by
    funext t
    exact outputAfterInput_patientPrefixGenerator expanded input t
  rw [houtput]
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT⟩ := hpatient.1
    let bad := expanded.language j \ family i
    have hbad : bad.Finite := by
      dsimp [bad]
      rw [hExpandedRange]
      exact (setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp hinput.2.2 |>.1
    obtain ⟨Tbad, hTbad⟩ := GenLimit.Generic.finset_eventually_subset_sample
      (L := Set.range input) (GenLimit.InfiniteContamination.stream_presents_range input)
      hbad.toFinset (by
        intro x hx
        have hx' : x ∈ bad := Set.Finite.mem_toFinset hbad |>.mp hx
        exact hExpandedRange ▸ hx'.1)
    refine ⟨max T Tbad, ?_⟩
    intro t ht
    have hp := hT t ((Nat.le_max_left _ _).trans ht)
    have hs : hbad.toFinset ⊆ GenLimit.Generic.sample input t := by
      intro x hx
      exact GenLimit.Generic.sample_mono
        ((Nat.le_max_right _ _).trans ht) (hTbad hx)
    refine ⟨?_, ?_, hp.2.2⟩
    · by_contra hnot
      have hxBad : GenLimit.PatientMachine.output expanded input t ∈ hbad.toFinset :=
        Set.Finite.mem_toFinset hbad |>.2 ⟨hp.1, hnot⟩
      obtain ⟨s, hslt, hseq⟩ := GenLimit.Generic.mem_sample_iff.mp (hs hxBad)
      exact hp.2.1 s (Nat.le_of_lt hslt) hseq
    · intro hsample
      obtain ⟨s, hslt, hseq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hp.2.1 s (Nat.le_of_lt_succ hslt) hseq
  · let D' := GenLimit.GeneratorFirst input
        (outputAfterInput (patientPrefixGenerator expanded) input) ∩ expanded.language j
    let D := GenLimit.GeneratorFirst input
        (outputAfterInput (patientPrefixGenerator expanded) input) ∩ family i
    have hKE : family i ⊆ expanded.language j := by
      rw [hExpandedRange]
      exact hinput.2.1
    have hdiff : (D' \ D).Finite := by
      apply ((setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp hinput.2.2).1.subset
      intro x hx
      have hxD' : x ∈ D' := hx.1
      have hxNotD : x ∉ D := hx.2
      have hxNotK : x ∉ family i := by
        intro hxK
        exact hxNotD ⟨hxD'.1, hxK⟩
      refine ⟨?_, hxNotK⟩
      rw [← hExpandedRange]
      exact hxD'.2
    exact hpatient.2.trans
      (relativeLowerDensity_transfer_finite_expansion
        (hInfinite i) (by intro x hx; exact hx.2) (by intro x hx; exact hx.2)
        hKE (by rw [← houtput]; simpa [D', D] using hdiff))

end Stage3Case019


namespace Stage3Case019

open GenLimit
open GenLimit.Generic
open GenLimit.InfiniteContamination

lemma patientPrefixGenerator_finite_contamination
    (O : GenLimit.OracleFamily) (input : Stream ℕ) (i : ℕ)
    (hinj : Function.Injective input)
    (hcovers : O.language i ⊆ Set.range input)
    (hfinite : (Set.range input \ O.language i).Finite) :
    GenLimit.NovelGeneratesInLimit input
        (outputAfterInput
          (patientPrefixGenerator (finiteExpansionOracleFamily O)) input)
        (O.language i) ∧
      (1 / 2 : ℝ) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input
              (outputAfterInput
                (patientPrefixGenerator (finiteExpansionOracleFamily O)) input) ∩
            O.language i)
          (O.language i) := by
  let expanded := finiteExpansionOracleFamily O
  have hcontam : FiniteNoiseFiniteOmissionEnumeration input (O.language i) := by
    refine ⟨hinj, ?_, ?_⟩
    · exact (finiteNoise_iff_valuesOutside_finite_of_injective hinj).mpr hfinite
    · unfold FiniteOmissions
      rw [Set.diff_eq_empty.mpr hcovers]
      exact Set.finite_empty
  obtain ⟨j, _hjBase, hjPresents⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  have hpatient :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      expanded input hjPresents
  have hExpandedRange : expanded.language j = Set.range input :=
    hjPresents.symm
  have houtput :
      outputAfterInput (patientPrefixGenerator expanded) input =
        GenLimit.PatientMachine.output expanded input := by
    funext t
    exact outputAfterInput_patientPrefixGenerator expanded input t
  rw [houtput]
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT⟩ := hpatient.1
    let bad := expanded.language j \ O.language i
    have hbad : bad.Finite := by
      dsimp [bad]
      rw [hExpandedRange]
      exact hfinite
    obtain ⟨Tbad, hTbad⟩ := GenLimit.Generic.finset_eventually_subset_sample
      (L := Set.range input) (GenLimit.InfiniteContamination.stream_presents_range input)
      hbad.toFinset (by
        intro x hx
        have hx' : x ∈ bad := Set.Finite.mem_toFinset hbad |>.mp hx
        exact hExpandedRange ▸ hx'.1)
    refine ⟨max T Tbad, ?_⟩
    intro t ht
    have hp := hT t ((Nat.le_max_left _ _).trans ht)
    have hs : hbad.toFinset ⊆ GenLimit.Generic.sample input t := by
      intro x hx
      exact GenLimit.Generic.sample_mono
        ((Nat.le_max_right _ _).trans ht) (hTbad hx)
    refine ⟨?_, ?_, hp.2.2⟩
    · by_contra hnot
      have hxBad : GenLimit.PatientMachine.output expanded input t ∈ hbad.toFinset :=
        Set.Finite.mem_toFinset hbad |>.2 ⟨hp.1, hnot⟩
      obtain ⟨s, hslt, hseq⟩ := GenLimit.Generic.mem_sample_iff.mp (hs hxBad)
      exact hp.2.1 s (Nat.le_of_lt hslt) hseq
    · intro hsample
      obtain ⟨s, hslt, hseq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hp.2.1 s (Nat.le_of_lt_succ hslt) hseq
  · let D' := GenLimit.GeneratorFirst input
        (outputAfterInput (patientPrefixGenerator expanded) input) ∩ expanded.language j
    let D := GenLimit.GeneratorFirst input
        (outputAfterInput (patientPrefixGenerator expanded) input) ∩ O.language i
    have hKE : O.language i ⊆ expanded.language j := by
      rw [hExpandedRange]
      exact hcovers
    have hdiff : (D' \ D).Finite := by
      apply hfinite.subset
      intro x hx
      have hxD' : x ∈ D' := hx.1
      have hxNotD : x ∉ D := hx.2
      have hxNotK : x ∉ O.language i := by
        intro hxK
        exact hxNotD ⟨hxD'.1, hxK⟩
      refine ⟨?_, hxNotK⟩
      rw [← hExpandedRange]
      exact hxD'.2
    exact hpatient.2.trans
      (relativeLowerDensity_transfer_finite_expansion
        (O.infinite' i) (by intro x hx; exact hx.2) (by intro x hx; exact hx.2)
        hKE (by rw [← houtput]; simpa [D', D] using hdiff))

end Stage3Case019
