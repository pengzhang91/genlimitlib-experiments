import Helpers

open Filter
open scoped Topology

namespace Stage3Case019

open GenLimit

noncomputable def semanticOracle
    (family : LanguageFamily ℕ) (hInfinite : ∀ i, (family i).Infinite) :
    OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem finiteContamination_of_atMost
    {stream : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (h : Generic.InjectiveValueContaminatedPresentationAtMost stream K q) :
    InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration stream K := by
  have hfinite : (Set.range stream \ K).Finite :=
    (Generic.setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp h.2.2 |>.1
  refine ⟨h.1, ?_, ?_⟩
  · exact (InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective h.1).mpr hfinite
  · rw [InfiniteContamination.FiniteOmissions, Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty

private theorem novel_transfer_of_finite_expansion
    {stream output : ℕ → ℕ} {K E : Set ℕ}
    (hpresents : Generic.Presents stream E)
    (hfinite : (E \ K).Finite)
    (hnovel : ∃ T, ∀ t, T ≤ t →
      output t ∈ E ∧
      (∀ s, s ≤ t → stream s ≠ output t) ∧
      (∀ s, s < t → output s ≠ output t)) :
    GenLimit.NovelGeneratesInLimit stream output K := by
  classical
  obtain ⟨T, hT⟩ := hnovel
  obtain ⟨Tseen, hseen⟩ :=
    Generic.finset_eventually_subset_sample hpresents hfinite.toFinset (by
      intro x hx
      exact ((Set.Finite.mem_toFinset hfinite).mp hx).1)
  refine ⟨max T Tseen, ?_⟩
  intro t ht
  have htT : T ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨houtE, hfresh, hnew⟩ := hT t htT
  have hsample : hfinite.toFinset ⊆ Generic.sample stream (t + 1) := by
    intro x hx
    exact Generic.sample_mono (Nat.le.step htSeen) (hseen hx)
  refine ⟨?_, ?_, hnew⟩
  · by_contra houtK
    have hbad : output t ∈ hfinite.toFinset :=
      (Set.Finite.mem_toFinset hfinite).mpr ⟨houtE, houtK⟩
    have hmem := hsample hbad
    rw [Generic.mem_sample_iff] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact hfresh s (by omega) heq
  · rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hs, heq⟩
    exact hfresh s (by omega) heq

 theorem stage3_countable_half_density : CountableClause := by
  intro q family hInfinite
  let O := semanticOracle family hInfinite
  let expanded := InfiniteContamination.finiteExpansionOracleFamily O
  let gen := PatientCausal.generator expanded
  refine ⟨gen, ?_⟩
  intro i input hinput
  let hcontam := finiteContamination_of_atMost hinput
  obtain ⟨j, hjBase, hjPresents⟩ :=
    InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hpatient := PatientMachine.patientScope_generation_and_lowerDensity
    expanded input hjPresents
  have houtput : ∀ t,
      outputAfterInput gen input t = PatientMachine.output expanded input t :=
    PatientCausal.output_generator expanded input
  have hE : expanded.language j = Set.range input := by
    exact hjPresents.symm
  have hfinite : (expanded.language j \ family i).Finite := by
    rw [hE]
    exact (Generic.setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp hinput.2.2 |>.1
  constructor
  · apply novel_transfer_of_finite_expansion hjPresents hfinite
    simpa only [houtput] using hpatient.1
  · have hdensityExpanded :
        (1 / 2 : ℝ) ≤ PatientScope.relativeLowerDensity
          (GeneratorFirst input (outputAfterInput gen input) ∩ expanded.language j)
          (expanded.language j) := by
      have houtfun : outputAfterInput gen input = PatientMachine.output expanded input :=
        funext houtput
      rw [houtfun]
      exact hpatient.2
    exact hdensityExpanded.trans
      (FiniteDensityTransfer.relativeLowerDensity_inter_mono_finite_expansion
        (A := GeneratorFirst input (outputAfterInput gen input))
        (hInfinite i) (by simpa [hE] using hinput.2.1) hfinite)

end Stage3Case019
