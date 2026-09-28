import output.DensityTransfer

open Stage3Case019
open GenLimit
open GenLimit.Generic

namespace Case019

noncomputable def oracleOfFamily
    (family : Stage3Case019.LanguageFamily ℕ)
    (hinfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

lemma boundedPresentation_finiteContamination
    {input : Stage3Case019.Stream ℕ} {K : Set ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration input K := by
  refine ⟨h.1, ?_, ?_⟩
  · apply (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective h.1).mpr
    exact (GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp h.2.2 |>.1
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty

lemma countable_half_density_fixed
    (q : ℕ) : Stage3Case019.CountableHalfDensity q := by
  intro family hinfinite
  let O := oracleOfFamily family hinfinite
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  let gen := patientPrefixGenerator E
  refine ⟨gen, ?_⟩
  intro i input hinput
  have hcontam := boundedPresentation_finiteContamination hinput
  obtain ⟨j, hjBase, hjPresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hrun :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity E input hjPresents
  have hout : outputAfterInput gen input = GenLimit.PatientMachine.output E input := by
    funext t
    exact patientPrefixGenerator_output E input t
  have hKE : family i ⊆ E.language j := by
    intro x hx
    rw [← hjPresents]
    exact hinput.2.1 hx
  have hextraneous : (E.language j \ family i).Finite := by
    rw [← hjPresents]
    exact GenLimit.InfiniteContamination.displayedNoise_finite hcontam.2.1
  have hnovelPatient : GenLimit.NovelGeneratesInLimit
      input (GenLimit.PatientMachine.output E input) (family i) := by
    obtain ⟨Tvalid, hvalid⟩ := hrun.1
    obtain ⟨Tseen, hseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample hjPresents
        hextraneous.toFinset (by
          intro x hx
          exact ((Set.Finite.mem_toFinset hextraneous).mp hx).1)
    refine ⟨max Tvalid Tseen, ?_⟩
    intro t ht
    have hv := hvalid t ((Nat.le_max_left _ _).trans ht)
    have hseenNow : hextraneous.toFinset ⊆ GenLimit.sample input (t + 1) := by
      intro x hx
      simpa [GenLimit.sample, GenLimit.Generic.sample] using
        (GenLimit.Generic.sample_mono
          ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)) (hseen hx))
    refine ⟨?_, ?_, hv.2.2⟩
    · by_contra houtside
      have hbad : GenLimit.PatientMachine.output E input t ∈ hextraneous.toFinset :=
        (Set.Finite.mem_toFinset hextraneous).mpr ⟨hv.1, houtside⟩
      have hsample : GenLimit.PatientMachine.output E input t ∈
          GenLimit.sample input (t + 1) := hseenNow hbad
      have hfresh : GenLimit.PatientMachine.output E input t ∉
          GenLimit.sample input (t + 1) := by
        intro hm
        obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hm
        exact hv.2.1 s (by omega) heq
      exact hfresh hsample
    · intro hm
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hm
      exact hv.2.1 s (by omega) heq
  constructor
  · rw [hout]
    exact hnovelPatient
  · rw [hout]
    have htransfer := relativeLowerDensity_finite_extension
      (K := family i) (E := E.language j)
      (D := GenLimit.GeneratorFirst input (GenLimit.PatientMachine.output E input))
      (hinfinite i) hKE hextraneous
    exact hrun.2.trans htransfer

end Case019
