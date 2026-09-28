import output.Helpers
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set
open Stage3Case019

namespace Case019

noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ)
    (hinfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily := by
  classical
  exact {
    language := family
    infinite' := hinfinite
    query := fun i x => decide (x ∈ family i)
    query_spec := by simp }

theorem countable_half_density (q : ℕ) : CountableHalfDensity q := by
  intro family hinfinite
  let O := oracleOfFamily family hinfinite
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientPrefixGenerator E, ?_⟩
  intro i input hpresentation
  have hfiniteRange : (Set.range input \ family i).Finite := by
    rcases hpresentation.2.2 with ⟨F, hF, _⟩
    rw [← hF]
    exact F.finite_toSet
  have hnoise : GenLimit.InfiniteContamination.FiniteNoise input (family i) :=
    (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
      hpresentation.1).2 hfiniteRange
  have hcontam :
      GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
        input (O.language i) := by
    refine ⟨hpresentation.1, ?_, ?_⟩
    · simpa [O, oracleOfFamily] using hnoise
    · simp [GenLimit.InfiniteContamination.FiniteOmissions, O, oracleOfFamily,
        Set.diff_eq_empty.mpr hpresentation.2.1]
  obtain ⟨j, _hj, hpresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hrun :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity E input hpresents
  have hKR : family i ⊆ E.language j := by
    intro x hx
    rw [← hpresents]
    exact hpresentation.2.1 hx
  have hfinite : (E.language j \ family i).Finite := by
    rw [← hpresents]
    exact hfiniteRange
  constructor
  · obtain ⟨Trun, hTrun⟩ := hrun.1
    obtain ⟨Tseen, hTseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample hpresents hfinite.toFinset (by
        intro x hx
        exact (Set.Finite.mem_toFinset hfinite |>.mp hx).1)
    refine ⟨max Trun Tseen, ?_⟩
    intro t ht
    have hr := hTrun t ((Nat.le_max_left _ _).trans ht)
    have hs : hfinite.toFinset ⊆ GenLimit.Generic.sample input (t + 1) := by
      intro x hx
      apply GenLimit.Generic.sample_mono
        ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t))
      exact hTseen hx
    rw [patientPrefixGenerator_outputAfterInput]
    refine ⟨?_, ?_, ?_⟩
    · by_contra hnot
      have hbad : GenLimit.PatientMachine.output E input t ∈ hfinite.toFinset :=
        (Set.Finite.mem_toFinset hfinite).mpr ⟨hr.1, hnot⟩
      have hmem := hs hbad
      rw [GenLimit.Generic.mem_sample_iff] at hmem
      obtain ⟨s, hslt, hseq⟩ := hmem
      exact hr.2.1 s (Nat.lt_succ_iff.mp hslt) hseq
    · intro hmem
      rw [GenLimit.mem_sample_iff] at hmem
      obtain ⟨s, hslt, hseq⟩ := hmem
      exact hr.2.1 s (Nat.lt_succ_iff.mp hslt) hseq
    · intro s hslt
      rw [patientPrefixGenerator_outputAfterInput]
      exact hr.2.2 s hslt
  · have hout : outputAfterInput (patientPrefixGenerator E) input =
        GenLimit.PatientMachine.output E input := by
      funext t
      exact patientPrefixGenerator_outputAfterInput E input t
    rw [hout]
    exact hrun.2.trans (relativeLowerDensity_transfer_finite
      (hinfinite i) hKR hfinite)

end Case019
