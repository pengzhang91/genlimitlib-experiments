import Stage3Model
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import WrapperProbe
import DensityProbe

namespace Case019Probe

open Stage3Case019
open GenLimit
open GenLimit.Generic
open GenLimit.InfiniteContamination

noncomputable def oracleOfFamily
    (family : GenLimit.Generic.LanguageFamily ℕ) (hinfinite : ∀ i, (family i).Infinite) :
    OracleFamily := by
  classical
  exact {
  language := family
  infinite' := hinfinite
  query i x := if x ∈ family i then true else false
  query_spec i x := by simp }

private theorem outputAfterInput_patientGenerator
    (O : OracleFamily) (input : GenLimit.Generic.Stream ℕ) :
    outputAfterInput (patientGenerator O) input = PatientMachine.output O input := by
  funext t
  exact patientGenerator_output_succ O input t

 theorem countableHalfDensity (q : ℕ) : CountableHalfDensity q := by
  intro family hinfinite
  let O := oracleOfFamily family hinfinite
  let E := finiteExpansionOracleFamily O
  let gen := patientGenerator E
  refine ⟨gen, ?_⟩
  intro i input hinput
  have hcontam : FiniteNoiseFiniteOmissionEnumeration input (O.language i) := by
    refine ⟨hinput.1, ?_, ?_⟩
    · rw [finiteNoise_iff_valuesOutside_finite_of_injective hinput.1]
      exact (setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp hinput.2.2 |>.1
    · unfold FiniteOmissions
      change (family i \ Set.range input).Finite
      rw [Set.diff_eq_empty.mpr hinput.2.1]
      exact Set.finite_empty
  obtain ⟨j, hj, hpresents⟩ := exists_finiteExpansion_index_for_stream O hcontam
  have hpatient := PatientMachine.patientScope_generation_and_lowerDensity E input hpresents
  have htrace : outputAfterInput gen input = PatientMachine.output E input := by
    exact outputAfterInput_patientGenerator E input
  have hKE : family i ⊆ E.language j := by
    intro x hx
    rw [← hpresents]
    exact hinput.2.1 hx
  have hfinite : (E.language j \ family i).Finite := by
    rw [← hpresents]
    exact displayedNoise_finite hcontam.2.1
  constructor
  · obtain ⟨Tvalid, hTvalid⟩ := hpatient.1
    obtain ⟨Tseen, hTseen⟩ := finset_eventually_subset_sample hpresents
      hfinite.toFinset (by
        intro x hx
        exact (Set.Finite.mem_toFinset hfinite).mp hx |>.1)
    refine ⟨max Tvalid Tseen, ?_⟩
    intro t ht
    have hv := hTvalid t ((Nat.le_max_left _ _).trans ht)
    have hs : hfinite.toFinset ⊆ GenLimit.sample input (t + 1) := by
      intro x hx
      have hg := GenLimit.Generic.sample_mono
        ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)) (hTseen hx)
      obtain ⟨s, hst, hsEq⟩ := GenLimit.Generic.mem_sample_iff.mp hg
      exact GenLimit.mem_sample_iff.mpr ⟨s, hst, hsEq⟩
    rw [htrace]
    refine ⟨?_, ?_, hv.2.2⟩
    · by_contra hnot
      have hsample := hs ((Set.Finite.mem_toFinset hfinite).mpr ⟨hv.1, hnot⟩)
      obtain ⟨s, hst, hsEq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hv.2.1 s (by omega) hsEq
    · intro hmem
      obtain ⟨s, hst, hsEq⟩ := GenLimit.mem_sample_iff.mp hmem
      exact hv.2.1 s (by omega) hsEq
  · rw [htrace]
    have hd := hpatient.2
    unfold PatientMachine.patientLowerDensity at hd
    exact hd.trans (PatientScope.relativeLowerDensity_transfer_finite_expansion
      (A := GeneratorFirst input (PatientMachine.output E input))
      (K := family i) (E := E.language j) (hinfinite i) hKE hfinite)

end Case019Probe
