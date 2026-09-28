import Stage3Model
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.MinimalPairClasses
import WrapperProbe
import DensityProbe

open Stage3Case019

namespace Case019

open GenLimit
open GenLimit.Generic
open GenLimit.InfiniteContamination
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private theorem corePresentation_finiteContamination
    {α : Type*} {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {q : ℕ}
    (h : InjectiveValueContaminatedPresentationAtMost stream L q) :
    FiniteNoiseFiniteOmissionEnumeration stream L := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [finiteNoise_iff_valuesOutside_finite_of_injective h.1]
    exact (setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp h.2.2 |>.1
  · unfold FiniteOmissions
    rw [Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty

private theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  letI : Infinite negativeIntegers := negativeIntegers_infinite.to_subtype
  intro hcountable
  let f : Set negativeIntegers → finiteOmissionClass q :=
    fun A =>
      ⟨(omissionMarkerFinset q : Set ℤ) ∪ positiveIntegers ∪
          ((fun z : negativeIntegers => z.1) '' A),
        Or.inl ⟨by intro z hz; exact Or.inl (Or.inl hz),
          ⟨0, by
            intro z hz
            exact Or.inl (Or.inr (by
              rw [← range_positiveCode]
              rcases hz with ⟨k, rfl⟩
              exact ⟨k, by simp [positiveCode]⟩))⟩⟩⟩
  have hf : Function.Injective f := by
    intro A B hAB
    apply Set.ext
    intro z
    have hzNeg : z.1 < 0 := z.2
    have hzNotMarker : z.1 ∉ (omissionMarkerFinset q : Set ℤ) := by
      intro hz
      exact (Int.not_lt_of_ge (omissionMarker_nonnegative hz)) hzNeg
    have hzNotPositive : z.1 ∉ positiveIntegers :=
      Int.not_lt_of_ge (Int.le_of_lt hzNeg)
    have himage (C : Set negativeIntegers) :
        z.1 ∈ (fun w : negativeIntegers => w.1) '' C ↔ z ∈ C := by
      constructor
      · rintro ⟨w, hw, hwz⟩
        simpa [Subtype.ext hwz] using hw
      · intro hzC
        exact ⟨z, hzC, rfl⟩
    have hmem := Set.ext_iff.mp (congrArg Subtype.val hAB) z.1
    change
      z.1 ∈ (omissionMarkerFinset q : Set ℤ) ∪ positiveIntegers ∪
          ((fun w : negativeIntegers => w.1) '' A) ↔
      z.1 ∈ (omissionMarkerFinset q : Set ℤ) ∪ positiveIntegers ∪
          ((fun w : negativeIntegers => w.1) '' B) at hmem
    simp only [Set.mem_union, himage] at hmem
    simpa [hzNotMarker, hzNotPositive] using hmem
  letI : Countable (finiteOmissionClass q) := hcountable.to_subtype
  have hpower : Countable (Set negativeIntegers) := hf.countable
  exact powerSet_not_countable negativeIntegers hpower

private theorem adjacentLevel_failure
    (q : ℕ) (gen : GenLimit.Generic.Generator ℤ) :
    ∃ K ∈ finiteOmissionClass q, ∃ input : GenLimit.Generic.Stream ℤ,
      InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
        ¬SampleFreshGeneratesAfterInput input (outputAfterInput gen input) K := by
  by_contra h
  have hgen : IsLimitGeneratorWithNoiseLevel gen (finiteOmissionClass q) (q + 1) := by
    intro K hK input hinput
    by_contra hfail
    apply h
    exact ⟨K, hK, input, hinput, by
      simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
        GenLimit.NoiseLossFeedback.CorrectAt,
        GenLimit.NoiseLossFeedback.observedThrough,
        GenLimit.NoiseLossFeedback.outputAt] using hfail⟩
  exact finiteNoiseLevel_lower q ⟨gen, hgen⟩


noncomputable def oracleOfFamily
    (family : GenLimit.Generic.LanguageFamily ℕ)
    (hinfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily := by
  classical
  exact {
    language := family
    infinite' := hinfinite
    query i x := if x ∈ family i then true else false
    query_spec i x := by simp }

private theorem outputAfterInput_patientGenerator
    (O : GenLimit.OracleFamily) (input : GenLimit.Generic.Stream ℕ) :
    outputAfterInput (Case019Probe.patientGenerator O) input =
      GenLimit.PatientMachine.output O input := by
  funext t
  exact Case019Probe.patientGenerator_output_succ O input t

theorem countableHalfDensity (q : ℕ) : CountableHalfDensity q := by
  intro family hinfinite
  let O := oracleOfFamily family hinfinite
  let E := finiteExpansionOracleFamily O
  let gen := Case019Probe.patientGenerator E
  refine ⟨gen, ?_⟩
  intro i input hinput
  have hcontam :
      FiniteNoiseFiniteOmissionEnumeration input (O.language i) :=
    corePresentation_finiteContamination hinput
  obtain ⟨j, hj, hpresents⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  have hpatient :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      E input hpresents
  have htrace :
      outputAfterInput gen input =
        GenLimit.PatientMachine.output E input :=
    outputAfterInput_patientGenerator E input
  have hKE : family i ⊆ E.language j := by
    intro x hx
    rw [← hpresents]
    exact hinput.2.1 hx
  have hfinite : (E.language j \ family i).Finite := by
    rw [← hpresents]
    exact displayedNoise_finite hcontam.2.1
  constructor
  · obtain ⟨Tvalid, hTvalid⟩ := hpatient.1
    obtain ⟨Tseen, hTseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample hpresents
        hfinite.toFinset (by
          intro x hx
          exact (Set.Finite.mem_toFinset hfinite).mp hx |>.1)
    refine ⟨max Tvalid Tseen, ?_⟩
    intro t ht
    have hv := hTvalid t ((Nat.le_max_left _ _).trans ht)
    have hs : hfinite.toFinset ⊆ GenLimit.sample input (t + 1) := by
      intro x hx
      have hg := GenLimit.Generic.sample_mono
        ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t))
        (hTseen hx)
      obtain ⟨s, hst, hsEq⟩ :=
        GenLimit.Generic.mem_sample_iff.mp hg
      exact GenLimit.mem_sample_iff.mpr ⟨s, hst, hsEq⟩
    rw [htrace]
    refine ⟨?_, ?_, hv.2.2⟩
    · by_contra hnot
      have hsample := hs
        ((Set.Finite.mem_toFinset hfinite).mpr ⟨hv.1, hnot⟩)
      obtain ⟨s, hst, hsEq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hv.2.1 s (by omega) hsEq
    · intro hmem
      obtain ⟨s, hst, hsEq⟩ := GenLimit.mem_sample_iff.mp hmem
      exact hv.2.1 s (by omega) hsEq
  · rw [htrace]
    have hd := hpatient.2
    unfold GenLimit.PatientMachine.patientLowerDensity at hd
    exact hd.trans
      (GenLimit.PatientScope.relativeLowerDensity_transfer_finite_expansion
        (A := GenLimit.GeneratorFirst input
          (GenLimit.PatientMachine.output E input))
        (K := family i) (E := E.language j)
        (hinfinite i) hKE hfinite)

theorem countableClause : CountableClause := by
  intro q
  exact countableHalfDensity q

end Case019
