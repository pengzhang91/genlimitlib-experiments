import Stage3Model
import «output».PatientCausal
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Stage3Case019

namespace Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  let encode : Set ℕ → Set ℤ := fun A =>
    (↑(omissionMarkerFinset q) : Set ℤ) ∪
      GenLimit.UnionClosedness.positiveIntegers ∪
        GenLimit.UnionClosedness.negativeCode '' A
  have hmem : ∀ A : Set ℕ, encode A ∈ finiteOmissionClass q := by
    intro A
    left
    constructor
    · exact fun _ hx => Or.inl (Or.inl hx)
    · refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact Or.inl (Or.inr (by simpa using GenLimit.UnionClosedness.positiveCode_mem n))
  have hencodeCountable : (Set.range encode).Countable := by
    apply hcountable.mono
    rintro _ ⟨A, rfl⟩
    exact hmem A
  have hinjective : Function.Injective encode := by
    intro A B hAB
    ext n
    have hneg : GenLimit.UnionClosedness.negativeCode n ∉
        (↑(omissionMarkerFinset q) : Set ℤ) :=
      negativeCode_not_marker q n
    have hnotPos : GenLimit.UnionClosedness.negativeCode n ∉
        GenLimit.UnionClosedness.positiveIntegers := by
      intro hp
      exact (Int.not_lt_of_ge (Int.le_of_lt hp))
        (GenLimit.UnionClosedness.negativeCode_mem n)
    have hA : GenLimit.UnionClosedness.negativeCode n ∈ encode A ↔ n ∈ A := by
      simp only [encode, Set.mem_union, Set.mem_image]
      constructor
      · rintro ((hm | hp) | ⟨m, hm, heq⟩)
        · exact False.elim (hneg hm)
        · exact False.elim (hnotPos hp)
        · exact GenLimit.UnionClosedness.negativeCode_injective heq ▸ hm
      · intro hn
        exact Or.inr ⟨n, hn, rfl⟩
    have hB : GenLimit.UnionClosedness.negativeCode n ∈ encode B ↔ n ∈ B := by
      simp only [encode, Set.mem_union, Set.mem_image]
      constructor
      · rintro ((hm | hp) | ⟨m, hm, heq⟩)
        · exact False.elim (hneg hm)
        · exact False.elim (hnotPos hp)
        · exact GenLimit.UnionClosedness.negativeCode_injective heq ▸ hm
      · intro hn
        exact Or.inr ⟨n, hn, rfl⟩
    rw [← hA, hAB, hB]
  let intoRange : Set ℕ → (Set.range encode) := fun A => ⟨encode A, A, rfl⟩
  have hintoRange : Function.Injective intoRange := by
    intro A B hAB
    exact hinjective (congrArg Subtype.val hAB)
  letI : Countable (Set.range encode) := hencodeCountable
  have : Countable (Set ℕ) := hintoRange.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ this

theorem finiteOmissionClass_negative (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  by_contra h
  push_neg at h
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hrun := h K hK input hinput
  rcases hrun with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt, outputAt, observedThrough] using hT t ht

theorem finiteOmissionClass_positive_sampleFresh (q : ℕ) :
    ∃ gen : Stage3Case019.Generator ℤ,
      ∀ K ∈ finiteOmissionClass q, ∀ input : Stage3Case019.Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K q →
          SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  obtain ⟨gen, hgen⟩ := finiteNoiseLevel_upper q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := hgen K hK input hinput
  refine ⟨T, ?_⟩
  intro t ht
  simpa [outputAfterInput, GenLimit.NoiseLossFeedback.CorrectAt,
    outputAt, observedThrough] using hT t ht


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

theorem countableHalfDensity_zero : Stage3Case019.CountableHalfDensity 0 := by
  intro family hinfinite
  let O := oracleOfFamily family hinfinite
  refine ⟨patientPrefixGenerator O, ?_⟩
  intro i input hinput
  have hrangeSubset : Set.range input ⊆ family i := by
    exact (GenLimit.Generic.setDifferenceAtMost_zero_iff_subset
      (Set.range input) (family i)).mp hinput.2.2
  have hpresents : GenLimit.Presents input (O.language i) := by
    apply Set.Subset.antisymm
    · exact hrangeSubset
    · exact hinput.2.1
  have hrun := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    O input hpresents
  have houtputs :
      Stage3Case019.outputAfterInput (patientPrefixGenerator O) input =
        GenLimit.PatientMachine.output O input := by
    funext t
    exact patientPrefixGenerator_output O input t
  constructor
  · obtain ⟨T, hT⟩ := hrun.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    rw [houtputs]
    refine ⟨hmem, ?_, hnovel⟩
    rw [GenLimit.mem_sample_iff]
    push_neg
    intro s hs
    exact hfresh s (Nat.lt_succ_iff.mp hs)
  · rw [houtputs]
    exact hrun.2

/-- Checked structural core of the adjacent-level separation.  The exact
stage-3 target additionally asks for output-output novelty and quarter density
on the positive side. -/
theorem separation_structural_core (q : ℕ) :
    ∃ family : Stage3Case019.LanguageClass ℤ,
      ¬family.Countable ∧
        (∀ K ∈ family, K.Infinite) ∧
        (∃ gen : Stage3Case019.Generator ℤ,
          ∀ K ∈ family, ∀ input : Stage3Case019.Stream ℤ,
            InjectiveValueContaminatedPresentationAtMost input K q →
              SampleFreshGeneratesAfterInput
                input (outputAfterInput gen input) K) ∧
        (∀ gen : Stage3Case019.Generator ℤ,
          ∃ K ∈ family, ∃ input : Stage3Case019.Stream ℤ,
            InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
              ¬SampleFreshGeneratesAfterInput
                input (outputAfterInput gen input) K) := by
  refine ⟨finiteOmissionClass q, finiteOmissionClass_not_countable q, ?_,
    finiteOmissionClass_positive_sampleFresh q,
    finiteOmissionClass_negative q⟩
  exact finiteOmissionClass_uus q

end Case019
