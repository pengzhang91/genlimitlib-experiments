import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open GenLimit.Generic
open Stage3Case019

namespace Stage3Case019

open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private def omissionEncodedLanguage (q : ℕ) (A : Set negativeIntegers) : Set ℤ :=
  (omissionMarkerFinset q : Set ℤ) ∪ positiveIntegers ∪
    ((fun z : negativeIntegers => z.1) '' A)

private theorem omissionEncodedLanguage_mem (q : ℕ) (A : Set negativeIntegers) :
    omissionEncodedLanguage q A ∈ finiteOmissionClass q := by
  left
  refine ⟨?_, 0, ?_⟩
  · exact Set.subset_union_left.trans Set.subset_union_left
  · rintro z ⟨k, rfl⟩
    exact Or.inl (Or.inr (positiveCode_mem (0 + k)))

private theorem omissionEncodedLanguage_injective (q : ℕ) :
    Function.Injective (omissionEncodedLanguage q) := by
  intro A B hAB
  apply Set.ext
  intro z
  have hzNeg : z.1 ∈ negativeIntegers := z.2
  have hzNotPos : z.1 ∉ positiveIntegers := by
    exact Int.not_lt_of_ge (Int.le_of_lt hzNeg)
  have hzNotMarker : z.1 ∉ omissionMarkerFinset q := by
    intro hz
    exact (Int.not_lt_of_ge (omissionMarker_nonnegative hz)) hzNeg
  have himage (C : Set negativeIntegers) :
      z.1 ∈ (fun w : negativeIntegers => w.1) '' C ↔ z ∈ C := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      simpa [Subtype.ext hwz] using hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hmem := Set.ext_iff.mp hAB z.1
  simp only [omissionEncodedLanguage, Set.mem_union, himage] at hmem
  simpa [hzNotMarker, hzNotPos] using hmem

 theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  letI : Infinite negativeIntegers := negativeIntegers_infinite.to_subtype
  intro hcountable
  let f : Set negativeIntegers → finiteOmissionClass q :=
    fun A => ⟨omissionEncodedLanguage q A, omissionEncodedLanguage_mem q A⟩
  have hf : Function.Injective f := by
    intro A B h
    apply omissionEncodedLanguage_injective q
    exact congrArg Subtype.val h
  letI : Countable (finiteOmissionClass q) := hcountable.to_subtype
  have hpower : Countable (Set negativeIntegers) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable negativeIntegers hpower

 theorem finiteNoiseLevel_lower_afterInput (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput input (outputAfterInput gen input) K := by
  intro gen
  by_contra h
  push_neg at h
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hs := h K hK input hinput
  rcases hs with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  have hc := hT t ht
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt] using hc

end Stage3Case019
