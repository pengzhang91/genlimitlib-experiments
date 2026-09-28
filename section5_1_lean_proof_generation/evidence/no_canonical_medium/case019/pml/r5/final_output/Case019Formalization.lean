import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Theorem41Cardinality

open Stage3Case019

namespace Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private def encodedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  (↑(omissionMarkerFinset q) : Set ℤ) ∪ positiveIntegers ∪
    negativeDeletionEncoding S

private theorem encodedLanguage_mem (q : ℕ) (S : Set ℕ) :
    encodedLanguage q S ∈ finiteOmissionClass q := by
  left
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · refine ⟨0, ?_⟩
    intro z hz
    rcases hz with ⟨k, rfl⟩
    exact Or.inl (Or.inr (by simpa using positiveCode_mem k))

private theorem oddNegative_mem_encodedLanguage (q : ℕ) (S : Set ℕ) (n : ℕ) :
    negativeCode (2 * n + 1) ∈ encodedLanguage q S ↔ n ∈ S := by
  have hnegative : negativeCode (2 * n + 1) ∈ negativeIntegers :=
    negativeCode_mem _
  have hnotMarker : negativeCode (2 * n + 1) ∉ omissionMarkerFinset q :=
    negativeCode_not_marker q _
  have hnotPositive : negativeCode (2 * n + 1) ∉ positiveIntegers := by
    simp [positiveIntegers, negativeCode]
  simp [encodedLanguage, hnotMarker, hnotPositive,
    oddNegative_mem_negativeDeletionEncoding]

private theorem encodedLanguage_injective (q : ℕ) :
    Function.Injective (encodedLanguage q) := by
  classical
  intro S T hST
  apply Set.ext
  intro n
  have hprobe := Set.ext_iff.mp hST (negativeCode (2 * n + 1))
  simpa [oddNegative_mem_encodedLanguage] using hprobe

private theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → finiteOmissionClass q :=
    fun S => ⟨encodedLanguage q S, encodedLanguage_mem q S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply encodedLanguage_injective q
    exact congrArg Subtype.val hST
  letI : Countable (finiteOmissionClass q) := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact powerSet_not_countable ℕ hpower

private theorem finiteNoise_failure (q : ℕ)
    (gen : Stage3Case019.Generator ℤ) :
    ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
      InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
        ¬SampleFreshGeneratesAfterInput
          input (outputAfterInput gen input) K := by
  by_contra hnone
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  by_contra hfail
  apply hnone
  refine ⟨K, hK, input, hinput, ?_⟩
  intro hsampleFresh
  apply hfail
  rcases hsampleFresh with ⟨T, hT⟩
  exact ⟨T, fun t ht => hT t ht⟩

/-- Checked negative and cardinality parts of the separation witness. -/
theorem separation_skeleton (q : ℕ) :
    ¬(finiteOmissionClass q).Countable ∧
      (∀ K ∈ finiteOmissionClass q, K.Infinite) ∧
      (∀ gen : Stage3Case019.Generator ℤ,
        ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
          InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) := by
  exact ⟨finiteOmissionClass_uncountable q,
    finiteOmissionClass_uus q, finiteNoise_failure q⟩

end Case019
