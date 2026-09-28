import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Theorem41Cardinality

open Stage3Case019

namespace Stage3Case019Proof

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

theorem finiteOmissionClass_infinite (q : ℕ) :
    ∀ K ∈ finiteOmissionClass q, K.Infinite := by
  exact finiteOmissionClass_uus q

theorem finiteOmissionClass_adjacent_failure (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  have hlower := finiteNoiseLevel_lower q
  simp only [GeneratableInLimitWithNoiseLevel, IsLimitGeneratorWithNoiseLevel] at hlower
  push_neg at hlower
  obtain ⟨K, hK, input, hinput, hfail⟩ := hlower gen
  refine ⟨K, hK, input, hinput, ?_⟩
  rintro ⟨T, hT⟩
  obtain ⟨t, ht, hbad⟩ := hfail T
  apply hbad
  simpa [outputAfterInput, GenLimit.NoiseLossFeedback.CorrectAt,
    observedThrough, outputAt] using hT t ht

end Stage3Case019Proof

namespace Stage3Case019Proof

open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private def encodedFirstLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  (omissionMarkerFinset q : Set ℤ) ∪ positiveIntegers ∪ negativeCode '' S

private theorem encodedFirstLanguage_mem (q : ℕ) (S : Set ℕ) :
    encodedFirstLanguage q S ∈ finiteOmissionClass q := by
  left
  refine ⟨?_, 0, ?_⟩
  · intro z hz
    exact Or.inl (Or.inl hz)
  · rintro z ⟨k, rfl⟩
    exact Or.inl (Or.inr (by simpa using positiveCode_mem k))

@[simp] private theorem negativeCode_mem_encodedFirstLanguage
    (q : ℕ) (S : Set ℕ) (n : ℕ) :
    negativeCode n ∈ encodedFirstLanguage q S ↔ n ∈ S := by
  constructor
  · intro h
    rcases h with hmp | himage
    · rcases hmp with hmarker | hpositive
      · exact False.elim (negativeCode_not_marker q n hmarker)
      · exact False.elim ((Int.not_lt_of_ge (Int.le_of_lt hpositive))
          (negativeCode_mem n))
    · obtain ⟨k, hk, hkn⟩ := himage
      exact negativeCode_injective hkn ▸ hk
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

private theorem encodedFirstLanguage_injective (q : ℕ) :
    Function.Injective (encodedFirstLanguage q) := by
  intro S T hST
  ext n
  have h := Set.ext_iff.mp hST (negativeCode n)
  simpa using h

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → finiteOmissionClass q :=
    fun S => ⟨encodedFirstLanguage q S, encodedFirstLanguage_mem q S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply encodedFirstLanguage_injective q
    exact congrArg Subtype.val hST
  letI : Countable (finiteOmissionClass q) := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact powerSet_not_countable ℕ hpower

end Stage3Case019Proof
