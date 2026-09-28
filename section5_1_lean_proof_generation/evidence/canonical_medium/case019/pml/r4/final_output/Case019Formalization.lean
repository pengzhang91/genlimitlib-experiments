import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Stage3Case019

namespace Stage3Case019Proof

open GenLimit.NoiseLossFeedback

theorem level_succ_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q,
        ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K := by
  intro gen
  by_contra hno
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  by_contra hfail
  apply hno
  refine ⟨K, hK, input, hinput, ?_⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    CorrectAt, outputAt, observedThrough] using hfail

theorem witness_languages_infinite (q : ℕ) :
    ∀ K ∈ finiteOmissionClass q, K.Infinite :=
  finiteOmissionClass_uus q

end Stage3Case019Proof

namespace Stage3Case019Proof

open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private def separationEncoding (q : ℕ) (S : Set ℕ) : Set ℤ :=
  (omissionMarkerFinset q : Set ℤ) ∪ positiveTail (q + 1) ∪ negativeCode '' S

private theorem separationEncoding_mem (q : ℕ) (S : Set ℕ) :
    separationEncoding q S ∈ finiteOmissionClass q := by
  left
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · exact ⟨q + 1, fun z hz => Or.inl (Or.inr hz)⟩

private theorem negativeCode_mem_separationEncoding_iff
    (q n : ℕ) (S : Set ℕ) :
    negativeCode n ∈ separationEncoding q S ↔ n ∈ S := by
  constructor
  · intro h
    rcases h with hfixed | himage
    · rcases hfixed with hmarker | htail
      · exact False.elim
          ((Int.not_lt_of_ge (omissionMarker_nonnegative hmarker))
            (negativeCode_mem n))
      · obtain ⟨k, hk⟩ := htail
        change positiveCode (q + 1 + k) = negativeCode n at hk
        have hpos : 0 < positiveCode (q + 1 + k) := positiveCode_mem _
        rw [hk] at hpos
        exact False.elim
          ((Int.not_lt_of_ge (Int.le_of_lt hpos)) (negativeCode_mem n))
    · obtain ⟨m, hm, hmn⟩ := himage
      have hmn' : m = n := negativeCode_injective hmn
      simpa [hmn'] using hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

private theorem separationEncoding_injective (q : ℕ) :
    Function.Injective (separationEncoding q) := by
  intro S T hST
  ext n
  rw [← negativeCode_mem_separationEncoding_iff q n S,
    ← negativeCode_mem_separationEncoding_iff q n T, hST]

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → {K // K ∈ finiteOmissionClass q} :=
    fun S => ⟨separationEncoding q S, separationEncoding_mem q S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply separationEncoding_injective q
    exact congrArg Subtype.val hST
  letI : Countable {K // K ∈ finiteOmissionClass q} := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

end Stage3Case019Proof

namespace Stage3Case019Proof

open GenLimit.NoiseLossFeedback

theorem level_validity (q : ℕ) :
    ∃ gen : Generator ℤ,
      ∀ K ∈ finiteOmissionClass q, ∀ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K q →
          SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  obtain ⟨gen, hgen⟩ := finiteNoiseLevel_upper q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := hgen K hK input hinput
  refine ⟨T, ?_⟩
  intro t ht
  simpa [outputAfterInput, CorrectAt, outputAt, observedThrough] using hT t ht

/-- The fully checked non-density core of the adjacent-level witness. -/
theorem separation_core (q : ℕ) :
    ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧
        (∀ K ∈ family, K.Infinite) ∧
        (∃ gen : Generator ℤ,
          ∀ K ∈ family, ∀ input : Stream ℤ,
            GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
                input K q →
              SampleFreshGeneratesAfterInput
                input (outputAfterInput gen input) K) ∧
        (∀ gen : Generator ℤ,
          ∃ K ∈ family, ∃ input : Stream ℤ,
            GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
                input K (q + 1) ∧
              ¬SampleFreshGeneratesAfterInput
                input (outputAfterInput gen input) K) := by
  exact ⟨finiteOmissionClass q,
    finiteOmissionClass_uncountable q,
    witness_languages_infinite q,
    level_validity q,
    level_succ_failure q⟩

end Stage3Case019Proof
