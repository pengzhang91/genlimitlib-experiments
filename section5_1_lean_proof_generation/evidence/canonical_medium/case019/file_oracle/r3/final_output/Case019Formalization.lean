import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Stage3Case019

namespace Case019Formalization

open GenLimit.Generic

/-- The marker-and-tail class used in the canonical proof consists entirely
of infinite languages. -/
theorem finiteOmissionClass_all_infinite (q : ℕ) :
    ∀ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q, K.Infinite := by
  exact GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q

/-- The supplied direct diagonal for the marker-and-tail class has exactly
 the quantifier order and inclusive-time freshness required by the negative
 part of `UncountableSeparation`. -/
theorem finiteOmissionClass_adjacent_negative (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stage3Case019.Stream ℤ,
          InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K := by
  classical
  intro gen
  by_contra hcounterexample
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hsampleFresh :
      SampleFreshGeneratesAfterInput
        input (outputAfterInput gen input) K := by
    by_contra hfail
    apply hcounterexample
    exact ⟨K, hK, input, hinput, hfail⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt,
    GenLimit.NoiseLossFeedback.observedThrough] using hsampleFresh


/-- The same marker-and-tail witness is extensionally uncountable. -/
theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass q).Countable := by
  classical
  intro hcountable
  let family := GenLimit.NoiseLossFeedback.finiteOmissionClass q
  let decode : {K // K ∈ family} → Set ℕ :=
    fun K => GenLimit.UnionClosedness.negativeCode ⁻¹' (K : Set ℤ)
  have hdecode : Function.Surjective decode := by
    intro S
    let K : Set ℤ :=
      (GenLimit.NoiseLossFeedback.omissionMarkerFinset q : Set ℤ) ∪
        GenLimit.UnionClosedness.positiveTail 0 ∪
          (GenLimit.UnionClosedness.negativeCode '' S)
    have hK : K ∈ family := by
      left
      constructor
      · exact fun z hz => Or.inl (Or.inl hz)
      · refine ⟨0, ?_⟩
        exact fun z hz => Or.inl (Or.inr hz)
    refine ⟨⟨K, hK⟩, ?_⟩
    ext n
    constructor
    · intro hn
      change GenLimit.UnionClosedness.negativeCode n ∈ K at hn
      rcases hn with hnBase | hnImage
      · rcases hnBase with hnMarker | hnPositive
        · exact False.elim
            (GenLimit.NoiseLossFeedback.negativeCode_not_marker q n hnMarker)
        · obtain ⟨k, hk⟩ := hnPositive
          have hnegative := GenLimit.UnionClosedness.negativeCode_mem n
          have hpositive := GenLimit.UnionClosedness.positiveCode_mem k
          change GenLimit.UnionClosedness.negativeCode n < 0 at hnegative
          change 0 < GenLimit.UnionClosedness.positiveCode k at hpositive
          have heq : GenLimit.UnionClosedness.positiveCode k =
              GenLimit.UnionClosedness.negativeCode n := by
            simpa using hk
          rw [heq] at hpositive
          omega
      · obtain ⟨m, hmS, hmn⟩ := hnImage
        have hmn' : m = n :=
          GenLimit.UnionClosedness.negativeCode_injective hmn
        simpa [hmn'] using hmS
    · intro hn
      change GenLimit.UnionClosedness.negativeCode n ∈ K
      exact Or.inr ⟨n, hn, rfl⟩
  letI : Countable {K // K ∈ family} := hcountable.to_subtype
  have hPower : Countable (Set ℕ) := hdecode.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hPower


/-- Checked structural and negative components of the separation clause. -/
theorem separation_witness_and_negative (q : ℕ) :
    ∃ family : Stage3Case019.LanguageClass ℤ,
      ¬family.Countable ∧
        (∀ K ∈ family, K.Infinite) ∧
          (∀ gen : Stage3Case019.Generator ℤ,
            ∃ K ∈ family, ∃ input : Stage3Case019.Stream ℤ,
              InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
                ¬SampleFreshGeneratesAfterInput
                  input (outputAfterInput gen input) K) := by
  exact ⟨GenLimit.NoiseLossFeedback.finiteOmissionClass q,
    finiteOmissionClass_not_countable q,
    finiteOmissionClass_all_infinite q,
    finiteOmissionClass_adjacent_negative q⟩

end Case019Formalization
