import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

/-- The first half of the P12 finite-omission class already has powerset cardinality. -/
theorem finiteOmissionFirstClass_uncountable (q : ℕ) :
    ¬(finiteOmissionFirstClass q).Countable := by
  intro hcountable
  let f : Set ℕ → Subtype (finiteOmissionFirstClass q) := fun A =>
    ⟨(omissionMarkerFinset q : Set ℤ) ∪
        GenLimit.UnionClosedness.positiveIntegers ∪
        GenLimit.UnionClosedness.negativeCode '' A,
      by
        constructor
        · exact fun z hz => Or.inl (Or.inl hz)
        · refine ⟨0, ?_⟩
          intro z hz
          obtain ⟨k, rfl⟩ := hz
          exact Or.inl (Or.inr
            (GenLimit.UnionClosedness.positiveCode_mem (0 + k)))⟩
  have hf : Function.Injective f := by
    intro A B hAB
    apply Set.ext
    intro n
    have hmem := Set.ext_iff.mp (congrArg Subtype.val hAB)
      (GenLimit.UnionClosedness.negativeCode n)
    dsimp [f] at hmem
    have hnotMarker :
        GenLimit.UnionClosedness.negativeCode n ∉ omissionMarkerFinset q := by
      intro hn
      exact (Int.not_lt_of_ge (omissionMarker_nonnegative hn))
        (GenLimit.UnionClosedness.negativeCode_mem n)
    have hnotPositive :
        GenLimit.UnionClosedness.negativeCode n ∉
          GenLimit.UnionClosedness.positiveIntegers := by
      exact Int.not_lt_of_ge (Int.le_of_lt
        (GenLimit.UnionClosedness.negativeCode_mem n))
    have hmem' :
        GenLimit.UnionClosedness.negativeCode n ∈
            GenLimit.UnionClosedness.negativeCode '' A ↔
          GenLimit.UnionClosedness.negativeCode n ∈
            GenLimit.UnionClosedness.negativeCode '' B := by
      simpa [hnotMarker, hnotPositive] using hmem
    constructor
    · intro hn
      have := hmem'.mp ⟨n, hn, rfl⟩
      obtain ⟨m, hm, heq⟩ := this
      have hmn : m = n :=
        GenLimit.UnionClosedness.negativeCode_injective heq
      simpa [hmn] using hm
    · intro hn
      have := hmem'.mpr ⟨n, hn, rfl⟩
      obtain ⟨m, hm, heq⟩ := this
      have hmn : m = n :=
        GenLimit.UnionClosedness.negativeCode_injective heq
      simpa [hmn] using hm
  letI : Countable (Subtype (finiteOmissionFirstClass q)) :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  apply finiteOmissionFirstClass_uncountable q
  exact hcountable.mono Set.subset_union_left

/-- P12's lower bound refutes exactly the weaker eventual target/sample freshness
used by the Case 019 negative clause. -/
theorem finiteOmissionClass_adjacent_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  by_contra hnone
  push_neg at hnone
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hsampleFresh := hnone K hK input hinput
  obtain ⟨T, hT⟩ := hsampleFresh
  refine ⟨T, ?_⟩
  intro t ht
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt, outputAt, observedThrough] using hT t ht

end Stage3Case019
