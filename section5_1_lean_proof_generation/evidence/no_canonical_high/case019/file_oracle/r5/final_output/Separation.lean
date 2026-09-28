import Helpers
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Filter
open scoped Topology

namespace Stage3Case019

open GenLimit
open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

private def encodedSecond (q : ℕ) (A : Set ℕ) : Set ℤ :=
  negativeIntegers ∪ positiveCode '' ((fun n : ℕ => q + n + 1) '' A)

private theorem encodedSecond_mem (q : ℕ) (A : Set ℕ) :
    encodedSecond q A ∈ finiteOmissionSecondClass q := by
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hmarker
    rcases hz with hzneg | ⟨n, ⟨a, ha, rfl⟩, rfl⟩
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hmarker)) hzneg
    · obtain ⟨k, hk, heq⟩ := mem_omissionMarkerFinset_iff.mp hmarker
      simp [positiveCode] at heq
      omega

private theorem encodedSecond_injective (q : ℕ) :
    Function.Injective (encodedSecond q) := by
  intro A B hAB
  ext n
  have htest : positiveCode (q + n + 1) ∈ encodedSecond q A ↔ n ∈ A := by
    constructor
    · intro h
      rcases h with hneg | ⟨m, ⟨a, ha, hm⟩, hcode⟩
      · exact False.elim ((Int.not_lt_of_ge (Int.ofNat_zero_le _)) hneg)
      · subst m
        have han : a = n := by
          have hh := positiveCode_injective hcode
          have heq : q + a + 1 = q + n + 1 := by simpa using hh
          omega
        simpa [han] using ha
    · intro hn
      right
      exact ⟨q + n + 1, ⟨n, hn, rfl⟩, rfl⟩
  have htestB : positiveCode (q + n + 1) ∈ encodedSecond q B ↔ n ∈ B := by
    constructor
    · intro h
      rcases h with hneg | ⟨m, ⟨a, ha, hm⟩, hcode⟩
      · exact False.elim ((Int.not_lt_of_ge (Int.ofNat_zero_le _)) hneg)
      · subst m
        have han : a = n := by
          have hh := positiveCode_injective hcode
          have heq : q + a + 1 = q + n + 1 := by simpa using hh
          omega
        simpa [han] using ha
    · intro hn
      right
      exact ⟨q + n + 1, ⟨n, hn, rfl⟩, rfl⟩
  rw [← htest, hAB, htestB]

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  have hrange : (Set.range (encodedSecond q)).Countable := by
    apply hcount.mono
    rintro K ⟨A, rfl⟩
    exact Set.mem_union_right _ (encodedSecond_mem q A)
  have hpre : (Set.univ : Set (Set ℕ)).Countable := by
    rw [← Set.preimage_range (encodedSecond q)]
    exact hrange.preimage (encodedSecond_injective q)
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (Set.countable_univ_iff.mp hpre)

theorem finiteOmissionClass_negative (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput input (outputAfterInput gen input) K := by
  intro gen
  by_contra hnone
  push_neg at hnone
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := hnone K hK input hinput
  exact ⟨T, fun t ht => by
    simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
      GenLimit.Generic.CorrectAt, outputAt] using hT t ht⟩

end Stage3Case019
