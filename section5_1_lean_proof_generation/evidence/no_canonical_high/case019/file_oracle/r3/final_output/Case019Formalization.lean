import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Stage3Case019

namespace Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

def secondEncoding (q : ℕ) (A : Set ℕ) : Set ℤ :=
  negativeIntegers ∪ positiveCode '' ((fun n => q + 1 + n) '' A)

theorem secondEncoding_mem_second (q : ℕ) (A : Set ℕ) :
    secondEncoding q A ∈ finiteOmissionSecondClass q := by
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hzMarker
    rcases hz with hzNeg | ⟨k, ⟨n, hnA, rfl⟩, rfl⟩
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hzMarker)) hzNeg
    · obtain ⟨m, hm, hmq⟩ := mem_omissionMarkerFinset_iff.mp hzMarker
      simp [positiveCode] at hmq
      omega

theorem secondEncoding_injective (q : ℕ) :
    Function.Injective (secondEncoding q) := by
  intro A B hAB
  ext n
  have hpos : 0 < positiveCode (q + 1 + n) := positiveCode_mem _
  have hA :
      positiveCode (q + 1 + n) ∈ secondEncoding q A ↔ n ∈ A := by
    constructor
    · intro h
      rcases h with hneg | ⟨k, ⟨m, hm, hkm⟩, hk⟩
      · exact False.elim ((Int.not_lt_of_ge (le_of_lt hpos)) hneg)
      · have heq : q + 1 + n = q + 1 + m :=
          positiveCode_injective (hk.symm.trans (congrArg positiveCode hkm.symm))
        have : n = m := by omega
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨q + 1 + n, ⟨n, hn, rfl⟩, rfl⟩
  have hB :
      positiveCode (q + 1 + n) ∈ secondEncoding q B ↔ n ∈ B := by
    constructor
    · intro h
      rcases h with hneg | ⟨k, ⟨m, hm, hkm⟩, hk⟩
      · exact False.elim ((Int.not_lt_of_ge (le_of_lt hpos)) hneg)
      · have heq : q + 1 + n = q + 1 + m :=
          positiveCode_injective (hk.symm.trans (congrArg positiveCode hkm.symm))
        have : n = m := by omega
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨q + 1 + n, ⟨n, hn, rfl⟩, rfl⟩
  rw [← hA, hAB, hB]

theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  have himage : Set.Countable (Set.range (secondEncoding q)) := by
    apply hcount.mono
    rintro K ⟨A, rfl⟩
    exact Or.inr (secondEncoding_mem_second q A)
  have hdomain : Countable (Set ℕ) := by
    rw [← Set.countable_univ_iff]
    exact Set.countable_of_injective_of_countable_image
      (s := Set.univ) (fun x _ y _ h => secondEncoding_injective q h)
      (by simpa [Set.image_univ] using himage)
  exact powerSet_not_countable ℕ hdomain

theorem negative_clause (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  have hlower := finiteNoiseLevel_lower q
  by_contra hnone
  push_neg at hnone
  apply hlower
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := hnone K hK input hinput
  refine ⟨T, ?_⟩
  intro t ht
  exact hT t ht



theorem weak_positive_clause (q : ℕ) :
    ∃ gen : Stage3Case019.Generator ℤ,
      ∀ K ∈ finiteOmissionClass q, ∀ input : Stage3Case019.Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K q →
          SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  obtain ⟨gen, hgen⟩ := finiteNoiseLevel_upper q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  exact hgen K hK input hinput


theorem weak_uncountable_separation (q : ℕ) :
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
  exact ⟨finiteOmissionClass q,
    finiteOmissionClass_not_countable q,
    finiteOmissionClass_uus q,
    weak_positive_clause q,
    negative_clause q⟩

end Case019

