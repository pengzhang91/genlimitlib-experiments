import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3Case019

open GenLimit.Generic
open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

theorem finiteOmissionClass_infinite (q : ℕ) :
    ∀ K ∈ finiteOmissionClass q, K.Infinite := by
  exact finiteOmissionClass_uus q

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  let encode : Set ℕ → finiteOmissionClass q := fun A =>
    ⟨(↑(omissionMarkerFinset q) : Set ℤ) ∪
        positiveTail (q + 1) ∪
        ((fun n : ℕ => negativeCode n) '' A),
      Or.inl ⟨fun z hz => Or.inl (Or.inl hz), q + 1,
        fun z hz => Or.inl (Or.inr hz)⟩⟩
  have hencode : Function.Injective encode := by
    intro A B hAB
    apply Set.ext
    intro n
    have hnotMarker : negativeCode n ∉ omissionMarkerFinset q :=
      negativeCode_not_marker q n
    have hnotTail : negativeCode n ∉ positiveTail (q + 1) := by
      rintro ⟨k, hk⟩
      have hnonneg : 0 ≤ positiveCode (q + 1 + k) := Int.ofNat_zero_le _
      change positiveCode (q + 1 + k) = negativeCode n at hk
      rw [hk] at hnonneg
      exact (Int.not_lt_of_ge hnonneg) (negativeCode_mem n)
    have hmem (S : Set ℕ) :
        negativeCode n ∈
            (↑(omissionMarkerFinset q) : Set ℤ) ∪
              positiveTail (q + 1) ∪
                ((fun k : ℕ => negativeCode k) '' S) ↔
          n ∈ S := by
      constructor
      · intro hnmem
        rcases hnmem with (hnmark | hntail) | hnimage
        · exact False.elim (hnotMarker hnmark)
        · exact False.elim (hnotTail hntail)
        · obtain ⟨k, hk, hkn⟩ := hnimage
          exact (negativeCode_injective hkn).symm ▸ hk
      · intro hn
        exact Or.inr ⟨n, hn, rfl⟩
    have hpoint := Set.ext_iff.mp (congrArg Subtype.val hAB) (negativeCode n)
    rw [hmem, hmem] at hpoint
    exact hpoint
  letI : Countable (finiteOmissionClass q) := hcountable.to_subtype
  have hpowerset : Countable (Set ℕ) := hencode.countable
  exact powerSet_not_countable ℕ hpowerset

theorem finiteOmissionClass_level_succ_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  have hlower := finiteNoiseLevel_lower q
  by_contra hnone
  apply hlower
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  by_contra hfail
  apply hnone
  push_neg at hfail
  refine ⟨K, hK, input, hinput, ?_⟩
  intro hsampleFresh
  obtain ⟨T, hT⟩ := hsampleFresh
  obtain ⟨t, ht, hbad⟩ := hfail T
  exact hbad (hT t ht)

end Stage3Case019
