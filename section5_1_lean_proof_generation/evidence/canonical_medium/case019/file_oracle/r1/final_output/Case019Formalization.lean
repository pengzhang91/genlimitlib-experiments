import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Stage3Case019

namespace Case019Formalization

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

def shiftedPositive (q n : ℕ) : ℤ := Int.ofNat (q + n + 1)

theorem shiftedPositive_injective (q : ℕ) :
    Function.Injective (shiftedPositive q) := by
  intro m n h
  have hnat : q + m + 1 = q + n + 1 := Int.ofNat_inj.mp h
  omega

def secondClassEmbedding (q : ℕ) (A : Set ℕ) : Set ℤ :=
  GenLimit.UnionClosedness.negativeIntegers ∪ shiftedPositive q '' A

theorem secondClassEmbedding_injective (q : ℕ) :
    Function.Injective (secondClassEmbedding q) := by
  intro A B hAB
  ext n
  let z := shiftedPositive q n
  have hzPos : 0 < z := by
    change (0 : ℤ) < Int.ofNat (q + n + 1)
    exact Int.ofNat_pos.mpr (by omega)
  have hzNotNeg : z ∉ GenLimit.UnionClosedness.negativeIntegers := by
    exact Int.not_lt_of_ge (Int.le_of_lt hzPos)
  have hmem (C : Set ℕ) : z ∈ secondClassEmbedding q C ↔ n ∈ C := by
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact False.elim (hzNotNeg hz)
      · obtain ⟨k, hk, hkz⟩ := hz
        have : k = n := shiftedPositive_injective q hkz
        simpa [this] using hk
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hmem A, hAB, hmem B]

theorem secondClassEmbedding_mem (q : ℕ) (A : Set ℕ) :
    secondClassEmbedding q A ∈ finiteOmissionClass q := by
  apply Set.mem_union_right
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hzMarker
    rcases hz with hzNeg | hzImage
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hzMarker)) hzNeg
    · obtain ⟨n, -, rfl⟩ := hzImage
      obtain ⟨k, hk, heq⟩ := mem_omissionMarkerFinset_iff.mp hzMarker
      have heqNat : k = q + n + 1 := Int.ofNat_inj.mp heq
      omega

theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  have hpre :
      ((secondClassEmbedding q) ⁻¹' finiteOmissionClass q).Countable :=
    hcount.preimage (secondClassEmbedding_injective q)
  have huniv :
      ((secondClassEmbedding q) ⁻¹' finiteOmissionClass q) = Set.univ := by
    ext A
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact secondClassEmbedding_mem q A
  have htype : Countable (Set ℕ) := by
    rw [huniv, Set.countable_univ_iff] at hpre
    exact hpre
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ htype

theorem finiteOmissionClass_negative (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  classical
  intro gen
  by_contra hwitness
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hfresh : SampleFreshGeneratesAfterInput
      input (outputAfterInput gen input) K := by
    by_contra hnot
    exact hwitness ⟨K, hK, input, hinput, hnot⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt, outputAt, observedThrough] using hfresh

theorem separation_witness_foundations (q : ℕ) :
    ∃ family : Stage3Case019.LanguageClass ℤ,
      ¬family.Countable ∧
        (∀ K ∈ family, K.Infinite) ∧
          (∀ gen : Stage3Case019.Generator ℤ,
            ∃ K ∈ family, ∃ input : Stage3Case019.Stream ℤ,
              InjectiveValueContaminatedPresentationAtMost
                  input K (q + 1) ∧
                ¬SampleFreshGeneratesAfterInput
                  input (outputAfterInput gen input) K) := by
  refine ⟨finiteOmissionClass q,
    finiteOmissionClass_not_countable q, finiteOmissionClass_uus q, ?_⟩
  exact finiteOmissionClass_negative q

end Case019Formalization
