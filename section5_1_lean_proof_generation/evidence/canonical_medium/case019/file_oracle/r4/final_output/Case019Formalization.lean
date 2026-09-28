import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Stage3Case019

namespace Case019Formalization

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

/-- The supplied direct diagonal already proves the exact weaker failure
predicate used by the Stage 3 separation clause. -/
theorem adjacentLevelFailure (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  by_contra h
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hsf :
      SampleFreshGeneratesAfterInput
        input (outputAfterInput gen input) K := by
    by_contra hnot
    exact h ⟨K, hK, input, hinput, hnot⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput, GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt,
    GenLimit.NoiseLossFeedback.observedThrough] using hsf

/-- Every member of the supplied adjacent-noise witness is infinite. -/
theorem finiteOmissionClass_infinite (q : ℕ) :
    ∀ K ∈ finiteOmissionClass q, K.Infinite := by
  exact finiteOmissionClass_uus q

private def variablePositive (q : ℕ) (A : Set ℕ) : Set ℤ :=
  {z | z < 0 ∨ ∃ n ∈ A, Int.ofNat (q + 1 + n) = z}

private theorem variablePositive_mem_class (q : ℕ) (A : Set ℕ) :
    variablePositive q A ∈ finiteOmissionClass q := by
  apply Set.mem_union_right
  constructor
  · intro z hz
    exact Or.inl hz
  · rw [Set.disjoint_left]
    intro z hz hzMarker
    rcases hz with hzneg | ⟨n, hn, rfl⟩
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hzMarker)) hzneg
    · obtain ⟨k, hk, heq⟩ := mem_omissionMarkerFinset_iff.mp hzMarker
      have : k = q + 1 + n := Int.ofNat_inj.mp heq
      omega

private theorem variablePositive_injective (q : ℕ) :
    Function.Injective (variablePositive q) := by
  intro A B hAB
  ext n
  have hmem (S : Set ℕ) :
      n ∈ S ↔ Int.ofNat (q + 1 + n) ∈ variablePositive q S := by
    constructor
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
    · intro hz
      rcases hz with hzneg | ⟨m, hm, heq⟩
      · exact False.elim ((Int.not_lt_of_ge (Int.ofNat_zero_le _)) hzneg)
      · have hnat : q + 1 + m = q + 1 + n := Int.ofNat_inj.mp heq
        have : m = n := by omega
        simpa [this] using hm
  rw [hmem A, hAB, ← hmem B]

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  let embed : Set ℕ → (finiteOmissionClass q : Set (Set ℤ)) :=
    fun A => ⟨variablePositive q A, variablePositive_mem_class q A⟩
  have hinj : Function.Injective embed := by
    intro A B h
    exact variablePositive_injective q (congrArg Subtype.val h)
  letI : Countable (finiteOmissionClass q : Set (Set ℤ)) := hcount
  haveI : Countable (Set ℕ) := hinj.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ inferInstance

end Case019Formalization
