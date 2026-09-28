import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set

namespace Stage3Case019Partial

open GenLimit.Generic
open GenLimit.NoiseLossFeedback

private def sparsePositive (q n : ℕ) : ℤ :=
  GenLimit.UnionClosedness.positiveCode (q + 1 + n)

private theorem sparsePositive_injective (q : ℕ) :
    Function.Injective (sparsePositive q) := by
  intro a b h
  exact Nat.add_left_cancel
    (GenLimit.UnionClosedness.positiveCode_injective h)

private def secondLanguage (q : ℕ) (A : Set ℕ) : Set ℤ :=
  GenLimit.UnionClosedness.negativeIntegers ∪ sparsePositive q '' A

private theorem secondLanguage_mem (q : ℕ) (A : Set ℕ) :
    secondLanguage q A ∈ finiteOmissionClass q := by
  apply Set.mem_union_right
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hzMarker
    rcases hz with hzNeg | ⟨n, -, rfl⟩
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hzMarker)) hzNeg
    · obtain ⟨k, hk, hzk⟩ := mem_omissionMarkerFinset_iff.mp hzMarker
      have hpos : (k : ℤ) = Int.ofNat (q + 1 + n + 1) := by
        simpa [sparsePositive, GenLimit.UnionClosedness.positiveCode] using hzk
      have : k = q + 1 + n + 1 := Int.ofNat_inj.mp hpos
      omega

private theorem secondLanguage_injective (q : ℕ) :
    Function.Injective (secondLanguage q) := by
  intro A B hAB
  ext n
  have hpos : sparsePositive q n ∉
      GenLimit.UnionClosedness.negativeIntegers := by
    exact Int.not_lt_of_ge
      (Int.le_of_lt (GenLimit.UnionClosedness.positiveCode_mem (q + 1 + n)))
  constructor
  · intro hn
    have hm : sparsePositive q n ∈ secondLanguage q A :=
      Set.mem_union_right _ ⟨n, hn, rfl⟩
    rw [hAB] at hm
    rcases hm with hm | ⟨m, hm, heq⟩
    · exact False.elim (hpos hm)
    · have : m = n := sparsePositive_injective q heq
      simpa [this] using hm
  · intro hn
    have hm : sparsePositive q n ∈ secondLanguage q B :=
      Set.mem_union_right _ ⟨n, hn, rfl⟩
    rw [← hAB] at hm
    rcases hm with hm | ⟨m, hm, heq⟩
    · exact False.elim (hpos hm)
    · have : m = n := sparsePositive_injective q heq
      simpa [this] using hm

private theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  have hpre : (secondLanguage q ⁻¹' finiteOmissionClass q).Countable :=
    hcount.preimage (secondLanguage_injective q)
  have huniv : secondLanguage q ⁻¹' finiteOmissionClass q = Set.univ := by
    ext A
    simp [secondLanguage_mem]
  have : Countable (Set ℕ) := Set.countable_univ_iff.mp (huniv ▸ hpre)
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ this

private theorem sampleFresh_iff_correctAt
    (gen : Generator ℤ) (input : Stream ℤ) (K : Language ℤ) :
    Stage3Case019.SampleFreshGeneratesAfterInput input
        (Stage3Case019.outputAfterInput gen input) K ↔
      ∃ T, ∀ t, T ≤ t →
        GenLimit.NoiseLossFeedback.CorrectAt gen K input t := by
  rfl

/-- Checked core of the separation clause: the supplied uncountable class is
level-q sample-fresh generatable and defeats every generator at level q+1.
The missing strengthening is output novelty plus the quarter-density bound. -/
theorem separation_core (q : ℕ) :
    ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧
      (∀ K ∈ family, K.Infinite) ∧
      (∃ gen : Generator ℤ,
        ∀ K ∈ family, ∀ input : Stream ℤ,
          InjectiveValueContaminatedPresentationAtMost input K q →
            Stage3Case019.SampleFreshGeneratesAfterInput
              input (Stage3Case019.outputAfterInput gen input) K) ∧
      (∀ gen : Generator ℤ,
        ∃ K ∈ family, ∃ input : Stream ℤ,
          InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
            ¬Stage3Case019.SampleFreshGeneratesAfterInput
              input (Stage3Case019.outputAfterInput gen input) K) := by
  refine ⟨finiteOmissionClass q, finiteOmissionClass_not_countable q,
    finiteOmissionClass_uus q, ?_, ?_⟩
  · obtain ⟨gen, hgen⟩ := finiteNoiseLevel_upper q
    refine ⟨gen, ?_⟩
    intro K hK input hinput
    exact sampleFresh_iff_correctAt gen input K |>.2 (hgen K hK input hinput)
  · intro gen
    by_contra hcounter
    push_neg at hcounter
    apply finiteNoiseLevel_lower q
    refine ⟨gen, ?_⟩
    intro K hK input hinput
    exact sampleFresh_iff_correctAt gen input K |>.1
      (hcounter K hK input hinput)

end Stage3Case019Partial
