import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

namespace Case019

open GenLimit

theorem sample_eq_of_eq_lt {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

theorem consistent_iff_of_eq_lt {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t i : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_eq_of_eq_lt h]

theorem recursiveCritical_iff_of_eq_lt {C : GenLimit.LanguageFamily}
    {a b : ℕ → ℕ} {t i : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa [GenLimit.RecursiveCritical] using
        consistent_iff_of_eq_lt (C := C) (i := 0) h
    | succ i =>
      simp only [GenLimit.RecursiveCritical]
      rw [consistent_iff_of_eq_lt (C := C) (i := i + 1) h]
      constructor
      · rintro ⟨hc, hh⟩
        exact ⟨hc, fun j hj hcrit => hh j hj ((ih j (by omega)).mpr hcrit)⟩
      · rintro ⟨hc, hh⟩
        exact ⟨hc, fun j hj hcrit => hh j hj ((ih j (by omega)).mp hcrit)⟩

open Stage3Case019
open GenLimit.NoiseLossFeedback

def separationEncodedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  (omissionMarkerFinset q : Set ℤ) ∪
    GenLimit.UnionClosedness.positiveTail 0 ∪
      GenLimit.UnionClosedness.negativeCode '' S

theorem separationEncodedLanguage_mem (q : ℕ) (S : Set ℕ) :
    separationEncodedLanguage q S ∈ finiteOmissionClass q := by
  left
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · exact ⟨0, fun z hz => Or.inl (Or.inr hz)⟩

@[simp] theorem negativeCode_mem_separationEncodedLanguage
    (q n : ℕ) (S : Set ℕ) :
    GenLimit.UnionClosedness.negativeCode n ∈
        separationEncodedLanguage q S ↔ n ∈ S := by
  constructor
  · rintro ((hmarker | htail) | himage)
    · have hnonnegative := omissionMarker_nonnegative hmarker
      have hnegative := GenLimit.UnionClosedness.negativeCode_mem n
      exact False.elim ((Int.not_lt_of_ge hnonnegative) hnegative)
    · rcases htail with ⟨k, hk⟩
      have hnegative := GenLimit.UnionClosedness.negativeCode_mem n
      have hpositive := GenLimit.UnionClosedness.positiveCode_mem (0 + k)
      have hpositive' : (0 : ℤ) < GenLimit.UnionClosedness.negativeCode n := by
        rw [← hk]
        exact hpositive
      exact False.elim ((Int.not_lt_of_ge (le_of_lt hpositive')) hnegative)
    · rcases himage with ⟨m, hmS, hmn⟩
      have hmn' : m = n :=
        GenLimit.UnionClosedness.negativeCode_injective hmn
      simpa [hmn'] using hmS
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

theorem separationEncodedLanguage_injective (q : ℕ) :
    Function.Injective (separationEncodedLanguage q) := by
  intro S T hST
  ext n
  have hprobe := Set.ext_iff.mp hST
    (GenLimit.UnionClosedness.negativeCode n)
  simpa using hprobe

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → finiteOmissionClass q :=
    fun S => ⟨separationEncodedLanguage q S,
      separationEncodedLanguage_mem q S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply separationEncodedLanguage_injective q
    exact congrArg Subtype.val hST
  letI : Countable (finiteOmissionClass q) := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

/-- The exact negative component required by the separation clause, for the
source's finite-omission witness class. -/
theorem finiteOmissionClass_adjacent_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  by_contra hcounter
  push_neg at hcounter
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hfresh := hcounter K hK input hinput
  rcases hfresh with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  exact hT t ht

/-- Checked witness data for every separation level: extensional
uncountability, infinitude of all targets, and the exact level-`q+1`
impossibility statement. -/
theorem separation_witness_checked (q : ℕ) :
    ¬(finiteOmissionClass q).Countable ∧
      (∀ K ∈ finiteOmissionClass q, K.Infinite) ∧
      (∀ gen : Generator ℤ,
        ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) := by
  exact ⟨finiteOmissionClass_uncountable q,
    finiteOmissionClass_uus q,
    finiteOmissionClass_adjacent_failure q⟩

end Case019
