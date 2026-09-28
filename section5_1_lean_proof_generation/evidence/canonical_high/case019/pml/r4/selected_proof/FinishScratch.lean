import Case019Formalization

open Stage3Case019

namespace Case019

abbrev omissionMarkers (q : ℕ) : Set ℤ :=
  (GenLimit.NoiseLossFeedback.omissionMarkerFinset q : Set ℤ)

abbrev negCode' := GenLimit.UnionClosedness.negativeCode

def encodedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  omissionMarkers q ∪ GenLimit.UnionClosedness.positiveTail (q + 1) ∪
    negCode' '' S

lemma encodedLanguage_mem_first (q : ℕ) (S : Set ℕ) :
    encodedLanguage q S ∈
      GenLimit.NoiseLossFeedback.finiteOmissionFirstClass q := by
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · refine ⟨q + 1, ?_⟩
    intro z hz
    exact Or.inl (Or.inr hz)

lemma negCode_mem_encodedLanguage (q n : ℕ) (S : Set ℕ) :
    negCode' n ∈ encodedLanguage q S ↔ n ∈ S := by
  constructor
  · intro hn
    rcases hn with (hmarker | htail) | hcode
    · exact False.elim
        (GenLimit.NoiseLossFeedback.negativeCode_not_marker q n hmarker)
    · rcases htail with ⟨k, hk⟩
      change GenLimit.UnionClosedness.positiveCode (q + 1 + k) = negCode' n at hk
      have hpositive := GenLimit.UnionClosedness.positiveCode_mem (q + 1 + k)
      rw [hk] at hpositive
      exact False.elim
        ((Int.not_lt_of_ge (Int.le_of_lt hpositive))
          (GenLimit.UnionClosedness.negativeCode_mem n))
    · rcases hcode with ⟨m, hm, hmn⟩
      exact (GenLimit.UnionClosedness.negativeCode_injective hmn).symm ▸ hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

lemma encodedLanguage_injective (q : ℕ) :
    Function.Injective (encodedLanguage q) := by
  intro S T hST
  apply Set.ext
  intro n
  have hprobe := Set.ext_iff.mp hST (negCode' n)
  rw [negCode_mem_encodedLanguage, negCode_mem_encodedLanguage] at hprobe
  exact hprobe

lemma finiteOmissionClass_uncountable (q : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → GenLimit.NoiseLossFeedback.finiteOmissionClass q :=
    fun S => ⟨encodedLanguage q S,
      Set.mem_union_left _ (encodedLanguage_mem_first q S)⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply encodedLanguage_injective q
    exact congrArg Subtype.val hST
  letI : Countable (GenLimit.NoiseLossFeedback.finiteOmissionClass q) :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

lemma finiteOmission_adjacent_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K := by
  intro gen
  by_contra hnone
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hsuccess : SampleFreshGeneratesAfterInput
      input (outputAfterInput gen input) K := by
    by_contra hfailure
    apply hnone
    exact ⟨K, hK, input, hinput, hfailure⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt] using hsuccess

end Case019

namespace Case019

theorem stage3_uncountable_separation_scratch :
    Stage3Case019.SeparationClause := by
  intro q
  refine ⟨GenLimit.NoiseLossFeedback.finiteOmissionClass q,
    finiteOmissionClass_uncountable q,
    GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q, ?_,
    finiteOmission_adjacent_failure q⟩
  refine ⟨sidePatientGenerator q, ?_⟩
  intro K hK input hinput
  rcases hK with hfirst | hsecond
  · exact ⟨sidePatientGenerator_first_novel hfirst hinput,
      sidePatientGenerator_first_density hfirst hinput⟩
  · exact ⟨sidePatientGenerator_second_novel hsecond hinput,
      sidePatientGenerator_second_density hsecond hinput⟩

end Case019
