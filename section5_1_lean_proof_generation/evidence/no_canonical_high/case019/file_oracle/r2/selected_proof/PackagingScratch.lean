import output.DensityScratch
import output.CountableMain

open Stage3Case019
open GenLimit.Generic

namespace Case019

noncomputable def encodedSecondLanguage (q : ℕ) (A : Set ℕ) : Set ℤ :=
  GenLimit.UnionClosedness.negativeIntegers ∪
    (fun a : ℕ => GenLimit.UnionClosedness.positiveCode (q + 1 + a)) '' A

lemma encodedSecondLanguage_mem (q : ℕ) (A : Set ℕ) :
    encodedSecondLanguage q A ∈
      GenLimit.NoiseLossFeedback.finiteOmissionSecondClass q := by
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hmarker
    rcases hz with hzneg | ⟨a, ha, rfl⟩
    · exact (Int.not_lt_of_ge
        (GenLimit.NoiseLossFeedback.omissionMarker_nonnegative hmarker)) hzneg
    · obtain ⟨k, hk, heq⟩ :=
        GenLimit.NoiseLossFeedback.mem_omissionMarkerFinset_iff.mp hmarker
      simp [GenLimit.UnionClosedness.positiveCode] at heq
      omega

lemma encodedSecondLanguage_injective (q : ℕ) :
    Function.Injective (encodedSecondLanguage q) := by
  intro A B hAB
  ext a
  constructor
  · intro ha
    have hmemA : GenLimit.UnionClosedness.positiveCode (q + 1 + a) ∈
        encodedSecondLanguage q A := by
      right
      exact ⟨a, ha, rfl⟩
    rw [hAB] at hmemA
    rcases hmemA with hneg | ⟨b, hb, heq⟩
    · have hpos := GenLimit.UnionClosedness.positiveCode_mem (q + 1 + a)
      exact False.elim ((Int.not_lt_of_ge (le_of_lt hpos)) hneg)
    · have hab := GenLimit.UnionClosedness.positiveCode_injective heq
      have : a = b := by omega
      simpa [this] using hb
  · intro ha
    have hmemB : GenLimit.UnionClosedness.positiveCode (q + 1 + a) ∈
        encodedSecondLanguage q B := by
      right
      exact ⟨a, ha, rfl⟩
    rw [← hAB] at hmemB
    rcases hmemB with hneg | ⟨b, hb, heq⟩
    · have hpos := GenLimit.UnionClosedness.positiveCode_mem (q + 1 + a)
      exact False.elim ((Int.not_lt_of_ge (le_of_lt hpos)) hneg)
    · have hab := GenLimit.UnionClosedness.positiveCode_injective heq
      have : a = b := by omega
      simpa [this] using hb

lemma finiteOmissionClass_not_countable (q : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass q).Countable := by
  intro hcount
  let f : Set ℕ → Set ℤ := encodedSecondLanguage q
  have hrangeSub : Set.range f ⊆
      GenLimit.NoiseLossFeedback.finiteOmissionClass q := by
    rintro K ⟨A, rfl⟩
    exact Or.inr (encodedSecondLanguage_mem q A)
  have hrangeCount : (Set.range f).Countable := hcount.mono hrangeSub
  have himageCount : (f '' Set.univ).Countable := by
    simpa [Set.image_univ] using hrangeCount
  have hpowersetCount : (Set.univ : Set (Set ℕ)).Countable :=
    Set.countable_of_injective_of_countable_image
      (encodedSecondLanguage_injective q).injOn himageCount
  haveI : Countable (Set ℕ) := Set.countable_univ_iff.mp hpowersetCount
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ inferInstance

lemma finiteOmission_negative_clause (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stage3Case019.Stream ℤ,
          InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K := by
  intro gen
  by_contra hfail
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hfresh : SampleFreshGeneratesAfterInput
      input (outputAfterInput gen input) K := by
    by_contra hnot
    exact hfail ⟨K, hK, input, hinput, hnot⟩
  exact hfresh

lemma uncountable_separation_fixed (q : ℕ) :
    Stage3Case019.UncountableSeparation q := by
  let family := GenLimit.NoiseLossFeedback.finiteOmissionClass q
  refine ⟨family, finiteOmissionClass_not_countable q, ?_, ?_, ?_⟩
  · exact GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q
  · refine ⟨denseSweepGenerator q, ?_⟩
    intro K hK input hinput
    rcases hK with hfirst | hsecond
    · have hnovel := denseSweep_first_novel hfirst hinput
      exact ⟨hnovel, denseSweep_quarter_density q input K hnovel⟩
    · have hnovel := denseSweep_second_novel hsecond hinput
      exact ⟨hnovel, denseSweep_quarter_density q input K hnovel⟩
  · exact finiteOmission_negative_clause q

end Case019
