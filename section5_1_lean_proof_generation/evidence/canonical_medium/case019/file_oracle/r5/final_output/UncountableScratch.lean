import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set
namespace TestUncountable
open GenLimit GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

noncomputable def codedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  negativeIntegers ∪ {z | ∃ n ∈ S, positiveCode (q + 1 + n) = z}

lemma codedLanguage_mem_second (q : ℕ) (S : Set ℕ) :
    codedLanguage q S ∈ finiteOmissionSecondClass q := by
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hmarker
    rcases hz with hzneg | ⟨n, hn, rfl⟩
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hmarker)) hzneg
    · obtain ⟨k, hk, heq⟩ := mem_omissionMarkerFinset_iff.mp hmarker
      have heq' : Int.ofNat k = Int.ofNat (q + 1 + n + 1) := by
        simpa [positiveCode] using heq
      have heqNat := Int.ofNat_inj.mp heq'
      omega

lemma mem_codedLanguage_positive (q n : ℕ) (S : Set ℕ) :
    positiveCode (q + 1 + n) ∈ codedLanguage q S ↔ n ∈ S := by
  constructor
  · intro h
    rcases h with hneg | ⟨m, hm, heq⟩
    · exfalso
      simp [negativeIntegers, positiveCode] at hneg
      omega
    · have : q + 1 + m = q + 1 + n := positiveCode_injective heq
      simpa [Nat.add_left_cancel_iff] using (show m = n by omega) ▸ hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

lemma codedLanguage_injective (q : ℕ) : Function.Injective (codedLanguage q) := by
  intro S T hST
  ext n
  rw [← mem_codedLanguage_positive q n S, hST, mem_codedLanguage_positive q n T]

lemma finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  have hrange : (Set.range (codedLanguage q)).Countable := by
    apply hcount.mono
    rintro K ⟨S, rfl⟩
    exact Or.inr (codedLanguage_mem_second q S)
  have himage : ((codedLanguage q) '' (Set.univ : Set (Set ℕ))).Countable := by
    simpa [Set.image_univ] using hrange
  have huniv : (Set.univ : Set (Set ℕ)).Countable :=
    Set.countable_of_injective_of_countable_image
      (codedLanguage_injective q).injOn himage
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (Set.countable_univ_iff.mp huniv)

end TestUncountable
