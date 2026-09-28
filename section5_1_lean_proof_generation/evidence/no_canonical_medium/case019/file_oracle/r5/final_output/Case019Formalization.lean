import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open Stage3Case019

noncomputable section

namespace Stage3Case019Proof

open GenLimit.NoiseLossFeedback
open GenLimit.UnionClosedness

noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ)
    (hInfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private def uncountableSubfamily (q : ℕ) (A : Set ℕ) : Set ℤ :=
  negativeIntegers ∪
    GenLimit.UnionClosedness.positiveCode '' ((fun n => q + n) '' A)

private theorem uncountableSubfamily_mem (q : ℕ) (A : Set ℕ) :
    uncountableSubfamily q A ∈ finiteOmissionClass q := by
  apply Set.mem_union_right
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hmarker
    rcases hz with hzneg | ⟨n, ⟨k, hkA, rfl⟩, rfl⟩
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hmarker)) hzneg
    · obtain ⟨m, hm, heq⟩ := mem_omissionMarkerFinset_iff.mp hmarker
      have : m = q + k + 1 := Int.ofNat_inj.mp (heq.trans rfl)
      omega

private theorem uncountableSubfamily_injective (q : ℕ) :
    Function.Injective (uncountableSubfamily q) := by
  intro A B hAB
  ext k
  have hpos : positiveCode (q + k) ∉ negativeIntegers := by
    simp [positiveCode, negativeIntegers]
    positivity
  have hmem (C : Set ℕ) :
      positiveCode (q + k) ∈ uncountableSubfamily q C ↔ k ∈ C := by
    simp only [uncountableSubfamily, Set.mem_union, hpos, false_or,
      Set.mem_image]
    constructor
    · rintro ⟨n, ⟨j, hj, hqj⟩, hn⟩
      have hn' := positiveCode_injective hn
      have hjk : j = k := Nat.add_left_cancel (hqj.trans hn')
      simpa [hjk] using hj
    · intro hk
      exact ⟨q + k, ⟨k, hk, rfl⟩, rfl⟩
  rw [← hmem A, hAB, hmem B]

private theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  have hrange : (Set.range (uncountableSubfamily q)).Countable :=
    hcount.mono (fun _ h => by
      obtain ⟨A, rfl⟩ := h
      exact uncountableSubfamily_mem q A)
  letI : Countable (Set.range (uncountableSubfamily q)) := hrange.to_subtype
  obtain ⟨encode, hencode⟩ :=
    (countable_iff_exists_injective (Set.range (uncountableSubfamily q))).mp inferInstance
  let lift : Set ℕ → Set.range (uncountableSubfamily q) :=
    fun A => ⟨uncountableSubfamily q A, ⟨A, rfl⟩⟩
  have hlift : Function.Injective lift := by
    intro A B h
    apply uncountableSubfamily_injective q
    exact congrArg Subtype.val h
  have hcountPower : Countable (Set ℕ) :=
    (countable_iff_exists_injective (Set ℕ)).mpr
      ⟨encode ∘ lift, hencode.comp hlift⟩
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hcountPower

private theorem separation_negative (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  intro gen
  by_contra h
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  by_contra hfail
  apply h
  refine ⟨K, hK, input, hinput, ?_⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    CorrectAt, outputAt, observedThrough] using hfail

private theorem atMost_to_finiteContamination
    {input : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (hinput :
      GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
        input K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
      input K := by
  refine ⟨hinput.1, ?_, ?_⟩
  · apply (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
      hinput.1).2
    obtain ⟨F, hF, _⟩ := hinput.2.2
    rw [← hF]
    exact F.finite_toSet
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr hinput.2.1]
    exact Set.finite_empty

/-- Checked reduction used by the countable clause: every bounded-noise input
is an exact presentation of a member of the supplied finite-expansion family. -/
theorem countable_exact_expansion_reduction
    (family : LanguageFamily ℕ)
    (hInfinite : ∀ i, (family i).Infinite)
    (i q : ℕ) (input : Stream ℕ)
    (hinput :
      GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
        input (family i) q) :
    ∃ j,
      GenLimit.InfiniteContamination.finiteExpansionBaseIndex j = i ∧
        GenLimit.Generic.Presents input
          ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily
            (oracleOfFamily family hInfinite)).language j) := by
  exact GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream
    (oracleOfFamily family hInfinite)
    (atMost_to_finiteContamination hinput)

/-- Fully checked portions of the separation witness: extensional
uncountability, infinitude, the level-q eventual sample-fresh generator, and
the fixed level-(q+1) counterexample for every generator. -/
theorem separation_checked_core (q : ℕ) :
    ¬(finiteOmissionClass q).Countable ∧
      (∀ K ∈ finiteOmissionClass q, K.Infinite) ∧
      (∃ gen : Generator ℤ,
        ∀ K ∈ finiteOmissionClass q, ∀ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K q →
            SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) ∧
      (∀ gen : Generator ℤ,
        ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) := by
  refine ⟨finiteOmissionClass_not_countable q,
    finiteOmissionClass_uus q, ?_, separation_negative q⟩
  obtain ⟨gen, hgen⟩ := finiteNoiseLevel_upper q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    CorrectAt, outputAt, observedThrough] using hgen K hK input hinput

end Stage3Case019Proof
