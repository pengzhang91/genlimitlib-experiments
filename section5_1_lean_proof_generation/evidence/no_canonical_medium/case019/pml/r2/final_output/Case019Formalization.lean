import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open Stage3Case019

namespace Case019

open GenLimit
open GenLimit.NoiseLossFeedback

noncomputable def pairFinsetSurjection : ℕ → ℕ × Finset ℕ :=
  Classical.choose (countable_iff_exists_surjective.mp inferInstance)

theorem pairFinsetSurjection_surjective : Function.Surjective pairFinsetSurjection :=
  Classical.choose_spec (countable_iff_exists_surjective.mp inferInstance)

noncomputable def contaminatedOracle
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite) : OracleFamily where
  language n := family (pairFinsetSurjection n).1 ∪ (pairFinsetSurjection n).2
  infinite' n := (hinf (pairFinsetSurjection n).1).mono Set.subset_union_left
  query n x := by
    classical
    exact decide (x ∈ family (pairFinsetSurjection n).1 ∪ (pairFinsetSurjection n).2)
  query_spec n x := by
    classical
    simp

/-- Every value-contaminated presentation is an exact presentation of one
finite extension represented in `contaminatedOracle`. -/
theorem exists_exact_contaminated_index
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite)
    (i q : ℕ) (input : Stream ℕ)
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input (family i) q) :
    ∃ z, GenLimit.Presents input ((contaminatedOracle family hinf).language z) ∧
      (((contaminatedOracle family hinf).language z) \ family i).Finite := by
  classical
  obtain ⟨F, hF, _hcard⟩ := hinput.2.2
  obtain ⟨z, hz⟩ := pairFinsetSurjection_surjective (i, F)
  refine ⟨z, ?_, ?_⟩
  · unfold GenLimit.Presents
    change Set.range input = family (pairFinsetSurjection z).1 ∪ ↑(pairFinsetSurjection z).2
    rw [hz]
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hxK : x ∈ family i
      · exact Or.inl hxK
      · exact Or.inr (by
          change x ∈ (F : Set ℕ)
          rw [hF]
          exact ⟨hx, hxK⟩)
    · rintro x (hxK | hxF)
      · exact hinput.2.1 hxK
      · change x ∈ (F : Set ℕ) at hxF
        rw [hF] at hxF
        exact hxF.1
  · change ((family (pairFinsetSurjection z).1 ∪
        (pairFinsetSurjection z).2) \ family i).Finite
    rw [hz]
    apply F.finite_toSet.subset
    intro x hx
    rcases hx.1 with hxK | hxF
    · exact False.elim (hx.2 hxK)
    · exact hxF

/-- The operational patient theorem applies to the exact finite extension
selected by `exists_exact_contaminated_index`. -/
theorem contaminated_patient_certificate
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite)
    (i q : ℕ) (input : Stream ℕ)
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input (family i) q) :
    ∃ z,
      (((contaminatedOracle family hinf).language z) \ family i).Finite ∧
      ((∃ T, ∀ t, T ≤ t →
          PatientMachine.output (contaminatedOracle family hinf) input t ∈
              (contaminatedOracle family hinf).language z ∧
          (∀ s, s ≤ t → input s ≠
              PatientMachine.output (contaminatedOracle family hinf) input t) ∧
          (∀ s, s < t →
              PatientMachine.output (contaminatedOracle family hinf) input s ≠
              PatientMachine.output (contaminatedOracle family hinf) input t)) ∧
        (1 / 2 : ℝ) ≤
          PatientMachine.patientLowerDensity
            (contaminatedOracle family hinf) input z) := by
  obtain ⟨z, hpresents, hfinite⟩ :=
    exists_exact_contaminated_index family hinf i q input hinput
  exact ⟨z, hfinite,
    PatientMachine.patientScope_generation_and_lowerDensity
      (contaminatedOracle family hinf) input hpresents⟩

/-- An explicit powerset encoding into the first half of the finite-omission
class. -/
def encodedFirstLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  (omissionMarkerFinset q : Set ℤ) ∪
    GenLimit.UnionClosedness.positiveIntegers ∪
    GenLimit.UnionClosedness.negativeCode '' S

theorem encodedFirstLanguage_mem (q : ℕ) (S : Set ℕ) :
    encodedFirstLanguage q S ∈ finiteOmissionClass q := by
  left
  constructor
  · exact fun x hx => Or.inl (Or.inl hx)
  · refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact Or.inl (Or.inr (by
      simpa using GenLimit.UnionClosedness.positiveCode_mem (0 + n)))

theorem encodedFirstLanguage_injective (q : ℕ) :
    Function.Injective (encodedFirstLanguage q) := by
  intro S T hST
  ext n
  have hprobe := Set.ext_iff.mp hST (GenLimit.UnionClosedness.negativeCode n)
  have hnegative :
      GenLimit.UnionClosedness.negativeCode n ∉
        GenLimit.UnionClosedness.positiveIntegers := by
    simp [GenLimit.UnionClosedness.positiveIntegers,
      GenLimit.UnionClosedness.negativeCode]
  have hmarker := negativeCode_not_marker q n
  simp only [encodedFirstLanguage, Set.mem_union, Set.mem_image] at hprobe
  simpa [hmarker, hnegative, GenLimit.UnionClosedness.negativeCode_injective.eq_iff]
    using hprobe

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → {K // K ∈ finiteOmissionClass q} :=
    fun S => ⟨encodedFirstLanguage q S, encodedFirstLanguage_mem q S⟩
  have hf : Function.Injective f := by
    intro S T h
    apply encodedFirstLanguage_injective q
    exact congrArg Subtype.val h
  letI : Countable {K // K ∈ finiteOmissionClass q} := hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

/-- Pointwise form of the supplied level-`q+1` impossibility theorem, matching
exactly the negative quantifier order required by `UncountableSeparation`. -/
theorem finiteNoise_explicit_failure (q : ℕ) (gen : Generator ℤ) :
    ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
      GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
          input K (q + 1) ∧
        ¬SampleFreshGeneratesAfterInput
          input (outputAfterInput gen input) K := by
  classical
  by_contra h
  push_neg at h
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := h K hK input hinput
  refine ⟨T, ?_⟩
  intro t ht
  exact hT t ht

/-- All non-density structural requirements of the separation witness are
certified by the supplied finite-noise class. -/
theorem finiteOmission_separation_structure (q : ℕ) :
    ¬(finiteOmissionClass q).Countable ∧
      (∀ K ∈ finiteOmissionClass q, K.Infinite) ∧
      (∀ gen : Generator ℤ,
        ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) := by
  exact ⟨finiteOmissionClass_uncountable q,
    finiteOmissionClass_uus q, finiteNoise_explicit_failure q⟩

end Case019
