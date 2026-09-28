import Stage3Model
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Pairing

open Set
open Stage3Case025

namespace Stage3Case025

/-- Finite occurrence contamination implies that only finitely many distinct
values in the input range lie outside the target. -/
theorem finite_range_diff_of_finite_violations
    (input : Stream) (K : Language)
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  apply (hbad.image input).subset
  intro x hx
  rcases hx.1 with ⟨t, rfl⟩
  exact ⟨t, hx.2, rfl⟩

/-- The range of a complete finitely contaminated presentation is a finite
addition of the target. -/
theorem range_eq_target_union_finite_noise
    (input : Stream) (K : Language)
    (hcomplete : CompleteFiniteOccurrencePresentation input K) :
    ∃ F : Set ℕ, F.Finite ∧ Set.range input = K ∪ F := by
  refine ⟨Set.range input \ K,
    finite_range_diff_of_finite_violations input K hcomplete.2, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · intro hx
    rcases hx with hxK | hxF
    · exact hcomplete.1 hxK
    · exact hxF.1

/-- Every stream is an exact positive presentation of its own range. -/
theorem presents_own_range (input : Stream) :
    GenLimit.Presents input (Set.range input) := by
  rfl


/-- A fixed enumeration of all finite additions of an indexed family. -/
noncomputable def finiteAdditionFamily (family : ℕ → Language) : ℕ → Language :=
  fun n =>
    family (Nat.unpair n).1 ∪
      (↑(Finset.equivBitIndices (Nat.unpair n).2) : Set ℕ)

theorem finiteAdditionFamily_infinite
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    ∀ n, (finiteAdditionFamily family n).Infinite := by
  intro n
  exact (hInfinite (Nat.unpair n).1).mono Set.subset_union_left

theorem mem_finiteAdditionFamily_of_finset
    (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    ∃ n, finiteAdditionFamily family n = family i ∪ (↑F : Set ℕ) := by
  refine ⟨Nat.pair i (Finset.equivBitIndices.symm F), ?_⟩
  simp [finiteAdditionFamily]

theorem mem_finiteAdditionFamily_of_finite
    (family : ℕ → Language) (i : ℕ) (F : Set ℕ) (hF : F.Finite) :
    ∃ n, finiteAdditionFamily family n = family i ∪ F := by
  rcases mem_finiteAdditionFamily_of_finset family i hF.toFinset with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [hF.coe_toFinset] using hn

/-- Every complete finitely contaminated input exactly presents a member of
`finiteAdditionFamily family`. -/
theorem contaminated_input_presents_finite_addition
    (family : ℕ → Language) (i : ℕ) (input : Stream)
    (hcomplete : CompleteFiniteOccurrencePresentation input (family i)) :
    ∃ n, GenLimit.Presents input (finiteAdditionFamily family n) := by
  rcases range_eq_target_union_finite_noise input (family i) hcomplete with
    ⟨F, hF, hrange⟩
  rcases mem_finiteAdditionFamily_of_finite family i F hF with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  exact hrange.trans hn.symm

end Stage3Case025

namespace Stage3Case025

/-- Checked reduction of finite occurrence noise to the positive-presentation
engine on the fixed finite-addition closure. The remaining transfer must remove
the finitely many added values from validity and relative density. -/
theorem finite_noise_reduction_to_positive
    (hPositive : PositivePresentationHalfDensity) :
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : OnlineGenerator,
        ∀ i (input : Stream),
          CompleteFiniteOccurrencePresentation input (family i) →
            ∃ (n : ℕ) (output : Stream),
              GenLimit.Presents input (finiteAdditionFamily family n) ∧
              Follows gen input output ∧
              GenLimit.NovelGeneratesInLimit input output
                (finiteAdditionFamily family n) ∧
              (1 / 2 : ℝ) ≤
                GenLimit.PatientScope.relativeLowerDensity
                  (GenLimit.GeneratorFirst input output ∩
                    finiteAdditionFamily family n)
                  (finiteAdditionFamily family n) := by
  intro family hInfinite
  rcases hPositive (finiteAdditionFamily family)
      (finiteAdditionFamily_infinite family hInfinite) with ⟨gen, hgen⟩
  refine ⟨gen, ?_⟩
  intro i input hcomplete
  rcases contaminated_input_presents_finite_addition family i input hcomplete with
    ⟨n, hpresents⟩
  rcases hgen n input hpresents with ⟨output, hfollows, hnovel, hdensity⟩
  exact ⟨n, output, hpresents, hfollows, hnovel, hdensity⟩

end Stage3Case025
