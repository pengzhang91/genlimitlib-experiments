import Stage3Model
import Mathlib.Logic.Equiv.Finset

open Set

namespace Stage3Case025

noncomputable def finiteExtensionFamily
    (family : ℕ → Language) : ℕ → Language :=
  fun n =>
    let code := Denumerable.ofNat (ℕ × Finset ℕ) n
    family code.1 ∪ (code.2 : Set ℕ)

theorem finiteExtensionFamily_infinite
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExtensionFamily family n).Infinite := by
  intro n
  exact (hfamily (Denumerable.ofNat (ℕ × Finset ℕ) n).1).mono subset_union_left

theorem finiteExtensionFamily_contains
    (family : ℕ → Language) (i : ℕ) (exceptions : Finset ℕ) :
    ∃ n, finiteExtensionFamily family n = family i ∪ (exceptions : Set ℕ) := by
  let n := @Encodable.encode (ℕ × Finset ℕ) Denumerable.prod.toEncodable (i, exceptions)
  refine ⟨n, ?_⟩
  change family (Denumerable.ofNat (ℕ × Finset ℕ) n).1 ∪
      ((Denumerable.ofNat (ℕ × Finset ℕ) n).2 : Set ℕ) = _
  have hcode : Denumerable.ofNat (ℕ × Finset ℕ) n = (i, exceptions) := by
    exact Denumerable.ofNat_encode (i, exceptions)
  rw [hcode]

def exceptionValues (input : Stream) (K : Language) : Set ℕ :=
  input '' GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)

theorem exceptionValues_finite
    {input : Stream} {K : Language}
    (hfinite : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (exceptionValues input K).Finite := by
  exact hfinite.image input

theorem range_eq_target_union_exceptions
    {input : Stream} {K : Language}
    (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ exceptionValues input K := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    by_cases hx : input t ∈ K
    · exact Or.inl hx
    · exact Or.inr ⟨t, hx, rfl⟩
  · intro x hx
    rcases hx with hx | ⟨t, _, rfl⟩
    · exact hcover hx
    · exact ⟨t, rfl⟩

theorem eventually_avoids_finite_of_eventually_norepeat
    {output : Stream} {E : Set ℕ} (hE : E.Finite)
    (hnorepeat : ∃ T, ∀ t, T ≤ t → ∀ s, s < t → output s ≠ output t) :
    ∃ T, ∀ t, T ≤ t → output t ∉ E := by
  classical
  letI := hE.fintype
  rcases hnorepeat with ⟨T₀, hnr⟩
  let occurrenceBound : E → ℕ := fun x =>
    if hx : x.1 ∈ Set.range output then Nat.find hx else 0
  let cutoff := T₀ + 1 + ∑ x : E, occurrenceBound x
  refine ⟨cutoff, ?_⟩
  intro t ht hout
  let x : E := ⟨output t, hout⟩
  have hxrange : x.1 ∈ Set.range output := ⟨t, rfl⟩
  let s := Nat.find hxrange
  have hsout : output s = output t := Nat.find_spec hxrange
  have hs_le_sum : s ≤ ∑ y : E, occurrenceBound y := by
    calc
      s = occurrenceBound x := by
        simp only [occurrenceBound]
        rw [dif_pos hxrange]
      _ ≤ ∑ y : E, occurrenceBound y := by
        exact Finset.single_le_sum (fun y _ => Nat.zero_le (occurrenceBound y))
          (Finset.mem_univ x)
  have hslt : s < t := by
    omega
  exact (hnr t (by omega) s hslt) hsout

theorem novel_over_finite_extension_eventually_target
    {input output : Stream} {K E : Language} (hE : E.Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output (K ∪ E)) :
    ∃ T, ∀ t, T ≤ t → output t ∈ K := by
  rcases hnovel with ⟨T₀, hnovel⟩
  obtain ⟨T₁, havoid⟩ := eventually_avoids_finite_of_eventually_norepeat hE
    ⟨T₀, fun t ht => (hnovel t ht).2.2⟩
  refine ⟨max T₀ T₁, ?_⟩
  intro t ht
  rcases (hnovel t (le_trans (le_max_left _ _) ht)).1 with hK | hEout
  · exact hK
  · exact False.elim (havoid t (le_trans (le_max_right _ _) ht) hEout)

end Stage3Case025

namespace Stage3Case025

/-- Checked finite-noise reduction up to the analytic fact that adjoining a
finite set does not change relative lower density. -/
theorem positive_engine_finite_noise_reduction
    (hpositive : PositivePresentationHalfDensity) :
    ∀ family : ℕ → Language, (∀ i, (family i).Infinite) →
      ∃ gen : OnlineGenerator,
        ∀ i (input : Stream),
          CompleteFiniteOccurrencePresentation input (family i) →
            ∃ output : Stream, ∃ E : Language,
              E.Finite ∧
              Follows gen input output ∧
              GenLimit.NovelGeneratesInLimit input output (family i) ∧
              (1 / 2 : ℝ) ≤
                GenLimit.PatientScope.relativeLowerDensity
                  (GenLimit.GeneratorFirst input output ∩ (family i ∪ E))
                  (family i ∪ E) := by
  intro family hfamily
  obtain ⟨gen, hgen⟩ := hpositive (finiteExtensionFamily family)
    (finiteExtensionFamily_infinite family hfamily)
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  let E := exceptionValues input (family i)
  have hE : E.Finite := exceptionValues_finite hpresentation.2
  let exceptions : Finset ℕ := hE.toFinset
  obtain ⟨n, hn⟩ := finiteExtensionFamily_contains family i exceptions
  have hEcoe : (exceptions : Set ℕ) = E := by
    exact hE.coe_toFinset
  have hpresents : GenLimit.Presents input (finiteExtensionFamily family n) := by
    rw [hn, hEcoe]
    exact range_eq_target_union_exceptions hpresentation.1
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen n input hpresents
  rw [hn, hEcoe] at hnovel hdensity
  refine ⟨output, E, hE, hfollows, ?_, hdensity⟩
  rcases hnovel with ⟨T₀, hnovel⟩
  have hnovelKE : GenLimit.NovelGeneratesInLimit input output (family i ∪ E) :=
    ⟨T₀, hnovel⟩
  obtain ⟨T₁, htarget⟩ :=
    novel_over_finite_extension_eventually_target (input := input) hE hnovelKE
  refine ⟨max T₀ T₁, ?_⟩
  intro t ht
  have ht₀ : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht₁ : T₁ ≤ t := le_trans (le_max_right _ _) ht
  exact ⟨htarget t ht₁, (hnovel t ht₀).2⟩

end Stage3Case025
