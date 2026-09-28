import Stage3Model
import DensityTransfer
import Mathlib.Combinatorics.Colex

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable section

private def decodedIndex (n : ℕ) : ℕ := (Nat.pairEquiv.symm n).1

private def decodedFinset (n : ℕ) : Finset ℕ :=
  Finset.equivBitIndices (Nat.pairEquiv.symm n).2

private def finiteExtensionFamily (family : ℕ → Language) : ℕ → Language :=
  fun n => family (decodedIndex n) ∪ (decodedFinset n : Set ℕ)

private theorem finiteExtensionFamily_infinite
    (family : ℕ → Language) (hfamily : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExtensionFamily family n).Infinite := by
  intro n
  exact (hfamily (decodedIndex n)).mono Set.subset_union_left

private def violationValues (input : Stream) (K : Language) : Set ℕ :=
  input '' GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)

private theorem violationValues_finite
    {input : Stream} {K : Language}
    (h : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (violationValues input K).Finite := by
  exact h.image input

private theorem range_eq_union_violationValues
    {input : Stream} {K : Language} (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ violationValues input K := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    by_cases hx : input t ∈ K
    · exact Or.inl hx
    · exact Or.inr ⟨t, hx, rfl⟩
  · rintro (hx | hx)
    · exact hcover hx
    · rcases hx with ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩

private theorem exists_extension_index
    (family : ℕ → Language) (i : ℕ) (B : Set ℕ) (hB : B.Finite) :
    ∃ n, finiteExtensionFamily family n = family i ∪ B := by
  let b : ℕ := Finset.equivBitIndices.symm hB.toFinset
  refine ⟨Nat.pairEquiv (i, b), ?_⟩
  simp [finiteExtensionFamily, decodedIndex, decodedFinset, b,
    Set.Finite.coe_toFinset]

private theorem tail_bad_times_finite
    {output : Stream} {B : Set ℕ} (hB : B.Finite) {T : ℕ}
    (hnovel : ∀ t, T ≤ t → ∀ s, s < t → output s ≠ output t) :
    {t | T ≤ t ∧ output t ∈ B}.Finite := by
  apply Set.Finite.of_injOn (f := output) (t := B)
  · intro t ht
    exact ht.2
  · intro s hs t ht heq
    rcases lt_trichotomy s t with hst | hst | hst
    · exact False.elim ((hnovel t ht.1 s hst) heq)
    · exact hst
    · exact False.elim ((hnovel s hs.1 t hst) heq.symm)
  · exact hB

private theorem eventually_avoids_finite
    {output : Stream} {B : Set ℕ} (hB : B.Finite) {T : ℕ}
    (hnovel : ∀ t, T ≤ t → ∀ s, s < t → output s ≠ output t) :
    ∃ T', ∀ t, T' ≤ t → output t ∉ B := by
  have hbad := tail_bad_times_finite hB hnovel
  rcases hbad.toFinset.exists_nat_subset_range with ⟨N, hN⟩
  refine ⟨max T N, ?_⟩
  intro t ht hmem
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hbadmem : t ∈ hbad.toFinset := by simpa using (show t ∈ {t | T ≤ t ∧ output t ∈ B} from ⟨htT, hmem⟩)
  have hlt : t < N := Finset.mem_range.mp (hN hbadmem)
  exact (Nat.not_lt_of_ge (le_trans (le_max_right _ _) ht)) hlt

theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro positiveEngine family hfamily
  have hextensionInfinite : ∀ n, (finiteExtensionFamily family n).Infinite :=
    finiteExtensionFamily_infinite family hfamily
  obtain ⟨gen, hgen⟩ := positiveEngine (finiteExtensionFamily family) hextensionInfinite
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  rcases hpresentation with ⟨hcover, hfiniteViolations⟩
  let B : Set ℕ := violationValues input (family i)
  have hB : B.Finite := violationValues_finite hfiniteViolations
  have hrange : Set.range input = family i ∪ B :=
    range_eq_union_violationValues hcover
  obtain ⟨j, hj⟩ := exists_extension_index family i B hB
  have hpresents : GenLimit.Presents input (finiteExtensionFamily family j) := by
    rw [hj]
    exact hrange
  obtain ⟨output, hfollow, hnovelExtension, hdensityExtension⟩ :=
    hgen j input hpresents
  refine ⟨output, hfollow, ?_, ?_⟩
  · rcases hnovelExtension with ⟨T, hT⟩
    have havoidsB : ∃ T', ∀ t, T' ≤ t → output t ∉ B :=
      eventually_avoids_finite hB (fun t ht s hs => (hT t ht).2.2 s hs)
    rcases havoidsB with ⟨T', hT'⟩
    refine ⟨max T T', ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htT' : T' ≤ t := le_trans (le_max_right _ _) ht
    have hproperties := hT t htT
    have htarget : output t ∈ family i := by
      rw [hj] at hproperties
      rcases hproperties.1 with htarget | hnoise
      · exact htarget
      · exact False.elim ((hT' t htT') hnoise)
    exact ⟨htarget, hproperties.2.1, hproperties.2.2⟩
  · rw [hj] at hdensityExtension
    exact hdensityExtension.trans
      (finite_change_relativeLowerDensity
        (GenLimit.GeneratorFirst input output) (family i) B (hfamily i) hB)

end

end Stage3Case025
