import Helpers

open Set
open Stage3Case025

noncomputable section

namespace Stage3Case025

theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hfamily
  obtain ⟨gen, hgen⟩ := hpositive (finiteExtensionFamily family)
    (finiteExtensionFamily_infinite family hfamily)
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  let B : Language := input '' GenLimit.Generic.ViolationIndices input (fun x => x ∈ family i)
  have hB : B.Finite := finite_violation_values hpresentation.2
  let s : Finset ℕ := hB.toFinset
  let j : ℕ := Nat.pair i (Encodable.encode s)
  have hext : finiteExtensionFamily family j = family i ∪ B := by
    change finiteExtensionFamily family (Nat.pair i (Encodable.encode s)) = family i ∪ B
    rw [finiteExtensionFamily_pair]
    simp [s]
  have hrange : Set.range input = family i ∪ B :=
    range_eq_target_union_violation_values hpresentation.1
  have hpresents : GenLimit.Presents input (finiteExtensionFamily family j) := by
    unfold GenLimit.Presents
    rw [hext]
    exact hrange
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows, novelGeneratesInLimit_remove_finite hB ?_, ?_⟩
  · rw [← hext]
    exact hnovel
  · apply relativeLowerDensity_remove_finite (hfamily i) hB
    rw [← hext]
    exact hdensity

end Stage3Case025
