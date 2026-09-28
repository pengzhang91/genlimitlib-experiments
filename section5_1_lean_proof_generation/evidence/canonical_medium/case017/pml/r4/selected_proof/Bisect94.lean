import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

open Set Filter

namespace Stage3Case017Proof

open GenLimit
open GenLimit.Generic
open GenLimit.PatientScope
open Stage3Case017

noncomputable def historySet {n : ℕ} (xs : Fin n → ℕ) : Finset ℕ :=
  sequenceSample xs

def roundCore {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) : Set ℕ :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

theorem exists_fresh (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    ∃ z, z ∈ C ∧ z ∉ seen := by
  have hnonempty := (hC.diff seen.finite_toSet).nonempty
  simpa only [Set.mem_diff, Finset.mem_coe] using hnonempty

noncomputable def leastFresh (C : Set ℕ) (hC : C.Infinite)
    (seen : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (exists_fresh C hC seen)

theorem leastFresh_mem (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFresh C hC seen ∈ C := by
  classical
  exact (Nat.find_spec (exists_fresh C hC seen)).1

theorem leastFresh_not_mem (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFresh C hC seen ∉ seen := by
  classical
  exact (Nat.find_spec (exists_fresh C hC seen)).2

theorem leastFresh_le (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ)
    {z : ℕ} (hzC : z ∈ C) (hzseen : z ∉ seen) :
    leastFresh C hC seen ≤ z := by
  classical
  exact Nat.find_min' (exists_fresh C hC seen) ⟨hzC, hzseen⟩

noncomputable def generator {m : ℕ} (family : Fin m → Set ℕ) : OnlineGenerator := by
  classical
  exact fun t xs ys =>
    let C := roundCore family xs
    let seen := historySet xs ∪ historySet ys
    if hC : C.Infinite then leastFresh C hC seen
    else leastFresh Set.univ Set.infinite_univ seen

theorem generator_not_input {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    generator family t xs ys ∉ historySet xs := by
  classical
  unfold generator
  dsimp only
  split_ifs with hC
  · exact fun h => leastFresh_not_mem _ hC _ (Finset.mem_union_left _ h)
  · exact fun h => leastFresh_not_mem _ Set.infinite_univ _ (Finset.mem_union_left _ h)

theorem generator_not_output {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    generator family t xs ys ∉ historySet ys := by
  classical
  unfold generator
  dsimp only
  split_ifs with hC
  · exact fun h => leastFresh_not_mem _ hC _ (Finset.mem_union_right _ h)
  · exact fun h => leastFresh_not_mem _ Set.infinite_univ _ (Finset.mem_union_right _ h)

theorem generator_mem_of_infinite {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (roundCore family xs).Infinite) :
    generator family t xs ys ∈ roundCore family xs := by
  classical
  simp [generator, hC, leastFresh_mem]

theorem generator_le_of_available {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (roundCore family xs).Infinite) {z : ℕ}
    (hzC : z ∈ roundCore family xs)
    (hzx : z ∉ historySet xs) (hzy : z ∉ historySet ys) :
    generator family t xs ys ≤ z := by
  classical
  simp only [generator, hC, dif_pos]
  apply leastFresh_le _ hC _ hzC
  simp only [Finset.mem_union, not_or]
  exact ⟨hzx, hzy⟩



end Stage3Case017Proof
theorem stage3_result : Stage3Case017.MainClaim := by sorry
