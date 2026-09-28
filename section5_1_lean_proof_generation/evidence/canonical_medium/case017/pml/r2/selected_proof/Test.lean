import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def prefixCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

theorem exists_available_of_infinite {S : Set ℕ} (hS : S.Infinite)
    (F : Finset ℕ) : ∃ z, z ∈ S ∧ z ∉ F := by
  have hdiff : (S \ (F : Set ℕ)).Infinite := hS.diff F.finite_toSet
  obtain ⟨z, hz⟩ := hdiff.nonempty
  exact ⟨z, hz.1, hz.2⟩

noncomputable def leastAvailable {S : Set ℕ} (hS : S.Infinite)
    (F : Finset ℕ) : ℕ :=
  Nat.find (exists_available_of_infinite hS F)

theorem leastAvailable_spec {S : Set ℕ} (hS : S.Infinite) (F : Finset ℕ) :
    leastAvailable hS F ∈ S ∧ leastAvailable hS F ∉ F :=
  Nat.find_spec (exists_available_of_infinite hS F)

theorem leastAvailable_le {S : Set ℕ} (hS : S.Infinite) (F : Finset ℕ)
    {z : ℕ} (hzS : z ∈ S) (hzF : z ∉ F) : leastAvailable hS F ≤ z := by
  exact Nat.find_min' (exists_available_of_infinite hS F) ⟨hzS, hzF⟩

noncomputable def generator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := fun t xs ys =>
  if h : (prefixCore family xs).Infinite then
    leastAvailable h (forbidden xs ys)
  else
    leastAvailable Set.infinite_univ (forbidden xs ys)


end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  sorry
