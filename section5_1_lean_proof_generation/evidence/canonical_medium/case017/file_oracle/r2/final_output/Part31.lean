import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Case017Proof

noncomputable def compatibleCore {m t : ℕ}
    (family : Fin m → Set ℕ) (xs : Fin t → ℕ) : Set ℕ :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def seen {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs ∪ GenLimit.Generic.sequenceSample ys

noncomputable def leastFresh (S : Set ℕ) (F : Finset ℕ)
    (hS : S.Infinite) : ℕ := by
  classical
  exact Nat.find (hS.exists_notMem_finset F)

lemma leastFresh_spec (S : Set ℕ) (F : Finset ℕ) (hS : S.Infinite) :
    leastFresh S F hS ∈ S ∧ leastFresh S F hS ∉ F := by
  classical
  exact Nat.find_spec (hS.exists_notMem_finset F)

lemma leastFresh_le (S : Set ℕ) (F : Finset ℕ) (hS : S.Infinite)
    {z : ℕ} (hzS : z ∈ S) (hzF : z ∉ F) :
    leastFresh S F hS ≤ z := by
  classical
  exact Nat.find_min' (hS.exists_notMem_finset F) ⟨hzS, hzF⟩

