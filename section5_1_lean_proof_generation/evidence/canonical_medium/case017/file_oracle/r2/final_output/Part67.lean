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

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Set ℕ) :
    Stage3Case017.OnlineGenerator :=
  fun t xs ys => by
    classical
    let C := compatibleCore family xs
    let F := seen xs ys
    exact if hC : C.Infinite then leastFresh C F hC
      else leastFresh Set.univ F Set.infinite_univ

noncomputable def outputPrefix (gen : Stage3Case017.OnlineGenerator)
    (input : ℕ → ℕ) : (t : ℕ) → Fin t → ℕ
  | 0 => Fin.elim0
  | t + 1 => Fin.lastCases
      (gen t (fun i => input i) (outputPrefix gen input t))
      (outputPrefix gen input t)

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : ℕ → ℕ) : ℕ → ℕ :=
  fun t => outputPrefix gen input (t + 1) (Fin.last t)

@[simp] lemma outputPrefix_castSucc (gen : Stage3Case017.OnlineGenerator)
    (input : ℕ → ℕ) {t : ℕ} (i : Fin t) :
    outputPrefix gen input (t + 1) i.castSucc = outputPrefix gen input t i := by
  simp [outputPrefix]

lemma outputPrefix_eq_trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : ℕ → ℕ) {t : ℕ} (i : Fin t) :
    outputPrefix gen input t i = trajectory gen input i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rfl
      · simpa only [outputPrefix_castSucc] using ih k


