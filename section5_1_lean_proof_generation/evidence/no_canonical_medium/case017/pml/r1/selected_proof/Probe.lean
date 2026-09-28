import Stage3Model
import GenLimit.Paper39_DenseGeneration.Partial.Trace
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Stage3Case017Proof

open GenLimit

noncomputable def finiteCore {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image xs ∪ Finset.univ.image ys

noncomputable def available {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ finiteCore family xs ∧ z ∉ forbidden xs ys

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    Stage3Case017.OnlineGenerator := fun _ xs ys => by
  classical
  exact if h : ∃ z, available family xs ys z then Nat.find h
    else Nat.find (Set.infinite_univ.exists_notMem_finset (forbidden xs ys))

 theorem greedyGenerator_fresh {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    greedyGenerator family t xs ys ∉ forbidden xs ys := by
  classical
  simp only [greedyGenerator]
  split
  · exact (Nat.find_spec ‹∃ z, available family xs ys z›).2
  · exact (Nat.find_spec
      (Set.infinite_univ.exists_notMem_finset (forbidden xs ys))).2

 theorem greedyGenerator_spec {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, available family xs ys z) :
    available family xs ys (greedyGenerator family t xs ys) := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_spec h

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
 decreasing_by exact i.isLt

 theorem trajectory_follows (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) :
#check trajectory.eq_1
#check trajectory.eq_def
#check trajectory._eq_1
end Stage3Case017Proof
