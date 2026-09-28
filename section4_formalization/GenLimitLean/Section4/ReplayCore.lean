import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Minimal

/-! Core finite-family notation for the written proper-replay characterization.
The semantic generator and replay definitions are those of P22 in GenLimitLib. -/

namespace Section4.Replay

open Set

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def profile (L : ι → Set α) (x : α) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x ∈ L i)

def residual (L : ι → Set α) (j i : ι) : Set α := L i \ L j

noncomputable def group (L : ι → Set α) (j : ι) (P : Finset ι) (i : ι) : Finset ι := by
  classical
  exact P.filter (fun k => residual L j k = residual L j i)

def CommonLower (L : ι → Set α) (E : Finset ι) (h : ι) : Prop :=
  ∀ k ∈ E, L h ⊆ L k

def GoodFirst (L : ι → Set α) (P : Finset ι) (j : ι) : Prop :=
  ∀ i ∈ P, ∃ h, CommonLower L (group L j P i) h

def Criterion (L : ι → Set α) : Prop :=
  ∀ x, (∃ i, x ∈ L i) → ∃ j, GoodFirst L (profile L x) j

def MinimalLanguage (L : ι → Set α) (h : ι) : Prop :=
  ∀ k, L k ⊆ L h → L h ⊆ L k

@[simp] theorem mem_profile (L : ι → Set α) (x : α) (i : ι) :
    i ∈ profile L x ↔ x ∈ L i := by
  classical
  simp [profile]

@[simp] theorem mem_group (L : ι → Set α) (j : ι) (P : Finset ι) (i k : ι) :
    k ∈ group L j P i ↔ k ∈ P ∧ residual L j k = residual L j i := by
  classical
  simp [group]

theorem self_mem_group (L : ι → Set α) (j : ι) {P : Finset ι} {i : ι}
    (hi : i ∈ P) : i ∈ group L j P i := by
  simp [hi]

theorem group_eq_of_residual_eq (L : ι → Set α) (j : ι) (P : Finset ι)
    {i k : ι} (h : residual L j i = residual L j k) :
    group L j P i = group L j P k := by
  classical
  ext l
  simp [h]

theorem residual_eq_mem_iff (L : ι → Set α) (j : ι) {i k : ι}
    (h : residual L j i = residual L j k) {x : α} (hx : x ∉ L j) :
    x ∈ L i ↔ x ∈ L k := by
  have := Set.ext_iff.mp h x
  simpa [residual, hx] using this

end Section4.Replay
