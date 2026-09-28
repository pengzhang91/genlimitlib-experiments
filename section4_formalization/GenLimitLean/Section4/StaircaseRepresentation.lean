import Section4.StaircaseFrontier
import Mathlib.Logic.Denumerable
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Countable

/-! A representation theorem for arbitrary disjoint finite common blocks and
countably infinite private blocks. The embedding need not exhaust the ambient
universe: it exhausts exactly the points used by the languages. -/
namespace Section4.Staircase

private def offset (a : ℕ → ℕ) (i : ℕ) := ∑ k ∈ Finset.range i, a k

private theorem offset_succ (a : ℕ → ℕ) (i : ℕ) :
    offset a (i+1) = offset a i + a i := by simp [offset, Finset.sum_range_succ]

private theorem offset_strict (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) :
    StrictMono (offset a) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [offset_succ]
  exact Nat.lt_add_of_pos_right (ha i)

private theorem offset_large (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) (i : ℕ) :
    i ≤ offset a i := by
  induction i with
  | zero => simp [offset]
  | succ i hi => rw [offset_succ]; have := ha i; omega

private noncomputable def blockIndex (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) (n : ℕ) : ℕ :=
  Nat.find (show ∃ i, n < offset a (i+1) from ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (offset_large a ha (n+1))⟩)

private theorem blockIndex_bounds (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) (n : ℕ) :
    offset a (blockIndex a ha n) ≤ n ∧ n < offset a (blockIndex a ha n + 1) := by
  have hex : ∃ i, n < offset a (i+1) := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (offset_large a ha (n+1))⟩
  change offset a (Nat.find hex) ≤ n ∧ n < offset a (Nat.find hex + 1)
  refine ⟨?_, Nat.find_spec hex⟩
  cases h : Nat.find hex with
  | zero => simp [offset]
  | succ j =>
    have := Nat.find_min hex (show j < Nat.find hex by omega)
    simpa [h] using Nat.le_of_not_lt this

private theorem blockIndex_eq (a : ℕ → ℕ) (ha : ∀ i, 0 < a i)
    {n i : ℕ} (hlo : offset a i ≤ n) (hhi : n < offset a (i+1)) :
    blockIndex a ha n = i := by
  have hb := blockIndex_bounds a ha n
  have hm := (offset_strict a ha).monotone
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have := hm (show blockIndex a ha n + 1 ≤ i by omega); omega
  · have := hm (show i+1 ≤ blockIndex a ha n by omega); omega

private noncomputable def blockCoordinate (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) (n : ℕ) :
    Fin (a (blockIndex a ha n)) :=
  ⟨n - offset a (blockIndex a ha n), by
    have hb := blockIndex_bounds a ha n
    rw [offset_succ] at hb
    omega⟩

/-- Representation with specified enumerations of each finite and private block. -/
theorem representation_of_enumerations {X : Type*} (C R : ℕ → Set X)
    (a : ℕ → ℕ) (ha : ∀ i, 0 < a i)
    (ec : ∀ i, Fin (a i) ≃ C i) (er : ∀ i, ℕ ≃ R i)
    (hCC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hRR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hCR : ∀ i j, Disjoint (C i) (R j)) :
    ∃ e : Point ↪ X, ∀ i,
      e '' (Family.ofBlocks a ha).target i = (⋃ k ≤ i, C k) ∪ R i := by
  classical
  let core : ℕ → X := fun n => ec (blockIndex a ha n) (blockCoordinate a ha n)
  have core_mem (n : ℕ) : core n ∈ C (blockIndex a ha n) :=
    (ec _ _).property
  have enum_inj (i j : ℕ) (u : Fin (a i)) (v : Fin (a j))
      (heq : (ec i u).val = (ec j v).val) : i = j ∧ u.val = v.val := by
    have hi : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hCC hne) (ec i u).property (heq ▸ (ec j v).property)
    subst j
    exact ⟨rfl, congrArg Fin.val ((ec i).injective (Subtype.ext heq))⟩
  have core_inj : Function.Injective core := by
    intro n m heq
    obtain ⟨hi,hcoord⟩ := enum_inj _ _ _ _ heq
    have hn := (blockIndex_bounds a ha n).1
    have hm := (blockIndex_bounds a ha m).1
    dsimp [blockCoordinate] at hcoord
    rw [hi] at hn hcoord
    omega
  have core_eval (n i : ℕ) (hi : blockIndex a ha n = i)
      (h : n - offset a i < a i) :
      core n = (ec i ⟨n - offset a i, h⟩).val := by
    subst i
    rfl
  have core_surj (i : ℕ) (x : C i) : ∃ n, blockIndex a ha n = i ∧ core n = x := by
    let r := (ec i).symm x
    let n := offset a i + r.val
    have hi : blockIndex a ha n = i := blockIndex_eq a ha (by omega) (by
      rw [offset_succ]; have := r.isLt; dsimp [n]; omega)
    refine ⟨n, hi, ?_⟩
    have hr : n - offset a i = r.val := by simp [n]
    rw [core_eval n i hi (by rw [hr]; exact r.isLt)]
    have hc' : (⟨n - offset a i, by rw [hr]; exact r.isLt⟩ : Fin (a i)) = r := Fin.ext hr
    rw [hc']
    exact congrArg Subtype.val ((ec i).apply_symm_apply x)
  let f : Point → X := Sum.elim core (fun q => er q.1 q.2)
  have hf : Function.Injective f := by
    intro p q heq
    cases p with
    | inl n =>
      cases q with
      | inl m => exact congrArg Sum.inl (core_inj heq)
      | inr q =>
        change core n = (er q.1 q.2).val at heq
        exact False.elim (Set.disjoint_left.mp (hCR _ _) (core_mem n) (heq ▸ (er q.1 q.2).property))
    | inr p =>
      cases q with
      | inl m =>
        change (er p.1 p.2).val = core m at heq
        exact False.elim (Set.disjoint_left.mp (hCR _ _) (core_mem m) (heq.symm ▸ (er p.1 p.2).property))
      | inr q =>
        rcases p with ⟨i,r⟩
        rcases q with ⟨j,s⟩
        change (er i r).val = (er j s).val at heq
        have hi : i = j := by
          by_contra hne
          exact Set.disjoint_left.mp (hRR hne) (er i r).property (heq ▸ (er j s).property)
        subst j
        have hj : r = s := (er i).injective (Subtype.ext heq)
        subst s
        rfl
  refine ⟨⟨f,hf⟩, ?_⟩
  intro i
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    cases p with
    | inl n =>
      apply Or.inl
      have hn : n < offset a (i+1) := hp
      have hbi : blockIndex a ha n ≤ i := by
        have hb := (blockIndex_bounds a ha n).1
        by_contra hnot
        have := (offset_strict a ha).monotone (show i+1 ≤ blockIndex a ha n by omega)
        omega
      exact Set.mem_iUnion.mpr ⟨_,Set.mem_iUnion.mpr ⟨hbi,core_mem n⟩⟩
    | inr q =>
      apply Or.inr
      have hqi : q.1 = i := hp
      simpa [f, hqi] using (er q.1 q.2).property
  · rintro (hx | hx)
    · obtain ⟨k,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hki,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨n,hn,hx⟩ := core_surj k ⟨x,hx⟩
      refine ⟨Sum.inl n, ?_, hx⟩
      change n < offset a (i+1)
      have hb := (blockIndex_bounds a ha n).2
      rw [hn] at hb
      exact lt_of_lt_of_le hb ((offset_strict a ha).monotone (Nat.succ_le_succ hki))
    · refine ⟨Sum.inr (i,(er i).symm ⟨x,hx⟩),rfl,?_⟩
      exact congrArg Subtype.val ((er i).apply_symm_apply ⟨x,hx⟩)

/-- Any abstract staircase family over a countable universe has the concrete
representation used by the exact-frontier theorem. -/
theorem exists_representation {X : Type*} (C R : ℕ → Set X)
    (hCf : ∀ i, (C i).Finite) (hCn : ∀ i, (C i).Nonempty)
    (hRi : ∀ i, (R i).Infinite) (hRc : ∀ i, (R i).Countable)
    (hCC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hRR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hCR : ∀ i j, Disjoint (C i) (R j)) :
    ∃ (ha : ∀ i, 0 < Nat.card (C i)) (e : Point ↪ X), ∀ i,
      e '' (Family.ofBlocks (fun i => Nat.card (C i)) ha).target i =
        (⋃ k ≤ i, C k) ∪ R i := by
  classical
  letI (i : ℕ) : Finite (C i) := (hCf i).to_subtype
  letI (i : ℕ) : Nonempty (C i) := (hCn i).to_subtype
  letI (i : ℕ) : Infinite (R i) := (hRi i).to_subtype
  letI (i : ℕ) : Countable (R i) := (hRc i).to_subtype
  have ha (i : ℕ) : 0 < Nat.card (C i) := Nat.card_pos
  refine ⟨ha, ?_⟩
  apply representation_of_enumerations C R (fun i => Nat.card (C i)) ha
    (fun i => (Finite.equivFin (C i)).symm)
    (fun i => Classical.choice (inferInstance : Nonempty (ℕ ≃ R i))) hCC hRR hCR

end Section4.Staircase

#print axioms Section4.Staircase.exists_representation
