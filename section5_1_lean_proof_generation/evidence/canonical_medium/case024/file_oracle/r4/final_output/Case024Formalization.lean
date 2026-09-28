import Helpers

open Filter MeasureTheory
open scoped Topology

namespace Case024

open Stage3Case024
open GenLimit.InfiniteContamination

def extraPrefix (j : ℕ) : Set ℕ :=
  {x | ∃ k, k < j ∧ sparseBetweenSquares k = x}

lemma extraPrefix_mono {i j : ℕ} (hij : i ≤ j) : extraPrefix i ⊆ extraPrefix j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

lemma sparseBetweenSquares_not_square (k : ℕ) : sparseBetweenSquares k ∉ Squares :=
  sparseBetweenSquares_nonsquare k

lemma sparseBetweenSquares_mem_extraPrefix {i j : ℕ} (hij : i < j) :
    sparseBetweenSquares i ∈ extraPrefix j :=
  ⟨i, hij, rfl⟩

lemma sparseBetweenSquares_not_mem_extraPrefix (i : ℕ) :
    sparseBetweenSquares i ∉ extraPrefix i := by
  rintro ⟨k, hk, heq⟩
  have : k = i := sparseBetweenSquares_strictMono.injective heq
  omega

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if (j : ℕ) + 1 = r then Set.univ else Squares ∪ extraPrefix j

lemma squares_subset_nestedFamily {r : ℕ} (j : Fin r) :
    Squares ⊆ nestedFamily r j := by
  intro x hx
  unfold nestedFamily
  split
  · trivial
  · exact Or.inl hx

lemma nestedFamily_infinite {r : ℕ} (j : Fin r) :
    (nestedFamily r j).Infinite :=
  squares_infinite.mono (squares_subset_nestedFamily j)

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = Squares := by
  unfold nestedFamily
  simp only [Fin.val_mk]
  have hne : 1 ≠ r := by omega
  simp [hne, extraPrefix]

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  unfold nestedFamily
  simp [show r - 1 + 1 = r by omega]

lemma nestedFamily_not_last_of_lt {r : ℕ} {i j : Fin r} (hij : (i : ℕ) < j)
    (hj : (j : ℕ) + 1 ≠ r) : (i : ℕ) + 1 ≠ r := by
  omega

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) : StrictlyNested (nestedFamily r) := by
  intro i j hij
  by_cases hjlast : (j : ℕ) + 1 = r
  · have hilast : (i : ℕ) + 1 ≠ r := by omega
    simp only [nestedFamily, hjlast, hilast, if_pos, if_neg]
    apply Set.ssubset_iff_subset_ne.mpr
    constructor
    · exact Set.subset_univ _
    · intro heq
      have heq' : Squares ∪ extraPrefix i = (Set.univ : Set ℕ) := by
        simpa using heq
      let w := sparseBetweenSquares r
      have hwuniv : w ∈ (Set.univ : Set ℕ) := trivial
      have hwnsq : w ∉ Squares := sparseBetweenSquares_not_square r
      have hwnextra : w ∉ extraPrefix i := by
        rintro ⟨k, hk, heqk⟩
        have hkr : k = r := sparseBetweenSquares_strictMono.injective heqk
        omega
      have hwleft : w ∈ Squares ∪ extraPrefix i := heq'.symm ▸ hwuniv
      exact hwleft.elim hwnsq hwnextra
  · have hilast : (i : ℕ) + 1 ≠ r := nestedFamily_not_last_of_lt hij hjlast
    simp only [nestedFamily, hjlast, hilast, if_pos, if_neg]
    apply Set.ssubset_iff_subset_ne.mpr
    constructor
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (extraPrefix_mono (Nat.le_of_lt hij) hx)
    · intro heq
      have heq' : Squares ∪ extraPrefix i = Squares ∪ extraPrefix j := by
        simpa using heq
      let w := sparseBetweenSquares i
      have hwright : w ∈ Squares ∪ extraPrefix j :=
        Or.inr (sparseBetweenSquares_mem_extraPrefix hij)
      have hwnsq : w ∉ Squares := sparseBetweenSquares_not_square i
      have hwnextra : w ∉ extraPrefix i := sparseBetweenSquares_not_mem_extraPrefix i
      have hwleft : w ∈ Squares ∪ extraPrefix i := heq'.symm ▸ hwright
      exact hwleft.elim hwnsq hwnextra

lemma nestedFamily_manyWitness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨nestedFamily_strict hr, ?_, globallyFeasible (nestedFamily r)
    (fun j => squares_subset_nestedFamily j), ?_⟩
  · intro j
    exact commonInput_legal_of_squares_subset (squares_subset_nestedFamily j)
      (nestedFamily_infinite j)
  · apply manyObstruction
    · exact ⟨⟨r - 1, by omega⟩, nestedFamily_last hr⟩
    · exact ⟨⟨0, by omega⟩, nestedFamily_zero hr⟩

lemma squares_strict_univ : Squares ⊂ (Set.univ : Set ℕ) := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · exact Set.subset_univ _
  · intro heq
    have hmem : sparseBetweenSquares 0 ∈ Squares := heq.symm ▸ (Set.mem_univ _)
    exact sparseBetweenSquares_not_square 0 hmem

end Case024

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact ⟨Squares, Set.univ, commonInput, squares_strict_univ,
      commonInput_legal_of_squares_subset Set.Subset.rfl squares_infinite,
      commonInput_legal_of_squares_subset (Set.subset_univ _) Set.infinite_univ,
      pairObstruction⟩
  · intro r hr
    exact ⟨nestedFamily r, commonInput, nestedFamily_manyWitness hr⟩
