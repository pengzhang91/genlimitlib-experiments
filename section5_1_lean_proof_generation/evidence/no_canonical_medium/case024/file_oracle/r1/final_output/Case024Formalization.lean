import Stage3Model
import «output».Helpers

open Filter MeasureTheory
open scoped Topology

namespace Case024

lemma pairObstruction : Stage3Case024.PairObstruction Square Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hInt0 _ hValid0 _
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hValid0] with ω hω
    exact path_density_univ_zero hω
  have hE1 : Stage3Case024.expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzero]
    simp
  have hE0 : Stage3Case024.expectedUpperDensity μ Square commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Square ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hInt0 (integrable_const 1)
            exact Filter.Eventually.of_forall (fun ω =>
              relativeUpperDensity_le_one _ _)
      _ = 1 := by simp
  constructor
  · rw [hE1]
    linarith
  · intro h
    rw [hE1] at h
    linarith

lemma pairClaim : ∃ K₀ K₁ : Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
    K₀ ⊂ K₁ ∧ Stage3Case024.Legal input K₀ ∧ Stage3Case024.Legal input K₁ ∧
      Stage3Case024.PairObstruction K₀ K₁ input := by
  refine ⟨Square, Set.univ, commonInput, ?_, legal_commonInput Set.Subset.rfl,
    legal_commonInput (Set.subset_univ Square), pairObstruction⟩
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ Square, ?_⟩
  intro h
  have hsquare : GenLimit.InfiniteContamination.SparseSquare 2 := by
    simpa [Square] using (h.symm.subset (Set.mem_univ 2))
  have hnonsquare := GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare 0
  exact hnonsquare (by simpa [GenLimit.InfiniteContamination.sparseBetweenSquares] using hsquare)


def finiteTags (i : ℕ) : Set ℕ :=
  {x | ∃ k, k < i ∧ GenLimit.InfiniteContamination.sparseBetweenSquares k = x}

def lastFin (r : ℕ) (hr : 2 ≤ r) : Fin r := ⟨r - 1, by omega⟩

noncomputable def nestedFamily (r : ℕ) (hr : 2 ≤ r) (i : Fin r) : Set ℕ :=
  if i = lastFin r hr then Set.univ else Square ∪ finiteTags i

lemma square_subset_nestedFamily {r : ℕ} (hr : 2 ≤ r) (i : Fin r) :
    Square ⊆ nestedFamily r hr i := by
  intro x hx
  by_cases hi : i = lastFin r hr
  · simp [nestedFamily, hi]
  · simp [nestedFamily, hi, hx]

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r hr ⟨0, by omega⟩ = Square := by
  have hne : (⟨0, by omega⟩ : Fin r) ≠ lastFin r hr := by
    intro h
    have := congrArg Fin.val h
    simp [lastFin] at this
    omega
  ext x
  simp [nestedFamily, hne, finiteTags]

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r hr (lastFin r hr) = Set.univ := by
  simp [nestedFamily]

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r hr) := by
  intro i j hij
  have hiLast : i ≠ lastFin r hr := by
    intro h
    have hi : (i : ℕ) = r - 1 := by simpa [h, lastFin]
    have hj : (j : ℕ) < r := j.isLt
    omega
  let x := GenLimit.InfiniteContamination.sparseBetweenSquares (i : ℕ)
  have hxNotSquare : x ∉ Square :=
    GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare i
  have hxNotTags : x ∉ finiteTags i := by
    rintro ⟨k, hk, heq⟩
    have hki : k = (i : ℕ) :=
      GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective heq
    omega
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · intro y hy
    by_cases hjLast : j = lastFin r hr
    · simp [nestedFamily, hjLast]
    · simp only [nestedFamily, hiLast, hjLast, if_false] at hy ⊢
      rcases hy with hySquare | ⟨k, hk, rfl⟩
      · exact Or.inl hySquare
      · exact Or.inr ⟨k, lt_trans hk hij, rfl⟩
  · intro heq
    have hxj : x ∈ nestedFamily r hr j := by
      by_cases hjLast : j = lastFin r hr
      · simp [nestedFamily, hjLast]
      · simp only [nestedFamily, hjLast, if_false, Set.mem_union]
        exact Or.inr ⟨i, hij, rfl⟩
    have hxi : x ∈ nestedFamily r hr i := heq.symm.subset hxj
    simp only [nestedFamily, hiLast, if_false, Set.mem_union] at hxi
    exact hxi.elim hxNotSquare hxNotTags


lemma nestedFamily_manyObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction
      (nestedFamily r hr) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hValid
  let zero : Fin r := ⟨0, by omega⟩
  have hValidZero := hValid zero
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hValidZero] with ω hω
    rw [nestedFamily_zero hr] at hω
    exact path_density_univ_zero hω
  refine ⟨lastFin r hr, ?_⟩
  rw [nestedFamily_last hr]
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae hzero]
  simp

lemma manyWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r hr) commonInput := by
  refine ⟨nestedFamily_strict hr, ?_,
    globallyFeasible_of_square_subset (nestedFamily r hr)
      (square_subset_nestedFamily hr), nestedFamily_manyObstruction hr⟩
  intro j
  exact legal_commonInput (square_subset_nestedFamily hr j)

lemma manyClaim : ∀ r : ℕ, 2 ≤ r →
    ∃ family : Fin r → Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      Stage3Case024.ManyTargetWitness family input := by
  intro r hr
  exact ⟨nestedFamily r hr, commonInput, manyWitness hr⟩

end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  exact ⟨Case024.pairClaim, Case024.manyClaim⟩
