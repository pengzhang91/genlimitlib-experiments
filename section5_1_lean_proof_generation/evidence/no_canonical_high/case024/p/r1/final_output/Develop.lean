import Helpers

open Filter MeasureTheory
open scoped Topology

namespace Case024

lemma generatorFirst_subset_squares_union_finset
    {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output squares) :
    ∃ F : Finset ℕ,
      GenLimit.GeneratorFirst input output ⊆ squares ∪ (F : Set ℕ) := by
  rcases h with ⟨T, hT⟩
  refine ⟨(Finset.range T).image output, ?_⟩
  intro x hx
  rcases hx with ⟨t, rfl, _⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht).1
  · refine Or.inr (Finset.mem_image.mpr ?_)
    exact ⟨t, Finset.mem_range.mpr (Nat.lt_of_not_ge ht), rfl⟩

lemma relativeUpperDensity_generatorFirst_univ_eq_zero
    {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output squares) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  rcases generatorFirst_subset_squares_union_finset h with ⟨F, hF⟩
  exact relativeUpperDensity_univ_eq_zero_of_subset_finset hF

lemma pairObstruction_squares_univ :
    Stage3Case024.PairObstruction squares Set.univ swapStream := by
  intro Ω _ μ _ gen output hfollow hmeas hint0 hint1 hvalid0 hvalid1
  have hzero_ae : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst swapStream (output ω)) Set.univ = 0 := by
    filter_upwards [hvalid0] with ω hω
    exact relativeUpperDensity_generatorFirst_univ_eq_zero hω
  have hzero : Stage3Case024.expectedUpperDensity μ Set.univ swapStream output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [MeasureTheory.integral_congr_ae hzero_ae]
    simp
  have hle : Stage3Case024.expectedUpperDensity μ squares swapStream output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    have hpoint : ∀ᵐ ω ∂μ,
        Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst swapStream (output ω)) squares ≤ (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
    have honeint : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    calc
      ∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst swapStream (output ω)) squares ∂μ
          ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := MeasureTheory.integral_mono_ae hint0 honeint hpoint
      _ = 1 := by simp
  constructor
  · rw [hzero, add_zero]
    exact hle
  · rw [hzero]
    intro h
    linarith [h.2]

end Case024

namespace Case024

noncomputable def freshSquare (F : Finset ℕ) : ℕ :=
  Classical.choose (squares_infinite.exists_not_mem_finset F)

lemma freshSquare_mem (F : Finset ℕ) : freshSquare F ∈ squares :=
  (Classical.choose_spec (squares_infinite.exists_not_mem_finset F)).1

lemma freshSquare_not_mem (F : Finset ℕ) : freshSquare F ∉ F :=
  (Classical.choose_spec (squares_infinite.exists_not_mem_finset F)).2

noncomputable def squareGenerator : Stage3Case024.OnlineGenerator :=
  fun _ input prior =>
    freshSquare ((Finset.univ.image input) ∪ (Finset.univ.image prior))

noncomputable def squareOutput (input : Stream) (t : ℕ) : ℕ :=
  squareGenerator t (fun i => input i) (fun i => squareOutput input i)
termination_by t

theorem squareOutput_follows (input : Stream) :
    Stage3Case024.Follows squareGenerator input (squareOutput input) := by
  intro t
  exact squareOutput.eq_1 input t

lemma image_fin_input_eq_sample (input : Stream) (t : ℕ) :
    Finset.univ.image (fun i : Fin t => input i) = GenLimit.sample input t := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
    exact Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, hi⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, hax⟩
    exact Finset.mem_image.mpr ⟨⟨a, Finset.mem_range.mp ha⟩, Finset.mem_univ _, hax⟩

lemma squareOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) squares := by
  refine ⟨0, fun t _ => ?_⟩
  rw [squareOutput.eq_1 input t]
  let F := (Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
    (Finset.univ.image (fun i : Fin t => squareOutput input i))
  have hm : freshSquare F ∈ squares := freshSquare_mem F
  have hn : freshSquare F ∉ F := freshSquare_not_mem F
  change freshSquare F ∈ squares ∧
    freshSquare F ∉ GenLimit.sample input (t + 1) ∧
    ∀ s < t, squareOutput input s ≠ freshSquare F
  refine ⟨hm, ?_, ?_⟩
  · intro hx
    apply hn
    apply Finset.mem_union_left
    rw [image_fin_input_eq_sample]
    exact hx
  · intro s hs heq
    apply hn
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, heq⟩

end Case024

namespace Case024

def marker (k : ℕ) : ℕ := k * k + 3 * k + 2

def markerPrefix (i : ℕ) : Language := {n | ∃ k, k < i ∧ n = marker k}

lemma marker_injective : Function.Injective marker := by
  intro a b h
  dsimp [marker] at h
  nlinarith

lemma marker_not_square (k : ℕ) : marker k ∉ squares :=
  between_not_square k

lemma marker_mem_prefix {i j : ℕ} (hij : i < j) : marker i ∈ markerPrefix j := by
  exact ⟨i, hij, rfl⟩

lemma marker_not_mem_prefix (i : ℕ) : marker i ∉ markerPrefix i := by
  rintro ⟨k, hk, heq⟩
  have := marker_injective heq.symm
  omega

def nestedFamily {r : ℕ} (i : Fin r) : Language :=
  if i.val + 1 = r then Set.univ else squares ∪ markerPrefix i.val

lemma squares_subset_nestedFamily {r : ℕ} (i : Fin r) :
    squares ⊆ nestedFamily i := by
  intro x hx
  unfold nestedFamily
  split_ifs
  · trivial
  · exact Or.inl hx

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily (⟨0, by omega⟩ : Fin r) = squares := by
  change (if 0 + 1 = r then Set.univ else squares ∪ markerPrefix 0) = squares
  rw [if_neg (by omega)]
  ext x
  simp [markerPrefix]

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily (⟨r - 1, by omega⟩ : Fin r) = Set.univ := by
  simp [nestedFamily]
  omega

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily (r := r)) := by
  intro i j hij
  have hi : i.val + 1 ≠ r := by omega
  have hsub : nestedFamily i ⊆ nestedFamily j := by
    intro x hx
    unfold nestedFamily at hx ⊢
    split_ifs with hj
    · trivial
    · rw [if_neg hi] at hx
      rcases hx with hs | hm
      · exact Or.inl hs
      · exact Or.inr (by
          rcases hm with ⟨k, hk, rfl⟩
          exact ⟨k, lt_trans hk hij, rfl⟩)
  rw [Set.ssubset_iff_exists]
  refine ⟨hsub, marker i.val, ?_, ?_⟩
  · unfold nestedFamily
    split_ifs
    · trivial
    · exact Or.inr (marker_mem_prefix hij)
  · unfold nestedFamily
    rw [if_neg hi]
    intro hm
    rcases hm with hs | hp
    · exact marker_not_square i.val hs
    · exact marker_not_mem_prefix i.val hp

lemma novel_mono {input output : Stream} {K : Language}
    (h : GenLimit.NovelGeneratesInLimit input output squares)
    (hsub : squares ⊆ K) :
    GenLimit.NovelGeneratesInLimit input output K := by
  rcases h with ⟨T, hT⟩
  refine ⟨T, fun t ht => ?_⟩
  rcases hT t ht with ⟨hmem, hfresh, hnovel⟩
  exact ⟨hsub hmem, hfresh, hnovel⟩

lemma nestedFamily_globallyFeasible {r : ℕ} :
    Stage3Case024.GloballyFeasible (nestedFamily (r := r)) := by
  refine ⟨squareGenerator, fun input _ => ⟨squareOutput input, squareOutput_follows input, ?_⟩⟩
  intro j
  exact novel_mono (squareOutput_novel input) (squares_subset_nestedFamily j)

lemma nestedFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily (r := r)) swapStream := by
  intro Ω _ μ _ gen output hfollow hmeas hint hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hsq : ∀ᵐ ω ∂μ,
      GenLimit.NovelGeneratesInLimit swapStream (output ω) squares := by
    have hv := hvalid first
    filter_upwards [hv] with ω hω
    simpa [first, nestedFamily_zero hr] using hω
  have hzero_ae : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst swapStream (output ω)) Set.univ = 0 := by
    filter_upwards [hsq] with ω hω
    exact relativeUpperDensity_generatorFirst_univ_eq_zero hω
  refine ⟨last, ?_⟩
  unfold Stage3Case024.expectedUpperDensity
  rw [nestedFamily_last hr]
  rw [MeasureTheory.integral_congr_ae hzero_ae]
  simp

lemma nestedFamily_legal {r : ℕ} (j : Fin r) :
    Stage3Case024.Legal swapStream (nestedFamily j) :=
  legal_swapStream_of_superset (squares_subset_nestedFamily j)

end Case024
