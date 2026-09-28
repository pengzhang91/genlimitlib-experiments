import «output».Case025Core

open Filter
open scoped Topology
open GenLimit

namespace Case025Helpers

private theorem prefixCount_le_add_of_diff_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    PatientScope.prefixCount A n ≤
      PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold PatientScope.prefixCount PatientScope.prefixFinset
  calc
    ((Finset.range n).filter fun x => x ∈ A).card ≤
        (((Finset.range n).filter fun x => x ∈ B) ∪ hfinite.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      by_cases hxB : x ∈ B
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx.1, hxB⟩)
      · exact Finset.mem_union_right _
          (Set.Finite.mem_toFinset hfinite |>.mpr ⟨hx.2, hxB⟩)
    _ ≤ ((Finset.range n).filter fun x => x ∈ B).card + hfinite.toFinset.card := by
      apply Finset.card_union_le

private theorem ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    (0 : ℝ) ≤ (PatientScope.prefixCount A n : ℝ) /
      (PatientScope.prefixCount K n : ℝ) :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (PatientScope.prefixCount A n : ℝ) /
        (PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : PatientScope.prefixCount K n = 0
  · simp [hzero]
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
    exact_mod_cast PatientScope.prefixCount_mono hAK n

 theorem relativeLowerDensity_finite_extension
    (A K E : Set ℕ) (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite)
    (hhalf : (1 / 2 : ℝ) ≤ PatientScope.relativeLowerDensity (A ∩ E) E) :
    (1 / 2 : ℝ) ≤ PatientScope.relativeLowerDensity (A ∩ K) K := by
  unfold PatientScope.relativeLowerDensity at hhalf ⊢
  have hnumFinite : ((A ∩ E) \ (A ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  let c : ℕ := hnumFinite.toFinset.card
  let ratioE : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (A ∩ E) n : ℝ) /
      (PatientScope.prefixCount E n : ℝ)
  let ratioK : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  let err : ℕ → ℝ := fun n =>
    (c : ℝ) / (PatientScope.prefixCount K n : ℝ)
  have hcompare : ∀ᶠ n : ℕ in atTop, ratioE n ≤ err n + ratioK n := by
    have hpositive : ∀ᶠ n : ℕ in atTop, 0 < PatientScope.prefixCount K n :=
      (PatientScope.tendsto_prefixCount_atTop hK).eventually (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < PatientScope.prefixCount K n := by exact_mod_cast hn
    have hnum := prefixCount_le_add_of_diff_finite hnumFinite n
    have hden := PatientScope.prefixCount_mono hKE n
    have hnumR :
        (PatientScope.prefixCount (A ∩ E) n : ℝ) ≤
          (PatientScope.prefixCount (A ∩ K) n : ℝ) + c := by
      simpa [c] using (show
        (PatientScope.prefixCount (A ∩ E) n : ℝ) ≤
          (PatientScope.prefixCount (A ∩ K) n + hnumFinite.toFinset.card : ℕ) by
            exact_mod_cast hnum)
    have hdenR :
        (PatientScope.prefixCount K n : ℝ) ≤
          (PatientScope.prefixCount E n : ℝ) := by
      exact_mod_cast hden
    dsimp only [ratioE, ratioK, err]
    have hEpos : (0 : ℝ) < PatientScope.prefixCount E n := lt_of_lt_of_le hnR hdenR
    calc
      (PatientScope.prefixCount (A ∩ E) n : ℝ) /
          (PatientScope.prefixCount E n : ℝ) ≤
        ((PatientScope.prefixCount (A ∩ K) n : ℝ) + c) /
          (PatientScope.prefixCount E n : ℝ) :=
            (div_le_div_iff_of_pos_right hEpos).2 hnumR
      _ ≤ ((PatientScope.prefixCount (A ∩ K) n : ℝ) + c) /
          (PatientScope.prefixCount K n : ℝ) := by
            apply div_le_div_of_nonneg_left
            · positivity
            · exact hnR
            · exact hdenR
      _ = (c : ℝ) / (PatientScope.prefixCount K n : ℝ) +
          (PatientScope.prefixCount (A ∩ K) n : ℝ) /
            (PatientScope.prefixCount K n : ℝ) := by ring
  have herr : Tendsto err atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp
        (PatientScope.tendsto_prefixCount_atTop hK))
  have hratioE_lower : IsBoundedUnder (· ≥ ·) atTop ratioE := by
    refine ⟨(0 : ℝ), ?_⟩
    change ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ ratioE n
    exact Eventually.of_forall fun n => ratio_nonneg _ _ n
  have hratioK_lower : IsBoundedUnder (· ≥ ·) atTop ratioK := by
    refine ⟨(0 : ℝ), ?_⟩
    change ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ ratioK n
    exact Eventually.of_forall fun n => ratio_nonneg _ _ n
  have hratioK_upper : IsBoundedUnder (· ≤ ·) atTop ratioK := by
    refine ⟨(1 : ℝ), ?_⟩
    change ∀ᶠ n : ℕ in atTop, ratioK n ≤ (1 : ℝ)
    exact Eventually.of_forall fun n => ratio_le_one Set.inter_subset_right n
  have herr_lower : IsBoundedUnder (· ≥ ·) atTop err := by
    refine ⟨(0 : ℝ), ?_⟩
    change ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ err n
    exact Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have herr_upper : IsBoundedUnder (· ≤ ·) atTop err := by
    refine ⟨(c : ℝ), ?_⟩
    change ∀ᶠ n : ℕ in atTop, err n ≤ (c : ℝ)
    filter_upwards [] with n
    dsimp only [err]
    by_cases hz : PatientScope.prefixCount K n = 0
    · simp [hz]
    · have hden : (1 : ℝ) ≤ PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
      calc
        (c : ℝ) / (PatientScope.prefixCount K n : ℝ) ≤ (c : ℝ) / 1 :=
          div_le_div_of_nonneg_left hc (by norm_num) hden
        _ = c := by simp
  have hsum_upper : IsCoboundedUnder (· ≥ ·) atTop (err + ratioK) :=
    isCoboundedUnder_ge_of_le atTop fun (n : ℕ) => by
      change err n + ratioK n ≤ (c : ℝ) + 1
      apply add_le_add
      · dsimp only [err]
        by_cases hz : PatientScope.prefixCount K n = 0
        · simp [hz]
        · have hden : (1 : ℝ) ≤ PatientScope.prefixCount K n := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
          have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
          calc
            (c : ℝ) / (PatientScope.prefixCount K n : ℝ) ≤ (c : ℝ) / 1 :=
              div_le_div_of_nonneg_left hc (by norm_num) hden
            _ = c := by simp
      · exact ratio_le_one Set.inter_subset_right n
  have hlimCompare : liminf ratioE atTop ≤ liminf (err + ratioK) atTop :=
    liminf_le_liminf hcompare hratioE_lower hsum_upper
  have hadd : liminf (err + ratioK) atTop ≤ limsup err atTop + liminf ratioK atTop :=
    liminf_add_le herr_lower herr_upper hratioK_lower hratioK_upper.isCoboundedUnder_ge
  have herrLimsup : limsup err atTop = 0 := herr.limsup_eq
  change (1 / 2 : ℝ) ≤ liminf ratioK atTop
  have hhalf' : (1 / 2 : ℝ) ≤ liminf ratioE atTop := by exact hhalf
  linarith

end Case025Helpers
