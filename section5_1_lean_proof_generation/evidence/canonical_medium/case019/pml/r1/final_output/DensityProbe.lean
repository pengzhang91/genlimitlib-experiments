import GenLimit.Paper39_DenseGeneration.Patient.Main

open Filter
open scoped Topology

namespace GenLimit.PatientScope

private theorem liminf_le_liminf_of_le_add_vanishing
    (f g e : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1)
    (hg0 : ∀ n, 0 ≤ g n) (hg1 : ∀ n, g n ≤ 1)
    (he : Tendsto e atTop (nhds 0))
    (hfg : ∀ᶠ n in atTop, f n ≤ g n + e n) :
    liminf f atTop ≤ liminf g atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop hg1)
    (isBoundedUnder_of ⟨0, hg0⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrf⟩ := exists_between hy
  have hfr : ∀ᶠ n in atTop, r < f n :=
    eventually_lt_of_lt_liminf hrf (isBoundedUnder_of ⟨0, hf0⟩)
  have her : ∀ᶠ n in atTop, e n < r - y := by
    exact he.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hfr, her, hfg] with n hn heN hle
  linarith

private theorem prefixCount_inter_le_add_diff
    (A K E : Set ℕ) (hfinite : (E \ K).Finite) (n : ℕ) :
    prefixCount (A ∩ E) n ≤
      prefixCount (A ∩ K) n + hfinite.toFinset.card := by
  classical
  unfold prefixCount
  let left := (Finset.range n).filter fun x => x ∈ A ∩ E
  let core := (Finset.range n).filter fun x => x ∈ A ∩ K
  let bad := (Finset.range n).filter fun x => x ∈ E \ K
  have hsub : left ⊆ core ∪ bad := by
    intro x hx
    simp only [left, core, bad, Finset.mem_filter, Finset.mem_union,
      Set.mem_inter_iff, Set.mem_diff] at hx ⊢
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx.1, hx.2.1, hxK⟩
    · exact Or.inr ⟨hx.1, hx.2.2, hxK⟩
  have hbad : bad.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Set.Finite.mem_toFinset]
    exact (Finset.mem_filter.mp hx).2
  simpa [left, core, prefixCount, prefixFinset] using (show
    left.card ≤ core.card + hfinite.toFinset.card from by
      calc
        left.card ≤ (core ∪ bad).card := Finset.card_le_card hsub
        _ ≤ core.card + bad.card := Finset.card_union_le _ _
        _ ≤ core.card + hfinite.toFinset.card := Nat.add_le_add_left hbad _)

private theorem relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (prefixCount A n : ℝ) / (prefixCount K n : ℝ) := by positivity

private theorem relativeRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : prefixCount K n = 0
  · simp [hzero]
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
    exact_mod_cast prefixCount_mono hAK n

 theorem relativeLowerDensity_transfer_finite_expansion
    {A K E : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    relativeLowerDensity (A ∩ E) E ≤
      relativeLowerDensity (A ∩ K) K := by
  unfold relativeLowerDensity
  let C : ℝ := hfinite.toFinset.card
  let error : ℕ → ℝ := fun n => C / (prefixCount K n : ℝ)
  have hcountT : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_prefixCount_atTop hK)
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcountT
  apply liminf_le_liminf_of_le_add_vanishing
    (fun n => (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ))
    (fun n => (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ))
    error
  · exact relativeRatio_nonneg _ _
  · exact relativeRatio_le_one Set.inter_subset_right
  · exact relativeRatio_nonneg _ _
  · exact relativeRatio_le_one Set.inter_subset_right
  · exact herror
  · filter_upwards [tendsto_prefixCount_atTop hK |>.eventually (eventually_gt_atTop 0)] with n hn
    have hkpos : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hden : (prefixCount K n : ℝ) ≤ prefixCount E n := by
      exact_mod_cast prefixCount_mono hKE n
    have hnum : (prefixCount (A ∩ E) n : ℝ) ≤
        prefixCount (A ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast prefixCount_inter_le_add_diff A K E hfinite n
    dsimp [error, C]
    calc
      (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ)
          ≤ (prefixCount (A ∩ E) n : ℝ) / (prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_left (by positivity) hkpos hden
      _ ≤ ((prefixCount (A ∩ K) n : ℝ) + hfinite.toFinset.card) /
            (prefixCount K n : ℝ) := div_le_div_of_nonneg_right hnum hkpos.le
      _ = (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ) +
            (hfinite.toFinset.card : ℝ) / (prefixCount K n : ℝ) := by rw [add_div]

end GenLimit.PatientScope
