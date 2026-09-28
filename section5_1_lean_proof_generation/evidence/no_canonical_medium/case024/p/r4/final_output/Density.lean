import «output».Construction

open Filter MeasureTheory
open scoped Topology

namespace Case024

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma relativeUpperDensity_le_one (A K : Set ℕ) (hK : K.Infinite) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) :=
    isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  apply limsup_le_of_le hcob
  rcases hK.exists_gt 0 with ⟨x, hxK, hxpos⟩
  filter_upwards [eventually_ge_atTop (x + 1)] with n hn
  have hden : 0 < GenLimit.PatientScope.prefixCount K n := by
    unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
    rw [Finset.card_pos]
    exact ⟨x, by simp [hxK, lt_of_lt_of_le (Nat.lt_succ_self x) hn]⟩
  apply (div_le_one (by exact_mod_cast hden)).2
  exact_mod_cast prefixCount_mono (Set.inter_subset_right) n

lemma generatorFirst_subset_of_novel {input output : ℕ → ℕ} {K : Set ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output K) :
    ∃ T, GenLimit.GeneratorFirst input output ⊆
      K ∪ (↑((Finset.range T).image output) : Set ℕ) := by
  rcases h with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro z hz
  rcases hz with ⟨t, rfl, _⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht).1
  · exact Or.inr (by
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨t, Nat.lt_of_not_ge ht, rfl⟩)

lemma prefixCount_generatorFirst_le {input output : ℕ → ℕ} {K : Set ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output K) :
    ∃ T, ∀ n,
      GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n ≤
        GenLimit.PatientScope.prefixCount K n + T := by
  rcases generatorFirst_subset_of_novel h with ⟨T, hsub⟩
  refine ⟨T, fun n => ?_⟩
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  calc
    ((Finset.range n).filter fun x => x ∈ GenLimit.GeneratorFirst input output).card ≤
        (((Finset.range n).filter fun x => x ∈ K) ∪ (Finset.range T).image output).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      rcases hsub hx.2 with hxK | hxE
      · simp [hx.1, hxK]
      · simp only [Finset.mem_union]
        exact Or.inr hxE
    _ ≤ ((Finset.range n).filter fun x => x ∈ K).card + ((Finset.range T).image output).card :=
      Finset.card_union_le _ _
    _ ≤ ((Finset.range n).filter fun x => x ∈ K).card + T := by
      gcongr
      exact Finset.card_image_le.trans_eq (Finset.card_range T)

lemma tendsto_generatorFirst_univ_ratio_zero {input output : ℕ → ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output squares) :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n : ℝ) /
        (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ)) atTop (𝓝 0) := by
  rcases prefixCount_generatorFirst_le h with ⟨T, hT⟩
  simp_rw [prefixCount_univ]
  have hTzero : Tendsto (fun n : ℕ => (T : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (T : ℝ) * (1 / (n : ℝ))) atTop (𝓝 ((T : ℝ) * 0)))
  apply squeeze_zero
  · intro n; positivity
  · intro n
    have hc : (GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount squares n : ℝ) + T := by
      exact_mod_cast hT n
    exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)
  · simpa [add_div] using tendsto_square_prefix_ratio_zero.add hTzero

lemma relativeUpperDensity_univ_eq_zero {input output : ℕ → ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output squares) :
    Stage3Case024.relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  simpa only [Set.inter_univ] using (tendsto_generatorFirst_univ_ratio_zero h).limsup_eq

end Case024
