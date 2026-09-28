import Helpers

open Filter MeasureTheory
open scoped Topology

namespace Case024

noncomputable section
open Classical

lemma prefixCount_univ (n : ℕ) : GenLimit.PatientScope.prefixCount Set.univ n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_squares (n : ℕ) :
    GenLimit.PatientScope.prefixCount Squares n = Nat.count (fun x => x ∈ Squares) n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range]

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma density_le_one (A K : Set ℕ) : Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  let u := fun n : ℕ =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hnonneg : ∀ n, (0 : ℝ) ≤ u n := fun n => by positivity
  have hone : ∀ n, u n ≤ 1 := by
    intro n
    have hc := prefixCount_mono (A := A ∩ K) (B := K) (Set.inter_subset_right) n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [u, hz]
    · have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast Nat.pos_of_ne_zero hz
      change (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        GenLimit.PatientScope.prefixCount K n ≤ 1
      rw [div_le_one hp]
      exact_mod_cast hc
  apply (Filter.limsup_le_iff
    (isCoboundedUnder_le_of_le atTop hnonneg)
    (show IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop u from by
      change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, u n ≤ b
      exact ⟨1, Filter.Eventually.of_forall hone⟩)).2
  intro y hy
  filter_upwards with n
  exact (hone n).trans_lt hy

lemma generatorFirst_subset_range (stream output : ℕ → ℕ) :
    GenLimit.GeneratorFirst stream output ⊆ Set.range output := by
  rintro x ⟨t, ht, _⟩
  exact ⟨t, ht⟩

lemma prefix_generatorFirst_le (stream output : ℕ → ℕ)
    (T : ℕ) (hvalid : ∀ t, T ≤ t → output t ∈ Squares) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst stream output) n ≤
      Nat.count (fun x => x ∈ Squares) n + T := by
  classical
  let left := GenLimit.PatientScope.prefixFinset (GenLimit.GeneratorFirst stream output) n
  let right := ((Finset.range n).filter fun x => x ∈ Squares) ∪
    (Finset.range T).image output
  have hsub : left ⊆ right := by
    intro x hx
    simp only [left, GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range] at hx
    by_cases hs : x ∈ Squares
    · simp [right, hx.1, hs]
    · obtain ⟨t, ht⟩ := generatorFirst_subset_range stream output hx.2
      have htT : t < T := by
        by_contra hnot
        exact hs (ht ▸ hvalid t (Nat.le_of_not_gt hnot))
      apply Finset.mem_union_right
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨t, htT, ht⟩
  unfold GenLimit.PatientScope.prefixCount
  calc
    left.card ≤ right.card := Finset.card_le_card hsub
    _ ≤ ((Finset.range n).filter fun x => x ∈ Squares).card +
        ((Finset.range T).image output).card := Finset.card_union_le _ _
    _ ≤ Nat.count (fun x => x ∈ Squares) n + T := by
      rw [← Nat.count_eq_card_filter_range]
      gcongr
      simpa using Finset.card_image_le (s := Finset.range T) (f := output)

lemma eventual_sparse_density_zero (stream output : ℕ → ℕ)
    (h : GenLimit.NovelGeneratesInLimit stream output Squares) :
    Stage3Case024.relativeUpperDensity (GenLimit.GeneratorFirst stream output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := h
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  have hbound : ∀ n, GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst stream output ∩ Set.univ) n ≤
      Nat.count (fun x => x ∈ Squares) n + T := by
    intro n
    simpa using prefix_generatorFirst_le stream output T (fun t ht => (hT t ht).1) n
  have hTdiv : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) _
    (by simpa using tendsto_count_squares_div.add hTdiv)
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [prefixCount_univ, ← add_div]
  gcongr
  exact_mod_cast hbound n

lemma expected_univ_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (stream : ℕ → ℕ) (output : Ω → ℕ → ℕ)
    (h : Stage3Case024.EventuallyFreshValid μ Squares stream output) :
    Stage3Case024.expectedUpperDensity μ Set.univ stream output = 0 := by
  unfold Stage3Case024.EventuallyFreshValid at h
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae (h.mono fun ω hω => eventual_sparse_density_zero stream (output ω) hω)]
  exact integral_zero Ω ℝ

lemma expected_le_one {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : Set ℕ) (stream : ℕ → ℕ) (output : Ω → ℕ → ℕ)
    (hint : Stage3Case024.DensityIntegrable μ K stream output) :
    Stage3Case024.expectedUpperDensity μ K stream output ≤ 1 := by
  unfold Stage3Case024.DensityIntegrable at hint
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst stream (output ω)) K ∂μ) ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
        apply integral_mono hint (integrable_const 1)
        intro ω
        exact density_le_one _ _
    _ = 1 := by simp

end
end Case024
