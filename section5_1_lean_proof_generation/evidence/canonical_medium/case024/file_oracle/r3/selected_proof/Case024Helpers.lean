import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open GenLimit
open GenLimit.InfiniteContamination

abbrev Squares : Set ℕ := {n | SparseSquare n}

theorem squares_infinite : Squares.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => k * k) := by
    intro a b hab
    nlinarith
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨k, rfl⟩
  exact sparseSquare_mul_self k

theorem prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    PatientScope.prefixCount A n ≤ PatientScope.prefixCount B n := by
  classical
  unfold PatientScope.prefixCount PatientScope.prefixFinset
  exact Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, h hx.2⟩)

@[simp] theorem prefixCount_univ (n : ℕ) :
    PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  classical
  simp [PatientScope.prefixCount, PatientScope.prefixFinset]

theorem prefixCount_le_add_finite_diff {A B : Set ℕ}
    (hfinite : (A \ B).Finite) (n : ℕ) :
    PatientScope.prefixCount A n ≤
      PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let a := PatientScope.prefixFinset A n
  let b := PatientScope.prefixFinset B n
  let d := PatientScope.prefixFinset (A \ B) n
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    have hx' := PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ (PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _
        (PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hd : d.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2
      (PatientScope.mem_prefixFinset.mp hx).2
  calc
    PatientScope.prefixCount A n = a.card := rfl
    _ ≤ (b ∪ d).card := Finset.card_le_card hsub
    _ ≤ b.card + d.card := Finset.card_union_le _ _
    _ ≤ b.card + hfinite.toFinset.card := Nat.add_le_add_left hd _
    _ = PatientScope.prefixCount B n + hfinite.toFinset.card := rfl

theorem prefixCount_squares_le (n : ℕ) :
    PatientScope.prefixCount Squares n ≤ Nat.sqrt n + 1 := by
  classical
  simpa [PatientScope.prefixCount, PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range] using count_sparseSquare_le_sqrt_add_one n

theorem tendsto_square_ratio :
    Tendsto (fun n : ℕ =>
      (PatientScope.prefixCount Squares n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    apply div_le_div_of_nonneg_right
    · have h : (PatientScope.prefixCount Squares n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
        exact_mod_cast prefixCount_squares_le n
      exact h
    · positivity
  · exact tendsto_sparseSqrt_add_one_div

theorem finite_output_off_squares {input output : ℕ → ℕ}
    (h : NovelGeneratesInLimit input output Squares) :
    (Set.range output \ Squares).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Finset.finite_toSet (Finset.range T |>.image output)).subset
  intro x hx
  obtain ⟨t, rfl⟩ := hx.1
  have ht : t < T := by
    by_contra hnot
    exact hx.2 (hT t (Nat.le_of_not_gt hnot)).1
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  exact ⟨t, ht, rfl⟩

theorem generatorFirst_subset_range (input output : ℕ → ℕ) :
    GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, ht, -⟩
  exact ⟨t, ht⟩

theorem generatorFirst_off_squares_finite {input output : ℕ → ℕ}
    (h : NovelGeneratesInLimit input output Squares) :
    (GeneratorFirst input output \ Squares).Finite := by
  exact (finite_output_off_squares h).subset (Set.diff_subset_diff_left
    (generatorFirst_subset_range input output))

theorem tendsto_generatorFirst_univ_ratio {input output : ℕ → ℕ}
    (h : NovelGeneratesInLimit input output Squares) :
    Tendsto (fun n : ℕ =>
      (PatientScope.prefixCount (GeneratorFirst input output) n : ℝ) /
        (n : ℝ)) atTop (𝓝 0) := by
  let bad := generatorFirst_off_squares_finite h
  let B := bad.toFinset.card
  have hbound : ∀ n : ℕ,
      (PatientScope.prefixCount (GeneratorFirst input output) n : ℝ) / (n : ℝ) ≤
        (PatientScope.prefixCount Squares n : ℝ) / (n : ℝ) + (B : ℝ) / (n : ℝ) := by
    intro n
    rw [← add_div]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_le_add_finite_diff bad n
    · positivity
  apply squeeze_zero
  · intro n
    positivity
  · exact hbound
  · simpa using tendsto_square_ratio.add
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (B : ℝ) / (n : ℝ)) atTop (𝓝 0))

theorem relativeUpperDensity_univ_eq_zero {input output : ℕ → ℕ}
    (h : NovelGeneratesInLimit input output Squares) :
    Stage3Case024.relativeUpperDensity (GeneratorFirst input output) Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  simp only [Set.inter_univ, prefixCount_univ]
  exact (tendsto_generatorFirst_univ_ratio h).limsup_eq
theorem relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  let u := fun n : ℕ =>
    (PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  have hu0 : ∀ n, 0 ≤ u n := fun n => by positivity
  have hu1 : ∀ n, u n ≤ 1 := fun n => by
    by_cases hz : PatientScope.prefixCount K n = 0
    · simp [u, hz]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall hu0
  · change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, u n ≤ b
    exact ⟨1, Eventually.of_forall hu1⟩

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  let u := fun n : ℕ =>
    (PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  have hu0 : ∀ n, 0 ≤ u n := fun n => by positivity
  have hu1 : ∀ n, u n ≤ 1 := fun n => by
    by_cases hz : PatientScope.prefixCount K n = 0
    · simp [u, hz]
    · apply (div_le_one (by positivity)).2
      have hn : PatientScope.prefixCount (A ∩ K) n ≤ PatientScope.prefixCount K n :=
        prefixCount_mono (A := A ∩ K) (B := K) Set.inter_subset_right n
      exact_mod_cast hn
  have hc : IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop u := by
    change ∃ b : ℝ, ∀ a : ℝ, (∀ᶠ n : ℕ in atTop, u n ≤ a) → b ≤ a
    refine ⟨0, ?_⟩
    intro a ha
    obtain ⟨n, hna, hn0⟩ := (ha.and (Eventually.of_forall hu0)).exists
    exact hn0.trans hna
  have hb : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop (fun _ : ℕ => (1 : ℝ)) := by
    change ∃ b : ℝ, ∀ᶠ _ : ℕ in atTop, (1 : ℝ) ≤ b
    exact ⟨1, Eventually.of_forall fun _ => le_rfl⟩
  calc
    limsup u atTop ≤ limsup (fun _ : ℕ => (1 : ℝ)) atTop :=
      limsup_le_limsup (Eventually.of_forall hu1) hc hb
    _ = 1 := by simpa using (limsup_const (f := atTop) (1 : ℝ))



noncomputable def freshSquare (t : ℕ) (input : Fin (t + 1) → ℕ)
    (output : Fin t → ℕ) : ℕ :=
  Classical.choose (squares_infinite.exists_not_mem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image output)))

theorem freshSquare_spec (t : ℕ) (input : Fin (t + 1) → ℕ)
    (output : Fin t → ℕ) :
    freshSquare t input output ∈ Squares ∧
      freshSquare t input output ∉ Finset.univ.image input ∧
      freshSquare t input output ∉ Finset.univ.image output := by
  have h := Classical.choose_spec (squares_infinite.exists_not_mem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image output)))
  exact ⟨h.1, fun hm => h.2 (Finset.mem_union_left _ hm),
    fun hm => h.2 (Finset.mem_union_right _ hm)⟩

noncomputable def squareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input output => freshSquare t input output

noncomputable def runGenerator (gen : Stage3Case024.OnlineGenerator)
    (input : Stage3Case024.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => runGenerator gen input i)
termination_by t
decreasing_by omega

theorem runGenerator_follows (gen : Stage3Case024.OnlineGenerator)
    (input : Stage3Case024.Stream) :
    Stage3Case024.Follows gen input (runGenerator gen input) := by
  intro t
  rw [runGenerator]

theorem squareGenerator_novel (input output : Stage3Case024.Stream)
    (hfollow : Stage3Case024.Follows squareGenerator input output) :
    NovelGeneratesInLimit input output Squares := by
  refine ⟨0, ?_⟩
  intro t _
  rw [hfollow t]
  have hs := freshSquare_spec t (fun i => input i) (fun i => output i)
  refine ⟨hs.1, ?_, ?_⟩
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hst, hsval⟩ := hmem
    apply hs.2.1
    apply Finset.mem_image.mpr
    exact ⟨⟨s, by omega⟩, Finset.mem_univ _, hsval⟩
  · intro s hst heq
    apply hs.2.2
    apply Finset.mem_image.mpr
    exact ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩

end Stage3Case024Proof
