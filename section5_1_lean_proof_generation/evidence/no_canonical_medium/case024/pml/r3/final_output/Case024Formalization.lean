import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import GenLimit.Support.Fresh

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof

open Stage3Case024
open GenLimit.InfiniteContamination

noncomputable section

local instance : DecidablePred SparseSquare := Classical.decPred _

def core : Set ℕ := {n | SparseSquare n}

theorem core_infinite : core.Infinite := by
  apply (Set.infinite_range_of_injective (fun a b h => by nlinarith :
    Function.Injective (fun n : ℕ => n * n))).mono
  rintro _ ⟨n, rfl⟩
  exact sparseSquare_mul_self n

def marker (n : ℕ) : ℕ := sparseBetweenSquares n

theorem marker_injective : Function.Injective marker :=
  sparseBetweenSquares_strictMono.injective

theorem marker_not_core (n : ℕ) : marker n ∉ core :=
  sparseBetweenSquares_nonsquare n

def initialMarkers (i : ℕ) : Set ℕ := marker '' Set.Iio i

def familySet (r i : ℕ) : Set ℕ :=
  if i + 1 = r then Set.univ else core ∪ initialMarkers i

def family (r : ℕ) : Fin r → Language := fun i => familySet r i

theorem core_subset_familySet (r i : ℕ) : core ⊆ familySet r i := by
  intro x hx
  simp only [familySet]
  split <;> simp_all

theorem familySet_subset_univ (r i : ℕ) : familySet r i ⊆ Set.univ :=
  Set.subset_univ _

theorem marker_mem_initialMarkers {i n : ℕ} (h : n < i) :
    marker n ∈ initialMarkers i := by
  exact ⟨n, h, rfl⟩

theorem initialMarkers_mono {i j : ℕ} (hij : i ≤ j) :
    initialMarkers i ⊆ initialMarkers j := by
  rintro x ⟨n, hn, rfl⟩
  exact ⟨n, lt_of_lt_of_le hn hij, rfl⟩

theorem marker_not_initialMarkers_self (i : ℕ) :
    marker i ∉ initialMarkers i := by
  rintro ⟨n, hn, hni⟩
  have hni' : n = i := marker_injective hni
  subst i
  exact Nat.lt_irrefl n hn

theorem family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (family r) := by
  intro i j hij
  have hilast : (i : ℕ) + 1 ≠ r := by omega
  by_cases hjlast : (j : ℕ) + 1 = r
  · constructor
    · rw [show family r j = Set.univ by simp [family, familySet, hjlast]]
      exact Set.subset_univ _
    · intro hreverse
      have hmemj : marker (i : ℕ) ∈ family r j := by
        simp [family, familySet, hjlast]
      have hnoti : marker (i : ℕ) ∉ family r i := by
        simp only [family, familySet, hilast, if_false, Set.mem_union]
        intro h
        rcases h with hcore | hmarkers
        · exact marker_not_core _ hcore
        · exact marker_not_initialMarkers_self _ hmarkers
      exact hnoti (hreverse hmemj)
  · constructor
    · simp only [family, familySet, hilast, hjlast, if_false]
      exact Set.union_subset_union_right _ (initialMarkers_mono (Nat.le_of_lt hij))
    · intro hreverse
      have hmemj : marker (i : ℕ) ∈ family r j := by
        simp only [family, familySet, hjlast, if_false, Set.mem_union]
        exact Or.inr (marker_mem_initialMarkers hij)
      have hnoti : marker (i : ℕ) ∉ family r i := by
        simp only [family, familySet, hilast, if_false, Set.mem_union]
        intro h
        rcases h with hcore | hmarkers
        · exact marker_not_core _ hcore
        · exact marker_not_initialMarkers_self _ hmarkers
      exact hnoti (hreverse hmemj)

def input : Stream :=
  sparseMergePresentation core (Set.univ \ core) core_infinite

theorem input_injective : Function.Injective input := by
  apply sparseMergePresentation_injective core_infinite
  exact Set.disjoint_sdiff_right

theorem input_range : Set.range input = Set.univ := by
  calc
    Set.range input = core ∪ (Set.univ \ core) :=
      range_sparseMergePresentation core_infinite
    _ = Set.univ := Set.union_diff_cancel (Set.subset_univ _)

theorem family_legal {r : ℕ} (j : Fin r) : Legal input (family r j) := by
  refine ⟨core_infinite.mono (core_subset_familySet r j), input_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, input_range]
    exact Set.subset_univ _
  · exact sparseMergePresentation_vanishingNoise_of_core_subset
      core_infinite (core_subset_familySet r j)

def forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

def freshGenerator : OnlineGenerator := fun t xs ys =>
  GenLimit.Support.freshFromInfinite core core_infinite (forbidden xs ys)

def run (gen : OnlineGenerator) (xs : Stream) : Stream
  | t => gen t (fun i => xs i) (fun i => run gen xs i)
termination_by t => t

theorem run_follows (gen : OnlineGenerator) (xs : Stream) :
    Follows gen xs (run gen xs) := by
  intro t
  rw [run]

theorem freshGenerator_mem (t : ℕ) (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : freshGenerator t xs ys ∈ core :=
  GenLimit.Support.freshFromInfinite_mem _ _ _

theorem freshGenerator_not_input (t : ℕ) (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (s : ℕ) (hs : s < t + 1) :
    freshGenerator t xs ys ≠ xs ⟨s, hs⟩ := by
  intro h
  have hnot := GenLimit.Support.freshFromInfinite_not_mem core core_infinite
    (forbidden xs ys)
  apply hnot
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _, h.symm⟩

theorem freshGenerator_not_output (t : ℕ) (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (s : ℕ) (hs : s < t) :
    freshGenerator t xs ys ≠ ys ⟨s, hs⟩ := by
  intro h
  have hnot := GenLimit.Support.freshFromInfinite_not_mem core core_infinite
    (forbidden xs ys)
  apply hnot
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _, h.symm⟩

theorem run_novel (xs : Stream) :
    GenLimit.NovelGeneratesInLimit xs (run freshGenerator xs) core := by
  refine ⟨0, ?_⟩
  intro t _
  rw [run]
  refine ⟨freshGenerator_mem t _ _, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact freshGenerator_not_input t _ _ s hs heq.symm
  · intro s hs
    exact (freshGenerator_not_output t (fun i => xs i)
      (fun i => run freshGenerator xs i) s hs).symm

theorem globallyFeasible {r : ℕ} : GloballyFeasible (family r) := by
  refine ⟨freshGenerator, ?_⟩
  intro xs _
  refine ⟨run freshGenerator xs, run_follows _ _, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := run_novel xs
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨core_subset_familySet r j hcore, hfresh, hnovel⟩

theorem prefixCount_core_eq_count (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n = Nat.count SparseSquare n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    core, Nat.count_eq_card_filter_range]

theorem core_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount core n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / n)
  · intro n
    positivity
  · intro n
    apply div_le_div_of_nonneg_right
    · have hcount : GenLimit.PatientScope.prefixCount core n ≤ Nat.sqrt n + 1 := by
        rw [prefixCount_core_eq_count]
        exact count_sparseSquare_le_sqrt_add_one n
      exact_mod_cast hcount
    · positivity
  · exact tendsto_sparseSqrt_add_one_div

theorem relativeUpperDensity_core_univ :
    relativeUpperDensity core Set.univ = 0 := by
  unfold relativeUpperDensity
  have hden (n : ℕ) :
      GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
    simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  simpa [hden] using core_ratio_tendsto_zero.limsup_eq

theorem relativeUpperDensity_nonneg (A K : Language) :
    0 ≤ relativeUpperDensity A K := by
  unfold relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall fun n => by positivity
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases h : GenLimit.PatientScope.prefixCount K n = 0
      · simp [h]
      · rw [div_le_one (by positivity)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n⟩

theorem relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · filter_upwards [] with n
    by_cases h : GenLimit.PatientScope.prefixCount K n = 0
    · simp [h]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n

theorem generatorFirst_subset_eventually
    {xs ys : Stream} {K : Language}
    (h : GenLimit.NovelGeneratesInLimit xs ys K) :
    (GenLimit.GeneratorFirst xs ys \ K).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_range (ys ∘ fun i : Fin T => (i : ℕ))).subset
  intro z hz
  obtain ⟨t, hyt, -⟩ := hz.1
  have ht : t < T := by
    by_contra hnot
    apply hz.2
    rw [← hyt]
    exact (hT t (Nat.le_of_not_gt hnot)).1
  exact ⟨⟨t, ht⟩, hyt⟩


theorem prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  calc
    (GenLimit.PatientScope.prefixFinset (A ∪ B) n).card ≤
        (GenLimit.PatientScope.prefixFinset A n ∪
          GenLimit.PatientScope.prefixFinset B n).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [GenLimit.PatientScope.mem_prefixFinset, Finset.mem_union] at hx ⊢
      rcases hx.2 with hxA | hxB
      · exact Or.inl ⟨hx.1, hxA⟩
      · exact Or.inr ⟨hx.1, hxB⟩
    _ ≤ (GenLimit.PatientScope.prefixFinset A n).card +
        (GenLimit.PatientScope.prefixFinset B n).card := Finset.card_union_le _ _

theorem prefixCount_le_card_finite {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  exact hF.mem_toFinset.mpr (Finset.mem_filter.mp hx).2

theorem upperDensity_zero_of_eventually_core
    {xs ys : Stream} (h : GenLimit.NovelGeneratesInLimit xs ys core) :
    relativeUpperDensity (GenLimit.GeneratorFirst xs ys) Set.univ = 0 := by
  let D := GenLimit.GeneratorFirst xs ys
  let F := D \ core
  have hF : F.Finite := generatorFirst_subset_eventually h
  have hsubset : D ⊆ core ∪ F := by
    intro x hx
    by_cases hxc : x ∈ core
    · exact Or.inl hxc
    · exact Or.inr ⟨hx, hxc⟩
  have hprefix (n : ℕ) :
      GenLimit.PatientScope.prefixCount (D ∩ Set.univ) n ≤
        GenLimit.PatientScope.prefixCount core n + hF.toFinset.card := by
    calc
      GenLimit.PatientScope.prefixCount (D ∩ Set.univ) n ≤
          GenLimit.PatientScope.prefixCount (core ∪ F) n :=
        GenLimit.PatientScope.prefixCount_mono
          (fun _ hx => hsubset hx.1) n
      _ ≤ GenLimit.PatientScope.prefixCount core n +
          GenLimit.PatientScope.prefixCount F n := prefixCount_union_le _ _ _
      _ ≤ GenLimit.PatientScope.prefixCount core n + hF.toFinset.card :=
        Nat.add_le_add_left (prefixCount_le_card_finite hF n) _
  have htendsto : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (D ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ))
      atTop (𝓝 0) := by
    have hfinite : Tendsto (fun n : ℕ => (hF.toFinset.card : ℝ) / n)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply squeeze_zero (g := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount core n : ℝ) / n +
        (hF.toFinset.card : ℝ) / n)
    · intro n; positivity
    · intro n
      have hden : GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
        simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
      rw [hden, ← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hprefix n) (by positivity)
    · simpa using core_ratio_tendsto_zero.add hfinite
  exact htendsto.limsup_eq

theorem density_zero_ae
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {xs : Stream} {output : Ω → Stream}
    (h : EventuallyFreshValid μ core xs output) :
    ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst xs (output ω)) Set.univ = 0 := by
  filter_upwards [h] with ω hω
  exact upperDensity_zero_of_eventually_core hω

theorem expected_density_univ_zero
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {xs : Stream} {output : Ω → Stream}
    (h : EventuallyFreshValid μ core xs output) :
    expectedUpperDensity μ Set.univ xs output = 0 := by
  unfold expectedUpperDensity
  calc
    (∫ ω, relativeUpperDensity (GenLimit.GeneratorFirst xs (output ω)) Set.univ ∂μ) =
        ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae (density_zero_ae μ h)
    _ = 0 := by simp

theorem expected_density_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {K : Language} {xs : Stream} {output : Ω → Stream}
    (hint : DensityIntegrable μ K xs output) :
    expectedUpperDensity μ K xs output ≤ 1 := by
  unfold expectedUpperDensity DensityIntegrable at *
  have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  calc
    (∫ ω, relativeUpperDensity (GenLimit.GeneratorFirst xs (output ω)) K ∂μ) ≤
        ∫ _ : Ω, (1 : ℝ) ∂μ := by
          apply integral_mono_ae hint hconst
          exact Filter.Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
    _ = 1 := by simp

theorem pairObstruction : PairObstruction core Set.univ input := by
  intro Ω _ μ _ gen output _ _ hint0 _ hvalid0 _
  have hzero : expectedUpperDensity μ Set.univ input output = 0 :=
    expected_density_univ_zero μ hvalid0
  have hle : expectedUpperDensity μ core input output ≤ 1 :=
    expected_density_le_one μ hint0
  constructor
  · rw [hzero, add_zero]
    exact hle
  · rw [hzero]
    norm_num

theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (family r) input := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hlastEq : r - 1 + 1 = r := by omega
  have hlast : family r last = Set.univ := by
    simp [family, familySet, last, hlastEq]
  have hcorevalid : EventuallyFreshValid μ core input output := by
    filter_upwards [hvalid ⟨0, by omega⟩] with ω hω
    obtain ⟨T, hT⟩ := hω
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    have hone : 1 ≠ r := by omega
    have hzeroFamily : family r ⟨0, by omega⟩ = core := by
      simp [family, familySet, hone, initialMarkers]
    rw [hzeroFamily] at hmem
    exact ⟨hmem, hfresh, hnovel⟩
  rw [hlast]
  exact expected_density_univ_zero μ hcorevalid

theorem main : MainClaim := by
  constructor
  · refine ⟨core, Set.univ, input, ?_, ?_, ?_, pairObstruction⟩
    · rw [Set.ssubset_univ_iff]
      intro hEq
      exact marker_not_core 0 (hEq.symm ▸ Set.mem_univ (marker 0))
    · refine ⟨core_infinite, input_injective, ?_, ?_⟩
      · rw [GenLimit.InfiniteContamination.NoOmissions, input_range]
        exact Set.subset_univ _
      · exact sparseMergePresentation_vanishingNoise_of_core_subset
          core_infinite Set.Subset.rfl
    · refine ⟨Set.infinite_univ, input_injective, ?_, ?_⟩
      · rw [GenLimit.InfiniteContamination.NoOmissions, input_range]
      · exact sparseMergePresentation_vanishingNoise_of_core_subset
          core_infinite (Set.subset_univ _)
  · intro r hr
    refine ⟨family r, input, family_strictlyNested hr, ?_, globallyFeasible,
      manyTargetObstruction hr⟩
    intro j
    exact family_legal j

end

end Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := Case024Proof.main
