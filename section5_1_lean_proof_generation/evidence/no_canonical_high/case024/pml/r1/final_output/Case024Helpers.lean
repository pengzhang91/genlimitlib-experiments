import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper17_InfiniteContamination.EvenDensity
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import GenLimit.Support.Fresh
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open GenLimit
open GenLimit.InfiniteContamination
open GenLimit.KleinbergWei

abbrev Core : Set ℕ := {n | SparseSquare n}

theorem core_infinite : Core.Infinite := by
  let f : ℕ → ℕ := fun k => k * k
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    nlinarith
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨k, rfl⟩
  exact sparseSquare_mul_self k

noncomputable def commonStream : Stage3Case024.Stream :=
  sparseMergePresentation Core Coreᶜ core_infinite

theorem commonStream_injective : Function.Injective commonStream := by
  apply sparseMergePresentation_injective core_infinite
  rw [Set.disjoint_left]
  intro x hx hxc
  exact hxc hx

theorem commonStream_range : Set.range commonStream = Set.univ := by
  rw [commonStream, range_sparseMergePresentation core_infinite]
  exact Set.union_compl_self Core

theorem commonStream_legal {K : Set ℕ} (hcore : Core ⊆ K) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨core_infinite.mono hcore, commonStream_injective, ?_, ?_⟩
  · intro x _
    rw [commonStream_range]
    exact Set.mem_univ x
  · exact sparseMergePresentation_vanishingNoise_of_core_subset core_infinite hcore

theorem core_proper_univ : Core ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro hreverse
  exact sparseBetweenSquares_nonsquare 0 (hreverse (Set.mem_univ _))

theorem relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n⟩

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact Eventually.of_forall fun n => by
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n

theorem core_prefixRatio_tendsto_zero :
    Tendsto (naturalOrder.prefixRatio Core) atTop (𝓝 0) := by
  classical
  apply squeeze_zero (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / (n : ℝ))
  · exact fun n => naturalOrder.prefixRatio_nonneg Core n
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [OrderedLanguage.prefixRatio, hn, if_false]
      apply div_le_div_of_nonneg_right
      · have hc : naturalOrder.prefixCount Core n ≤ Nat.sqrt n + 1 := by
          change ((Finset.range n).filter SparseSquare).card ≤ Nat.sqrt n + 1
          simpa [Nat.count_eq_card_filter_range] using count_sparseSquare_le_sqrt_add_one n
        exact_mod_cast hc
      · positivity
  · exact tendsto_sparseSqrt_add_one_div

theorem core_upperDensity_zero : naturalOrder.upperDensity Core = 0 :=
  core_prefixRatio_tendsto_zero.limsup_eq

theorem relativeUpperDensity_univ_eq_natural (A : Set ℕ) :
    Stage3Case024.relativeUpperDensity A Set.univ = naturalOrder.upperDensity A := by
  unfold Stage3Case024.relativeUpperDensity OrderedLanguage.upperDensity
  congr 1
  funext n
  rw [Set.inter_univ]
  by_cases hn : n = 0
  · simp [hn, GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
      OrderedLanguage.prefixRatio, OrderedLanguage.prefixCount, naturalOrder]
  · simp [hn, GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
      OrderedLanguage.prefixRatio, OrderedLanguage.prefixCount, naturalOrder]

theorem relativeUpperDensity_univ_zero_of_diff_core_finite
    {A : Set ℕ} (hfinite : (A \ Core).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  rw [relativeUpperDensity_univ_eq_natural]
  apply le_antisymm
  · calc
      naturalOrder.upperDensity A ≤ naturalOrder.upperDensity (Core ∪ (A \ Core)) := by
        apply naturalOrder.upperDensity_mono
        intro x hx
        by_cases hxc : x ∈ Core
        · exact Or.inl hxc
        · exact Or.inr ⟨hx, hxc⟩
      _ ≤ naturalOrder.upperDensity Core + naturalOrder.upperDensity (A \ Core) :=
        naturalOrder.upperDensity_union_le _ _
      _ = 0 := by
        rw [core_upperDensity_zero,
          naturalOrder.upperDensity_eq_zero_of_finite hfinite]
        norm_num
  · exact naturalOrder.upperDensity_nonneg A

theorem generatorFirst_diff_core_finite
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Core) :
    (GenLimit.GeneratorFirst input output \ Core).Finite := by
  obtain ⟨T, hT⟩ := hvalid
  apply Set.Finite.subset (Set.finite_range fun t : Fin T => output t)
  intro x hx
  obtain ⟨t, hout, -⟩ := hx.1
  have ht : t < T := by
    by_contra hnot
    have hmem := (hT t (Nat.le_of_not_gt hnot)).1
    exact hx.2 (hout ▸ hmem)
  exact ⟨⟨t, ht⟩, hout⟩

theorem path_density_univ_zero
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Core) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  exact relativeUpperDensity_univ_zero_of_diff_core_finite
    (generatorFirst_diff_core_finite hvalid)

def extra (i : ℕ) : Set ℕ :=
  {x | ∃ k < i, x = sparseBetweenSquares k}

theorem extra_mono {i j : ℕ} (hij : i ≤ j) : extra i ⊆ extra j := by
  rintro x ⟨k, hki, rfl⟩
  exact ⟨k, lt_of_lt_of_le hki hij, rfl⟩

theorem sparseBetween_not_mem_extra (i : ℕ) :
    sparseBetweenSquares i ∉ extra i := by
  rintro ⟨k, hki, heq⟩
  have := sparseBetweenSquares_strictMono.injective heq
  omega

def family (r : ℕ) (i : Fin r) : Set ℕ :=
  if i.1 = r - 1 then Set.univ else Core ∪ extra i.1

theorem core_subset_family (r : ℕ) (i : Fin r) : Core ⊆ family r i := by
  intro x hx
  simp only [family]
  split
  · exact Set.mem_univ x
  · exact Or.inl hx

theorem family_zero_eq_core {r : ℕ} (hr : 2 ≤ r) :
    family r ⟨0, by omega⟩ = Core := by
  simp [family, extra]
  omega

def lastIndex (r : ℕ) (hr : 2 ≤ r) : Fin r := ⟨r - 1, by omega⟩

theorem family_last_eq_univ (r : ℕ) (hr : 2 ≤ r) :
    family r (lastIndex r hr) = Set.univ := by
  simp [family, lastIndex]

theorem family_strictlyNested (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (family r) := by
  intro i j hij
  have hi_last : i.1 ≠ r - 1 := by omega
  rw [family, if_neg hi_last]
  by_cases hj_last : j.1 = r - 1
  · rw [family, if_pos hj_last]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hreverse
    have hw := hreverse (Set.mem_univ (sparseBetweenSquares i.1))
    rcases hw with hsq | hextra
    · exact sparseBetweenSquares_nonsquare i.1 hsq
    · exact sparseBetween_not_mem_extra i.1 hextra
  · rw [family, if_neg hj_last]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hcore | hextra
      · exact Or.inl hcore
      · exact Or.inr (extra_mono (Nat.le_of_lt hij) hextra)
    · intro hreverse
      have hw := hreverse (Or.inr ⟨i.1, hij, rfl⟩)
      rcases hw with hsq | hextra
      · exact sparseBetweenSquares_nonsquare i.1 hsq
      · exact sparseBetween_not_mem_extra i.1 hextra

def row (t : ℕ) : Set ℕ :=
  Set.range fun k => Nat.pair t k * Nat.pair t k

theorem row_infinite (t : ℕ) : (row t).Infinite := by
  apply Set.infinite_range_of_injective
  intro a b hab
  have hp : Nat.pair t a = Nat.pair t b := by nlinarith
  exact (Nat.pair_eq_pair.mp hp).2

theorem row_subset_core (t : ℕ) : row t ⊆ Core := by
  rintro _ ⟨k, rfl⟩
  exact sparseSquare_mul_self (Nat.pair t k)

theorem row_index_eq_of_eq {s t x : ℕ} (hs : x ∈ row s) (ht : x ∈ row t) : s = t := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, hab⟩ := ht
  have hp : Nat.pair s a = Nat.pair t b := by nlinarith
  exact (Nat.pair_eq_pair.mp hp).1

noncomputable def freshGen : Stage3Case024.OnlineGenerator :=
  fun t input _ =>
    GenLimit.Support.freshFromInfinite (row t) (row_infinite t)
      (Finset.univ.image input)

noncomputable def freshOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t =>
    GenLimit.Support.freshFromInfinite (row t) (row_infinite t)
      (Finset.univ.image fun i : Fin (t + 1) => input i)

theorem freshOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshGen input (freshOutput input) := by
  intro t
  rfl

theorem freshOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (freshOutput input) Core := by
  refine ⟨0, ?_⟩
  intro t _
  have hrow : freshOutput input t ∈ row t :=
    GenLimit.Support.freshFromInfinite_mem _ _ _
  refine ⟨row_subset_core t hrow, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hst, hs⟩ := hsample
    have hmem : freshOutput input t ∈
        Finset.univ.image (fun i : Fin (t + 1) => input i) := by
      apply Finset.mem_image.mpr
      exact ⟨⟨s, hst⟩, Finset.mem_univ _, hs⟩
    exact GenLimit.Support.freshFromInfinite_not_mem _ _ _ hmem
  · intro s hst heq
    have hsrow : freshOutput input s ∈ row s :=
      GenLimit.Support.freshFromInfinite_mem _ _ _
    have : s = t := row_index_eq_of_eq hsrow (heq ▸ hrow)
    omega

theorem family_globallyFeasible (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.GloballyFeasible (family r) := by
  refine ⟨freshGen, ?_⟩
  intro input _
  refine ⟨freshOutput input, freshOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨core_subset_family r j hcore, hfresh, hnovel⟩

theorem expected_core_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (input : Stage3Case024.Stream)
    (output : Ω → Stage3Case024.Stream)
    (hint : Stage3Case024.DensityIntegrable μ Core input output) :
    Stage3Case024.expectedUpperDensity μ Core input output ≤ 1 := by
  unfold Stage3Case024.expectedUpperDensity
  have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Core ∂μ) ≤
        ∫ _ : Ω, (1 : ℝ) ∂μ := by
          apply integral_mono_ae hint hconst
          exact Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
    _ = 1 := by simp

theorem expected_univ_zero
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : Stage3Case024.Stream) (output : Ω → Stage3Case024.Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ Core input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.expectedUpperDensity
  apply integral_eq_zero_of_ae
  filter_upwards [hvalid] with ω hω
  exact path_density_univ_zero hω

theorem pair_obstruction : Stage3Case024.PairObstruction Core Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hintCore _ hvalidCore _
  have hcore := expected_core_le_one μ commonStream output hintCore
  have huniv := expected_univ_zero μ commonStream output hvalidCore
  constructor
  · rw [huniv]
    linarith
  · intro hboth
    rw [huniv] at hboth
    linarith

theorem family_obstruction (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (family r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  refine ⟨lastIndex r hr, ?_⟩
  rw [family_last_eq_univ]
  apply expected_univ_zero μ commonStream output
  simpa [family_zero_eq_core hr] using hvalid (⟨0, by omega⟩ : Fin r)

end Stage3Case024Proof
