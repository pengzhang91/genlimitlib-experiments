import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import GenLimit.Support.Fresh
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open Stage3Case024
open GenLimit
open GenLimit.InfiniteContamination

abbrev Squares : Set ℕ := {n | SparseSquare n}

theorem squares_infinite : Squares.Infinite := by
  apply (Set.infinite_range_of_injective (Nat.pow_left_injective (by norm_num : 2 ≠ 0))).mono
  rintro _ ⟨k, rfl⟩
  simpa [Squares, pow_two] using sparseSquare_mul_self k

theorem nonsquares_infinite : Squaresᶜ.Infinite := by
  simpa [Squares, SparseNonSquare] using sparseNonSquare_infinite

noncomputable def commonInput : Stream :=
  squareSparseMerge Squares Squaresᶜ squares_infinite nonsquares_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  apply squareSparseMerge_injective squares_infinite nonsquares_infinite
  rw [Set.disjoint_left]
  intro x hx hxcomp
  exact hxcomp hx

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_squareSparseMerge squares_infinite nonsquares_infinite]
  exact Set.union_compl_self Squares

theorem legal_commonInput_of_squares_subset {K : Stage3Case024.Language}
    (hsub : Squares ⊆ K) (hK : K.Infinite) : Legal commonInput K := by
  refine ⟨hK, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      squares_infinite nonsquares_infinite hsub

theorem legal_commonInput_squares : Legal commonInput Squares :=
  legal_commonInput_of_squares_subset Set.Subset.rfl squares_infinite

theorem legal_commonInput_univ : Legal commonInput Set.univ :=
  legal_commonInput_of_squares_subset (Set.subset_univ Squares)
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)

theorem prefixCount_nonneg_ratio (A K : Stage3Case024.Language) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n := by
  positivity

theorem relativeUpperDensity_le_one (A K : Stage3Case024.Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (prefixCount_nonneg_ratio A K)
  · apply Eventually.of_forall
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n

theorem prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount Squares n ≤ Nat.sqrt n + 1 := by
  classical
  simpa [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, Squares,
    Nat.count_eq_card_filter_range] using count_sparseSquare_le_sqrt_add_one n

theorem prefixCount_finite_le {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  exact Set.Finite.mem_toFinset hF |>.2 (Finset.mem_filter.mp hx).2

@[simp] theorem prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

theorem relativeUpperDensity_univ_eq_zero_of_subset_squares_union_finite
    {A F : Set ℕ} (hF : F.Finite) (hsub : A ⊆ Squares ∪ F) :
    relativeUpperDensity A Set.univ = 0 := by
  let B := hF.toFinset.card
  have hbound : ∀ n,
      (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          GenLimit.PatientScope.prefixCount Set.univ n ≤
        ((Nat.sqrt n : ℝ) + 1) / n + (B : ℝ) / n := by
    intro n
    have hcountA :
        GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n ≤
          GenLimit.PatientScope.prefixCount Squares n +
            GenLimit.PatientScope.prefixCount F n := by
      classical
      unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
      let left := (Finset.range n).filter (fun x => x ∈ Squares)
      let right := (Finset.range n).filter (fun x => x ∈ F)
      have hsubset :
          (Finset.range n).filter (fun x => x ∈ A ∩ Set.univ) ⊆ left ∪ right := by
        intro x hx
        have hxA : x ∈ A := (Finset.mem_filter.mp hx).2.1
        rcases hsub hxA with hxS | hxF
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hx).1, hxS⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hx).1, hxF⟩)
      simpa [left, right] using
        (Finset.card_le_card hsubset).trans (Finset.card_union_le left right)
    have hcount :
        GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n ≤
          Nat.sqrt n + 1 + B := by
      exact hcountA.trans (Nat.add_le_add (prefixCount_squares_le n)
        (by simpa [B] using prefixCount_finite_le hF n))
    rw [Set.inter_univ, prefixCount_univ]
    rw [← add_div]
    have hcount' :
        GenLimit.PatientScope.prefixCount A n ≤ Nat.sqrt n + 1 + B := by
      simpa using hcount
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount') (by positivity)
  have htendsto : Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / n + (B : ℝ) / n)
      atTop (𝓝 0) := by
    simpa using tendsto_sparseSqrt_add_one_div.add
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  unfold relativeUpperDensity
  apply le_antisymm
  · calc
      limsup (fun n : ℕ =>
          (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
            GenLimit.PatientScope.prefixCount Set.univ n) atTop
          ≤ limsup (fun n : ℕ =>
              ((Nat.sqrt n : ℝ) + 1) / n + (B : ℝ) / n) atTop := by
              exact limsup_le_limsup (Eventually.of_forall hbound)
                (isCoboundedUnder_le_of_le atTop
                  (prefixCount_nonneg_ratio A Set.univ))
                htendsto.isBoundedUnder_le
      _ = 0 := htendsto.limsup_eq
  · apply le_limsup_of_frequently_le
    · exact Frequently.of_forall (prefixCount_nonneg_ratio A Set.univ)
    · exact isBoundedUnder_of ⟨1, fun n => by
        by_cases hn : GenLimit.PatientScope.prefixCount Set.univ n = 0
        · simp [hn]
        · rw [div_le_one (by positivity)]
          exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n⟩

theorem generatorFirst_subset_squares_union_finite_of_eventual
    {input output : Stream} (h : GenLimit.NovelGeneratesInLimit input output Squares) :
    ∃ F : Set ℕ, F.Finite ∧ GenLimit.GeneratorFirst input output ⊆ Squares ∪ F := by
  obtain ⟨T, hT⟩ := h
  let F : Set ℕ := output '' Set.Iio T
  refine ⟨F, (Set.finite_Iio T).image output, ?_⟩
  intro x hx
  obtain ⟨t, htx, -⟩ := hx
  by_cases ht : t < T
  · exact Set.mem_union_right _ ⟨t, ht, htx⟩
  · exact Set.mem_union_left _ (htx ▸ (hT t (Nat.le_of_not_gt ht)).1)

theorem relativeUpperDensity_generatorFirst_univ_eq_zero_of_eventual
    {input output : Stream} (h : GenLimit.NovelGeneratesInLimit input output Squares) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨F, hF, hsub⟩ :=
    generatorFirst_subset_squares_union_finite_of_eventual h
  exact relativeUpperDensity_univ_eq_zero_of_subset_squares_union_finite hF hsub

noncomputable def freshGenerator (K : Stage3Case024.Language) (hK : K.Infinite) : OnlineGenerator :=
  fun _ inputHistory outputHistory =>
    GenLimit.Support.freshFromInfinite K hK
      (Finset.univ.image inputHistory ∪ Finset.univ.image outputHistory)

noncomputable def runGenerator (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => Nat.strongRec (motive := fun _ => ℕ)
    (fun n rec => gen n (fun i => input i) (fun i => rec i.1 i.2)) t

theorem runGenerator_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (runGenerator gen input) := by
  intro t
  rw [runGenerator, Nat.strongRec_eq]
  rfl

theorem freshGenerator_novel (K : Stage3Case024.Language) (hK : K.Infinite) (input : Stream) :
    GenLimit.NovelGeneratesInLimit input
      (runGenerator (freshGenerator K hK) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  have hfollow := runGenerator_follows (freshGenerator K hK) input t
  rw [hfollow]
  constructor
  · exact GenLimit.Support.freshFromInfinite_mem K hK _
  constructor
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hst, hs⟩ := hsample
    have hmem : input s ∈ Finset.univ.image (fun i : Fin (t + 1) => input i) := by
      apply Finset.mem_image.mpr
      exact ⟨⟨s, hst⟩, Finset.mem_univ _, rfl⟩
    exact GenLimit.Support.freshFromInfinite_not_mem K hK _
      (Finset.mem_union_left _ (hs ▸ hmem))
  · intro s hst hs
    have hmem : runGenerator (freshGenerator K hK) input s ∈
        Finset.univ.image
          (fun i : Fin t => runGenerator (freshGenerator K hK) input i) := by
      apply Finset.mem_image.mpr
      exact ⟨⟨s, hst⟩, Finset.mem_univ _, rfl⟩
    exact GenLimit.Support.freshFromInfinite_not_mem K hK _
      (Finset.mem_union_right _ (hs ▸ hmem))

theorem globallyFeasible_of_smallest
    {r : ℕ} (family : Fin r → Stage3Case024.Language)
    (K : Stage3Case024.Language) (hK : K.Infinite)
    (hsub : ∀ j, K ⊆ family j) : GloballyFeasible family := by
  refine ⟨freshGenerator K hK, ?_⟩
  intro input _
  refine ⟨runGenerator (freshGenerator K hK) input,
    runGenerator_follows _ _, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshGenerator_novel K hK input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hsub j hmem, hfresh, hnovel⟩

def markers (n : ℕ) : Set ℕ :=
  ↑((Finset.range n).image sparseBetweenSquares)

theorem marker_mem_markers {i n : ℕ} (h : i < n) :
    sparseBetweenSquares i ∈ markers n := by
  simp only [markers, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  exact ⟨i, h, rfl⟩

theorem marker_not_mem_markers_self (i : ℕ) :
    sparseBetweenSquares i ∉ markers i := by
  intro h
  simp only [markers, Finset.mem_coe, Finset.mem_image,
    Finset.mem_range] at h
  obtain ⟨a, ha, hai⟩ := h
  have : a = i := sparseBetweenSquares_strictMono.injective hai
  omega

theorem marker_not_mem_squares (i : ℕ) :
    sparseBetweenSquares i ∉ Squares := by
  exact sparseBetweenSquares_nonsquare i

theorem marker_not_mem_prefix (i : ℕ) :
    sparseBetweenSquares i ∉ Squares ∪ markers i := by
  intro h
  rcases h with h | h
  · exact marker_not_mem_squares i h
  · exact marker_not_mem_markers_self i h

theorem markers_mono {i j : ℕ} (h : i ≤ j) : markers i ⊆ markers j := by
  intro x hx
  simp only [markers, Finset.mem_coe, Finset.mem_image,
    Finset.mem_range] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha.trans_le h, rfl⟩

def nestedFamily (r : ℕ) (j : Fin r) : Stage3Case024.Language :=
  if (j : ℕ) + 1 = r then Set.univ else Squares ∪ markers j

theorem squares_subset_nestedFamily (r : ℕ) (j : Fin r) :
    Squares ⊆ nestedFamily r j := by
  intro x hx
  by_cases hlast : (j : ℕ) + 1 = r
  · simp [nestedFamily, hlast]
  · rw [nestedFamily, if_neg hlast]
    exact Set.mem_union_left _ hx

theorem nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = Squares := by
  have hnot : 0 + 1 ≠ r := by omega
  simp [nestedFamily, hnot, markers]

def lastIndex (r : ℕ) (hr : 1 ≤ r) : Fin r := ⟨r - 1, by omega⟩

theorem nestedFamily_last {r : ℕ} (hr : 1 ≤ r) :
    nestedFamily r (lastIndex r hr) = Set.univ := by
  have hlast : (r - 1) + 1 = r := by omega
  simp [nestedFamily, lastIndex, hlast]

theorem strictlyNested_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hinot : (i : ℕ) + 1 ≠ r := by omega
  by_cases hjlast : (j : ℕ) + 1 = r
  · rw [nestedFamily, if_neg hinot, nestedFamily, if_pos hjlast,
      Set.ssubset_def]
    constructor
    · exact Set.subset_univ _
    · intro hback
      exact marker_not_mem_prefix i (hback (Set.mem_univ _))
  · rw [nestedFamily, if_neg hinot, nestedFamily, if_neg hjlast,
      Set.ssubset_def]
    constructor
    · intro x hx
      rcases hx with hx | hx
      · exact Set.mem_union_left _ hx
      · exact Set.mem_union_right _ (markers_mono hij.le hx)
    · intro hback
      apply marker_not_mem_prefix i
      apply hback
      exact Set.mem_union_right _ (marker_mem_markers hij)

theorem legal_nestedFamily (r : ℕ) (j : Fin r) :
    Legal commonInput (nestedFamily r j) :=
  legal_commonInput_of_squares_subset
    (squares_subset_nestedFamily r j)
    (squares_infinite.mono (squares_subset_nestedFamily r j))

theorem expected_univ_eq_zero_of_eventual_squares
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (input : Stream) (output : Ω → Stream)
    (hvalid : EventuallyFreshValid μ Squares input output) :
    expectedUpperDensity μ Set.univ input output = 0 := by
  unfold expectedUpperDensity
  calc
    (∫ ω, relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) =
        ∫ _ : Ω, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          exact hvalid.mono fun ω hω =>
            relativeUpperDensity_generatorFirst_univ_eq_zero_of_eventual hω
    _ = 0 := by simp

theorem pairObstruction : PairObstruction Squares Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hIntSquares _ hvalidSquares _
  have huniv : expectedUpperDensity μ Set.univ commonInput output = 0 :=
    expected_univ_eq_zero_of_eventual_squares μ commonInput output hvalidSquares
  have hsquares : expectedUpperDensity μ Squares commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Squares ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
            exact integral_mono_ae hIntSquares (integrable_const 1)
              (Eventually.of_forall fun ω =>
                relativeUpperDensity_le_one
                  (GenLimit.GeneratorFirst commonInput (output ω)) Squares)
      _ = 1 := by simp
  constructor
  · rw [huniv, add_zero]
    exact hsquares
  · intro hboth
    rw [huniv] at hboth
    linarith

theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let zero : Fin r := ⟨0, by omega⟩
  let last : Fin r := lastIndex r (by omega)
  have hvalidSquares : EventuallyFreshValid μ Squares commonInput output := by
    simpa [zero, nestedFamily_zero hr] using hvalid zero
  refine ⟨last, ?_⟩
  rw [show nestedFamily r last = Set.univ by
    simpa [last] using nestedFamily_last (r := r) (by omega)]
  exact expected_univ_eq_zero_of_eventual_squares
    μ commonInput output hvalidSquares

theorem manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨strictlyNested_nestedFamily hr, legal_nestedFamily r,
    globallyFeasible_of_smallest (nestedFamily r) Squares squares_infinite
      (squares_subset_nestedFamily r), manyTargetObstruction hr⟩

end Stage3Case024Proof
