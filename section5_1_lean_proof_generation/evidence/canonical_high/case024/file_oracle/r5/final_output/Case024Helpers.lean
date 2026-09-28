import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024

open GenLimit.InfiniteContamination

abbrev Squares : Set ℕ := {n | SparseSquare n}
abbrev NonSquares : Set ℕ := {n | SparseNonSquare n}

theorem squares_infinite : Squares.Infinite := by
  let f : ℕ → ℕ := fun n => n * n
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    nlinarith
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n, rfl⟩
  exact sparseSquare_mul_self n

theorem nonsquares_infinite : NonSquares.Infinite :=
  sparseNonSquare_infinite

theorem squares_disjoint_nonsquares : Disjoint Squares NonSquares := by
  rw [Set.disjoint_left]
  intro n hn hnn
  exact hnn hn

theorem squares_union_nonsquares : Squares ∪ NonSquares = Set.univ := by
  ext n
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact Classical.em (SparseSquare n)

noncomputable def commonInput : Stage3Case024.Stream :=
  squareSparseMerge Squares NonSquares squares_infinite nonsquares_infinite

theorem commonInput_injective : Function.Injective commonInput :=
  squareSparseMerge_injective squares_infinite nonsquares_infinite
    squares_disjoint_nonsquares

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_squareSparseMerge squares_infinite nonsquares_infinite,
    squares_union_nonsquares]

theorem commonInput_legal_squares : Stage3Case024.Legal commonInput Squares := by
  refine ⟨squares_infinite, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ _
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      squares_infinite nonsquares_infinite (Set.Subset.rfl)

theorem commonInput_legal_univ :
    Stage3Case024.Legal commonInput (Set.univ : Set ℕ) := by
  refine ⟨Set.infinite_univ, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    have : (fun _ : ℕ => (0 : ℝ)) =
        GenLimit.InfiniteContamination.empiricalNoiseRate commonInput Set.univ := by
      funext n
      simp [GenLimit.InfiniteContamination.empiricalNoiseRate,
        GenLimit.InfiniteContamination.noiseCount]
    rw [← this]
    exact tendsto_const_nhds

theorem prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount Squares n ≤ Nat.sqrt n + 1 := by
  simpa [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, Squares,
    Nat.count_eq_card_filter_range] using count_sparseSquare_le_sqrt_add_one n

@[simp] theorem prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

theorem generatorFirst_subset_range (input output : Stage3Case024.Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro z ⟨t, htz, -⟩
  exact ⟨t, htz⟩

theorem finite_outside_squares_of_eventually_valid
    {input output : Stage3Case024.Stream}
    (h : GenLimit.NovelGeneratesInLimit input output Squares) :
    (Set.range output \ Squares).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_Iio T).image output |>.subset
  rintro z ⟨⟨t, rfl⟩, htSquare⟩
  refine ⟨t, ?_, rfl⟩
  by_contra hnot
  exact htSquare (hT t (Nat.le_of_not_gt hnot)).1

theorem prefixCount_generatorFirst_le
    {input output : Stage3Case024.Stream}
    (hfinite : (Set.range output \ Squares).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output) n ≤
      Nat.sqrt n + 1 + hfinite.toFinset.card := by
  classical
  let D := GenLimit.GeneratorFirst input output
  let F := hfinite.toFinset
  have hsub : GenLimit.PatientScope.prefixFinset D n ⊆
      GenLimit.PatientScope.prefixFinset Squares n ∪ F := by
    intro z hz
    have hzD : z ∈ D := (GenLimit.PatientScope.mem_prefixFinset.mp hz).2
    have hzRange : z ∈ Set.range output :=
      generatorFirst_subset_range input output hzD
    by_cases hzSquare : z ∈ Squares
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hz).1, hzSquare⟩)
    · exact Finset.mem_union_right _
        (Set.Finite.mem_toFinset hfinite |>.2 ⟨hzRange, hzSquare⟩)
  calc
    GenLimit.PatientScope.prefixCount D n =
        (GenLimit.PatientScope.prefixFinset D n).card := rfl
    _ ≤ (GenLimit.PatientScope.prefixFinset Squares n ∪ F).card :=
      Finset.card_le_card hsub
    _ ≤ (GenLimit.PatientScope.prefixFinset Squares n).card + F.card :=
      Finset.card_union_le _ _
    _ = GenLimit.PatientScope.prefixCount Squares n + F.card := rfl
    _ ≤ Nat.sqrt n + 1 + F.card :=
      Nat.add_le_add_right (prefixCount_squares_le n) _

theorem tendsto_sparse_bound (C : ℕ) :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 + C : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hC : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  convert tendsto_sparseSqrt_add_one_div.add hC using 1
  · funext n
    push_cast
    ring
  · simp

theorem relativeUpperDensity_univ_eq_zero
    {input output : Stage3Case024.Stream}
    (h : GenLimit.NovelGeneratesInLimit input output Squares) :
    Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  let hfinite := finite_outside_squares_of_eventually_valid h
  have htend : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input output) n : ℝ) /
          (n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun n : ℕ =>
        ((Nat.sqrt n + 1 + hfinite.toFinset.card : ℕ) : ℝ) / (n : ℝ))
    · exact Eventually.of_forall fun n => by positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      apply div_le_div_of_nonneg_right
      · exact_mod_cast prefixCount_generatorFirst_le hfinite n
      · positivity
    · exact tendsto_sparse_bound hfinite.toFinset.card
  unfold Stage3Case024.relativeUpperDensity
  simpa [prefixCount_univ] using htend.limsup_eq

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  refine limsup_le_of_le
    (isCoboundedUnder_le_of_eventually_le atTop
      (Eventually.of_forall fun n => by positivity)) ?_
  exact Eventually.of_forall fun n => by
    change ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)) ≤ (1 : ℝ)
    have hcard : GenLimit.PatientScope.prefixCount (A ∩ K) n ≤
        GenLimit.PatientScope.prefixCount K n := by
      exact Finset.card_le_card (by
        intro z hz
        exact GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hz).1,
            (GenLimit.PatientScope.mem_prefixFinset.mp hz).2.2⟩ :
          GenLimit.PatientScope.prefixFinset (A ∩ K) n ⊆
            GenLimit.PatientScope.prefixFinset K n)
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · have hnum : GenLimit.PatientScope.prefixCount (A ∩ K) n = 0 :=
        Nat.eq_zero_of_le_zero (hzero ▸ hcard)
      simp [hzero, hnum]
    · apply (div_le_one (show (0 : ℝ) <
          GenLimit.PatientScope.prefixCount K n by positivity)).2
      exact_mod_cast hcard


theorem legal_of_squares_subset {K : Set ℕ} (hsub : Squares ⊆ K) :
    Stage3Case024.Legal commonInput K := by
  refine ⟨squares_infinite.mono hsub, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ _
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      squares_infinite nonsquares_infinite hsub

abbrev marker (k : ℕ) : ℕ := sparseBetweenSquares k

def MarkerPrefix (j : ℕ) : Set ℕ :=
  {x | ∃ k, k < j ∧ marker k = x}

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Set ℕ :=
  if (j : ℕ) + 1 = r then Set.univ else Squares ∪ MarkerPrefix j

theorem marker_nonsquare (k : ℕ) : marker k ∈ NonSquares :=
  sparseBetweenSquares_nonsquare k

theorem marker_injective : Function.Injective marker :=
  sparseBetweenSquares_strictMono.injective

theorem marker_not_mem_prefix (k : ℕ) : marker k ∉ MarkerPrefix k := by
  rintro ⟨q, hq, heq⟩
  have : q = k := marker_injective heq
  omega

theorem marker_mem_prefix {i j : ℕ} (hij : i < j) :
    marker i ∈ MarkerPrefix j :=
  ⟨i, hij, rfl⟩

theorem marker_not_square (k : ℕ) : marker k ∉ Squares :=
  marker_nonsquare k

theorem nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = Squares := by
  unfold nestedFamily
  simp only [Fin.val_zero]
  rw [if_neg (by omega)]
  ext x
  simp [MarkerPrefix]

theorem nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  unfold nestedFamily
  simp only [Fin.val_mk]
  rw [if_pos (by omega)]

theorem squares_subset_nestedFamily {r : ℕ} (j : Fin r) :
    Squares ⊆ nestedFamily r j := by
  intro x hx
  simp only [nestedFamily]
  split
  · simp
  · exact Set.mem_union_left _ hx

theorem nestedFamily_strict {r : ℕ} (_hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiNotLast : (i : ℕ) + 1 ≠ r := by omega
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    simp only [nestedFamily, hiNotLast, if_false] at hx
    simp only [nestedFamily]
    split
    · simp
    · rcases hx with hxSquare | ⟨k, hki, hkx⟩
      · exact Set.mem_union_left _ hxSquare
      · exact Set.mem_union_right _ ⟨k, lt_trans hki hij, hkx⟩
  · intro heq
    have hjmem : marker i ∈ nestedFamily r j := by
      simp only [nestedFamily]
      split
      · simp
      · exact Set.mem_union_right _ (marker_mem_prefix hij)
    have himem : marker i ∈ nestedFamily r i := heq ▸ hjmem
    simp only [nestedFamily, hiNotLast, if_false, Set.mem_union] at himem
    exact himem.elim (marker_not_square i) (marker_not_mem_prefix i)

theorem nestedFamily_legal {r : ℕ} (j : Fin r) :
    Stage3Case024.Legal commonInput (nestedFamily r j) :=
  legal_of_squares_subset (squares_subset_nestedFamily j)

noncomputable def squareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ =>
    let total := ∑ i, input i
    let base := total + t + 1
    base * base

noncomputable def squareOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => squareGenerator t (fun i => input i) (fun _ => 0)

theorem squareOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows squareGenerator input (squareOutput input) := by
  intro t
  simp [squareOutput, squareGenerator]

theorem prefixSum_mono (input : Stage3Case024.Stream) {s t : ℕ} (hst : s ≤ t) :
    (∑ n ∈ Finset.range (s + 1), input n) ≤
      ∑ n ∈ Finset.range (t + 1), input n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hst 1)
  · intro i _ _
    exact Nat.zero_le _

theorem input_le_prefixSum (input : Stage3Case024.Stream) {q t : ℕ} (hq : q < t + 1) :
    input q ≤ ∑ n ∈ Finset.range (t + 1), input n := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (input i))
    (Finset.mem_range.mpr hq)

theorem squareOutput_formula (input : Stage3Case024.Stream) (t : ℕ) :
    squareOutput input t =
      ((∑ n ∈ Finset.range (t + 1), input n) + t + 1) ^ 2 := by
  simp [squareOutput, squareGenerator, Fin.sum_univ_eq_sum_range, pow_two]

theorem squareOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) Squares := by
  refine ⟨0, ?_⟩
  intro t _
  let total := ∑ n ∈ Finset.range (t + 1), input n
  let base := total + t + 1
  have hformula : squareOutput input t = base ^ 2 := by
    simpa [total, base] using squareOutput_formula input t
  have hbase : 0 < base := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hformula]
    exact ⟨base, by simp [pow_two]⟩
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨q, hq, hqeq⟩ := hmem
    have hinput : input q ≤ total := input_le_prefixSum input hq
    have hsquare : base ≤ base ^ 2 := by nlinarith
    have : input q < squareOutput input t := by
      rw [hformula]
      omega
    exact (ne_of_lt this) hqeq
  · intro s hst
    let totalS := ∑ n ∈ Finset.range (s + 1), input n
    let baseS := totalS + s + 1
    have hsum : totalS ≤ total := prefixSum_mono input (Nat.le_of_lt hst)
    have hbaseS : baseS < base := by
      dsimp [baseS, base]
      omega
    have houtS : squareOutput input s = baseS ^ 2 := by
      simpa [totalS, baseS] using squareOutput_formula input s
    rw [houtS, hformula]
    nlinarith

theorem nestedFamily_globallyFeasible {r : ℕ} (_hr : 2 ≤ r) :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨squareGenerator, ?_⟩
  intro input _
  refine ⟨squareOutput input, squareOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := squareOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hsquare, hfresh, hnovel⟩ := hT t ht
  exact ⟨squares_subset_nestedFamily j hsquare, hfresh, hnovel⟩

end Case024
