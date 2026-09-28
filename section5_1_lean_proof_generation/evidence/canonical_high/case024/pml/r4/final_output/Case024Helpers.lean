import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024Proof

open GenLimit.InfiniteContamination
open GenLimit.PatientScope
open Stage3Case024

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

def core : Set ℕ := {n | SparseSquare n}

theorem core_infinite : core.Infinite := by
  have hsquare : Function.Injective (fun n : ℕ => n * n) := by
    intro a b hab
    nlinarith
  exact (Set.infinite_range_of_injective hsquare).mono (by
    rintro _ ⟨n, rfl⟩
    exact sparseSquare_mul_self n)

noncomputable def commonInput : Stream :=
  sparseMergePresentation core (Set.univ \ core) core_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  apply sparseMergePresentation_injective core_infinite
  exact Set.disjoint_sdiff_right

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation core_infinite]
  exact Set.union_diff_cancel (Set.subset_univ core)

theorem commonInput_legal_of_core_subset {K : Language}
    (hcoreK : core ⊆ K) : Legal commonInput K := by
  refine ⟨core_infinite.mono hcoreK, commonInput_injective, ?_, ?_⟩
  · intro x hx
    rw [commonInput_range]
    exact Set.mem_univ x
  · exact sparseMergePresentation_vanishingNoise_of_core_subset
      core_infinite hcoreK

theorem core_ssubset_univ : core ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have hbad := h (show sparseBetweenSquares 0 ∈ (Set.univ : Set ℕ) by simp)
  exact sparseBetweenSquares_nonsquare 0 hbad

theorem prefixCount_core (n : ℕ) :
    prefixCount core n = Nat.count SparseSquare n := by
  classical
  rw [prefixCount, prefixFinset, Nat.count_eq_card_filter_range]
  rfl

theorem prefixCount_univ (n : ℕ) :
    prefixCount (Set.univ : Set ℕ) n = n := by
  classical
  simp [prefixCount, prefixFinset]

theorem prefixCount_le_core_add_finite {A : Set ℕ}
    (hfinite : (A \ core).Finite) (n : ℕ) :
    prefixCount A n ≤ Nat.count SparseSquare n + hfinite.toFinset.card := by
  classical
  let left := prefixFinset A n
  let squares := prefixFinset core n
  have hsub : left ⊆ squares ∪ hfinite.toFinset := by
    intro x hx
    have hxA : x ∈ A := (mem_prefixFinset.mp hx).2
    by_cases hxcore : x ∈ core
    · exact Finset.mem_union_left _ (mem_prefixFinset.mpr
        ⟨(mem_prefixFinset.mp hx).1, hxcore⟩)
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset hfinite).2 ⟨hxA, hxcore⟩)
  calc
    prefixCount A n = left.card := rfl
    _ ≤ (squares ∪ hfinite.toFinset).card := Finset.card_le_card hsub
    _ ≤ squares.card + hfinite.toFinset.card := Finset.card_union_le _ _
    _ = Nat.count SparseSquare n + hfinite.toFinset.card := by
      rw [← prefixCount_core n]
      rfl

theorem tendsto_core_add_const_ratio (B : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((Nat.count SparseSquare n + B : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hB : Tendsto (fun n : ℕ => (B : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero'
    (g := fun n : ℕ =>
      ((Nat.sqrt n : ℝ) + 1) / (n : ℝ) + (B : ℝ) / (n : ℝ))
  · exact Eventually.of_forall fun n => by positivity
  · exact Eventually.of_forall fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · have hnnonneg : (0 : ℝ) ≤ n := by positivity
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hnnonneg
        norm_cast
        exact Nat.add_le_add_right (count_sparseSquare_le_sqrt_add_one n) B
  · simpa using tendsto_sparseSqrt_add_one_div.add hB

theorem relativeUpperDensity_univ_eq_zero_of_finite_diff
    {A : Language} (hfinite : (A \ core).Finite) :
    relativeUpperDensity A Set.univ = 0 := by
  unfold relativeUpperDensity
  have htendsto : Tendsto
      (fun n : ℕ =>
        (prefixCount (A ∩ (Set.univ : Set ℕ)) n : ℝ) /
          (prefixCount (Set.univ : Set ℕ) n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun n : ℕ =>
        ((Nat.count SparseSquare n + hfinite.toFinset.card : ℕ) : ℝ) /
          (n : ℝ))
    · exact Eventually.of_forall fun n => by positivity
    · exact Eventually.of_forall fun n => by
        rw [Set.inter_univ, prefixCount_univ]
        by_cases hn : n = 0
        · simp [hn]
        · apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast prefixCount_le_core_add_finite hfinite n
    · exact tendsto_core_add_const_ratio hfinite.toFinset.card
  exact htendsto.limsup_eq

theorem relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  let ratio : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  have hratio : ∀ n, ratio n ≤ 1 := by
    intro n
    by_cases hzero : prefixCount K n = 0
    · simp [ratio, hzero]
    · have hpos : (0 : ℝ) < prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      simp only [ratio]
      rw [div_le_one hpos]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  have hnonneg : ∀ n, 0 ≤ ratio n := by
    intro n
    simp only [ratio]
    positivity
  exact limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop hnonneg)
    (Eventually.of_forall hratio)

theorem output_diff_core_finite {output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit commonInput output core) :
    (Set.range output \ core).Finite := by
  obtain ⟨T, hT⟩ := hvalid
  apply (Set.finite_range (fun i : Fin T => output i)).subset
  rintro x ⟨⟨t, rfl⟩, htcore⟩
  have ht : t < T := by
    by_contra hnot
    exact htcore (hT t (Nat.le_of_not_gt hnot)).1
  exact ⟨⟨t, ht⟩, rfl⟩

theorem generatorFirst_diff_core_finite {output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit commonInput output core) :
    (GenLimit.GeneratorFirst commonInput output \ core).Finite := by
  apply (output_diff_core_finite hvalid).subset
  rintro x ⟨⟨t, htx, -⟩, hxcore⟩
  exact ⟨⟨t, htx⟩, hxcore⟩


theorem pairObstruction : PairObstruction core Set.univ commonInput := by
  intro Ω _ μ _ gen output _hfollows _hmeas hintCore _hintUniv
    hvalidCore _hvalidUniv
  have hdensityUniv : ∀ᵐ ω ∂μ,
      relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hvalidCore] with ω hω
    exact relativeUpperDensity_univ_eq_zero_of_finite_diff
      (generatorFirst_diff_core_finite hω)
  have hexpectUniv : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    rw [integral_congr_ae hdensityUniv]
    simp
  have hexpectCore : expectedUpperDensity μ core commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) core ∂μ)
          ≤ ∫ _ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hintCore
              (integrable_const (1 : ℝ))
            exact Eventually.of_forall fun ω =>
              relativeUpperDensity_le_one
                (GenLimit.GeneratorFirst commonInput (output ω)) core
      _ = 1 := by simp
  constructor
  · rw [hexpectUniv]
    linarith
  · intro hboth
    rw [hexpectUniv] at hboth
    linarith


def historyBase (input : Stream) (t : ℕ) : ℕ :=
  t + 1 + ∑ i : Fin (t + 1), input i

def squareGenerator : OnlineGenerator := fun t inputHistory _outputHistory =>
  let base := t + 1 + ∑ i, inputHistory i
  base * base

def squareOutput (input : Stream) : Stream := fun t =>
  historyBase input t * historyBase input t

theorem squareOutput_follows (input : Stream) :
    Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

theorem historyBase_mono {input : Stream} {s t : ℕ} (hst : s ≤ t) :
    historyBase input s ≤ historyBase input t := by
  have hsum :
      (∑ i ∈ Finset.range (s + 1), input i) ≤
        ∑ i ∈ Finset.range (t + 1), input i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (Nat.add_le_add_right hst 1)
    · intro i _ _
      exact Nat.zero_le _
  simp only [historyBase, Fin.sum_univ_eq_sum_range]
  omega

theorem historyBase_strictMono (input : Stream) :
    StrictMono (historyBase input) := by
  intro s t hst
  have hsum := historyBase_mono (input := input) (Nat.le_of_lt hst)
  unfold historyBase at hsum ⊢
  simp only [Fin.sum_univ_eq_sum_range] at hsum ⊢
  have hsums :
      (∑ i ∈ Finset.range (s + 1), input i) ≤
        ∑ i ∈ Finset.range (t + 1), input i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intro i _ _
      exact Nat.zero_le _
  omega

theorem input_lt_historyBase (input : Stream) {s t : ℕ} (hst : s ≤ t) :
    input s < historyBase input t := by
  have hmem : s ∈ Finset.range (t + 1) := by simp; omega
  have hle : input s ≤ ∑ i ∈ Finset.range (t + 1), input i := by
    apply Finset.single_le_sum
    · intro i _
      exact Nat.zero_le _
    · exact hmem
  unfold historyBase
  simp only [Fin.sum_univ_eq_sum_range]
  omega

theorem squareOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) core := by
  refine ⟨0, ?_⟩
  intro t _ht
  have hbasepos : 0 < historyBase input t := by
    unfold historyBase
    omega
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨historyBase input t, rfl⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hst, hs⟩ := hsample
    have hin : input s < historyBase input t :=
      input_lt_historyBase input (Nat.le_of_lt_succ hst)
    have hbasele : historyBase input t ≤ squareOutput input t := by
      unfold squareOutput
      nlinarith
    omega
  · intro s hst heq
    have hbase : historyBase input s < historyBase input t :=
      historyBase_strictMono input hst
    unfold squareOutput at heq
    nlinarith

theorem globallyFeasible_of_core_subset {r : ℕ}
    {family : Fin r → Language} (hcore : ∀ j, core ⊆ family j) :
    GloballyFeasible family := by
  refine ⟨squareGenerator, ?_⟩
  intro input _hlegal
  refine ⟨squareOutput input, squareOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := squareOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hcore j hmem, hfresh, hnovel⟩


def markerPrefix (j : ℕ) : Language :=
  {x | ∃ k, k < j ∧ sparseBetweenSquares k = x}

def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if (j : ℕ) + 1 = r then Set.univ else core ∪ markerPrefix j

theorem marker_not_core (k : ℕ) : sparseBetweenSquares k ∉ core :=
  sparseBetweenSquares_nonsquare k

theorem marker_not_markerPrefix (k : ℕ) :
    sparseBetweenSquares k ∉ markerPrefix k := by
  rintro ⟨q, hq, heq⟩
  have : q = k := sparseBetweenSquares_strictMono.injective heq
  omega

theorem marker_mem_markerPrefix {i j : ℕ} (hij : i < j) :
    sparseBetweenSquares i ∈ markerPrefix j :=
  ⟨i, hij, rfl⟩

theorem nestedFamily_core_subset (r : ℕ) (j : Fin r) :
    core ⊆ nestedFamily r j := by
  intro x hx
  unfold nestedFamily
  split
  · simp
  · exact Set.mem_union_left _ hx

theorem nestedFamily_strictlyNested {r : ℕ} (_hr : 2 ≤ r) :
    StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiNotLast : (i : ℕ) + 1 ≠ r := by
    omega
  by_cases hjLast : (j : ℕ) + 1 = r
  · have hjEq : nestedFamily r j = Set.univ := by
      simp [nestedFamily, hjLast]
    rw [hjEq]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hback
    have hmemi := hback (Set.mem_univ (sparseBetweenSquares i))
    simp only [nestedFamily, hiNotLast, if_false, Set.mem_union,
      markerPrefix] at hmemi
    rcases hmemi with hcore | hprefix
    · exact marker_not_core i hcore
    · exact marker_not_markerPrefix i hprefix
  · refine ⟨?_, ?_⟩
    · intro x hx
      simp only [nestedFamily, hiNotLast, hjLast, if_false,
        Set.mem_union, markerPrefix] at hx ⊢
      rcases hx with hcore | ⟨k, hki, hkx⟩
      · exact Or.inl hcore
      · exact Or.inr ⟨k, lt_trans hki hij, hkx⟩
    · intro hback
      have hmemj : sparseBetweenSquares i ∈ nestedFamily r j := by
        simp only [nestedFamily, hjLast, if_false, Set.mem_union]
        exact Or.inr (marker_mem_markerPrefix hij)
      have hmemi := hback hmemj
      simp only [nestedFamily, hiNotLast, if_false, Set.mem_union] at hmemi
      rcases hmemi with hcore | hprefix
      · exact marker_not_core i hcore
      · exact marker_not_markerPrefix i hprefix

theorem nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = core := by
  have hne : 1 ≠ r := by omega
  ext x
  simp [nestedFamily, markerPrefix, hne]

theorem nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [nestedFamily]
  omega

theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _hfollows _hmeas _hint hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hvalidCore : EventuallyFreshValid μ core commonInput output := by
    have h := hvalid first
    simpa [first, nestedFamily_zero hr] using h
  have hdensityUniv : ∀ᵐ ω ∂μ,
      relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hvalidCore] with ω hω
    exact relativeUpperDensity_univ_eq_zero_of_finite_diff
      (generatorFirst_diff_core_finite hω)
  refine ⟨last, ?_⟩
  have hlast : nestedFamily r last = Set.univ := by
    simpa [last] using nestedFamily_last hr
  rw [hlast]
  unfold expectedUpperDensity
  rw [integral_congr_ae hdensityUniv]
  simp

theorem manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨nestedFamily_strictlyNested hr, ?_, ?_, manyTargetObstruction hr⟩
  · intro j
    exact commonInput_legal_of_core_subset (nestedFamily_core_subset r j)
  · exact globallyFeasible_of_core_subset (nestedFamily_core_subset r)

end Case024Proof
