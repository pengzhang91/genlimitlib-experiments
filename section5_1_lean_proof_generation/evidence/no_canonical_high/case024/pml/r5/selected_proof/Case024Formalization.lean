import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Nth

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof


def squares : Set ℕ := {n | GenLimit.InfiniteContamination.SparseSquare n}

theorem squares_infinite : squares.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => n * n) := by
    intro a b hab
    nlinarith
  exact (Set.infinite_range_of_injective hinj).mono <| by
    rintro _ ⟨n, rfl⟩
    exact GenLimit.InfiniteContamination.sparseSquare_mul_self n

noncomputable def commonInput : Stage3Case024.Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation squares squaresᶜ squares_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  apply GenLimit.InfiniteContamination.sparseMergePresentation_injective squares_infinite
  rw [Set.disjoint_left]
  simp

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, GenLimit.InfiniteContamination.range_sparseMergePresentation squares_infinite]
  exact Set.union_compl_self squares

theorem commonInput_vanishing {K : Set ℕ} (hsub : squares ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise commonInput K := by
  exact GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
    squares_infinite hsub

theorem commonInput_legal {K : Set ℕ} (hsub : squares ⊆ K) :
    Stage3Case024.Legal commonInput K := by
  refine ⟨squares_infinite.mono hsub, commonInput_injective, ?_,
    commonInput_vanishing hsub⟩
  rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
  exact Set.subset_univ K

theorem prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n ≤ Nat.sqrt n + 1 := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  change ((Finset.range n).filter GenLimit.InfiniteContamination.SparseSquare).card ≤ _
  rw [← Nat.count_eq_card_filter_range]
  exact GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  let ratio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hle : ∀ n, ratio n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratio, hn]
    · dsimp [ratio]
      rw [div_le_one]
      · exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
      · exact_mod_cast Nat.pos_of_ne_zero hn
  have hnonneg : ∀ n, 0 ≤ ratio n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  rw [Stage3Case024.relativeUpperDensity]
  change limsup ratio atTop ≤ 1
  calc
    limsup ratio atTop ≤ limsup (fun _ : ℕ => (1 : ℝ)) atTop := by
      exact limsup_le_limsup (Eventually.of_forall hle)
        (hu := isCoboundedUnder_le_of_le atTop hnonneg)
        (hv := tendsto_const_nhds.isBoundedUnder_le)
    _ = 1 := tendsto_const_nhds.limsup_eq

theorem generatorFirst_prefixCount_le
    {input output : ℕ → ℕ} {K : Set ℕ} {T n : ℕ}
    (hvalid : ∀ t, T ≤ t → output t ∈ K) :
    GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n ≤
      GenLimit.PatientScope.prefixCount K n + T := by
  classical
  let early : Finset ℕ := (Finset.range T).image output
  have hsubset :
      GenLimit.PatientScope.prefixFinset (GenLimit.GeneratorFirst input output) n ⊆
        GenLimit.PatientScope.prefixFinset K n ∪ early := by
    intro x hx
    have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
    obtain ⟨t, htx, -⟩ := hxA
    by_cases ht : T ≤ t
    · exact Finset.mem_union_left _ <| GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hx).1, htx ▸ hvalid t ht⟩
    · exact Finset.mem_union_right _ <| Finset.mem_image.mpr
        ⟨t, Finset.mem_range.mpr (Nat.lt_of_not_ge ht), htx⟩
  calc
    GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n
        ≤ (GenLimit.PatientScope.prefixFinset K n ∪ early).card :=
      Finset.card_le_card hsubset
    _ ≤ (GenLimit.PatientScope.prefixFinset K n).card + early.card :=
      Finset.card_union_le (GenLimit.PatientScope.prefixFinset K n) early
    _ ≤ GenLimit.PatientScope.prefixCount K n + T := by
      unfold GenLimit.PatientScope.prefixCount
      exact Nat.add_le_add_left (Finset.card_image_le.trans_eq (Finset.card_range T)) _

theorem generatorFirst_univ_density_zero
    {input output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output squares) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := hvalid
  let ratio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n : ℝ) / (n : ℝ)
  let bound : ℕ → ℝ := fun n =>
    ((Nat.sqrt n : ℝ) + 1 + T) / (n : ℝ)
  have hratio_nonneg : ∀ n, 0 ≤ ratio n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hratio_le : ∀ n, ratio n ≤ bound n := by
    intro n
    by_cases hn : n = 0
    · simp [ratio, bound, hn]
    · apply div_le_div_of_nonneg_right
      · exact_mod_cast (generatorFirst_prefixCount_le
          (K := squares) (T := T) (n := n) (fun t ht => (hT t ht).1) |>.trans
          (Nat.add_le_add_right (prefixCount_squares_le n) T))
      · positivity
  have hbound : Tendsto bound atTop (𝓝 0) := by
    have hconst : Tendsto (fun n : ℕ => (T : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat T
    convert GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.add hconst using 1 <;>
      ext n <;> simp [bound, add_div]
  have hratio : Tendsto ratio atTop (𝓝 0) :=
    squeeze_zero hratio_nonneg
      hratio_le hbound
  change limsup (fun n : ℕ =>
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
      (GenLimit.PatientScope.prefixCount Set.univ n : ℝ)) atTop = 0
  have heq : (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
        (GenLimit.PatientScope.prefixCount Set.univ n : ℝ)) = ratio := by
    funext n
    rw [Set.inter_univ]
    simp [ratio, GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  rw [heq]
  exact hratio.limsup_eq


theorem pairObstruction :
    Stage3Case024.PairObstruction squares Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hIntSquares _ hValidSquares _
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hValidSquares.mono fun _ hvalid => generatorFirst_univ_density_zero hvalid
  have hExpectedUniv :
      Stage3Case024.expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzero]
    simp
  have hExpectedSquares :
      Stage3Case024.expectedUpperDensity μ squares commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) squares ∂μ)
          ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hIntSquares (integrable_const 1)
            exact Eventually.of_forall fun ω =>
              relativeUpperDensity_le_one
                (GenLimit.GeneratorFirst commonInput (output ω)) squares
      _ = 1 := by simp
  constructor
  · rw [hExpectedUniv]
    linarith
  · rw [hExpectedUniv]
    intro h
    linarith [h.2]

noncomputable def nonsquareAt (k : ℕ) : ℕ :=
  Nat.nth GenLimit.InfiniteContamination.SparseNonSquare k

theorem nonsquareAt_nonsquare (k : ℕ) :
    GenLimit.InfiniteContamination.SparseNonSquare (nonsquareAt k) := by
  exact Nat.nth_mem_of_infinite
    GenLimit.InfiniteContamination.sparseNonSquare_infinite k

theorem nonsquareAt_injective : Function.Injective nonsquareAt := by
  exact Nat.nth_injective GenLimit.InfiniteContamination.sparseNonSquare_infinite

noncomputable def initialNonsquares (i : ℕ) : Set ℕ :=
  {x | ∃ k < i, x = nonsquareAt k}

noncomputable def targetFamily (r : ℕ) (i : Fin r) : Set ℕ :=
  if i.val + 1 = r then Set.univ
  else squares ∪ initialNonsquares i.val

theorem squares_subset_targetFamily (r : ℕ) (i : Fin r) :
    squares ⊆ targetFamily r i := by
  intro x hx
  simp only [targetFamily]
  split_ifs
  · trivial
  · exact Set.mem_union_left _ hx

theorem targetFamily_infinite (r : ℕ) (i : Fin r) :
    (targetFamily r i).Infinite :=
  squares_infinite.mono (squares_subset_targetFamily r i)

theorem targetFamily_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  intro i j hij
  have hiNotLast : i.val + 1 ≠ r := by
    intro hi
    have hjlt : j.val < r := j.isLt
    omega
  rw [targetFamily, if_neg hiNotLast]
  by_cases hjLast : j.val + 1 = r
  · rw [targetFamily, if_pos hjLast]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hreverse
    have hwitness : nonsquareAt i.val ∈ Set.univ := Set.mem_univ _
    have hnot : nonsquareAt i.val ∉ squares ∪ initialNonsquares i.val := by
      rintro (hsquare | hinitial)
      · exact nonsquareAt_nonsquare i.val hsquare
      · obtain ⟨k, hk, heq⟩ := hinitial
        have hki : i.val = k := nonsquareAt_injective heq
        omega
    exact hnot (hreverse hwitness)
  · rw [targetFamily, if_neg hjLast]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hxSquare | hxInitial
      · exact Set.mem_union_left _ hxSquare
      · exact Set.mem_union_right _ <| by
          obtain ⟨k, hk, rfl⟩ := hxInitial
          exact ⟨k, hk.trans hij, rfl⟩
    · intro hreverse
      have hwitness : nonsquareAt i.val ∈ squares ∪ initialNonsquares j.val :=
        Set.mem_union_right _ ⟨i.val, hij, rfl⟩
      have hnot : nonsquareAt i.val ∉ squares ∪ initialNonsquares i.val := by
        rintro (hsquare | hinitial)
        · exact nonsquareAt_nonsquare i.val hsquare
        · obtain ⟨k, hk, heq⟩ := hinitial
          have hki : i.val = k := nonsquareAt_injective heq
          omega
      exact hnot (hreverse hwitness)


noncomputable def squareIndex (input : Stage3Case024.Stream) (t : ℕ) : ℕ :=
  t + 1 + ∑ s ∈ Finset.range (t + 1), input s

noncomputable def feasibleGenerator : Stage3Case024.OnlineGenerator :=
  fun t inputPrefix _ =>
    Nat.nth GenLimit.InfiniteContamination.SparseSquare
      (t + 1 + ∑ i : Fin (t + 1), inputPrefix i)

noncomputable def feasibleOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => Nat.nth GenLimit.InfiniteContamination.SparseSquare (squareIndex input t)

theorem feasibleOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows feasibleGenerator input (feasibleOutput input) := by
  intro t
  simp only [feasibleGenerator, feasibleOutput, squareIndex]
  rw [Fin.sum_univ_eq_sum_range]

theorem squareIndex_lt_squareIndex {input : Stage3Case024.Stream} {s t : ℕ}
    (hst : s < t) : squareIndex input s < squareIndex input t := by
  have hrange : Finset.range (s + 1) ⊆ Finset.range (t + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have hsum :
      ∑ k ∈ Finset.range (s + 1), input k ≤
        ∑ k ∈ Finset.range (t + 1), input k :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange fun _ _ _ => Nat.zero_le _
  simp only [squareIndex]
  omega

theorem feasibleOutput_novelSquares (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (feasibleOutput input) squares := by
  refine ⟨0, ?_⟩
  intro t _
  constructor
  · exact Nat.nth_mem_of_infinite squares_infinite (squareIndex input t)
  constructor
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    have hsSum : input s ≤ ∑ k ∈ Finset.range (t + 1), input k := by
      apply Finset.single_le_sum (fun k _ => Nat.zero_le (input k))
      exact Finset.mem_range.mpr hs
    have hInputIndex : input s < squareIndex input t := by
      simp only [squareIndex]
      omega
    have hIndexOutput : squareIndex input t ≤ feasibleOutput input t := by
      exact (Nat.nth_strictMono squares_infinite).id_le (squareIndex input t)
    exact (hInputIndex.trans_le hIndexOutput).ne heq
  · intro s hs
    have hindex : squareIndex input s < squareIndex input t :=
      squareIndex_lt_squareIndex hs
    exact (Nat.nth_strictMono squares_infinite hindex).ne

theorem feasibleOutput_novelTarget (input : Stage3Case024.Stream) (r : ℕ) (j : Fin r) :
    GenLimit.NovelGeneratesInLimit input (feasibleOutput input) (targetFamily r j) := by
  obtain ⟨T, hT⟩ := feasibleOutput_novelSquares input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨squares_subset_targetFamily r j hmem, hfresh, hnovel⟩

theorem targetFamily_globallyFeasible (r : ℕ) :
    Stage3Case024.GloballyFeasible (targetFamily r) := by
  refine ⟨feasibleGenerator, ?_⟩
  intro input _
  exact ⟨feasibleOutput input, feasibleOutput_follows input,
    fun j => feasibleOutput_novelTarget input r j⟩

theorem targetFamily_commonInput_legal (r : ℕ) (j : Fin r) :
    Stage3Case024.Legal commonInput (targetFamily r j) :=
  commonInput_legal (squares_subset_targetFamily r j)

theorem targetFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hValid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hFirstTarget : targetFamily r first = squares := by
    ext x
    simp [targetFamily, first, initialNonsquares]
    omega
  have hLastTarget : targetFamily r last = Set.univ := by
    simp [targetFamily, last]
    omega
  have hValidSquares : Stage3Case024.EventuallyFreshValid μ squares commonInput output := by
    rw [← hFirstTarget]
    exact hValid first
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hValidSquares.mono fun _ hvalid => generatorFirst_univ_density_zero hvalid
  refine ⟨last, ?_⟩
  rw [hLastTarget]
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae hzero]
  simp

end Case024Proof

open Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  have hsquaresProper : squares ⊂ Set.univ := by
    refine ⟨Set.subset_univ _, ?_⟩
    intro hreverse
    exact nonsquareAt_nonsquare 0 (hreverse (Set.mem_univ _))
  constructor
  · exact ⟨squares, Set.univ, commonInput, hsquaresProper,
      commonInput_legal Set.Subset.rfl, commonInput_legal (Set.subset_univ _),
      pairObstruction⟩
  · intro r hr
    exact ⟨targetFamily r, commonInput,
      targetFamily_strictlyNested hr,
      targetFamily_commonInput_legal r,
      targetFamily_globallyFeasible r,
      targetFamily_manyTargetObstruction hr⟩
