import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024Proof
open Stage3Case024
open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

def squares : Language := {n | SparseSquare n}

theorem squares_infinite : squares.Infinite := by
  have hmono : StrictMono (fun n : ℕ => n * n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    nlinarith
  apply (Set.infinite_range_of_injective hmono.injective).mono
  rintro _ ⟨n, rfl⟩
  exact ⟨n, rfl⟩

noncomputable def commonInput : Stream :=
  sparseMergePresentation squares squaresᶜ squares_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  apply sparseMergePresentation_injective squares_infinite
  rw [Set.disjoint_left]
  exact fun _ hx hxc => hxc hx

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation squares_infinite]
  exact Set.union_compl_self squares

theorem commonInput_legal {K : Language} (hcore : squares ⊆ K)
    (hK : K.Infinite) : Legal commonInput K := by
  refine ⟨hK, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact sparseMergePresentation_vanishingNoise_of_core_subset
      squares_infinite hcore

noncomputable def ambientOrder : GenLimit.KleinbergWei.OrderedLanguage where
  carrier := Set.univ
  enumeration := id
  enumeration_injective := Function.injective_id
  range_enumeration := Set.range_id

theorem ambient_prefixCount (A : Language) (n : ℕ) :
    ambientOrder.prefixCount A n = GenLimit.PatientScope.prefixCount A n := by
  classical
  simp [ambientOrder, GenLimit.KleinbergWei.OrderedLanguage.prefixCount,
    GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

theorem relativeUpperDensity_univ (A : Language) :
    relativeUpperDensity A Set.univ = ambientOrder.upperDensity A := by
  unfold relativeUpperDensity GenLimit.KleinbergWei.OrderedLanguage.upperDensity
    GenLimit.KleinbergWei.OrderedLanguage.prefixRatio
  apply limsup_congr
  filter_upwards with n
  have hnum : GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n =
      GenLimit.PatientScope.prefixCount A n := by
    unfold GenLimit.PatientScope.prefixCount
    congr 1
    ext x
    simp [GenLimit.PatientScope.prefixFinset]
  have hden : GenLimit.PatientScope.prefixCount Set.univ n = n := by
    simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  rw [hnum, hden]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
    rfl

theorem squares_prefixCount (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n = Nat.count SparseSquare n := by
  letI : DecidablePred SparseSquare := Classical.decPred _
  rw [Nat.count_eq_card_filter_range]
  rfl

theorem squares_upperDensity_zero : ambientOrder.upperDensity squares = 0 := by
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / (n : ℝ))
  · exact fun n => ambientOrder.prefixRatio_nonneg squares n
  · intro n
    by_cases hn : n = 0
    · subst n
      simp
    · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
      rw [ambient_prefixCount, squares_prefixCount]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast count_sparseSquare_le_sqrt_add_one n
      · positivity
  · exact tendsto_sparseSqrt_add_one_div

theorem relativeUpperDensity_univ_eq_zero_of_finite_diff
    {A : Language} (hfinite : (A \ squares).Finite) :
    relativeUpperDensity A Set.univ = 0 := by
  rw [relativeUpperDensity_univ]
  apply le_antisymm
  · calc
      ambientOrder.upperDensity A ≤
          ambientOrder.upperDensity (squares ∪ (A \ squares)) := by
            apply ambientOrder.upperDensity_mono
            intro x hx
            by_cases hs : x ∈ squares
            · exact Or.inl hs
            · exact Or.inr ⟨hx, hs⟩
      _ ≤ ambientOrder.upperDensity squares +
          ambientOrder.upperDensity (A \ squares) :=
            ambientOrder.upperDensity_union_le _ _
      _ = 0 := by
        rw [squares_upperDensity_zero,
          ambientOrder.upperDensity_eq_zero_of_finite hfinite, add_zero]
  · exact ambientOrder.upperDensity_nonneg A

theorem relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · filter_upwards with n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · rw [div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_card (by
        intro x hx
        exact GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hx).1,
            (GenLimit.PatientScope.mem_prefixFinset.mp hx).2.2⟩)

theorem generatorFirst_diff_squares_finite {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output squares) :
    (GenLimit.GeneratorFirst input output \ squares).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_range (fun t : Fin T => output t)).subset
  intro x hx
  obtain ⟨⟨t, htx, -⟩, hxs⟩ := hx
  by_cases ht : t < T
  · exact ⟨⟨t, ht⟩, htx⟩
  · have hTt : T ≤ t := Nat.le_of_not_gt ht
    exact (hxs (htx ▸ (hT t hTt).1)).elim

theorem eventual_squares_gives_zero {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (input : Stream) (output : Ω → Stream)
    (h : EventuallyFreshValid μ squares input output) :
    ∀ᵐ ω ∂μ, relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Set.univ = 0 := by
  filter_upwards [h] with ω hω
  exact relativeUpperDensity_univ_eq_zero_of_finite_diff
    (generatorFirst_diff_squares_finite hω)

def extras (i : ℕ) : Language :=
  {x | ∃ k, k < i ∧ Nat.nth SparseNonSquare k = x}

def nestedFamily (r : ℕ) (i : Fin r) : Language :=
  if (i : ℕ) + 1 = r then Set.univ else squares ∪ extras i

theorem squares_subset_nestedFamily {r : ℕ} (i : Fin r) :
    squares ⊆ nestedFamily r i := by
  intro x hx
  unfold nestedFamily
  split
  · exact Set.mem_univ x
  · exact Or.inl hx

theorem nestedFamily_infinite {r : ℕ} (i : Fin r) :
    (nestedFamily r i).Infinite :=
  squares_infinite.mono (squares_subset_nestedFamily i)

theorem nth_nonsquare (k : ℕ) : Nat.nth SparseNonSquare k ∉ squares := by
  exact Nat.nth_mem_of_infinite sparseNonSquare_infinite k

theorem nth_nonsquare_not_extras (i : ℕ) :
    Nat.nth SparseNonSquare i ∉ extras i := by
  rintro ⟨k, hki, hk⟩
  have hinj := Nat.nth_injective sparseNonSquare_infinite hk
  omega

theorem strictlyNested_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiNotLast : (i : ℕ) + 1 ≠ r := by omega
  by_cases hjLast : (j : ℕ) + 1 = r
  · rw [nestedFamily, if_neg hiNotLast, nestedFamily, if_pos hjLast]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hEq
    have hmem : Nat.nth SparseNonSquare i ∈ squares ∪ extras i :=
      hEq (Set.mem_univ _)
    rcases hmem with hs | he
    · exact nth_nonsquare i hs
    · exact nth_nonsquare_not_extras i he
  · rw [nestedFamily, if_neg hiNotLast, nestedFamily, if_neg hjLast]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hs | ⟨k, hki, rfl⟩
      · exact Or.inl hs
      · exact Or.inr ⟨k, lt_trans hki hij, rfl⟩
    · intro hEq
      have hmem : Nat.nth SparseNonSquare i ∈ squares ∪ extras i :=
        hEq (Or.inr ⟨i, hij, rfl⟩)
      rcases hmem with hs | he
      · exact nth_nonsquare i hs
      · exact nth_nonsquare_not_extras i he

def squareGenerator : OnlineGenerator := fun t input _ =>
  let b := t + 1 + ∑ i, input i
  b * b

def squareOutput (input : Stream) : Stream := fun t =>
  squareGenerator t (fun i => input i) (fun _ => 0)

theorem squareOutput_follows (input : Stream) :
    Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

theorem input_lt_squareOutput (input : Stream) (t : ℕ) (i : Fin (t + 1)) :
    input i < squareOutput input t := by
  have hle : input i ≤ ∑ j : Fin (t + 1), input j := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin (t + 1) => input j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  simp only [squareOutput, squareGenerator]
  nlinarith

theorem squareOutput_strictMono (input : Stream) :
    StrictMono (squareOutput input) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have hsum : (∑ i : Fin (t + 2), input i) =
      (∑ i : Fin (t + 1), input i) + input (t + 1) := by
    rw [Fin.sum_univ_castSucc]
    rfl
  simp only [squareOutput, squareGenerator]
  rw [hsum]
  apply Nat.mul_self_lt_mul_self
  omega

theorem squareOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) squares := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨t + 1 + ∑ i : Fin (t + 1), input i, rfl⟩
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨i, hi, heq⟩ := hmem
    exact (ne_of_lt (input_lt_squareOutput input t ⟨i, hi⟩)) heq
  · intro s hs
    exact ne_of_lt (squareOutput_strictMono input hs)

theorem globallyFeasible_nestedFamily {r : ℕ} :
    GloballyFeasible (nestedFamily r) := by
  refine ⟨squareGenerator, ?_⟩
  intro input _
  refine ⟨squareOutput input, squareOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := squareOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hs, hfresh, hnovel⟩ := hT t ht
  exact ⟨squares_subset_nestedFamily j hs, hfresh, hnovel⟩

theorem pairObstruction : PairObstruction squares Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hIntSquares hIntUniv hSquares _
  have hzeroAE := eventual_squares_gives_zero μ commonInput output hSquares
  have hzero : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    rw [integral_congr_ae hzeroAE]
    simp
  have hle : expectedUpperDensity μ squares commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    have hone : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) squares ∂μ)
          ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hIntSquares hone
            exact Filter.Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · rw [hzero, add_zero]
    exact hle
  · rw [hzero]
    norm_num

theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ hInt hValid
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hfirst : nestedFamily r ⟨0, by omega⟩ = squares := by
    ext x
    simp [nestedFamily, extras]
    omega
  have hlastEq : (last : ℕ) + 1 = r := by
    dsimp [last]
    omega
  have hlast : nestedFamily r last = Set.univ := by
    simp [nestedFamily, hlastEq]
  have hzeroAE := eventual_squares_gives_zero μ commonInput output
    (hfirst ▸ hValid ⟨0, by omega⟩)
  rw [hlast]
  unfold expectedUpperDensity
  rw [integral_congr_ae hzeroAE]
  simp

theorem manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨strictlyNested_nestedFamily hr, ?_, globallyFeasible_nestedFamily,
    manyTargetObstruction hr⟩
  intro j
  exact commonInput_legal (squares_subset_nestedFamily j) (nestedFamily_infinite j)

end Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024Proof.squares, Set.univ, Case024Proof.commonInput, ?_,
      Case024Proof.commonInput_legal Set.Subset.rfl Case024Proof.squares_infinite,
      Case024Proof.commonInput_legal (Set.subset_univ _) Set.infinite_univ,
      Case024Proof.pairObstruction⟩
    exact ⟨Set.subset_univ _, by
      intro h
      have h2 : 2 ∈ Case024Proof.squares := h (Set.mem_univ 2)
      obtain ⟨k, hk⟩ := h2
      have hklt : k < 3 := by nlinarith
      interval_cases k <;> norm_num at hk⟩
  · intro r hr
    exact ⟨Case024Proof.nestedFamily r, Case024Proof.commonInput,
      Case024Proof.manyTargetWitness hr⟩
