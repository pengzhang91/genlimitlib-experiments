import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.MeasureTheory.Integral.Bochner.L1

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof

open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

abbrev squareLanguage : Stage3Case024.Language := {n | SparseSquare n}

theorem squareLanguage_infinite : squareLanguage.Infinite := by
  apply (Set.infinite_range_of_injective (f := fun n : ℕ => n * n))
  intro a b hab
  nlinarith

theorem squareLanguage_compl_infinite : squareLanguageᶜ.Infinite := by
  apply (Set.infinite_range_of_injective sparseBetweenSquares_strictMono.injective).mono
  rintro _ ⟨k, rfl⟩
  exact sparseBetweenSquares_nonsquare k

noncomputable def commonInput : Stage3Case024.Stream :=
  squareSparseMerge squareLanguage squareLanguageᶜ
    squareLanguage_infinite squareLanguage_compl_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  exact squareSparseMerge_injective squareLanguage_infinite
    squareLanguage_compl_infinite (by
      rw [Set.disjoint_compl_right_iff_subset])

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_squareSparseMerge squareLanguage_infinite
    squareLanguage_compl_infinite, Set.union_compl_self]

theorem commonInput_legal (K : Stage3Case024.Language)
    (hcore : squareLanguage ⊆ K) : Stage3Case024.Legal commonInput K := by
  refine ⟨squareLanguage_infinite.mono hcore, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      squareLanguage_infinite squareLanguage_compl_infinite hcore

noncomputable def freshSquareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ =>
    let bound := 1 + t + Finset.univ.sum input
    bound * bound

noncomputable def freshSquareOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => freshSquareGenerator t (fun i => input i) (fun _ => 0)

theorem freshSquareOutput_strictMono (input : Stage3Case024.Stream) :
    StrictMono (freshSquareOutput input) := by
  apply strictMono_nat_of_lt_succ
  intro t
  simp only [freshSquareOutput, freshSquareGenerator]
  have hsum :
      Finset.univ.sum (fun i : Fin (t + 1) => input i) ≤
        Finset.univ.sum (fun i : Fin (t + 2) => input i) := by
    calc
      Finset.univ.sum (fun i : Fin (t + 1) => input i) =
          Finset.univ.sum (fun i : Fin (t + 1) => input i.castSucc) := by rfl
      _ ≤ Finset.univ.sum (fun i : Fin (t + 1) => input i.castSucc) +
          input (Fin.last (t + 1)) := Nat.le_add_right _ _
      _ = Finset.univ.sum (fun i : Fin (t + 2) => input i) :=
        (Fin.sum_univ_castSucc (fun i : Fin (t + 2) => input i)).symm
  have hbound :
      1 + t + Finset.univ.sum (fun i : Fin (t + 1) => input i) <
        1 + (t + 1) + Finset.univ.sum (fun i : Fin (t + 2) => input i) := by
    omega
  exact Nat.mul_self_lt_mul_self hbound

theorem freshSquareGenerator_spec (input : Stage3Case024.Stream) :
    ∃ output : Stage3Case024.Stream,
      Stage3Case024.Follows freshSquareGenerator input output ∧
      GenLimit.NovelGeneratesInLimit input output squareLanguage := by
  refine ⟨freshSquareOutput input, ?_, 0, ?_⟩
  · intro t
    simp [freshSquareOutput, freshSquareGenerator]
  · intro t _
    simp only [freshSquareOutput, freshSquareGenerator]
    let bound := 1 + t +
      Finset.univ.sum (fun i : Fin (t + 1) => input i)
    have hinput (s : ℕ) (hs : s < t + 1) : input s < bound * bound := by
      let i : Fin (t + 1) := ⟨s, hs⟩
      have hle : input i ≤ Finset.univ.sum (fun j : Fin (t + 1) => input j) := by
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin (t + 1) => input j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      change input s ≤ Finset.univ.sum (fun j : Fin (t + 1) => input j) at hle
      have hib : input s < bound := by omega
      have hb : 0 < bound := by simp [bound]
      nlinarith
    refine ⟨⟨bound, rfl⟩, ?_, ?_⟩
    · intro hmem
      rw [GenLimit.mem_sample_iff] at hmem
      rcases hmem with ⟨s, hs, heq⟩
      exact (Nat.ne_of_lt (hinput s hs)) heq
    · intro s hs heq
      exact (freshSquareOutput_strictMono input hs).ne heq

theorem generatorFirst_subset_range (input output : Stage3Case024.Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro z ⟨t, ht, -⟩
  exact ⟨t, ht⟩

theorem range_diff_finite_of_eventual_square
    {input output : Stage3Case024.Stream}
    (h : GenLimit.NovelGeneratesInLimit input output squareLanguage) :
    (Set.range output \ squareLanguage).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_range (f := fun t : Fin T => output t)).subset
  rintro z ⟨⟨t, rfl⟩, ht⟩
  have hlt : t < T := by
    by_contra hnot
    exact ht (hT t (Nat.le_of_not_gt hnot)).1
  exact ⟨⟨t, hlt⟩, rfl⟩

theorem prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

theorem prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simp only [Set.mem_union]
  change ((Finset.range n).filter (fun x => x ∈ A ∨ x ∈ B)).card ≤ _
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

theorem prefixCount_square (n : ℕ) :
    GenLimit.PatientScope.prefixCount squareLanguage n =
      Nat.count SparseSquare n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  rw [Nat.count_eq_card_filter_range]
  change ((Finset.range n).filter SparseSquare).card = _
  rfl

theorem relativeUpperDensity_le_one (A K : Stage3Case024.Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.limsup_le_of_le
    (hf := Filter.isCoboundedUnder_le_of_le atTop (fun n => by positivity))
  filter_upwards with n
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · rw [div_le_one (by positivity)]
    exact_mod_cast prefixCount_mono Set.inter_subset_right n

theorem relativeUpperDensity_univ_eq_zero_of_finite_diff
    (A : Stage3Case024.Language) (hfinite : (A \ squareLanguage).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  let F := A \ squareLanguage
  have hsubset : A ⊆ squareLanguage ∪ F := by
    intro x hx
    by_cases hs : x ∈ squareLanguage
    · exact Or.inl hs
    · exact Or.inr ⟨hx, hs⟩
  have hbound (n : ℕ) :
      GenLimit.PatientScope.prefixCount A n ≤
        Nat.sqrt n + 1 + hfinite.toFinset.card := by
    calc
      GenLimit.PatientScope.prefixCount A n ≤
          GenLimit.PatientScope.prefixCount (squareLanguage ∪ F) n :=
        prefixCount_mono hsubset n
      _ ≤ GenLimit.PatientScope.prefixCount squareLanguage n +
          GenLimit.PatientScope.prefixCount F n := prefixCount_union_le _ _ _
      _ ≤ (Nat.sqrt n + 1) + hfinite.toFinset.card := by
        apply Nat.add_le_add
        · rw [prefixCount_square]
          exact count_sparseSquare_le_sqrt_add_one n
        · unfold GenLimit.PatientScope.prefixCount
          apply Finset.card_le_card
          intro x hx
          exact (Set.Finite.mem_toFinset hfinite).2
            (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
  have htend : Tendsto
      (fun n : ℕ => (((Nat.sqrt n : ℝ) + 1) + hfinite.toFinset.card) / n)
      atTop (𝓝 0) := by
    have hc : Tendsto (fun n : ℕ => (hfinite.toFinset.card : ℝ) / n)
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    convert tendsto_sparseSqrt_add_one_div.add hc using 1
    · funext n
      rw [add_div]
    · norm_num
  have hratio : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          GenLimit.PatientScope.prefixCount Set.univ n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) htend
    · intro n
      positivity
    · intro n
      by_cases hn : n = 0
      · simp [hn, prefixCount_univ]
      · simp only [Set.inter_univ, prefixCount_univ]
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hbound n
        · positivity
  exact hratio.limsup_eq

theorem generatorFirst_density_zero
    {input output : Stage3Case024.Stream}
    (h : GenLimit.NovelGeneratesInLimit input output squareLanguage) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  apply relativeUpperDensity_univ_eq_zero_of_finite_diff
  exact (range_diff_finite_of_eventual_square h).subset
    (Set.diff_subset_diff_left (generatorFirst_subset_range input output))

theorem pairObstruction :
    Stage3Case024.PairObstruction squareLanguage Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hint0 _ hevent0 _
  have hz : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hevent0.mono (fun _ h => generatorFirst_density_zero h)
  have hle : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) squareLanguage ≤ 1 :=
    Filter.Eventually.of_forall fun _ => relativeUpperDensity_le_one _ _
  have eint1 : Stage3Case024.expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hz, integral_zero]
  have eint0 : Stage3Case024.expectedUpperDensity μ squareLanguage commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    simpa using integral_mono_ae hint0 (integrable_const 1) hle
  constructor
  · rw [eint1, add_zero]
    exact eint0
  · rw [eint1]
    norm_num

def addedPoints (j : ℕ) : Set ℕ :=
  {x | ∃ k < j, x = sparseBetweenSquares k}

def targetFamily (r : ℕ) (j : Fin r) : Stage3Case024.Language :=
  if (j : ℕ) + 1 = r then Set.univ else squareLanguage ∪ addedPoints j

theorem square_subset_targetFamily (r : ℕ) (j : Fin r) :
    squareLanguage ⊆ targetFamily r j := by
  intro x hx
  simp only [targetFamily]
  split <;> simp_all

theorem targetFamily_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  intro i j hij
  have hi_not_last : (i : ℕ) + 1 ≠ r := by omega
  simp only [targetFamily, hi_not_last, if_false]
  by_cases hj_last : (j : ℕ) + 1 = r
  · simp only [hj_last, if_true]
    rw [Set.ssubset_iff_of_subset (Set.subset_univ _)]
    refine ⟨sparseBetweenSquares j, Set.mem_univ _, ?_⟩
    intro hmem
    rcases hmem with hsquare | hadd
    · exact sparseBetweenSquares_nonsquare j hsquare
    · rcases hadd with ⟨k, hk, heq⟩
      have : k = j := sparseBetweenSquares_strictMono.injective heq.symm
      omega
  · simp only [hj_last, if_false]
    have hsub : squareLanguage ∪ addedPoints ↑i ⊆
        squareLanguage ∪ addedPoints ↑j := by
      intro x hx
      rcases hx with hx | ⟨k, hk, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, hk.trans hij, rfl⟩
    rw [Set.ssubset_iff_of_subset hsub]
    refine ⟨sparseBetweenSquares i, Or.inr ⟨i, hij, rfl⟩, ?_⟩
    intro hmem
    rcases hmem with hsquare | ⟨k, hk, heq⟩
    · exact sparseBetweenSquares_nonsquare i hsquare
    · have : (i : ℕ) = k := sparseBetweenSquares_strictMono.injective heq
      omega

theorem freshSquareGenerator_global (r : ℕ) :
    Stage3Case024.GloballyFeasible (targetFamily r) := by
  refine ⟨freshSquareGenerator, ?_⟩
  intro input _
  obtain ⟨output, hfollow, hnovel⟩ := freshSquareGenerator_spec input
  exact ⟨output, hfollow, fun j => by
    obtain ⟨T, hT⟩ := hnovel
    refine ⟨T, fun t ht => ?_⟩
    obtain ⟨hmem, hfresh, hnew⟩ := hT t ht
    exact ⟨square_subset_targetFamily r j hmem, hfresh, hnew⟩⟩

theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hevent
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hlast : (last : ℕ) + 1 = r := by simp [last]; omega
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    (hevent ⟨0, by omega⟩).mono (fun _ h =>
      generatorFirst_density_zero
        (by
          obtain ⟨T, hT⟩ := h
          refine ⟨T, fun t ht => ?_⟩
          have hone : 1 ≠ r := by omega
          simpa [targetFamily, addedPoints, hone] using hT t ht))
  unfold Stage3Case024.expectedUpperDensity
  simp only [targetFamily, hlast, if_true]
  rw [integral_congr_ae hzero, integral_zero]

theorem manyTargetWitness (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (targetFamily r) commonInput := by
  refine ⟨targetFamily_strictlyNested hr, ?_, freshSquareGenerator_global r,
    manyTargetObstruction hr⟩
  intro j
  exact commonInput_legal _ (square_subset_targetFamily r j)

end Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024Proof.squareLanguage, Set.univ,
      Case024Proof.commonInput, ?_, ?_, ?_, Case024Proof.pairObstruction⟩
    · rw [Set.ssubset_iff_of_subset (Set.subset_univ _)]
      exact ⟨GenLimit.InfiniteContamination.sparseBetweenSquares 0, Set.mem_univ _,
        GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare 0⟩
    · exact Case024Proof.commonInput_legal _ (fun _ h => h)
    · exact Case024Proof.commonInput_legal _ (Set.subset_univ _)
  · intro r hr
    exact ⟨Case024Proof.targetFamily r, Case024Proof.commonInput,
      Case024Proof.manyTargetWitness r hr⟩
