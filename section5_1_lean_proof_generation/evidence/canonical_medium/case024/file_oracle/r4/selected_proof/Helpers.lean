import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

open Stage3Case024
open GenLimit.InfiniteContamination

abbrev Squares : Set ℕ := {n | SparseSquare n}

lemma squares_infinite : Squares.Infinite := by
  let f : ℕ → ℕ := fun n => n * n
  have hf : Function.Injective f := by
    exact (strictMono_nat_of_lt_succ (fun n => by simp [f]; nlinarith)).injective
  exact (Set.infinite_range_of_injective hf).mono (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩)

lemma squares_compl_infinite : Squaresᶜ.Infinite := by
  simpa [Squares, SparseNonSquare] using sparseNonSquare_infinite

noncomputable def commonInput : Stream :=
  sparseMergePresentation Squares Squaresᶜ squares_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply sparseMergePresentation_injective squares_infinite
  rw [Set.disjoint_left]
  simp

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation squares_infinite]
  exact Set.union_compl_self Squares

lemma commonInput_legal_of_squares_subset {K : Language} (hK : Squares ⊆ K)
    (hKinf : K.Infinite) : Legal commonInput K := by
  refine ⟨hKinf, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ _
  · exact sparseMergePresentation_vanishingNoise_of_core_subset squares_infinite hK

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount Squares n ≤ Nat.sqrt n + 1 := by
  simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Squares, Nat.count_eq_card_filter_range] using count_sparseSquare_le_sqrt_add_one n

lemma prefixCount_le_add_finite {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let FA := GenLimit.PatientScope.prefixFinset A n
  let FB := GenLimit.PatientScope.prefixFinset B n
  let D := hfinite.toFinset
  have hsub : FA ⊆ FB ∪ D := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxb : x ∈ B
    · exact Finset.mem_union_left _ (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxb⟩)
    · exact Finset.mem_union_right _ (Set.Finite.mem_toFinset hfinite |>.2 ⟨hx'.2, hxb⟩)
  calc
    GenLimit.PatientScope.prefixCount A n = FA.card := rfl
    _ ≤ (FB ∪ D).card := Finset.card_le_card hsub
    _ ≤ FB.card + D.card := Finset.card_union_le _ _
    _ = GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := rfl

lemma finite_outside_squares_of_eventual
    {output : Stream} (h : GenLimit.NovelGeneratesInLimit commonInput output Squares) :
    (Set.range output \ Squares).Finite := by
  obtain ⟨T, hT⟩ := h
  apply ((Set.finite_Iio T).image output).subset
  rintro x ⟨⟨t, rfl⟩, hnot⟩
  have ht : t < T := by
    by_contra hn
    exact hnot (hT t (Nat.le_of_not_gt hn)).1
  exact ⟨t, ht, rfl⟩

lemma generatorFirst_subset_range (input output : Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, htx, -⟩
  exact ⟨t, htx⟩

lemma finite_generatorFirst_outside_squares
    {output : Stream} (h : GenLimit.NovelGeneratesInLimit commonInput output Squares) :
    (GenLimit.GeneratorFirst commonInput output \ Squares).Finite := by
  apply (finite_outside_squares_of_eventual h).subset
  intro x hx
  exact ⟨generatorFirst_subset_range commonInput output hx.1, hx.2⟩

lemma ratio_tendsto_zero_of_finite_outside_squares
    {A : Set ℕ} (hfinite : (A \ Squares).Finite) :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ (Set.univ : Set ℕ)) n : ℝ) /
        (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ))
      atTop (𝓝 0) := by
  have hupper : ∀ n : ℕ,
      (GenLimit.PatientScope.prefixCount (A ∩ (Set.univ : Set ℕ)) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ) ≤
        ((Nat.sqrt n : ℝ) + 1 + hfinite.toFinset.card) / n := by
    intro n
    simp only [Set.inter_univ, prefixCount_univ]
    by_cases hn : n = 0
    · simp [hn]
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast (prefixCount_le_add_finite hfinite n |>.trans
        (Nat.add_le_add_right (prefixCount_squares_le n) _))
  have hbound : Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + hfinite.toFinset.card) / n)
      atTop (𝓝 0) := by
    have hc : Tendsto
        (fun n : ℕ => (hfinite.toFinset.card : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [add_div, Nat.cast_ofNat, Nat.cast_add, add_zero] using
      tendsto_sparseSqrt_add_one_div.add hc
  apply squeeze_zero
  · intro n
    positivity
  · exact hupper
  · exact hbound

lemma relativeUpperDensity_univ_eq_zero_of_finite_outside_squares
    {A : Set ℕ} (hfinite : (A \ Squares).Finite) :
    relativeUpperDensity A Set.univ = 0 := by
  unfold relativeUpperDensity
  exact (ratio_tendsto_zero_of_finite_outside_squares hfinite).limsup_eq

lemma relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · apply Eventually.of_forall
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n

lemma relativeUpperDensity_nonneg (A K : Language) :
    0 ≤ relativeUpperDensity A K := by
  unfold relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall (fun n => by positivity)
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        exact_mod_cast prefixCount_mono Set.inter_subset_right n⟩

lemma pairObstruction : PairObstruction Squares Set.univ commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas hint0 hint1 hev0 _hev1
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hev0.mono (fun ω hω =>
      relativeUpperDensity_univ_eq_zero_of_finite_outside_squares
        (finite_generatorFirst_outside_squares hω))
  have e1zero : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    rw [integral_congr_ae hzero]
    simp
  have e0le : expectedUpperDensity μ Squares commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Squares ∂μ)
          ≤ ∫ _ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hint0 (integrable_const 1)
            exact Filter.Eventually.of_forall (fun ω => relativeUpperDensity_le_one _ _)
      _ = 1 := by simp
  constructor
  · simpa [e1zero] using e0le
  · intro hboth
    rw [e1zero] at hboth
    linarith

noncomputable def freshSquareGenerator : OnlineGenerator := fun t input _output =>
  let M := Finset.univ.sup (fun i : Fin (t + 1) => input i)
  (M + t + 1) * (M + t + 1)

lemma freshSquareGenerator_mem (t : ℕ) (input : Fin (t + 1) → ℕ)
    (output : Fin t → ℕ) : freshSquareGenerator t input output ∈ Squares := by
  exact ⟨_, rfl⟩

lemma freshSquareGenerator_gt_input (t : ℕ) (input : Fin (t + 1) → ℕ)
    (output : Fin t → ℕ) (i : Fin (t + 1)) :
    input i < freshSquareGenerator t input output := by
  dsimp [freshSquareGenerator]
  have hi : input i ≤ Finset.univ.sup (fun j : Fin (t + 1) => input j) :=
    Finset.le_sup (Finset.mem_univ i)
  have hpos : 0 < Finset.univ.sup (fun j : Fin (t + 1) => input j) + t + 1 := by omega
  nlinarith

lemma freshSquareGenerator_strict_time {input output : Stream}
    (hfollow : Follows freshSquareGenerator input output) : StrictMono output := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [hfollow t, hfollow (t + 1)]
  dsimp [freshSquareGenerator]
  let M := Finset.univ.sup (fun i : Fin (t + 1) => input i)
  let N := Finset.univ.sup (fun i : Fin (t + 2) => input i)
  have hMN : M ≤ N := by
    apply Finset.sup_le
    intro i _
    exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin (t + 2) => input j)
      (Finset.mem_univ ⟨i, Nat.lt_succ_of_lt i.isLt⟩)
  have hpos : 0 < M + t + 1 := by omega
  nlinarith

lemma freshSquareGenerator_valid {input output : Stream}
    (hfollow : Follows freshSquareGenerator input output) :
    GenLimit.NovelGeneratesInLimit input output Squares := by
  refine ⟨0, ?_⟩
  intro t _
  constructor
  · rw [hfollow t]
    exact freshSquareGenerator_mem _ _ _
  constructor
  · intro hsamp
    rw [GenLimit.mem_sample_iff] at hsamp
    obtain ⟨i, hi, hieq⟩ := hsamp
    have hlt := freshSquareGenerator_gt_input t (fun i => input i) (fun i => output i)
      ⟨i, hi⟩
    rw [← hfollow t, hieq] at hlt
    omega
  · intro s hst
    exact ne_of_lt (freshSquareGenerator_strict_time hfollow hst)

noncomputable def freshSquareOutput (input : Stream) : Stream := fun t =>
  freshSquareGenerator t (fun i => input i) (fun i => 0)

lemma freshSquareOutput_follows (input : Stream) :
    Follows freshSquareGenerator input (freshSquareOutput input) := by
  intro t
  rfl

lemma globallyFeasible {r : ℕ} (family : Fin r → Language)
    (hsquares : ∀ j, Squares ⊆ family j) : GloballyFeasible family := by
  refine ⟨freshSquareGenerator, ?_⟩
  intro input _hlegal
  refine ⟨freshSquareOutput input, freshSquareOutput_follows input, ?_⟩
  intro j
  have hsq := freshSquareGenerator_valid (freshSquareOutput_follows input)
  obtain ⟨T, hT⟩ := hsq
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hsquares j hmem, hfresh, hnovel⟩

lemma manyObstruction {r : ℕ} (family : Fin r → Language)
    (hzero : ∃ j, family j = Set.univ)
    (hbase : ∃ j, family j = Squares) :
    ManyTargetObstruction family commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas _hint hev
  obtain ⟨j0, hj0⟩ := hbase
  obtain ⟨j1, hj1⟩ := hzero
  refine ⟨j1, ?_⟩
  rw [hj1]
  unfold expectedUpperDensity
  calc
    (∫ ω, relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ ∂μ) =
        ∫ _ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hev j0] with ω hω
      rw [hj0] at hω
      exact relativeUpperDensity_univ_eq_zero_of_finite_outside_squares
        (finite_generatorFirst_outside_squares hω)
    _ = 0 := by simp

end Case024
