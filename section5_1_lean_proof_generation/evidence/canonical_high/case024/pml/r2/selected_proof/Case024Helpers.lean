import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Support.Fresh
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024Helpers

open GenLimit.InfiniteContamination

abbrev Sparse : Set ℕ := {n | SparseSquare n}
abbrev Exceptional : Set ℕ := Sparseᶜ

private theorem squareMap_injective : Function.Injective (fun n : ℕ => n * n) := by
  intro a b hab
  nlinarith [Nat.zero_le a, Nat.zero_le b]

theorem sparse_infinite : Sparse.Infinite := by
  apply (Set.infinite_range_of_injective squareMap_injective).mono
  rintro _ ⟨n, rfl⟩
  exact sparseSquare_mul_self n

theorem exceptional_infinite : Exceptional.Infinite := by
  simpa [Exceptional, Sparse, SparseNonSquare] using sparseNonSquare_infinite

noncomputable def commonStream : Stage3Case024.Stream :=
  squareSparseMerge Sparse Exceptional sparse_infinite exceptional_infinite

theorem commonStream_injective : Function.Injective commonStream := by
  apply squareSparseMerge_injective sparse_infinite exceptional_infinite
  rw [Set.disjoint_left]
  intro x hx hxc
  exact hxc hx

theorem commonStream_range : Set.range commonStream = Set.univ := by
  rw [commonStream, range_squareSparseMerge sparse_infinite exceptional_infinite]
  simp [Exceptional]

theorem commonStream_vanishing (K : Set ℕ) (hK : Sparse ⊆ K) :
    VanishingNoise commonStream K := by
  exact squareSparseMerge_vanishingNoise_of_core_subset
    sparse_infinite exceptional_infinite hK

theorem commonStream_legal (K : Stage3Case024.Language)
    (hKinf : K.Infinite) (hK : Sparse ⊆ K) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨hKinf, commonStream_injective, ?_, commonStream_vanishing K hK⟩
  intro x hx
  rw [commonStream_range]
  exact Set.mem_univ x

theorem sparse_legal : Stage3Case024.Legal commonStream Sparse :=
  commonStream_legal Sparse sparse_infinite Set.Subset.rfl

theorem univ_legal : Stage3Case024.Legal commonStream Set.univ :=
  commonStream_legal Set.univ Set.infinite_univ (Set.subset_univ _)

end Case024Helpers

namespace Case024Helpers

open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

private theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

@[simp] theorem prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · apply Eventually.of_forall
    intro n
    have hcount := prefixCount_mono (A := A ∩ K) (B := K) Set.inter_subset_right n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      rw [div_le_one hpos]
      exact_mod_cast hcount

private theorem generatorFirst_subset_range (input output : ℕ → ℕ) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, htx, -⟩
  exact ⟨t, htx⟩

private theorem range_diff_sparse_finite {output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit output output Sparse := by
      assumption) : (Set.range output \ Sparse).Finite := by
  obtain ⟨T, hT⟩ := hvalid
  apply ((Set.finite_Iio T).image output).subset
  rintro x ⟨⟨t, rfl⟩, hnot⟩
  have ht : t < T := by
    by_contra hge
    exact hnot (hT t (Nat.le_of_not_gt hge)).1
  exact ⟨t, ht, rfl⟩

private theorem first_subset_sparse_union_finite
    {input output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Sparse) :
    ∃ F : Set ℕ, F.Finite ∧
      GenLimit.GeneratorFirst input output ⊆ Sparse ∪ F := by
  let F := Set.range output \ Sparse
  have hF : F.Finite := by
    obtain ⟨T, hT⟩ := hvalid
    apply ((Set.finite_Iio T).image output).subset
    rintro x ⟨⟨t, rfl⟩, hnot⟩
    have ht : t < T := by
      by_contra hge
      exact hnot (hT t (Nat.le_of_not_gt hge)).1
    exact ⟨t, ht, rfl⟩
  refine ⟨F, hF, ?_⟩
  intro x hx
  have hrange := generatorFirst_subset_range input output hx
  by_cases hs : x ∈ Sparse
  · exact Or.inl hs
  · exact Or.inr ⟨hrange, hs⟩

private theorem prefixCount_le_sparse_add_finite
    {A F : Set ℕ} (hF : F.Finite) (hA : A ⊆ Sparse ∪ F) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      Nat.count SparseSquare n + hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  calc
    (GenLimit.PatientScope.prefixFinset A n).card ≤
        (GenLimit.PatientScope.prefixFinset Sparse n ∪ hF.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      rw [GenLimit.PatientScope.mem_prefixFinset] at hx
      rcases hA hx.2 with hs | hfin
      · apply Finset.mem_union_left
        rw [GenLimit.PatientScope.mem_prefixFinset]
        exact ⟨hx.1, hs⟩
      · apply Finset.mem_union_right
        exact hF.mem_toFinset.mpr hfin
    _ ≤ (GenLimit.PatientScope.prefixFinset Sparse n).card + hF.toFinset.card :=
      Finset.card_union_le _ _
    _ = Nat.count SparseSquare n + hF.toFinset.card := by
      rw [Nat.count_eq_card_filter_range]
      rfl

private theorem sparse_add_const_ratio_tendsto (c : ℕ) :
    Tendsto (fun n : ℕ =>
      (((Nat.sqrt n + 1 + c : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ => (c : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hs := tendsto_sparseSqrt_add_one_div.add hc
  convert hs using 1
  · funext n
    push_cast
    rw [add_div]
  · norm_num

private theorem ratio_univ_tendsto_zero
    {A F : Set ℕ} (hF : F.Finite) (hA : A ⊆ Sparse ∪ F) :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [] with n
    positivity
  · filter_upwards [] with n
    simp only [Set.inter_univ, prefixCount_univ]
    show (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ) ≤
      ((Nat.sqrt n + 1 + hF.toFinset.card : ℕ) : ℝ) / (n : ℝ)
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (prefixCount_le_sparse_add_finite hF hA n |>.trans
        (Nat.add_le_add_right (count_sparseSquare_le_sqrt_add_one n)
          hF.toFinset.card))
    · positivity
  · exact sparse_add_const_ratio_tendsto hF.toFinset.card

theorem relativeUpperDensity_univ_eq_zero
    {input output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Sparse) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨F, hF, hsub⟩ := first_subset_sparse_union_finite hvalid
  unfold Stage3Case024.relativeUpperDensity
  exact (ratio_univ_tendsto_zero hF hsub).limsup_eq

end Case024Helpers

namespace Case024Helpers

open GenLimit.InfiniteContamination

private theorem expected_sparse_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (input : Stage3Case024.Stream)
    (output : Ω → Stage3Case024.Stream)
    (hint : Stage3Case024.DensityIntegrable μ Sparse input output) :
    Stage3Case024.expectedUpperDensity μ Sparse input output ≤ 1 := by
  unfold Stage3Case024.DensityIntegrable at hint
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Sparse ∂μ) ≤
        ∫ _ : Ω, (1 : ℝ) ∂μ := by
      apply integral_mono hint (integrable_const 1)
      intro ω
      exact relativeUpperDensity_le_one _ _
    _ = 1 := by
      rw [integral_const, measureReal_univ_eq_one]
      norm_num

private theorem expected_univ_eq_zero
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : Stage3Case024.Stream) (output : Ω → Stage3Case024.Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ Sparse input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.EventuallyFreshValid at hvalid
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae]
  · exact integral_zero Ω ℝ
  · filter_upwards [hvalid] with ω hω
    exact relativeUpperDensity_univ_eq_zero hω

 theorem pairObstruction :
    Stage3Case024.PairObstruction Sparse Set.univ commonStream := by
  intro Ω _ μ _ gen output _hfollow _hmeas hintSparse _hintUniv
    hvalidSparse _hvalidUniv
  have hsparse := expected_sparse_le_one μ commonStream output hintSparse
  have huniv := expected_univ_eq_zero μ commonStream output hvalidSparse
  constructor
  · rw [huniv]
    linarith
  · intro hboth
    rw [huniv] at hboth
    norm_num at hboth

end Case024Helpers

namespace Case024Helpers

noncomputable def freshGenerator : Stage3Case024.OnlineGenerator :=
  fun t inputs outputs =>
    GenLimit.Support.freshFromInfinite Sparse sparse_infinite
      ((Finset.univ.image inputs) ∪ (Finset.univ.image outputs))

private theorem freshGenerator_mem (t : ℕ) (inputs : Fin (t + 1) → ℕ)
    (outputs : Fin t → ℕ) : freshGenerator t inputs outputs ∈ Sparse := by
  exact GenLimit.Support.freshFromInfinite_mem _ _ _

private theorem freshGenerator_not_input (t : ℕ)
    (inputs : Fin (t + 1) → ℕ) (outputs : Fin t → ℕ) (i : Fin (t + 1)) :
    freshGenerator t inputs outputs ≠ inputs i := by
  intro heq
  have hnot := GenLimit.Support.freshFromInfinite_not_mem Sparse sparse_infinite
    ((Finset.univ.image inputs) ∪ (Finset.univ.image outputs))
  apply hnot
  apply Finset.mem_union_left
  rw [Finset.mem_image]
  exact ⟨i, Finset.mem_univ _, heq.symm⟩

private theorem freshGenerator_not_output (t : ℕ)
    (inputs : Fin (t + 1) → ℕ) (outputs : Fin t → ℕ) (i : Fin t) :
    freshGenerator t inputs outputs ≠ outputs i := by
  intro heq
  have hnot := GenLimit.Support.freshFromInfinite_not_mem Sparse sparse_infinite
    ((Finset.univ.image inputs) ∪ (Finset.univ.image outputs))
  apply hnot
  apply Finset.mem_union_right
  rw [Finset.mem_image]
  exact ⟨i, Finset.mem_univ _, heq.symm⟩

noncomputable def freshRun (input : Stage3Case024.Stream) (t : ℕ) : ℕ :=
  freshGenerator t (fun i => input i) (fun i => freshRun input i)
termination_by t
decreasing_by exact i.isLt

theorem freshRun_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshGenerator input (freshRun input) := by
  intro t
  rw [freshRun]

private theorem freshRun_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (freshRun input) Sparse := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨?_, ?_, ?_⟩
  · rw [freshRun]
    exact freshGenerator_mem t _ _
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    have hne := freshGenerator_not_input t
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => freshRun input i) ⟨s, hs⟩
    have hrun : freshRun input t = freshGenerator t
        (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => freshRun input i) := by
      rw [freshRun]
    exact hne (hrun.symm.trans heq.symm)
  · intro s hs
    have hne := freshGenerator_not_output t
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => freshRun input i) ⟨s, hs⟩
    have hrun : freshRun input t = freshGenerator t
        (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => freshRun input i) := by
      rw [freshRun]
    intro heq
    exact hne (hrun.symm.trans heq.symm)

theorem globallyFeasible_of_sparse_subset {r : ℕ}
    (family : Fin r → Stage3Case024.Language)
    (hsub : ∀ j, Sparse ⊆ family j) :
    Stage3Case024.GloballyFeasible family := by
  refine ⟨freshGenerator, ?_⟩
  intro input _hlegal
  refine ⟨freshRun input, freshRun_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshRun_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hsub j hmem, hfresh, hnovel⟩

end Case024Helpers

namespace Case024Helpers

open GenLimit.InfiniteContamination

abbrev specialPoint := sparseBetweenSquares

def extras (i : ℕ) : Set ℕ := specialPoint '' Set.Iio i

private theorem extras_mono {i j : ℕ} (hij : i ≤ j) : extras i ⊆ extras j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

private theorem specialPoint_not_sparse (i : ℕ) : specialPoint i ∉ Sparse :=
  sparseBetweenSquares_nonsquare i

private theorem specialPoint_not_extras (i : ℕ) : specialPoint i ∉ extras i := by
  rintro ⟨k, hk, heq⟩
  exact (ne_of_lt (sparseBetweenSquares_strictMono hk)) heq

noncomputable def nestedFamily (r : ℕ) (i : Fin r) : Stage3Case024.Language :=
  if i.1 = r - 1 then Set.univ else Sparse ∪ extras i.1

private theorem nestedFamily_of_not_last {r : ℕ} (i : Fin r)
    (hi : i.1 ≠ r - 1) : nestedFamily r i = Sparse ∪ extras i.1 := by
  simp [nestedFamily, hi]

private theorem nestedFamily_last {r : ℕ} (hr : 0 < r) :
    nestedFamily r ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩ = Set.univ := by
  simp [nestedFamily]

private theorem nestedFamily_sparse_subset (r : ℕ) (i : Fin r) :
    Sparse ⊆ nestedFamily r i := by
  unfold nestedFamily
  split
  · exact Set.subset_univ _
  · exact Set.subset_union_left

private theorem nestedFamily_infinite (r : ℕ) (i : Fin r) :
    (nestedFamily r i).Infinite :=
  sparse_infinite.mono (nestedFamily_sparse_subset r i)

private theorem nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiNotLast : i.1 ≠ r - 1 := by
    intro hi
    have hjlt : j.1 < r := j.2
    omega
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    rw [nestedFamily_of_not_last i hiNotLast] at hx
    unfold nestedFamily
    split
    · exact Set.mem_univ x
    · rcases hx with hs | he
      · exact Or.inl hs
      · exact Or.inr (extras_mono (Nat.le_of_lt hij) he)
  · intro heq
    have hwit_i : specialPoint i.1 ∉ nestedFamily r i := by
      rw [nestedFamily_of_not_last i hiNotLast]
      intro hmem
      rcases hmem with hs | he
      · exact specialPoint_not_sparse i.1 hs
      · exact specialPoint_not_extras i.1 he
    have hwit_j : specialPoint i.1 ∈ nestedFamily r j := by
      unfold nestedFamily
      split
      · exact Set.mem_univ _
      · exact Or.inr ⟨i.1, hij, rfl⟩
    exact hwit_i (heq ▸ hwit_j)

private theorem nestedFamily_legal (r : ℕ) (i : Fin r) :
    Stage3Case024.Legal commonStream (nestedFamily r i) :=
  commonStream_legal _ (nestedFamily_infinite r i)
    (nestedFamily_sparse_subset r i)

end Case024Helpers

namespace Case024Helpers

private theorem nestedFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonStream := by
  intro Ω _ μ _ gen output _hfollow _hmeas _hint hvalid
  have hrpos : 0 < r := by omega
  let first : Fin r := ⟨0, hrpos⟩
  let last : Fin r := ⟨r - 1, Nat.sub_lt hrpos Nat.zero_lt_one⟩
  have hfirstNotLast : first.1 ≠ r - 1 := by
    dsimp [first]
    omega
  have hfirst : nestedFamily r first = Sparse := by
    rw [nestedFamily_of_not_last first hfirstNotLast]
    change Sparse ∪ extras 0 = Sparse
    simp [extras]
  have hlast : nestedFamily r last = Set.univ := by
    exact nestedFamily_last hrpos
  have hvalidSparse : Stage3Case024.EventuallyFreshValid μ Sparse commonStream output := by
    simpa [hfirst] using hvalid first
  have hzero := expected_univ_eq_zero μ commonStream output hvalidSparse
  refine ⟨last, ?_⟩
  simpa [hlast] using hzero

private theorem nestedFamily_witness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonStream := by
  refine ⟨nestedFamily_strict hr, ?_, ?_, nestedFamily_manyTargetObstruction hr⟩
  · intro j
    exact nestedFamily_legal r j
  · exact globallyFeasible_of_sparse_subset (nestedFamily r)
      (nestedFamily_sparse_subset r)

theorem manyTargetClaim : ∀ r : ℕ, 2 ≤ r →
    ∃ family : Fin r → Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      Stage3Case024.ManyTargetWitness family input := by
  intro r hr
  exact ⟨nestedFamily r, commonStream, nestedFamily_witness hr⟩

private theorem sparse_ssubset_univ : Sparse ⊂ (Set.univ : Set ℕ) := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨Set.subset_univ _, ?_⟩
  intro heq
  have hnot := specialPoint_not_sparse 0
  apply hnot
  rw [heq]
  exact Set.mem_univ _

theorem pairClaim :
    ∃ K₀ K₁ : Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      K₀ ⊂ K₁ ∧ Stage3Case024.Legal input K₀ ∧
        Stage3Case024.Legal input K₁ ∧
        Stage3Case024.PairObstruction K₀ K₁ input := by
  exact ⟨Sparse, Set.univ, commonStream, sparse_ssubset_univ,
    sparse_legal, univ_legal, pairObstruction⟩

end Case024Helpers
