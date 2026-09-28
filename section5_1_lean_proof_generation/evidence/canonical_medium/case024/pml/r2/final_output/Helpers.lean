import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper17_InfiniteContamination.EvenDensity
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

open Filter MeasureTheory
open scoped Topology

namespace Case024Helpers

open Stage3Case024

noncomputable def avoidGenerator (core : Set ℕ) (hcore : core.Infinite) :
    OnlineGenerator :=
  fun _ input output =>
    Classical.choose
      (hcore.exists_notMem_finset
        ((Finset.univ.image input) ∪ (Finset.univ.image output)))

noncomputable def runGenerator (gen : OnlineGenerator) (input : Stream) : Stream
  | t => gen t (fun i => input i) (fun i => runGenerator gen input i)
termination_by t => t

theorem runGenerator_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (runGenerator gen input) := by
  intro t
  rw [runGenerator]

theorem avoidGenerator_mem (core : Set ℕ) (hcore : core.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    avoidGenerator core hcore t input output ∈ core := by
  exact (Classical.choose_spec
    (hcore.exists_notMem_finset
      ((Finset.univ.image input) ∪ (Finset.univ.image output)))).1

theorem avoidGenerator_not_input (core : Set ℕ) (hcore : core.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (i : Fin (t + 1)) :
    avoidGenerator core hcore t input output ≠ input i := by
  have hnot := (Classical.choose_spec
    (hcore.exists_notMem_finset
      ((Finset.univ.image input) ∪ (Finset.univ.image output)))).2
  intro heq
  apply hnot
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq.symm⟩

theorem avoidGenerator_not_output (core : Set ℕ) (hcore : core.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (i : Fin t) :
    avoidGenerator core hcore t input output ≠ output i := by
  have hnot := (Classical.choose_spec
    (hcore.exists_notMem_finset
      ((Finset.univ.image input) ∪ (Finset.univ.image output)))).2
  intro heq
  apply hnot
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq.symm⟩

theorem runGenerator_novel (core : Set ℕ) (hcore : core.Infinite)
    (input : Stream) :
    GenLimit.NovelGeneratesInLimit input
      (runGenerator (avoidGenerator core hcore) input) core := by
  refine ⟨0, ?_⟩
  intro t _
  constructor
  · rw [runGenerator]
    exact avoidGenerator_mem core hcore t _ _
  constructor
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    have ht := runGenerator_follows (avoidGenerator core hcore) input t
    exact avoidGenerator_not_input core hcore t _ _ ⟨s, hs⟩
      (heq.trans ht).symm
  · intro s hs heq
    have ht := runGenerator_follows (avoidGenerator core hcore) input t
    exact avoidGenerator_not_output core hcore t _ _ ⟨s, hs⟩
      (heq.trans ht).symm

theorem globallyFeasible_of_commonCore {r : ℕ} (family : Fin r → Language)
    (core : Language) (hcore : core.Infinite)
    (hsubset : ∀ j, core ⊆ family j) :
    GloballyFeasible family := by
  refine ⟨avoidGenerator core hcore, ?_⟩
  intro input _
  refine ⟨runGenerator (avoidGenerator core hcore) input,
    runGenerator_follows _ _, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := runGenerator_novel core hcore input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hsubset j hmem, hfresh, hnovel⟩


noncomputable local instance :
    DecidablePred GenLimit.InfiniteContamination.SparseSquare :=
  Classical.decPred _

def squareCore : Language :=
  {n | GenLimit.InfiniteContamination.SparseSquare n}

theorem squareCore_infinite : squareCore.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => n * n) := by
    intro a b hab
    nlinarith
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact GenLimit.InfiniteContamination.sparseSquare_mul_self n

theorem squareCore_prefixRatio (n : ℕ) :
    (GenLimit.InfiniteContamination.naturalOrder).prefixRatio squareCore n =
      (Nat.count GenLimit.InfiniteContamination.SparseSquare n : ℝ) / n := by
  classical
  by_cases hn : n = 0
  · simp [hn, GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
  · simp only [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, hn, if_false]
    congr 1
    change (((Finset.range n).filter
      GenLimit.InfiniteContamination.SparseSquare).card : ℝ) = _
    rw [Nat.count_eq_card_filter_range]

theorem tendsto_squareCore_prefixRatio :
    Tendsto ((GenLimit.InfiniteContamination.naturalOrder).prefixRatio squareCore) atTop (𝓝 0) := by
  refine squeeze_zero
    (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / n)
    (fun n => (GenLimit.InfiniteContamination.naturalOrder).prefixRatio_nonneg squareCore n)
    ?_ GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div
  intro n
  rw [squareCore_prefixRatio]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n
  · exact Nat.cast_nonneg n

theorem squareCore_upperDensity_zero :
    (GenLimit.InfiniteContamination.naturalOrder).upperDensity squareCore = 0 := by
  exact tendsto_squareCore_prefixRatio.limsup_eq

theorem relativeUpperDensity_univ (A : Language) :
    relativeUpperDensity A Set.univ =
      (GenLimit.InfiniteContamination.naturalOrder).upperDensity A := by
  unfold relativeUpperDensity GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  congr 1
  funext n
  classical
  by_cases hn : n = 0
  · subst n
    simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
      GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]
  · simp [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio,
      GenLimit.KleinbergWei.OrderedLanguage.prefixCount,
      GenLimit.InfiniteContamination.naturalOrder,
      GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset, hn]

theorem relativeUpperDensity_univ_eq_zero_of_subset_union_finite
    {A F : Language} (hF : F.Finite) (hsub : A ⊆ squareCore ∪ F) :
    relativeUpperDensity A Set.univ = 0 := by
  rw [relativeUpperDensity_univ]
  apply le_antisymm
  · calc
      (GenLimit.InfiniteContamination.naturalOrder).upperDensity A ≤
          (GenLimit.InfiniteContamination.naturalOrder).upperDensity (squareCore ∪ F) :=
        (GenLimit.InfiniteContamination.naturalOrder).upperDensity_mono hsub
      _ ≤ (GenLimit.InfiniteContamination.naturalOrder).upperDensity squareCore +
          (GenLimit.InfiniteContamination.naturalOrder).upperDensity F :=
        (GenLimit.InfiniteContamination.naturalOrder).upperDensity_union_le squareCore F
      _ = 0 := by
        rw [squareCore_upperDensity_zero,
          (GenLimit.InfiniteContamination.naturalOrder).upperDensity_eq_zero_of_finite hF]
        norm_num
  · exact (GenLimit.InfiniteContamination.naturalOrder).upperDensity_nonneg A

theorem relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply Filter.limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (fun n => by positivity))
  filter_upwards [] with n
  have hcount := GenLimit.PatientScope.prefixCount_mono
    (Set.inter_subset_right : A ∩ K ⊆ K) n
  by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hz]
  · rw [div_le_one]
    · exact_mod_cast hcount
    · exact_mod_cast Nat.pos_of_ne_zero hz



noncomputable def commonInput : Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation
    squareCore (Set.univ \ squareCore) squareCore_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  apply GenLimit.InfiniteContamination.sparseMergePresentation_injective
    squareCore_infinite
  exact Set.disjoint_sdiff_right

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput,
    GenLimit.InfiniteContamination.range_sparseMergePresentation
      squareCore_infinite]
  exact Set.union_diff_cancel (Set.subset_univ squareCore)

theorem commonInput_legal (K : Language) (hsub : squareCore ⊆ K) :
    Legal commonInput K := by
  constructor
  · exact squareCore_infinite.mono hsub
  constructor
  · exact commonInput_injective
  constructor
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact
      GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
        squareCore_infinite hsub

theorem generatorFirst_density_zero_of_eventually_square
    (input output : Stream)
    (h : GenLimit.NovelGeneratesInLimit input output squareCore) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := h
  let F : Set ℕ := output '' Set.Iio T
  have hF : F.Finite := (Set.finite_Iio T).image output
  apply relativeUpperDensity_univ_eq_zero_of_subset_union_finite hF
  intro x hx
  obtain ⟨t, hout, _⟩ := hx
  by_cases ht : T ≤ t
  · exact Or.inl (hout ▸ (hT t ht).1)
  · exact Or.inr ⟨t, Set.mem_Iio.mpr (Nat.lt_of_not_ge ht), hout⟩

theorem pairObstruction : PairObstruction squareCore Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hIntCore hIntUniv hValidCore _
  have hzeroAE :
      (fun ω => relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hValidCore] with ω hω
    exact generatorFirst_density_zero_of_eventually_square commonInput (output ω) hω
  have hExpectedUniv :
      expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    exact MeasureTheory.integral_eq_zero_of_ae hzeroAE
  have hExpectedCore :
      expectedUpperDensity μ squareCore commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) squareCore ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
        apply MeasureTheory.integral_mono_ae hIntCore hconst
        exact Filter.Eventually.of_forall fun ω =>
          relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · rw [hExpectedUniv, add_zero]
    exact hExpectedCore
  · intro hboth
    rw [hExpectedUniv] at hboth
    linarith



def exceptionalPoint (n : ℕ) : ℕ :=
  GenLimit.InfiniteContamination.sparseBetweenSquares n

def extrasBelow (n : ℕ) : Language :=
  exceptionalPoint '' Set.Iio n

def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if j.val + 1 = r then Set.univ else squareCore ∪ extrasBelow j.val

theorem exceptionalPoint_not_square (n : ℕ) :
    exceptionalPoint n ∉ squareCore := by
  exact GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare n

theorem exceptionalPoint_injective : Function.Injective exceptionalPoint :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective

theorem extrasBelow_mono {a b : ℕ} (hab : a ≤ b) :
    extrasBelow a ⊆ extrasBelow b := by
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, Set.mem_Iio.mpr ((Set.mem_Iio.mp hk).trans_le hab), rfl⟩

theorem exceptionalPoint_not_extrasBelow (n : ℕ) :
    exceptionalPoint n ∉ extrasBelow n := by
  rintro ⟨k, hk, heq⟩
  have hkn : k = n := exceptionalPoint_injective heq
  exact (Nat.ne_of_lt (Set.mem_Iio.mp hk)) hkn

theorem nestedFamily_square_subset {r : ℕ} (j : Fin r) :
    squareCore ⊆ nestedFamily r j := by
  intro x hx
  by_cases hj : j.val + 1 = r
  · simp [nestedFamily, hj]
  · rw [nestedFamily, if_neg hj]
    exact Set.mem_union_left _ hx

theorem nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = squareCore := by
  have hne : 0 + 1 ≠ r := by omega
  simp [nestedFamily, hne, extrasBelow]

theorem nestedFamily_last {r : ℕ} (_hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [nestedFamily]
  omega

theorem nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiNotLast : i.val + 1 ≠ r := by omega
  constructor
  · intro x hx
    by_cases hjLast : j.val + 1 = r
    · simp [nestedFamily, hjLast]
    · rw [nestedFamily, if_neg hiNotLast] at hx
      rw [nestedFamily, if_neg hjLast]
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (extrasBelow_mono (Nat.le_of_lt hij) hx)
  · intro hreverse
    have hmemJ : exceptionalPoint i.val ∈ nestedFamily r j := by
      by_cases hjLast : j.val + 1 = r
      · simp [nestedFamily, hjLast]
      · rw [nestedFamily, if_neg hjLast]
        exact Or.inr ⟨i.val, Set.mem_Iio.mpr hij, rfl⟩
    have hmemI := hreverse hmemJ
    rw [nestedFamily, if_neg hiNotLast] at hmemI
    rcases hmemI with hsquare | hextra
    · exact exceptionalPoint_not_square i.val hsquare
    · exact exceptionalPoint_not_extrasBelow i.val hextra

theorem nestedFamily_manyObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let j0 : Fin r := ⟨0, by omega⟩
  let jlast : Fin r := ⟨r - 1, by omega⟩
  have hvalidSquare : EventuallyFreshValid μ squareCore commonInput output := by
    simpa [j0, nestedFamily_zero hr] using hvalid j0
  have hzeroAE :
      (fun ω => relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hvalidSquare] with ω hω
    exact generatorFirst_density_zero_of_eventually_square commonInput (output ω) hω
  refine ⟨jlast, ?_⟩
  rw [show nestedFamily r jlast = Set.univ by
    simpa [jlast] using nestedFamily_last hr]
  unfold expectedUpperDensity
  exact MeasureTheory.integral_eq_zero_of_ae hzeroAE

theorem nestedFamily_witness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨nestedFamily_strict hr, ?_, ?_, nestedFamily_manyObstruction hr⟩
  · intro j
    exact commonInput_legal _ (nestedFamily_square_subset j)
  · exact globallyFeasible_of_commonCore (nestedFamily r) squareCore
      squareCore_infinite nestedFamily_square_subset


end Case024Helpers
