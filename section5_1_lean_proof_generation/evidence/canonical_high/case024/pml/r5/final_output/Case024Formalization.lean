import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024Formalization

open Stage3Case024
open GenLimit.InfiniteContamination

def squareCore : Set ℕ := {n | SparseSquare n}

theorem squareCore_infinite : squareCore.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => n * n) := by
    intro a b hab
    nlinarith
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro _ ⟨n, rfl⟩
    exact sparseSquare_mul_self n)

noncomputable def commonInput : Stream :=
  sparseMergePresentation squareCore squareCoreᶜ squareCore_infinite

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation squareCore_infinite]
  exact Set.union_compl_self squareCore

theorem commonInput_legal_of_core_subset {K : Language}
    (hcore : squareCore ⊆ K) (hinfinite : K.Infinite) :
    Legal commonInput K := by
  refine ⟨hinfinite, ?_⟩
  refine ⟨sparseMergePresentation_injective squareCore_infinite (by
      rw [Set.disjoint_left]
      intro x hx hxc
      exact hxc hx),
    ?_, sparseMergePresentation_vanishingNoise_of_core_subset squareCore_infinite hcore⟩
  intro x hx
  rw [commonInput_range]
  exact Set.mem_univ x

theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

theorem relativeUpperDensity_nonneg (A K : Language) :
    0 ≤ relativeUpperDensity A K := by
  unfold relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · have hle := prefixCount_mono (A := A ∩ K) (B := K) Set.inter_subset_right n
        have hnum : GenLimit.PatientScope.prefixCount (A ∩ K) n = 0 := by
          omega
        simp [hzero, hnum]
      · rw [div_le_one]
        · exact_mod_cast prefixCount_mono Set.inter_subset_right n
        · exact_mod_cast Nat.pos_of_ne_zero hzero⟩

theorem relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact Eventually.of_forall fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · have hle := prefixCount_mono (A := A ∩ K) (B := K) Set.inter_subset_right n
        have hnum : GenLimit.PatientScope.prefixCount (A ∩ K) n = 0 := by
          omega
        simp [hzero, hnum]
      · rw [div_le_one]
        · exact_mod_cast prefixCount_mono Set.inter_subset_right n
        · exact_mod_cast Nat.pos_of_ne_zero hzero

theorem prefixCount_squareCore_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount squareCore n ≤ Nat.sqrt n + 1 := by
  classical
  rw [show GenLimit.PatientScope.prefixCount squareCore n = Nat.count SparseSquare n by
    simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
      Nat.count_eq_card_filter_range, squareCore]]
  exact count_sparseSquare_le_sqrt_add_one n

theorem relativeUpperDensity_univ_eq_zero_of_subset_finite
    {A F : Language} (hF : F.Finite) (hsub : A ⊆ squareCore ∪ F) :
    relativeUpperDensity A Set.univ = 0 := by
  let C := hF.toFinset.card
  have hcount (n : ℕ) :
      GenLimit.PatientScope.prefixCount A n ≤ Nat.sqrt n + 1 + C := by
    calc
      GenLimit.PatientScope.prefixCount A n ≤
          GenLimit.PatientScope.prefixCount (squareCore ∪ F) n :=
        prefixCount_mono hsub n
      _ ≤ GenLimit.PatientScope.prefixCount squareCore n +
          GenLimit.PatientScope.prefixCount F n := by
        classical
        unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
        apply (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range, Set.mem_union,
          Finset.mem_union] at hx ⊢
        rcases hx.2 with hxcore | hxF
        · exact Or.inl ⟨hx.1, hxcore⟩
        · exact Or.inr ⟨hx.1, hxF⟩
      _ ≤ (Nat.sqrt n + 1) + C := by
        apply Nat.add_le_add (prefixCount_squareCore_le n)
        classical
        unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset C
        exact Finset.card_le_card (by
          intro x hx
          simpa using (Finset.mem_filter.mp hx).2)
  have htendsto : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount Set.univ n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero
      (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + C) / (n : ℝ))
    · intro n
      positivity
    · intro n
      by_cases hn : n = 0
      · simp [hn, GenLimit.PatientScope.prefixCount,
          GenLimit.PatientScope.prefixFinset]
      · have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        simp only [Set.inter_univ]
        have hden : GenLimit.PatientScope.prefixCount Set.univ n = n := by
          simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
        rw [hden]
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcount n
        · exact hnnonneg
    · have hconst : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [add_div] using tendsto_sparseSqrt_add_one_div.add hconst
  unfold relativeUpperDensity
  exact htendsto.limsup_eq

theorem generatorFirst_subset_range (input output : Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, htx, -⟩
  exact ⟨t, htx⟩

theorem density_zero_of_eventual_sparse
    {input output : Stream} {L : Language}
    (hfinite : (L \ squareCore).Finite)
    (hvalid : GenLimit.NovelGeneratesInLimit input output L) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := hvalid
  let early : Set ℕ := Set.range (fun t : Fin T => output t)
  have hearly : early.Finite := Set.finite_range _
  let F : Set ℕ := (L \ squareCore) ∪ early
  have hF : F.Finite := hfinite.union hearly
  apply relativeUpperDensity_univ_eq_zero_of_subset_finite hF
  intro x hx
  obtain ⟨t, rfl⟩ := generatorFirst_subset_range input output hx
  by_cases ht : T ≤ t
  · have houtL := (hT t ht).1
    by_cases hcore : output t ∈ squareCore
    · exact Or.inl hcore
    · exact Or.inr (Or.inl ⟨houtL, hcore⟩)
  · exact Or.inr (Or.inr ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩)

def freshCoreGenerator : OnlineGenerator := fun t input output =>
  let m := 1 + (∑ i, input i) + ∑ i, output i
  m * m

noncomputable def freshCoreOutput (input : Stream) (t : ℕ) : ℕ :=
  freshCoreGenerator t (fun i => input i) (fun i => freshCoreOutput input i)
termination_by t
decreasing_by omega

theorem freshCore_follows (input : Stream) :
    Follows freshCoreGenerator input (freshCoreOutput input) := by
  intro t
  rw [freshCoreOutput.eq_1]

theorem freshCore_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (freshCoreOutput input) squareCore := by
  refine ⟨0, ?_⟩
  intro t _
  let inputSum := ∑ i : Fin (t + 1), input i
  let outputSum := ∑ i : Fin t, freshCoreOutput input i
  let m := 1 + inputSum + outputSum
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hout : freshCoreOutput input t = m * m := by
    rw [freshCoreOutput.eq_1]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    exact ⟨m, rfl⟩
  · rw [hout]
    intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hst, hs⟩ := hmem
    have hinput : input s ≤ inputSum := by
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun i : Fin (t + 1) => input i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨s, hst⟩)
    have hlt : input s < m * m := by
      have : input s < m := by
        dsimp [m]
        omega
      nlinarith
    exact (ne_of_lt hlt) hs
  · intro s hst
    rw [hout]
    have houtput : freshCoreOutput input s ≤ outputSum := by
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun i : Fin t => freshCoreOutput input i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨s, hst⟩)
    have hlt : freshCoreOutput input s < m * m := by
      have : freshCoreOutput input s < m := by
        dsimp [m]
        omega
      nlinarith
    exact ne_of_lt hlt

def additions (j : ℕ) : Set ℕ :=
  sparseBetweenSquares '' Set.Iio j

def stageLanguage (j : ℕ) : Language := squareCore ∪ additions j

theorem additions_finite (j : ℕ) : (additions j).Finite :=
  (Set.finite_Iio j).image sparseBetweenSquares

theorem additions_mono {i j : ℕ} (hij : i ≤ j) :
    additions i ⊆ additions j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

theorem stageLanguage_mono {i j : ℕ} (hij : i ≤ j) :
    stageLanguage i ⊆ stageLanguage j :=
  Set.union_subset_union Set.Subset.rfl (additions_mono hij)

theorem sparseBetweenSquares_not_mem_stage (i : ℕ) :
    sparseBetweenSquares i ∉ stageLanguage i := by
  rintro (hcore | ⟨k, hk, heq⟩)
  · exact sparseBetweenSquares_nonsquare i hcore
  · have hki : k = i := sparseBetweenSquares_strictMono.injective heq
    subst k
    exact Nat.lt_irrefl i hk

theorem stageLanguage_ssubset {i j : ℕ} (hij : i < j) :
    stageLanguage i ⊂ stageLanguage j := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨stageLanguage_mono hij.le, ?_⟩
  intro heq
  have hmem : sparseBetweenSquares i ∈ stageLanguage j :=
    Or.inr ⟨i, hij, rfl⟩
  exact sparseBetweenSquares_not_mem_stage i (heq ▸ hmem)

theorem stageLanguage_infinite (j : ℕ) : (stageLanguage j).Infinite :=
  squareCore_infinite.mono Set.subset_union_left

theorem stageLanguage_diff_core_finite (j : ℕ) :
    (stageLanguage j \ squareCore).Finite := by
  exact (additions_finite j).subset (by
    intro x hx
    exact hx.1.resolve_left hx.2)

def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if (j : ℕ) + 1 = r then Set.univ else stageLanguage j

theorem nestedFamily_core_subset {r : ℕ} (j : Fin r) :
    squareCore ⊆ nestedFamily r j := by
  by_cases hj : (j : ℕ) + 1 = r
  · simp [nestedFamily, hj]
  · simp [nestedFamily, hj, stageLanguage]

theorem nestedFamily_infinite {r : ℕ} (j : Fin r) :
    (nestedFamily r j).Infinite :=
  squareCore_infinite.mono (nestedFamily_core_subset j)

theorem nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hilast : (i : ℕ) + 1 ≠ r := by omega
  by_cases hjlast : (j : ℕ) + 1 = r
  · simp only [nestedFamily, hilast, hjlast, if_false, if_true]
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    let witness := sparseBetweenSquares i
    have hnot : witness ∉ stageLanguage i := sparseBetweenSquares_not_mem_stage i
    exact hnot (heq ▸ Set.mem_univ witness)
  · simp only [nestedFamily, hilast, hjlast, if_false]
    exact stageLanguage_ssubset hij

theorem nestedFamily_legal {r : ℕ} (j : Fin r) :
    Legal commonInput (nestedFamily r j) :=
  commonInput_legal_of_core_subset (nestedFamily_core_subset j) (nestedFamily_infinite j)

theorem nestedFamily_feasible {r : ℕ} : GloballyFeasible (nestedFamily r) := by
  refine ⟨freshCoreGenerator, ?_⟩
  intro input _
  refine ⟨freshCoreOutput input, freshCore_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshCore_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨nestedFamily_core_subset j hcore, hfresh, hnovel⟩

theorem pair_obstruction : PairObstruction squareCore Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hintCore hintUniv hvalidCore _
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hvalidCore] with ω hω
    exact density_zero_of_eventual_sparse (by simpa using Set.finite_empty) hω
  have hEuniv : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    simpa using integral_congr_ae hzero
  have hEcore : expectedUpperDensity μ squareCore commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    have hone : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have hle := integral_mono_ae hintCore hone
      (Eventually.of_forall fun ω =>
        relativeUpperDensity_le_one
          (GenLimit.GeneratorFirst commonInput (output ω)) squareCore)
    simpa using hle
  constructor
  · rw [hEuniv, add_zero]
    exact hEcore
  · rw [hEuniv]
    intro hboth
    linarith

theorem many_obstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hlast : ((last : Fin r) : ℕ) + 1 = r := by
    dsimp [last]
    omega
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hvalid ⟨0, by omega⟩] with ω hω
    have hfirst : nestedFamily r ⟨0, by omega⟩ = stageLanguage 0 := by
      simp [nestedFamily]
      omega
    rw [hfirst] at hω
    exact density_zero_of_eventual_sparse (stageLanguage_diff_core_finite 0) hω
  have hexpect : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    simpa using integral_congr_ae hzero
  simpa [nestedFamily, hlast] using hexpect

theorem many_witness (r : ℕ) (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) commonInput := by
  exact ⟨nestedFamily_strict hr, nestedFamily_legal,
    nestedFamily_feasible, many_obstruction hr⟩

end Case024Formalization

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024Formalization.squareCore, Set.univ,
      Case024Formalization.commonInput, ?_⟩
    refine ⟨?_, Case024Formalization.commonInput_legal_of_core_subset
      Set.Subset.rfl Case024Formalization.squareCore_infinite,
      Case024Formalization.commonInput_legal_of_core_subset (Set.subset_univ _) Set.infinite_univ,
      Case024Formalization.pair_obstruction⟩
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hnot := GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare 0
    have hmem : GenLimit.InfiniteContamination.sparseBetweenSquares 0 ∈
        Case024Formalization.squareCore := by
      rw [heq]
      exact Set.mem_univ _
    exact hnot hmem
  · intro r hr
    exact ⟨Case024Formalization.nestedFamily r,
      Case024Formalization.commonInput,
      Case024Formalization.many_witness r hr⟩
