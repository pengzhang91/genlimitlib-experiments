import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof

open Stage3Case024

abbrev core : Set ℕ := {n | GenLimit.InfiniteContamination.SparseSquare n}

noncomputable local instance :
    DecidablePred GenLimit.InfiniteContamination.SparseSquare := Classical.decPred _

theorem core_infinite : core.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => n * n)
  · intro m n h
    exact Nat.mul_self_inj.mp h
  · intro n
    exact ⟨n, rfl⟩

noncomputable def commonInput : Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation core coreᶜ core_infinite

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput,
    GenLimit.InfiniteContamination.range_sparseMergePresentation core_infinite]
  exact Set.union_compl_self core

theorem commonInput_injective : Function.Injective commonInput := by
  apply GenLimit.InfiniteContamination.sparseMergePresentation_injective core_infinite
  exact Set.disjoint_compl_right_iff_subset.mpr Set.Subset.rfl

theorem commonInput_legal {K : Language} (hcore : core ⊆ K) :
    Legal commonInput K := by
  refine ⟨core_infinite.mono hcore, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact
      GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
        core_infinite hcore

theorem prefixCount_le_squareCount (A : Set ℕ) (n : ℕ) (hA : A ⊆ core) :
    GenLimit.PatientScope.prefixCount A n ≤
      Nat.count GenLimit.InfiniteContamination.SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hA hx.2⟩

theorem square_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount core n : ℝ) / n)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / n)
  · exact Filter.Eventually.of_forall fun n => by positivity
  · exact Filter.Eventually.of_forall fun n => by
      by_cases hn : n = 0
      · subst n
        simp
      · apply div_le_div_of_nonneg_right
        · have hnat :=
            (prefixCount_le_squareCount core n Set.Subset.rfl).trans
              (GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n)
          exact_mod_cast hnat
        · positivity
  · exact GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div

theorem relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (fun n => by positivity))
  exact Filter.Eventually.of_forall fun n => by
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n

theorem generatorFirst_subset_core_union_early
    {input output : Stream} {T : ℕ}
    (hvalid : ∀ t, T ≤ t → output t ∈ core) :
    GenLimit.GeneratorFirst input output ⊆
      core ∪ Set.range (fun t : Fin T => output t) := by
  intro x hx
  obtain ⟨t, rfl, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Or.inl (hvalid t ht)
  · exact Or.inr ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩

theorem prefixCount_generatorFirst_le
    {input output : Stream} {T n : ℕ}
    (hvalid : ∀ t, T ≤ t → output t ∈ core) :
    GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n ≤
      GenLimit.PatientScope.prefixCount core n + T := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  let early : Finset ℕ := Finset.univ.image (fun t : Fin T => output t)
  have hsub : GenLimit.PatientScope.prefixFinset
        (GenLimit.GeneratorFirst input output) n ⊆
      GenLimit.PatientScope.prefixFinset core n ∪ early := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    rcases generatorFirst_subset_core_union_early hvalid hx'.2 with hcore | hearly
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hcore⟩)
    · obtain ⟨t, rfl⟩ := hearly
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
  calc
    (GenLimit.PatientScope.prefixFinset
      (GenLimit.GeneratorFirst input output) n).card ≤
        (GenLimit.PatientScope.prefixFinset core n ∪ early).card :=
      Finset.card_le_card hsub
    _ ≤ (GenLimit.PatientScope.prefixFinset core n).card + early.card :=
      Finset.card_union_le _ _
    _ ≤ (GenLimit.PatientScope.prefixFinset core n).card + T := by
      apply Nat.add_le_add_left
      calc
        early.card ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_image_le
        _ = T := by simp

theorem univ_density_zero_of_eventual_core
    {input output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output core) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := hvalid
  have hbound (n : ℕ) :
      (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount Set.univ n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount core n : ℝ) / n + T / n := by
    simp only [Set.inter_univ]
    rw [show GenLimit.PatientScope.prefixCount Set.univ n = n by
      simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]]
    by_cases hn : n = 0
    · simp [hn]
    · rw [← add_div]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast prefixCount_generatorFirst_le
          (fun t ht => (hT t ht).1)
      · positivity
  have htendsto : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount Set.univ n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      positivity
    · exact hbound
    · simpa using square_ratio_tendsto_zero.add
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  exact htendsto.limsup_eq

noncomputable def available {t : ℕ} (xs : Fin (t + 1) → ℕ) : Set ℕ :=
  core \ (Finset.univ.image xs : Finset ℕ)

theorem available_infinite {t : ℕ} (xs : Fin (t + 1) → ℕ) :
    (available xs).Infinite := by
  exact core_infinite.diff (Finset.finite_toSet (Finset.univ.image xs))

noncomputable def freshGenerator : OnlineGenerator :=
  fun t xs _ => Nat.nth (fun x => x ∈ available xs) t

noncomputable def freshOutput (input : Stream) : Stream :=
  fun t => freshGenerator t (fun i => input i) (fun i => 0)

theorem freshOutput_follows (input : Stream) :
    Follows freshGenerator input (freshOutput input) := by
  intro t
  rfl

theorem freshOutput_available (input : Stream) (t : ℕ) :
    freshOutput input t ∈ available (fun i : Fin (t + 1) => input i) := by
  classical
  exact Nat.nth_mem_of_infinite (available_infinite _) t

theorem freshOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (freshOutput input) core := by
  classical
  refine ⟨0, ?_⟩
  intro t _
  have havail := freshOutput_available input t
  refine ⟨havail.1, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact havail.2 (Finset.mem_image.mpr
      ⟨⟨s, hs⟩, Finset.mem_univ _, heq⟩)
  · intro s hs heq
    let ps : ℕ → Prop := fun x => x ∈ available (fun i : Fin (s + 1) => input i)
    let pt : ℕ → Prop := fun x => x ∈ available (fun i : Fin (t + 1) => input i)
    have hps : {x | ps x}.Infinite := available_infinite _
    have hpt : {x | pt x}.Infinite := available_infinite _
    have hsubset : ∀ x, pt x → ps x := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro hmem
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
      apply hx.2
      exact Finset.mem_image.mpr
        ⟨⟨i, lt_trans i.isLt (Nat.succ_lt_succ hs)⟩, Finset.mem_univ _, hi⟩
    have hcount : Nat.count pt (freshOutput input t) ≤
        Nat.count ps (freshOutput input t) :=
      Nat.count_mono_left hsubset
    have htcount : Nat.count pt (freshOutput input t) = t := by
      change Nat.count pt (Nat.nth pt t) = t
      exact Nat.count_nth_of_infinite hpt t
    have hscount : Nat.count ps (freshOutput input s) = s := by
      change Nat.count ps (Nat.nth ps s) = s
      exact Nat.count_nth_of_infinite hps s
    rw [htcount] at hcount
    rw [← heq, hscount] at hcount
    omega

theorem globallyFeasible_of_core_subset {r : ℕ} (fam : Fin r → Language)
    (hcore : ∀ j, core ⊆ fam j) : GloballyFeasible fam := by
  refine ⟨freshGenerator, ?_⟩
  intro input _
  refine ⟨freshOutput input, freshOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hcore j hmem, hfresh, hnovel⟩

def marker (k : ℕ) : ℕ :=
  GenLimit.InfiniteContamination.sparseBetweenSquares k

theorem marker_not_core (k : ℕ) : marker k ∉ core :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare k

theorem marker_injective : Function.Injective marker :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective

def family {r : ℕ} (i : Fin r) : Language :=
  if (i : ℕ) + 1 = r then Set.univ
  else core ∪ marker '' Set.Iio (i : ℕ)

theorem core_subset_family {r : ℕ} (i : Fin r) : core ⊆ family i := by
  intro x hx
  by_cases hi : (i : ℕ) + 1 = r
  · simp [family, hi]
  · exact by simp [family, hi, hx]

theorem family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (@family r) := by
  intro i j hij
  rw [Set.ssubset_iff_subset_ne]
  have hiNotLast : (i : ℕ) + 1 ≠ r := by omega
  constructor
  · intro x hx
    by_cases hj : (j : ℕ) + 1 = r
    · simp [family, hj]
    · simp only [family, hj, hiNotLast, if_false] at hx ⊢
      rcases hx with hx | ⟨k, hk, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, lt_trans hk hij, rfl⟩
  · intro heq
    have hjmem : marker (i : ℕ) ∈ family j := by
      by_cases hj : (j : ℕ) + 1 = r
      · simp [family, hj]
      · simp only [family, hj, if_false, Set.mem_union, Set.mem_image, Set.mem_Iio]
        exact Or.inr ⟨i, hij, rfl⟩
    have himem : marker (i : ℕ) ∈ family i := heq ▸ hjmem
    simp only [family, hiNotLast, if_false, Set.mem_union, Set.mem_image,
      Set.mem_Iio] at himem
    rcases himem with hcore | ⟨k, hk, hki⟩
    · exact marker_not_core _ hcore
    · have hki' : k = (i : ℕ) := marker_injective hki
      omega

theorem pairObstruction : PairObstruction core Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hint0 _ hvalid0 _
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hvalid0.mono fun ω hω => univ_density_zero_of_eventual_core hω
  have hE1 : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    rw [integral_congr_ae hzero]
    simp
  have hle : expectedUpperDensity μ core commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) core ∂μ) ≤
          ∫ _ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hint0 (integrable_const 1)
        exact Filter.Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · simpa [hE1] using hle
  · intro hboth
    rw [hE1] at hboth
    linarith

theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (@family r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let zero : Fin r := ⟨0, by omega⟩
  let top : Fin r := ⟨r - 1, by omega⟩
  refine ⟨top, ?_⟩
  have htopIndex : (top : ℕ) + 1 = r := by
    change r - 1 + 1 = r
    exact Nat.sub_add_cancel (by omega)
  have htop : family top = Set.univ := by
    simp [family, htopIndex]
  have hzeroIndex : (zero : ℕ) + 1 ≠ r := by
    change 0 + 1 ≠ r
    omega
  have hfamily0 : family zero = core := by
    simp [family, hzeroIndex, zero]
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) (family top) = 0 := by
    filter_upwards [hvalid zero] with ω hω
    rw [htop]
    apply univ_density_zero_of_eventual_core
    obtain ⟨T, hT⟩ := hω
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    rw [hfamily0] at hmem
    exact ⟨hmem, hfresh, hnovel⟩
  unfold expectedUpperDensity
  rw [integral_congr_ae hzero]
  simp

theorem mainClaim : MainClaim := by
  constructor
  · refine ⟨core, Set.univ, commonInput, ?_, commonInput_legal Set.Subset.rfl,
      commonInput_legal (Set.subset_univ core), pairObstruction⟩
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨Set.subset_univ core, ?_⟩
    intro h
    apply marker_not_core 0
    rw [h]
    exact Set.mem_univ _
  · intro r hr
    refine ⟨@family r, commonInput, family_strictlyNested hr, ?_,
      globallyFeasible_of_core_subset family core_subset_family,
      manyTargetObstruction hr⟩
    intro j
    exact commonInput_legal (core_subset_family j)

end Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  exact Case024Proof.mainClaim
