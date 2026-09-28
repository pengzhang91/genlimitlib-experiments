import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Analysis.SpecificLimits.Basic

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof

open GenLimit.InfiniteContamination

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

lemma sparseSquare_infinite : {n : ℕ | SparseSquare n}.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => n * n) := by
    intro a b hab
    nlinarith [Nat.zero_le a, Nat.zero_le b]
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro _ ⟨n, rfl⟩
    exact sparseSquare_mul_self n)

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simp

lemma prefixCount_sparseSquare (n : ℕ) :
    GenLimit.PatientScope.prefixCount {x : ℕ | SparseSquare x} n =
      Nat.count SparseSquare n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  rw [Nat.count_eq_card_filter_range]
  congr

lemma prefixCount_le_sparse_add
    {A : Set ℕ} (hfinite : (A \ {x : ℕ | SparseSquare x}).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      Nat.count SparseSquare n + hfinite.toFinset.card := by
  classical
  let F := hfinite.toFinset
  have hsub : A ⊆ {x : ℕ | SparseSquare x} ∪ (F : Set ℕ) := by
    intro x hx
    by_cases hs : SparseSquare x
    · exact Set.mem_union_left _ hs
    · exact Set.mem_union_right _ (hfinite.mem_toFinset.mpr ⟨hx, hs⟩)
  calc
    GenLimit.PatientScope.prefixCount A n ≤
        GenLimit.PatientScope.prefixCount
          ({x : ℕ | SparseSquare x} ∪ (F : Set ℕ)) n :=
      prefixCount_mono hsub n
    _ ≤ GenLimit.PatientScope.prefixCount {x : ℕ | SparseSquare x} n + F.card := by
      unfold GenLimit.PatientScope.prefixCount
      classical
      calc
        (GenLimit.PatientScope.prefixFinset
            ({x : ℕ | SparseSquare x} ∪ (F : Set ℕ)) n).card ≤
            (GenLimit.PatientScope.prefixFinset {x : ℕ | SparseSquare x} n ∪ F).card := by
          apply Finset.card_le_card
          intro x hx
          rw [GenLimit.PatientScope.mem_prefixFinset] at hx
          rcases hx.2 with hs | hF
          · exact Finset.mem_union_left _
              (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx.1, hs⟩)
          · exact Finset.mem_union_right _ hF
        _ ≤ (GenLimit.PatientScope.prefixFinset {x : ℕ | SparseSquare x} n).card + F.card :=
          Finset.card_union_le _ _
    _ = Nat.count SparseSquare n + hfinite.toFinset.card := by
      rw [prefixCount_sparseSquare]

lemma tendsto_relative_univ_zero
    {A : Set ℕ} (hfinite : (A \ {x : ℕ | SparseSquare x}).Finite) :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ))
      atTop (𝓝 0) := by
  let C : ℕ := hfinite.toFinset.card
  have hC : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hupper : Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / (n : ℝ) + (C : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa using tendsto_sparseSqrt_add_one_div.add hC
  apply squeeze_zero' (g := fun n : ℕ =>
      ((Nat.sqrt n : ℝ) + 1) / (n : ℝ) + (C : ℝ) / (n : ℝ))
  · exact Eventually.of_forall fun n => by positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Set.inter_univ, prefixCount_univ]
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hnpos).2
    have hcount := prefixCount_le_sparse_add hfinite n
    have hsqrt := count_sparseSquare_le_sqrt_add_one n
    exact_mod_cast hcount.trans (Nat.add_le_add_right hsqrt C)
  · exact hupper

lemma relativeUpperDensity_univ_eq_zero
    {A : Set ℕ} (hfinite : (A \ {x : ℕ | SparseSquare x}).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  exact (tendsto_relative_univ_zero hfinite).limsup_eq

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  filter_upwards with n
  let a := GenLimit.PatientScope.prefixCount (A ∩ K) n
  let b := GenLimit.PatientScope.prefixCount K n
  by_cases hb : b = 0
  · simp [b, hb]
  · have hbpos : (0 : ℝ) < b := by
      exact_mod_cast Nat.pos_of_ne_zero hb
    apply (div_le_iff₀ hbpos).2
    simpa [a, b] using prefixCount_mono Set.inter_subset_right n

lemma generatorFirst_diff_sparse_finite
    {input output : Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output
      {x : ℕ | SparseSquare x}) :
    (GenLimit.GeneratorFirst input output \ {x : ℕ | SparseSquare x}).Finite := by
  classical
  obtain ⟨T, hT⟩ := hvalid
  apply Set.Finite.subset
    (Set.finite_coe_iff.mpr ((Finset.range T).image output).finite_toSet)
  intro x hx
  obtain ⟨t, htx, -⟩ := hx.1
  have ht : t < T := by
    by_contra hnot
    have hmem := (hT t (Nat.le_of_not_gt hnot)).1
    rw [htx] at hmem
    exact hx.2 hmem
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨t, Finset.mem_range.mpr ht, htx⟩)

lemma pairObstruction
    (input : Stream) :
    Stage3Case024.PairObstruction {x : ℕ | SparseSquare x} Set.univ input := by
  intro Ω _ μ _ gen output hfollow hmeas hint0 hint1 hvalid0 hvalid1
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ = 0 := by
    filter_upwards [hvalid0] with ω hω
    exact relativeUpperDensity_univ_eq_zero
      (generatorFirst_diff_sparse_finite hω)
  have hexp1 : Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzero]
    simp
  have hexp0 : Stage3Case024.expectedUpperDensity μ
      {x : ℕ | SparseSquare x} input output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst input (output ω))
          {x : ℕ | SparseSquare x} ∂μ) ≤ ∫ _ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hint0 (integrable_const 1)
        exact Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · rw [hexp1, add_zero]
    exact hexp0
  · intro hboth
    rw [hexp1] at hboth
    linarith


noncomputable def finiteExtras (j : ℕ) : Finset ℕ :=
  (Finset.range j).image sparseBetweenSquares

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if j.1 + 1 = r then Set.univ
  else {x : ℕ | SparseSquare x} ∪ (finiteExtras j.1 : Set ℕ)

lemma sparseBetweenSquares_not_mem_extras_self (i : ℕ) :
    sparseBetweenSquares i ∉ finiteExtras i := by
  classical
  intro hmem
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hmem
  have hki : k < i := Finset.mem_range.mp hk
  exact (Nat.ne_of_lt hki)
    (sparseBetweenSquares_strictMono.injective heq)

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, lt_of_lt_of_le (by omega) hr⟩ =
      {x : ℕ | SparseSquare x} := by
  classical
  simp [nestedFamily, finiteExtras]
  omega

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  have hlast : r - 1 + 1 = r := by omega
  simp [nestedFamily, hlast]

lemma squares_subset_nestedFamily {r : ℕ} (hr : 2 ≤ r) (j : Fin r) :
    {x : ℕ | SparseSquare x} ⊆ nestedFamily r j := by
  classical
  by_cases hlast : j.1 + 1 = r
  · simp [nestedFamily, hlast]
  · simp only [nestedFamily, hlast, ↓reduceIte]
    exact Set.subset_union_left

lemma strictlyNested_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  classical
  intro i j hij
  have hiNotLast : i.1 + 1 ≠ r := by
    intro hi
    have hjlt : j.1 < r := j.2
    omega
  have hsub : nestedFamily r i ⊆ nestedFamily r j := by
    by_cases hjLast : j.1 + 1 = r
    · simp [nestedFamily, hjLast]
    · simp only [nestedFamily, hiNotLast, hjLast, ↓reduceIte]
      intro x hx
      rcases hx with hs | hx
      · exact Set.mem_union_left _ hs
      · exact Set.mem_union_right _ (by
          unfold finiteExtras at hx ⊢
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
          apply Finset.mem_image.mpr
          exact ⟨k, Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.le_of_lt hij)), rfl⟩)
  refine Set.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  let witness := sparseBetweenSquares i.1
  have hwj : witness ∈ nestedFamily r j := by
    by_cases hjLast : j.1 + 1 = r
    · simp [nestedFamily, hjLast]
    · simp only [nestedFamily, hjLast, ↓reduceIte]
      exact Set.mem_union_right _ (by
        unfold witness finiteExtras
        apply Finset.mem_image.mpr
        exact ⟨i.1, Finset.mem_range.mpr hij, rfl⟩)
  have hwi : witness ∉ nestedFamily r i := by
    simp only [nestedFamily, hiNotLast, ↓reduceIte]
    intro hw
    rcases hw with hs | hextra
    · exact sparseBetweenSquares_nonsquare i.1 hs
    · exact sparseBetweenSquares_not_mem_extras_self i.1 hextra
  exact hwi (heq ▸ hwj)

noncomputable def commonInput : Stream :=
  sparseMergePresentation {x : ℕ | SparseSquare x}
    ({x : ℕ | SparseSquare x}ᶜ) sparseSquare_infinite

lemma range_commonInput : Set.range commonInput = Set.univ := by
  unfold commonInput
  rw [range_sparseMergePresentation sparseSquare_infinite]
  exact Set.union_compl_self _

lemma commonInput_injective : Function.Injective commonInput := by
  unfold commonInput
  apply sparseMergePresentation_injective sparseSquare_infinite
  rw [Set.disjoint_left]
  exact fun _ hx hxc => hxc hx

lemma legal_commonInput_nestedFamily {r : ℕ} (hr : 2 ≤ r) (j : Fin r) :
    Stage3Case024.Legal commonInput (nestedFamily r j) := by
  constructor
  · exact sparseSquare_infinite.mono (squares_subset_nestedFamily hr j)
  · refine ⟨commonInput_injective, ?_, ?_⟩
    · unfold GenLimit.InfiniteContamination.NoOmissions
      rw [range_commonInput]
      exact Set.subset_univ _
    · unfold commonInput
      exact sparseMergePresentation_vanishingNoise_of_core_subset
        sparseSquare_infinite (squares_subset_nestedFamily hr j)

noncomputable def freshGenerator (K : Language) (hK : K.Infinite) :
    Stage3Case024.OnlineGenerator :=
  fun _ input output => Classical.choose
    (hK.exists_not_mem_finset
      ((Finset.univ.image input) ∪ (Finset.univ.image output)))

lemma freshGenerator_spec (K : Language) (hK : K.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshGenerator K hK t input output ∈ K ∧
      freshGenerator K hK t input output ∉ Finset.univ.image input ∧
      freshGenerator K hK t input output ∉ Finset.univ.image output := by
  unfold freshGenerator
  simpa only [Finset.mem_union, not_or] using
    Classical.choose_spec
      (hK.exists_not_mem_finset
        ((Finset.univ.image input) ∪ (Finset.univ.image output)))

noncomputable def generatedOutput
    (K : Language) (hK : K.Infinite) (input : Stream) : Stream := by
  let rec output (t : ℕ) : ℕ :=
    freshGenerator K hK t (fun i => input i) (fun i => output i)
  termination_by t
  decreasing_by exact i.isLt
  exact output

lemma generatedOutput_follows
    (K : Language) (hK : K.Infinite) (input : Stream) :
    Stage3Case024.Follows (freshGenerator K hK) input
      (generatedOutput K hK input) := by
  intro t
  exact generatedOutput.output.eq_def K hK input t

lemma generatedOutput_novel
    (K : Language) (hK : K.Infinite) (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (generatedOutput K hK input) K := by
  refine ⟨0, ?_⟩
  intro t ht
  have hspec := freshGenerator_spec K hK t
    (fun i => input i) (fun i => generatedOutput K hK input i)
  rw [← generatedOutput_follows K hK input t] at hspec
  refine ⟨hspec.1, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    apply hspec.2.1
    apply Finset.mem_image.mpr
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, heq⟩
  · intro s hs heq
    apply hspec.2.2
    apply Finset.mem_image.mpr
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, heq⟩

lemma globallyFeasible_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  let j0 : Fin r := ⟨0, by omega⟩
  have hK : (nestedFamily r j0).Infinite :=
    sparseSquare_infinite.mono (squares_subset_nestedFamily hr j0)
  refine ⟨freshGenerator (nestedFamily r j0) hK, ?_⟩
  intro input hlegal
  refine ⟨generatedOutput (nestedFamily r j0) hK input,
    generatedOutput_follows _ _ _, ?_⟩
  intro j
  have hnovel := generatedOutput_novel (nestedFamily r j0) hK input
  obtain ⟨T, hT⟩ := hnovel
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hdistinct⟩ := hT t ht
  have hsub : nestedFamily r j0 ⊆ nestedFamily r j := by
    rw [nestedFamily_zero hr]
    exact squares_subset_nestedFamily hr j
  exact ⟨hsub hmem, hfresh, hdistinct⟩

lemma manyTargetObstruction_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output hfollow hmeas hint hvalid
  let j0 : Fin r := ⟨0, by omega⟩
  let jlast : Fin r := ⟨r - 1, by omega⟩
  have hvalid0 : ∀ᵐ ω ∂μ,
      GenLimit.NovelGeneratesInLimit commonInput (output ω)
        {x : ℕ | SparseSquare x} := by
    filter_upwards [hvalid j0] with ω hω
    simpa [j0, nestedFamily_zero hr] using hω
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 := by
    filter_upwards [hvalid0] with ω hω
    exact relativeUpperDensity_univ_eq_zero
      (generatorFirst_diff_sparse_finite hω)
  refine ⟨jlast, ?_⟩
  unfold Stage3Case024.expectedUpperDensity
  rw [show nestedFamily r jlast = Set.univ by
    simpa [jlast] using nestedFamily_last hr]
  rw [integral_congr_ae hzero]
  simp

lemma manyTargetWitness_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonInput := by
  exact ⟨strictlyNested_nestedFamily hr,
    legal_commonInput_nestedFamily hr,
    globallyFeasible_nestedFamily hr,
    manyTargetObstruction_nestedFamily hr⟩

end Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨{x : ℕ | GenLimit.InfiniteContamination.SparseSquare x}, Set.univ,
      Case024Proof.commonInput, ?_, ?_, ?_, Case024Proof.pairObstruction _⟩
    · refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
      intro heq
      have hmem : GenLimit.InfiniteContamination.sparseBetweenSquares 0 ∈
          ({x : ℕ | GenLimit.InfiniteContamination.SparseSquare x} : Set ℕ) := by
        rw [heq]
        trivial
      exact GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare 0 hmem
    · constructor
      · exact Case024Proof.sparseSquare_infinite
      · refine ⟨Case024Proof.commonInput_injective, ?_, ?_⟩
        · unfold GenLimit.InfiniteContamination.NoOmissions
          rw [Case024Proof.range_commonInput]
          exact Set.subset_univ _
        · unfold Case024Proof.commonInput
          exact GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
            Case024Proof.sparseSquare_infinite Set.Subset.rfl
    · constructor
      · exact Set.infinite_univ
      · refine ⟨Case024Proof.commonInput_injective, ?_, ?_⟩
        · unfold GenLimit.InfiniteContamination.NoOmissions
          rw [Case024Proof.range_commonInput]
        · unfold Case024Proof.commonInput
          exact GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
            Case024Proof.sparseSquare_infinite (Set.subset_univ _)
  · intro r hr
    exact ⟨Case024Proof.nestedFamily r, Case024Proof.commonInput,
      Case024Proof.manyTargetWitness_nestedFamily hr⟩
