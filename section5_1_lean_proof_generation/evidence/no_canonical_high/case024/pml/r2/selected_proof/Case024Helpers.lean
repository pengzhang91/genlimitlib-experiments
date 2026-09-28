import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper17_InfiniteContamination.EvenDensity
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

abbrev Core : Set ℕ :=
  {n | GenLimit.InfiniteContamination.SparseSquare n}

lemma core_infinite : Core.Infinite := by
  have hmono : StrictMono (fun n : ℕ => n * n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    nlinarith
  apply (Set.infinite_range_of_injective hmono.injective).mono
  rintro _ ⟨n, rfl⟩
  exact ⟨n, rfl⟩

lemma relativeUpperDensity_univ (A : Set ℕ) :
    Stage3Case024.relativeUpperDensity A Set.univ =
      GenLimit.InfiniteContamination.naturalOrder.upperDensity A := by
  unfold Stage3Case024.relativeUpperDensity
  unfold GenLimit.KleinbergWei.OrderedLanguage.upperDensity
  congr 1
  funext n
  rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio]
  by_cases hn : n = 0
  · subst n
    simp [GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset,
      GenLimit.KleinbergWei.OrderedLanguage.prefixCount,
      GenLimit.InfiniteContamination.naturalOrder]
  · have hnum :
        GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n =
          GenLimit.InfiniteContamination.naturalOrder.prefixCount A n := by
      unfold GenLimit.PatientScope.prefixCount
      unfold GenLimit.PatientScope.prefixFinset
      unfold GenLimit.KleinbergWei.OrderedLanguage.prefixCount
      congr 1
      ext x
      simp [GenLimit.InfiniteContamination.naturalOrder]

    rw [hnum]
    simp [hn, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]

lemma core_prefixRatio_tendsto_zero :
    Tendsto
      (GenLimit.InfiniteContamination.naturalOrder.prefixRatio Core)
      atTop (𝓝 0) := by
  refine squeeze_zero
    (fun n => GenLimit.InfiniteContamination.naturalOrder.prefixRatio_nonneg Core n)
    (fun n => ?_) GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div
  by_cases hn : n = 0
  · subst n
    simp
  · rw [GenLimit.KleinbergWei.OrderedLanguage.prefixRatio, if_neg hn]
    have hcount :
        GenLimit.InfiniteContamination.naturalOrder.prefixCount Core n ≤
          Nat.sqrt n + 1 := by
      simpa [GenLimit.KleinbergWei.OrderedLanguage.prefixCount,
        GenLimit.InfiniteContamination.naturalOrder, Core,
        Nat.count_eq_card_filter_range] using
        GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount)
      (Nat.cast_nonneg n)

lemma core_upperDensity_zero :
    GenLimit.InfiniteContamination.naturalOrder.upperDensity Core = 0 := by
  exact core_prefixRatio_tendsto_zero.limsup_eq

lemma relativeUpperDensity_zero_of_subset_core_union_finite
    {A F : Set ℕ} (hF : F.Finite) (hA : A ⊆ Core ∪ F) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  rw [relativeUpperDensity_univ]
  apply le_antisymm
  · calc
      GenLimit.InfiniteContamination.naturalOrder.upperDensity A ≤
          GenLimit.InfiniteContamination.naturalOrder.upperDensity (Core ∪ F) :=
        GenLimit.InfiniteContamination.naturalOrder.upperDensity_mono hA
      _ ≤ GenLimit.InfiniteContamination.naturalOrder.upperDensity Core +
          GenLimit.InfiniteContamination.naturalOrder.upperDensity F :=
        GenLimit.InfiniteContamination.naturalOrder.upperDensity_union_le Core F
      _ = 0 := by
        rw [core_upperDensity_zero,
          GenLimit.InfiniteContamination.naturalOrder.upperDensity_eq_zero_of_finite hF]
        norm_num
  · exact GenLimit.InfiniteContamination.naturalOrder.upperDensity_nonneg A

lemma generatorFirst_subset_core_union_finite
    {input output : Stage3Case024.Stream}
    (h : GenLimit.NovelGeneratesInLimit input output Core) :
    ∃ F : Set ℕ, F.Finite ∧
      GenLimit.GeneratorFirst input output ⊆ Core ∪ F := by
  obtain ⟨T, hT⟩ := h
  let F : Set ℕ := output '' Set.Iio T
  refine ⟨F, (Set.finite_Iio T).image output, ?_⟩
  intro x hx
  obtain ⟨t, htx, _⟩ := hx
  by_cases ht : T ≤ t
  · apply Or.inl
    rw [← htx]
    exact (hT t ht).1
  · exact Or.inr ⟨t, Nat.lt_of_not_ge ht, htx⟩

lemma density_zero_of_novel_core
    {input output : Stage3Case024.Stream}
    (h : GenLimit.NovelGeneratesInLimit input output Core) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨F, hF, hsub⟩ := generatorFirst_subset_core_union_finite h
  exact relativeUpperDensity_zero_of_subset_core_union_finite hF hsub

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · filter_upwards [] with n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · rw [div_le_one (by positivity)]
      exact_mod_cast Finset.card_le_card (by
        intro x hx
        simp only [GenLimit.PatientScope.prefixFinset] at hx ⊢
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hx.2.2⟩)

end Stage3Case024Proof

namespace Stage3Case024Proof

noncomputable def commonStream : Stage3Case024.Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation
    Core Coreᶜ core_infinite

lemma commonStream_injective : Function.Injective commonStream := by
  apply GenLimit.InfiniteContamination.sparseMergePresentation_injective
    core_infinite
  rw [Set.disjoint_compl_right_iff_subset]

lemma commonStream_range : Set.range commonStream = Set.univ := by
  rw [commonStream,
    GenLimit.InfiniteContamination.range_sparseMergePresentation core_infinite]
  exact Set.union_compl_self Core

lemma commonStream_legal {K : Set ℕ}
    (hcore : Core ⊆ K) (hK : K.Infinite) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨hK, commonStream_injective, ?_, ?_⟩
  · intro x hx
    rw [commonStream_range]
    trivial
  · exact
      GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
        core_infinite hcore

abbrev extraPoint (k : ℕ) : ℕ :=
  GenLimit.InfiniteContamination.sparseBetweenSquares k

def Extras (i : ℕ) : Set ℕ := extraPoint '' Set.Iio i

def Family (r : ℕ) (i : Fin r) : Stage3Case024.Language :=
  if (i : ℕ) = r - 1 then Set.univ else Core ∪ Extras i

lemma extraPoint_injective : Function.Injective extraPoint :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective

lemma extraPoint_not_core (k : ℕ) : extraPoint k ∉ Core :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare k

lemma core_subset_family {r : ℕ} (i : Fin r) : Core ⊆ Family r i := by
  intro x hx
  simp only [Family]
  split
  · trivial
  · exact Or.inl hx

lemma family_infinite {r : ℕ} (i : Fin r) : (Family r i).Infinite :=
  core_infinite.mono (core_subset_family i)

lemma family_zero {r : ℕ} (hr : 2 ≤ r) :
    Family r ⟨0, by omega⟩ = Core := by
  ext x
  simp [Family, Extras]
  omega

lemma family_last {r : ℕ} (hr : 2 ≤ r) :
    Family r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [Family]

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (Family r) := by
  intro i j hij
  have hiLast : (i : ℕ) ≠ r - 1 := by omega
  rw [Set.ssubset_def]
  constructor
  · intro x hx
    by_cases hjLast : (j : ℕ) = r - 1
    · simp [Family, hjLast]
    · simp only [Family, hiLast, if_false] at hx
      simp only [Family, hjLast, if_false]
      rcases hx with hx | ⟨k, hk, rfl⟩
      · exact Or.inl hx
      · have hk' : k < (i : ℕ) := by
          simpa only [Set.mem_Iio] using hk
        exact Or.inr ⟨k, lt_trans hk' hij, rfl⟩
  · intro hback
    have hwj : extraPoint i ∈ Family r j := by
      by_cases hjLast : (j : ℕ) = r - 1
      · simp [Family, hjLast]
      · simp [Family, hjLast, Extras]
        exact Or.inr ⟨i, hij, rfl⟩
    have hwi := hback hwj
    simp only [Family, hiLast, if_false] at hwi
    rcases hwi with hcore | ⟨k, hk, heq⟩
    · exact extraPoint_not_core i hcore
    · have hki : k = i := extraPoint_injective heq
      subst k
      exact (Nat.lt_irrefl i) hk

lemma family_legal {r : ℕ} (i : Fin r) :
    Stage3Case024.Legal commonStream (Family r i) :=
  commonStream_legal (core_subset_family i) (family_infinite i)

noncomputable def usedValues (t : ℕ)
    (input : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image input ∪ Finset.univ.image previous

lemma available_core (t : ℕ)
    (input : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) :
    ∃ x ∈ Core, x ∉ usedValues t input previous :=
  core_infinite.exists_not_mem_finset (usedValues t input previous)

noncomputable def coreGenerator : Stage3Case024.OnlineGenerator :=
  fun t input previous => Classical.choose (available_core t input previous)

lemma coreGenerator_spec (t : ℕ)
    (input : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) :
    coreGenerator t input previous ∈ Core ∧
      coreGenerator t input previous ∉ usedValues t input previous := by
  exact Classical.choose_spec (available_core t input previous)

noncomputable def coreOutput (input : Stage3Case024.Stream) (t : ℕ) : ℕ :=
  coreGenerator t (fun i => input i) (fun i => coreOutput input i)
termination_by t

decreasing_by exact i.isLt

lemma coreOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows coreGenerator input (coreOutput input) := by
  intro t
  rw [coreOutput]

lemma coreOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (coreOutput input) Core := by
  refine ⟨0, ?_⟩
  intro t _
  have hspec := coreGenerator_spec t
    (fun i => input i) (fun i => coreOutput input i)
  refine ⟨?_, ?_, ?_⟩
  · rw [coreOutput]
    exact hspec.1
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    have hmem : input s ∈ usedValues t
        (fun i => input i) (fun i => coreOutput input i) := by
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨⟨s, by omega⟩, Finset.mem_univ _, rfl⟩
    rw [heq] at hmem
    rw [coreOutput] at hmem
    exact hspec.2 hmem
  · intro s hs heq
    have hmem : coreOutput input s ∈ usedValues t
        (fun i => input i) (fun i => coreOutput input i) := by
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩
    rw [heq] at hmem
    rw [coreOutput] at hmem
    exact hspec.2 hmem

lemma globallyFeasible_family {r : ℕ} :
    Stage3Case024.GloballyFeasible (Family r) := by
  refine ⟨coreGenerator, ?_⟩
  intro input _
  refine ⟨coreOutput input, coreOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := coreOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨core_subset_family j hcore, hfresh, hnovel⟩

end Stage3Case024Proof

namespace Stage3Case024Proof

lemma pairObstruction :
    Stage3Case024.PairObstruction Core Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hIntCore hIntUniv hValidCore _
  have hzero :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hValidCore] with ω hω
    exact density_zero_of_novel_core hω
  have hUnivZero :
      Stage3Case024.expectedUpperDensity μ Set.univ commonStream output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzero]
    simp
  have hCoreLe :
      Stage3Case024.expectedUpperDensity μ Core commonStream output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonStream (output ω)) Core ∂μ) ≤
          ∫ _ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hIntCore
          (integrable_const (1 : ℝ))
        exact Filter.Eventually.of_forall fun ω =>
          relativeUpperDensity_le_one
            (GenLimit.GeneratorFirst commonStream (output ω)) Core
      _ = 1 := by simp
  constructor
  · rw [hUnivZero, add_zero]
    exact hCoreLe
  · rw [hUnivZero]
    intro h
    linarith

lemma core_ssubset_univ : Core ⊂ (Set.univ : Set ℕ) := by
  rw [Set.ssubset_def]
  constructor
  · exact Set.subset_univ Core
  · intro h
    exact extraPoint_not_core 0 (h trivial)

lemma manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (Family r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hValid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hcoreValid :
      ∀ᵐ ω ∂μ, GenLimit.NovelGeneratesInLimit commonStream (output ω) Core := by
    have h := hValid first
    unfold Stage3Case024.EventuallyFreshValid at h
    simpa [first, family_zero hr] using h
  refine ⟨last, ?_⟩
  unfold Stage3Case024.expectedUpperDensity
  have hzero :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonStream (output ω)) (Family r last)) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hcoreValid] with ω hω
    rw [show Family r last = Set.univ by simpa [last] using family_last hr]
    exact density_zero_of_novel_core hω
  rw [integral_congr_ae hzero]
  simp

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (Family r) commonStream := by
  refine ⟨family_strictlyNested hr, ?_, globallyFeasible_family,
    manyTargetObstruction hr⟩
  intro j
  exact family_legal j

end Stage3Case024Proof
