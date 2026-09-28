import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

def core : Set ℕ := {n | SparseSquare n}

theorem core_infinite : core.Infinite := by
  let f : ℕ → ℕ := fun n => n * n
  have hf : Function.Injective f := by
    intro a b hab
    exact Nat.mul_self_inj.mp hab
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n, rfl⟩
  exact sparseSquare_mul_self n

noncomputable def commonStream : Stage3Case024.Stream :=
  sparseMergePresentation core coreᶜ core_infinite

theorem commonStream_injective : Function.Injective commonStream := by
  apply sparseMergePresentation_injective core_infinite
  exact Set.disjoint_compl_right_iff_subset.mpr (Set.Subset.rfl)

theorem commonStream_range : Set.range commonStream = Set.univ := by
  rw [commonStream, range_sparseMergePresentation core_infinite]
  exact Set.union_compl_self core

theorem legal_commonStream_of_core_subset
    {K : Stage3Case024.Language} (hcore : core ⊆ K) (hK : K.Infinite) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨hK, commonStream_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonStream_range]
    exact Set.subset_univ K
  · exact sparseMergePresentation_vanishingNoise_of_core_subset core_infinite hcore

theorem prefixCount_nonneg_ratio (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

theorem prefixCount_inter_le (A K : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∩ K) n ≤
      GenLimit.PatientScope.prefixCount K n := by
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hx.2.2⟩

theorem prefixRatio_le_one (A K : Set ℕ) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · rw [div_le_one]
    · exact_mod_cast prefixCount_inter_le A K n
    · exact_mod_cast Nat.pos_of_ne_zero hzero

theorem relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall (prefixCount_nonneg_ratio A K)
  · exact isBoundedUnder_of ⟨1, prefixRatio_le_one A K⟩

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (prefixCount_nonneg_ratio A K)
  · exact Eventually.of_forall (prefixRatio_le_one A K)

theorem prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

theorem prefixCount_core (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n = Nat.count SparseSquare n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range, core]

theorem prefixCount_le_core_add_finite
    {A : Set ℕ} (F : Finset ℕ) (hA : A ⊆ core ∪ (F : Set ℕ)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount core n + F.card := by
  classical
  calc
    GenLimit.PatientScope.prefixCount A n ≤
        (GenLimit.PatientScope.prefixFinset core n ∪ F).card := by
      apply Finset.card_le_card
      intro x hx
      rw [GenLimit.PatientScope.mem_prefixFinset] at hx
      rcases hA hx.2 with hxcore | hxF
      · exact Finset.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx.1, hxcore⟩)
      · exact Finset.mem_union_right _ hxF
    _ ≤ (GenLimit.PatientScope.prefixFinset core n).card + F.card :=
      Finset.card_union_le _ _
    _ = GenLimit.PatientScope.prefixCount core n + F.card := rfl

theorem tendsto_square_error_div (B : ℕ) :
    Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + B) / (n : ℝ))
      atTop (𝓝 0) := by
  have hB : Tendsto (fun n : ℕ => (B : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [add_div, zero_add] using tendsto_sparseSqrt_add_one_div.add hB

theorem relativeUpperDensity_univ_eq_zero_of_subset_core_finite
    {A : Set ℕ} (F : Finset ℕ) (hA : A ⊆ core ∪ (F : Set ℕ)) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  have hbound : ∀ n,
      (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount Set.univ n : ℝ) ≤
        ((Nat.sqrt n : ℝ) + 1 + F.card) / (n : ℝ) := by
    intro n
    simp only [Set.inter_univ, prefixCount_univ]
    apply div_le_div_of_nonneg_right
    · have hc := prefixCount_le_core_add_finite F hA n
      rw [prefixCount_core] at hc
      exact_mod_cast (hc.trans
        (Nat.add_le_add_right (count_sparseSquare_le_sqrt_add_one n) F.card))
    · positivity
  apply le_antisymm
  · unfold Stage3Case024.relativeUpperDensity
    calc
      limsup
          (fun n : ℕ =>
            (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
              (GenLimit.PatientScope.prefixCount Set.univ n : ℝ)) atTop ≤
          limsup (fun n : ℕ =>
            ((Nat.sqrt n : ℝ) + 1 + F.card) / (n : ℝ)) atTop := by
        apply limsup_le_limsup
        · exact Eventually.of_forall hbound
        · exact isCoboundedUnder_le_of_le atTop
            (prefixCount_nonneg_ratio A Set.univ)
        · exact (tendsto_square_error_div F.card).isBoundedUnder_le
      _ = 0 := (tendsto_square_error_div F.card).limsup_eq
  · exact relativeUpperDensity_nonneg A Set.univ

theorem generatorFirst_subset_core_union_prefix
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output core) :
    ∃ F : Finset ℕ, GenLimit.GeneratorFirst input output ⊆ core ∪ (F : Set ℕ) := by
  obtain ⟨T, hT⟩ := hvalid
  refine ⟨Finset.image output (Finset.range T), ?_⟩
  intro x hx
  obtain ⟨t, htx, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (htx ▸ (hT t ht).1)
  · exact Set.mem_union_right _ (by
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨t, Finset.mem_range.mpr (Nat.lt_of_not_ge ht), htx⟩)

theorem relativeUpperDensity_generatorFirst_univ_eq_zero
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output core) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨F, hF⟩ := generatorFirst_subset_core_union_prefix hvalid
  exact relativeUpperDensity_univ_eq_zero_of_subset_core_finite F hF

noncomputable def historyBound {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : ℕ :=
  max (Finset.univ.sup input) (Finset.univ.sup output)

noncomputable def freshSquareGenerator : Stage3Case024.OnlineGenerator :=
  fun _ input output => (historyBound input output + 1) * (historyBound input output + 1)

theorem input_le_historyBound {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (i : Fin (t + 1)) :
    input i ≤ historyBound input output := by
  exact (Finset.le_sup (f := input) (Finset.mem_univ i)).trans (Nat.le_max_left _ _)

theorem output_le_historyBound {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (i : Fin t) :
    output i ≤ historyBound input output := by
  exact (Finset.le_sup (f := output) (Finset.mem_univ i)).trans (Nat.le_max_right _ _)

theorem freshSquareGenerator_mem_core {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshSquareGenerator t input output ∈ core := by
  exact ⟨historyBound input output + 1, rfl⟩

theorem freshSquareGenerator_ne_input {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (i : Fin (t + 1)) :
    freshSquareGenerator t input output ≠ input i := by
  have hi := input_le_historyBound input output i
  unfold freshSquareGenerator
  nlinarith

theorem freshSquareGenerator_ne_output {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (i : Fin t) :
    freshSquareGenerator t input output ≠ output i := by
  have hi := output_le_historyBound input output i
  unfold freshSquareGenerator
  nlinarith

noncomputable def runFreshSquare (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => freshSquareGenerator t (fun i => input i) (fun i => runFreshSquare input i)
termination_by t => t
decreasing_by exact i.isLt

theorem runFreshSquare_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshSquareGenerator input (runFreshSquare input) := by
  intro t
  rw [runFreshSquare]

theorem runFreshSquare_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (runFreshSquare input) core := by
  refine ⟨0, ?_⟩
  intro t _
  rw [runFreshSquare]
  refine ⟨freshSquareGenerator_mem_core _ _, ?_, ?_⟩
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨i, hi, heq⟩ := hmem
    exact freshSquareGenerator_ne_input
      (fun j : Fin (t + 1) => input j)
      (fun j : Fin t => runFreshSquare input j)
      ⟨i, hi⟩ heq.symm
  · intro s hs heq
    exact freshSquareGenerator_ne_output
      (fun j : Fin (t + 1) => input j)
      (fun j : Fin t => runFreshSquare input j)
      ⟨s, hs⟩ heq.symm


theorem novel_mono {input output : Stage3Case024.Stream} {K L : Set ℕ}
    (hKL : K ⊆ L) (h : GenLimit.NovelGeneratesInLimit input output K) :
    GenLimit.NovelGeneratesInLimit input output L := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hKL hmem, hfresh, hnovel⟩


def extra (j : ℕ) : Set ℕ :=
  {x | ∃ k < j, sparseBetweenSquares k = x}


def layer (j : ℕ) : Set ℕ := core ∪ extra j


def family (r : ℕ) (j : Fin r) : Stage3Case024.Language :=
  if (j : ℕ) + 1 = r then Set.univ else layer j


theorem extra_mono {i j : ℕ} (hij : i ≤ j) : extra i ⊆ extra j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, hk.trans_le hij, rfl⟩


theorem sparseBetweenSquares_not_core (k : ℕ) :
    sparseBetweenSquares k ∉ core :=
  sparseBetweenSquares_nonsquare k


theorem sparseBetweenSquares_not_extra_self (i : ℕ) :
    sparseBetweenSquares i ∉ extra i := by
  rintro ⟨k, hk, heq⟩
  have := sparseBetweenSquares_strictMono.injective heq
  omega


theorem sparseBetweenSquares_not_layer_self (i : ℕ) :
    sparseBetweenSquares i ∉ layer i := by
  rintro (hi | hi)
  · exact sparseBetweenSquares_not_core i hi
  · exact sparseBetweenSquares_not_extra_self i hi


theorem layer_subset {i j : ℕ} (hij : i ≤ j) : layer i ⊆ layer j := by
  intro x hx
  rcases hx with hx | hx
  · exact Set.mem_union_left _ hx
  · exact Set.mem_union_right _ (extra_mono hij hx)


theorem layer_ssubset {i j : ℕ} (hij : i < j) : layer i ⊂ layer j := by
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨layer_subset hij.le, ?_⟩
  intro heq
  have hmem : sparseBetweenSquares i ∈ layer j :=
    Set.mem_union_right _ ⟨i, hij, rfl⟩
  exact sparseBetweenSquares_not_layer_self i (heq ▸ hmem)


theorem layer_infinite (j : ℕ) : (layer j).Infinite :=
  core_infinite.mono (fun _ hx => Set.mem_union_left _ hx)


theorem core_subset_layer (j : ℕ) : core ⊆ layer j :=
  fun _ hx => Set.mem_union_left _ hx


theorem family_zero {r : ℕ} (hr : 2 ≤ r) :
    family r ⟨0, Nat.zero_lt_of_lt hr⟩ = core := by
  simp [family, layer, extra]
  omega


theorem family_last {r : ℕ} (hr : 2 ≤ r) :
    family r ⟨r - 1, Nat.sub_lt (by omega) (by omega)⟩ = Set.univ := by
  simp [family]
  omega


theorem core_subset_family {r : ℕ} (j : Fin r) : core ⊆ family r j := by
  unfold family
  split
  · exact Set.subset_univ _
  · exact core_subset_layer j


theorem family_infinite {r : ℕ} (j : Fin r) : (family r j).Infinite := by
  exact core_infinite.mono (core_subset_family j)


theorem family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (family r) := by
  intro i j hij
  have hilast : (i : ℕ) + 1 ≠ r := by omega
  by_cases hjlast : (j : ℕ) + 1 = r
  · change (if (i : ℕ) + 1 = r then Set.univ else layer i) ⊂
      (if (j : ℕ) + 1 = r then Set.univ else layer j)
    rw [if_pos hjlast, if_neg hilast]
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hmem : sparseBetweenSquares i ∈ (Set.univ : Set ℕ) := Set.mem_univ _
    exact sparseBetweenSquares_not_layer_self i (heq ▸ hmem)
  · change (if (i : ℕ) + 1 = r then Set.univ else layer i) ⊂
      (if (j : ℕ) + 1 = r then Set.univ else layer j)
    rw [if_neg hjlast, if_neg hilast]
    exact layer_ssubset hij


theorem family_legal {r : ℕ} (j : Fin r) :
    Stage3Case024.Legal commonStream (family r j) :=
  legal_commonStream_of_core_subset (core_subset_family j) (family_infinite j)


theorem globallyFeasible_family {r : ℕ} :
    Stage3Case024.GloballyFeasible (family r) := by
  refine ⟨freshSquareGenerator, ?_⟩
  intro input _
  refine ⟨runFreshSquare input, runFreshSquare_follows input, ?_⟩
  intro j
  exact novel_mono (core_subset_family j) (runFreshSquare_novel input)


theorem pairObstruction :
    Stage3Case024.PairObstruction core Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hIntCore _ hValidCore _
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ = 0 :=
    hValidCore.mono fun ω hω =>
      relativeUpperDensity_generatorFirst_univ_eq_zero hω
  have hExpectedUniv :
      Stage3Case024.expectedUpperDensity μ Set.univ commonStream output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    exact (integral_congr_ae hzero).trans (integral_zero Ω ℝ)
  have hCoreLe :
      Stage3Case024.expectedUpperDensity μ core commonStream output ≤ 1 := by
    unfold Stage3Case024.DensityIntegrable at hIntCore
    unfold Stage3Case024.expectedUpperDensity
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have hle := integral_mono_ae hIntCore hconst
      (Filter.Eventually.of_forall fun ω =>
        relativeUpperDensity_le_one
          (GenLimit.GeneratorFirst commonStream (output ω)) core)
    simpa using hle
  constructor
  · rw [hExpectedUniv]
    linarith
  · intro hboth
    rw [hExpectedUniv] at hboth
    linarith


theorem manyTargetObstruction_family {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (family r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hValid
  let first : Fin r := ⟨0, Nat.zero_lt_of_lt hr⟩
  let last : Fin r := ⟨r - 1, Nat.sub_lt (by omega) (by omega)⟩
  have hcoreValid : Stage3Case024.EventuallyFreshValid μ core commonStream output := by
    simpa [first, family_zero hr] using hValid first
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ = 0 :=
    hcoreValid.mono fun ω hω =>
      relativeUpperDensity_generatorFirst_univ_eq_zero hω
  refine ⟨last, ?_⟩
  rw [show family r last = Set.univ by simpa [last] using family_last hr]
  unfold Stage3Case024.expectedUpperDensity
  exact (integral_congr_ae hzero).trans (integral_zero Ω ℝ)


theorem manyTargetWitness_family {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (family r) commonStream := by
  refine ⟨family_strictlyNested hr, ?_, globallyFeasible_family,
    manyTargetObstruction_family hr⟩
  exact family_legal

end Case024
