import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024

open Stage3Case024
open GenLimit
open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

abbrev Core : Set ℕ := {n | SparseSquare n}
abbrev Exceptional : Set ℕ := Coreᶜ

lemma core_infinite : Core.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n => n * n)
  · intro a b h
    nlinarith
  · intro n
    exact sparseSquare_mul_self n

lemma exceptional_infinite : Exceptional.Infinite := by
  exact sparseNonSquare_infinite

lemma core_exceptional_disjoint : Disjoint Core Exceptional := by
  rw [Set.disjoint_left]
  simp

noncomputable def commonInput : Stream :=
  squareSparseMerge Core Exceptional core_infinite exceptional_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  exact squareSparseMerge_injective core_infinite exceptional_infinite
    core_exceptional_disjoint

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_squareSparseMerge core_infinite exceptional_infinite]
  exact Set.union_compl_self Core

lemma commonInput_legal_of_core_subset {K : Set ℕ} (hcore : Core ⊆ K)
    (hinf : K.Infinite) : Legal commonInput K := by
  refine ⟨hinf, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      core_infinite exceptional_infinite hcore

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  have heq :
      (↑(GenLimit.PatientScope.prefixFinset (A ∪ B) n) : Set ℕ) =
        (↑(GenLimit.PatientScope.prefixFinset A n) : Set ℕ) ∪
          (↑(GenLimit.PatientScope.prefixFinset B n) : Set ℕ) := by
    ext x
    constructor
    · intro hx
      have hx' := GenLimit.PatientScope.mem_prefixFinset.mp
        (show x ∈ GenLimit.PatientScope.prefixFinset (A ∪ B) n from hx)
      rcases hx'.2 with hxA | hxB
      · exact Set.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxA⟩)
      · exact Set.mem_union_right _
          (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · intro hx
      rcases hx with hxA | hxB
      · have hxA' := GenLimit.PatientScope.mem_prefixFinset.mp
          (show x ∈ GenLimit.PatientScope.prefixFinset A n from hxA)
        exact GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨hxA'.1, Set.mem_union_left _ hxA'.2⟩
      · have hxB' := GenLimit.PatientScope.mem_prefixFinset.mp
          (show x ∈ GenLimit.PatientScope.prefixFinset B n from hxB)
        exact GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨hxB'.1, Set.mem_union_right _ hxB'.2⟩
  rw [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixCount, ← Set.ncard_coe_finset,
    ← Set.ncard_coe_finset, ← Set.ncard_coe_finset, heq]
  exact Set.ncard_union_le _ _

lemma prefixCount_le (A : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simpa using Finset.card_filter_le (s := Finset.range n) (p := fun x => x ∈ A)

lemma prefixCount_core (n : ℕ) :
    GenLimit.PatientScope.prefixCount Core n = Nat.count SparseSquare n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range, Core]

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ relativeUpperDensity A K := by
  unfold relativeUpperDensity
  apply le_limsup_of_frequently_le
  · apply Frequently.of_forall
    intro n
    positivity
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · apply (div_le_one (by positivity)).2
        exact_mod_cast prefixCount_mono Set.inter_subset_right n⟩

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · apply Eventually.of_forall
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono Set.inter_subset_right n

lemma generatorFirst_subset_range (input output : Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, ht, -⟩
  exact ⟨t, ht⟩

lemma range_eventually_core_subset (output : Stream)
    (h : GenLimit.NovelGeneratesInLimit commonInput output Core) :
    Set.range output ⊆ Core ∪ Set.range (fun i : Fin h.choose => output i) := by
  rintro x ⟨t, rfl⟩
  by_cases ht : h.choose ≤ t
  · exact Set.mem_union_left _ ((h.choose_spec t ht).1)
  · exact Set.mem_union_right _ ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩

lemma prefixCount_range_fin_le (output : Stream) (T n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.range (fun i : Fin T => output i)) n ≤ T := by
  classical
  let values : Set ℕ := Set.range (fun i : Fin T => output i)
  have hfinite : values.Finite := Set.finite_range _
  have hprefix :
      (↑(GenLimit.PatientScope.prefixFinset values n) : Set ℕ) ⊆ values := by
    intro x hx
    exact (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
  calc
    GenLimit.PatientScope.prefixCount values n
        = Set.ncard (↑(GenLimit.PatientScope.prefixFinset values n) : Set ℕ) := by
          rw [GenLimit.PatientScope.prefixCount, Set.ncard_coe_finset]
    _ ≤ Set.ncard values := Set.ncard_le_ncard hprefix hfinite
    _ ≤ T := by
      rw [show values = (fun i : Fin T => output i) '' Set.univ by
        ext x
        simp [values]]
      simpa using Set.ncard_image_le (f := fun i : Fin T => output i)
        (s := Set.univ)

lemma prefixCount_generatorFirst_le (output : Stream)
    (h : GenLimit.NovelGeneratesInLimit commonInput output Core) (n : ℕ) :
    GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst commonInput output) n ≤
      Nat.sqrt n + 1 + h.choose := by
  calc
    GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst commonInput output) n
        ≤ GenLimit.PatientScope.prefixCount
            (Core ∪ Set.range (fun i : Fin h.choose => output i)) n :=
      prefixCount_mono
        (Set.Subset.trans (generatorFirst_subset_range commonInput output)
          (range_eventually_core_subset output h)) n
    _ ≤ GenLimit.PatientScope.prefixCount Core n +
          GenLimit.PatientScope.prefixCount
            (Set.range (fun i : Fin h.choose => output i)) n :=
      prefixCount_union_le Core
        (Set.range (fun i : Fin h.choose => output i)) n
    _ ≤ (Nat.sqrt n + 1) + h.choose := by
      gcongr
      · rw [prefixCount_core]
        exact count_sparseSquare_le_sqrt_add_one n
      · exact prefixCount_range_fin_le output h.choose n

lemma tendsto_sparse_bound (T : ℕ) :
    Tendsto (fun n : ℕ => (((Nat.sqrt n + 1 + T : ℕ) : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
  have hT : Tendsto (fun n : ℕ => (T : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  simpa only [Nat.cast_add, Nat.cast_one, add_div, zero_add] using
    tendsto_sparseSqrt_add_one_div.add hT

lemma relativeUpperDensity_univ_eq_zero (output : Stream)
    (h : GenLimit.NovelGeneratesInLimit commonInput output Core) :
    relativeUpperDensity (GenLimit.GeneratorFirst commonInput output) Set.univ = 0 := by
  apply Tendsto.limsup_eq
  simp only [Set.inter_univ]
  apply squeeze_zero
  · intro n
    positivity
  · intro n
    have hcast :
        (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst commonInput output) n : ℝ) ≤
          (Nat.sqrt n + 1 + h.choose : ℕ) := by
      exact_mod_cast prefixCount_generatorFirst_le output h n
    simpa only [prefixCount_univ] using
      div_le_div_of_nonneg_right hcast (by positivity)
  · exact tendsto_sparse_bound h.choose

lemma pair_obstruction : PairObstruction Core Set.univ commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas hintCore hintUniv hvalidCore _hvalidUniv
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hvalidCore.mono fun ω hω => relativeUpperDensity_univ_eq_zero (output ω) hω
  have eintUniv : expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold expectedUpperDensity
    exact (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun ω => relativeUpperDensity_nonneg _ _) hintUniv).2 hzero
  have eintCore : expectedUpperDensity μ Core commonInput output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      (∫ ω, relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Core ∂μ)
          ≤ ∫ _ω, (1 : ℝ) ∂μ :=
        integral_mono_ae hintCore (integrable_const 1)
          (Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _)
      _ = 1 := by simp
  rw [eintUniv, add_zero]
  refine ⟨eintCore, ?_⟩
  intro hboth
  linarith


def marker (k : ℕ) : ℕ := sparseBetweenSquares k

lemma marker_nonsquare (k : ℕ) : marker k ∉ Core :=
  sparseBetweenSquares_nonsquare k

lemma marker_injective : Function.Injective marker :=
  sparseBetweenSquares_strictMono.injective

def markerPrefix (j : ℕ) : Set ℕ := marker '' Set.Iio j

lemma marker_mem_prefix {k j : ℕ} (hkj : k < j) : marker k ∈ markerPrefix j :=
  ⟨k, hkj, rfl⟩

lemma marker_not_mem_prefix_self (k : ℕ) : marker k ∉ markerPrefix k := by
  rintro ⟨q, hq, heq⟩
  exact (Nat.ne_of_lt hq) (marker_injective heq)

lemma markerPrefix_mono {i j : ℕ} (hij : i ≤ j) :
    markerPrefix i ⊆ markerPrefix j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

def nestedFamily (r : ℕ) (j : Fin r) : Set ℕ :=
  if (j : ℕ) = r - 1 then Set.univ else Core ∪ markerPrefix j

lemma nestedFamily_core_subset (r : ℕ) (j : Fin r) :
    Core ⊆ nestedFamily r j := by
  intro x hx
  unfold nestedFamily
  by_cases hj : (j : ℕ) = r - 1
  · rw [if_pos hj]
    exact Set.mem_univ x
  · rw [if_neg hj]
    exact Set.mem_union_left _ hx

lemma nestedFamily_infinite (r : ℕ) (j : Fin r) :
    (nestedFamily r j).Infinite :=
  core_infinite.mono (nestedFamily_core_subset r j)

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = Core := by
  unfold nestedFamily
  have hzero : (0 : ℕ) ≠ r - 1 := by omega
  rw [if_neg hzero]
  ext x
  constructor
  · rintro (hx | ⟨k, hk, rfl⟩)
    · exact hx
    · exact (Nat.not_lt_zero k hk).elim
  · intro hx
    exact Set.mem_union_left _ hx

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  unfold nestedFamily
  rw [if_pos rfl]

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiLast : (i : ℕ) ≠ r - 1 := by omega
  by_cases hjLast : (j : ℕ) = r - 1
  · change (if (i : ℕ) = r - 1 then Set.univ else Core ∪ markerPrefix i) ⊂
      (if (j : ℕ) = r - 1 then Set.univ else Core ∪ markerPrefix j)
    rw [if_neg hiLast, if_pos hjLast]
    refine Set.ssubset_univ_iff.mpr ?_
    intro heq
    have hm : marker r ∈ Core ∪ markerPrefix i := by
      rw [heq]
      exact Set.mem_univ _
    rcases hm with hmCore | ⟨k, hk, heqMarker⟩
    · exact marker_nonsquare r hmCore
    · have hkr : k = r := marker_injective heqMarker
      subst k
      exact (Nat.not_lt_of_ge (Nat.le_of_lt i.isLt)) hk
  · change (if (i : ℕ) = r - 1 then Set.univ else Core ∪ markerPrefix i) ⊂
      (if (j : ℕ) = r - 1 then Set.univ else Core ∪ markerPrefix j)
    rw [if_neg hiLast, if_neg hjLast]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | ⟨k, hk, rfl⟩
      · exact Set.mem_union_left _ hx
      · exact Set.mem_union_right _ ⟨k, lt_trans hk hij, rfl⟩
    · intro hsub
      have hm : marker i ∈ Core ∪ markerPrefix i :=
        hsub (Set.mem_union_right _ (marker_mem_prefix hij))
      rcases hm with hmCore | hmPrefix
      · exact marker_nonsquare i hmCore
      · exact marker_not_mem_prefix_self i hmPrefix

noncomputable def prefixSum (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ :=
  ∑ i, xs i

noncomputable def squareGenerator : OnlineGenerator :=
  fun t xs _ys => (prefixSum t xs + t + 1) * (prefixSum t xs + t + 1)

noncomputable def squareOutput (input : Stream) : Stream :=
  fun t => squareGenerator t (fun i => input i) (fun _ => 0)

lemma squareOutput_follows (input : Stream) :
    Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

lemma input_le_prefixSum (input : Stream) (t : ℕ) (i : Fin (t + 1)) :
    input i ≤ prefixSum t (fun q => input q) := by
  unfold prefixSum
  simpa using (Finset.single_le_sum
    (s := Finset.univ)
    (f := fun q : Fin (t + 1) => input q)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i))

lemma prefixSum_mono (input : Stream) {s t : ℕ} (hst : s ≤ t) :
    prefixSum s (fun q => input q) ≤ prefixSum t (fun q => input q) := by
  unfold prefixSum
  rw [Fin.sum_univ_eq_sum_range input (s + 1),
    Fin.sum_univ_eq_sum_range input (t + 1)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hst)) (fun _ _ _ => Nat.zero_le _)

lemma squareOutput_mem_core (input : Stream) (t : ℕ) :
    squareOutput input t ∈ Core := by
  exact ⟨prefixSum t (fun q => input q) + t + 1, rfl⟩

lemma squareOutput_fresh_input (input : Stream) (t : ℕ) :
    squareOutput input t ∉ GenLimit.sample input (t + 1) := by
  rw [GenLimit.mem_sample_iff]
  rintro ⟨s, hst, hs⟩
  let b := prefixSum t (fun q => input q) + t + 1
  have hsle : input s ≤ prefixSum t (fun q => input q) :=
    input_le_prefixSum input t ⟨s, hst⟩
  have hltb : input s < b := by
    dsimp [b]
    omega
  have hble : b ≤ b * b := by
    apply Nat.le_mul_self
  have : input s < squareOutput input t := by
    exact lt_of_lt_of_le hltb hble
  omega

lemma squareOutput_strictMono (input : Stream) : StrictMono (squareOutput input) := by
  apply strictMono_nat_of_lt_succ
  intro t
  let a := prefixSum t (fun q => input q) + t + 1
  let b := prefixSum (t + 1) (fun q => input q) + (t + 1) + 1
  have hab : a < b := by
    dsimp [a, b]
    have hsum := prefixSum_mono input (s := t) (t := t + 1) (Nat.le_succ t)
    omega
  dsimp [squareOutput, squareGenerator]
  exact Nat.mul_self_lt_mul_self hab

lemma squareOutput_novel (input : Stream) {K : Set ℕ} (hcore : Core ⊆ K) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) K := by
  refine ⟨0, ?_⟩
  intro t _ht
  refine ⟨hcore (squareOutput_mem_core input t), squareOutput_fresh_input input t, ?_⟩
  intro s hst
  exact ne_of_lt (squareOutput_strictMono input hst)

lemma nestedFamily_globallyFeasible {r : ℕ} (hr : 2 ≤ r) :
    GloballyFeasible (nestedFamily r) := by
  refine ⟨squareGenerator, ?_⟩
  intro input _hlegal
  refine ⟨squareOutput input, squareOutput_follows input, ?_⟩
  intro j
  exact squareOutput_novel input (nestedFamily_core_subset r j)

lemma nestedFamily_obstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas hint hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hvalidCore : EventuallyFreshValid μ Core commonInput output := by
    simpa [first, nestedFamily_zero hr] using hvalid first
  have hzeroPath : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hvalidCore.mono fun ω hω => relativeUpperDensity_univ_eq_zero (output ω) hω
  refine ⟨last, ?_⟩
  rw [show nestedFamily r last = Set.univ by
    simpa [last] using nestedFamily_last hr]
  unfold expectedUpperDensity
  exact (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun ω => relativeUpperDensity_nonneg _ _)
    (by simpa [last, nestedFamily_last hr] using hint last)).2 hzeroPath

lemma nestedFamily_witness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨nestedFamily_strict hr, ?_, nestedFamily_globallyFeasible hr,
    nestedFamily_obstruction hr⟩
  intro j
  exact commonInput_legal_of_core_subset
    (nestedFamily_core_subset r j) (nestedFamily_infinite r j)

lemma core_strict_univ : Core ⊂ (Set.univ : Set ℕ) := by
  apply Set.ssubset_univ_iff.mpr
  intro heq
  exact marker_nonsquare 0 (heq ▸ Set.mem_univ (marker 0))

end Case024

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  refine ⟨?_, ?_⟩
  · exact ⟨Core, Set.univ, commonInput, core_strict_univ,
      commonInput_legal_of_core_subset Set.Subset.rfl core_infinite,
      commonInput_legal_of_core_subset (Set.subset_univ Core) Set.infinite_univ,
      pair_obstruction⟩
  · intro r hr
    exact ⟨nestedFamily r, commonInput, nestedFamily_witness hr⟩
