import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper17_InfiniteContamination.EvenDensity

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof

open GenLimit
open GenLimit.InfiniteContamination
open GenLimit.KleinbergWei

noncomputable local instance : DecidablePred SparseNonSquare :=
  Classical.decPred _

abbrev core : Set ℕ := {n | SparseSquare n}

theorem core_infinite : core.Infinite := by
  have hmono : StrictMono (fun n : ℕ => n * n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    nlinarith
  exact (Set.infinite_range_of_injective hmono.injective).mono (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩)

theorem core_compl_infinite : coreᶜ.Infinite := by
  simpa [core, SparseNonSquare] using sparseNonSquare_infinite

noncomputable def commonStream : Stage3Case024.Stream :=
  squareSparseMerge core coreᶜ core_infinite core_compl_infinite

theorem commonStream_injective : Function.Injective commonStream := by
  apply squareSparseMerge_injective core_infinite core_compl_infinite
  rw [Set.disjoint_left]
  intro x hx hxc
  exact hxc hx

theorem commonStream_range : Set.range commonStream = Set.univ := by
  rw [commonStream, range_squareSparseMerge core_infinite core_compl_infinite]
  exact Set.union_compl_self core

theorem commonStream_legal_of_core_subset
    {K : Set ℕ} (hinfinite : K.Infinite) (hcore : core ⊆ K) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨hinfinite, commonStream_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonStream_range]
    exact Set.subset_univ K
  · simpa [commonStream] using
      squareSparseMerge_vanishingNoise_of_core_subset
        core_infinite core_compl_infinite hcore

theorem patient_prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

theorem relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall (fun n => div_nonneg (by positivity) (by positivity))
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by positivity)]
        exact_mod_cast patient_prefixCount_mono Set.inter_subset_right n⟩

theorem relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => div_nonneg (by positivity) (by positivity))
  · exact Eventually.of_forall fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by positivity)]
        exact_mod_cast patient_prefixCount_mono Set.inter_subset_right n

theorem relativeUpperDensity_univ_eq (A : Set ℕ) :
    Stage3Case024.relativeUpperDensity A Set.univ =
      naturalOrder.upperDensity A := by
  unfold Stage3Case024.relativeUpperDensity OrderedLanguage.upperDensity
  congr 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
      OrderedLanguage.prefixRatio]
  · simp only [Set.inter_univ]
    simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
      OrderedLanguage.prefixRatio, OrderedLanguage.prefixCount, naturalOrder, hn]

theorem naturalOrder_upperDensity_core :
    naturalOrder.upperDensity core = 0 := by
  apply Tendsto.limsup_eq
  refine squeeze_zero (fun n => naturalOrder.prefixRatio_nonneg core n) ?_
    tendsto_sparseSqrt_add_one_div
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp only [OrderedLanguage.prefixRatio, hn, if_false]
    have hcount : naturalOrder.prefixCount core n ≤ Nat.sqrt n + 1 := by
      simpa [OrderedLanguage.prefixCount, naturalOrder, core,
        Nat.count_eq_card_filter_range] using
        count_sparseSquare_le_sqrt_add_one n
    have hcountReal :
        (naturalOrder.prefixCount core n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
      exact_mod_cast hcount
    exact div_le_div_of_nonneg_right hcountReal (by positivity)

theorem eventual_mem_range_diff_finite
    {output : ℕ → ℕ} {K : Set ℕ}
    (h : ∃ T, ∀ t, T ≤ t → output t ∈ K) :
    (Set.range output \ K).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_range fun t : Fin T => output t).subset
  rintro x ⟨⟨t, rfl⟩, htK⟩
  have ht : t < T := by
    by_contra hnot
    exact htK (hT t (Nat.le_of_not_gt hnot))
  exact ⟨⟨t, ht⟩, rfl⟩

theorem generatorFirst_subset_range (input output : ℕ → ℕ) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, htx, -⟩
  exact ⟨t, htx⟩

theorem relativeUpperDensity_univ_eq_zero_of_eventual_core
    {input output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output core) :
    Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  let F : Set ℕ := Set.range output \ core
  have hF : F.Finite := eventual_mem_range_diff_finite ⟨hvalid.choose, fun t ht =>
    (hvalid.choose_spec t ht).1⟩
  have hsubset : GenLimit.GeneratorFirst input output ⊆ core ∪ F := by
    intro x hx
    have hxrange := generatorFirst_subset_range input output hx
    by_cases hxcore : x ∈ core
    · exact Or.inl hxcore
    · exact Or.inr ⟨hxrange, hxcore⟩
  rw [relativeUpperDensity_univ_eq]
  apply le_antisymm
  · calc
      naturalOrder.upperDensity (GenLimit.GeneratorFirst input output) ≤
          naturalOrder.upperDensity (core ∪ F) :=
        naturalOrder.upperDensity_mono hsubset
      _ ≤ naturalOrder.upperDensity core + naturalOrder.upperDensity F :=
        naturalOrder.upperDensity_union_le core F
      _ = 0 := by rw [naturalOrder_upperDensity_core,
        naturalOrder.upperDensity_eq_zero_of_finite hF, add_zero]
  · exact naturalOrder.upperDensity_nonneg _

theorem expected_univ_eq_zero_of_eventual_core
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : ℕ → ℕ) (output : Ω → ℕ → ℕ)
    (hvalid : Stage3Case024.EventuallyFreshValid μ core input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.expectedUpperDensity
  apply integral_eq_zero_of_ae
  exact hvalid.mono fun ω hω =>
    relativeUpperDensity_univ_eq_zero_of_eventual_core hω


theorem core_ssubset_univ : core ⊂ (Set.univ : Set ℕ) := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have hmem : sparseBetweenSquares 0 ∈ core := by
    rw [h]
    trivial
  exact sparseBetweenSquares_nonsquare 0 hmem

theorem pair_obstruction :
    Stage3Case024.PairObstruction core Set.univ commonStream := by
  intro Ω _ μ _ gen output _hfollow _hmeas hintCore _hintUniv
    hvalidCore _hvalidUniv
  have hzero :
      Stage3Case024.expectedUpperDensity μ Set.univ commonStream output = 0 :=
    expected_univ_eq_zero_of_eventual_core μ commonStream output hvalidCore
  have hle :
      Stage3Case024.expectedUpperDensity μ core commonStream output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonStream (output ω)) core ∂μ) ≤
          ∫ _ω, (1 : ℝ) ∂μ := by
        apply integral_mono_ae hintCore (integrable_const 1)
        exact Eventually.of_forall fun ω =>
          relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · rw [hzero, add_zero]
    exact hle
  · rw [hzero]
    norm_num


def initialExceptional (j : ℕ) : Set ℕ :=
  {x | SparseNonSquare x ∧ Nat.count SparseNonSquare x < j}

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Set ℕ :=
  if (j : ℕ) = r - 1 then Set.univ else core ∪ initialExceptional j

noncomputable def exceptionalPoint (j : ℕ) : ℕ :=
  Nat.nth SparseNonSquare j

@[simp] theorem exceptionalPoint_nonsquare (j : ℕ) :
    SparseNonSquare (exceptionalPoint j) :=
  Nat.nth_mem_of_infinite sparseNonSquare_infinite j

@[simp] theorem count_exceptionalPoint (j : ℕ) :
    Nat.count SparseNonSquare (exceptionalPoint j) = j :=
  Nat.count_nth_of_infinite sparseNonSquare_infinite j

@[simp] theorem exceptionalPoint_not_core (j : ℕ) :
    exceptionalPoint j ∉ core := by
  exact exceptionalPoint_nonsquare j

@[simp] theorem exceptionalPoint_mem_initialExceptional_iff (i j : ℕ) :
    exceptionalPoint i ∈ initialExceptional j ↔ i < j := by
  simp [initialExceptional]

theorem core_subset_nestedFamily (r : ℕ) (j : Fin r) :
    core ⊆ nestedFamily r j := by
  intro x hx
  unfold nestedFamily
  split_ifs
  · trivial
  · exact Or.inl hx

theorem nestedFamily_infinite (r : ℕ) (j : Fin r) :
    (nestedFamily r j).Infinite :=
  core_infinite.mono (core_subset_nestedFamily r j)

theorem nestedFamily_last {r : ℕ} (hr : 0 < r) :
    nestedFamily r ⟨r - 1, Nat.sub_lt hr Nat.zero_lt_one⟩ = Set.univ := by
  simp [nestedFamily]

theorem nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = core := by
  have hlast : (0 : ℕ) ≠ r - 1 := by omega
  simp [nestedFamily, hlast, initialExceptional]

theorem nestedFamily_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiLast : (i : ℕ) ≠ r - 1 := by
    intro hi
    have hjle : (j : ℕ) ≤ r - 1 := by omega
    omega
  by_cases hjLast : (j : ℕ) = r - 1
  · simp only [nestedFamily, hiLast, hjLast, if_false, if_true]
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hmem : exceptionalPoint i ∈ core ∪ initialExceptional i := by
      rw [heq]
      trivial
    rcases hmem with hcore | hextra
    · exact exceptionalPoint_not_core i hcore
    · have himpossible :=
        (exceptionalPoint_mem_initialExceptional_iff i i).mp hextra
      omega
  · simp only [nestedFamily, hiLast, hjLast, if_false]
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨hx.1, lt_trans hx.2 hij⟩
    · intro heq
      have hmemJ : exceptionalPoint i ∈ core ∪ initialExceptional j :=
        Or.inr ((exceptionalPoint_mem_initialExceptional_iff i j).mpr hij)
      have hmemI : exceptionalPoint i ∈ core ∪ initialExceptional i := by
        rw [heq]
        exact hmemJ
      rcases hmemI with hcore | hextra
      · exact exceptionalPoint_not_core i hcore
      · have himpossible :=
        (exceptionalPoint_mem_initialExceptional_iff i i).mp hextra
        omega

noncomputable def freshCoreAt (t : ℕ)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : ℕ := by
  classical
  let forbidden := Finset.univ.image input ∪ Finset.univ.image output
  have hexists : ∃ x, x ∈ core ∧ x ∉ forbidden := by
    by_contra hnot
    push_neg at hnot
    exact core_infinite (forbidden.finite_toSet.subset hnot)
  exact Classical.choose hexists

 theorem freshCoreAt_spec (t : ℕ)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshCoreAt t input output ∈ core ∧
      (∀ i, input i ≠ freshCoreAt t input output) ∧
      (∀ i, output i ≠ freshCoreAt t input output) := by
  classical
  unfold freshCoreAt
  let forbidden := Finset.univ.image input ∪ Finset.univ.image output
  let hexists : ∃ x, x ∈ core ∧ x ∉ forbidden := by
    by_contra hnot
    push_neg at hnot
    exact core_infinite (forbidden.finite_toSet.subset hnot)
  have hchoose := Classical.choose_spec hexists
  refine ⟨hchoose.1, ?_, ?_⟩
  · intro i hi
    exact hchoose.2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, by simp, hi⟩))
  · intro i hi
    exact hchoose.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, by simp, hi⟩))

noncomputable def freshGenerator : Stage3Case024.OnlineGenerator :=
  freshCoreAt

noncomputable def freshRun (input : Stage3Case024.Stream) (t : ℕ) : ℕ :=
  freshCoreAt t (fun i => input i)
    (fun i => freshRun input i)
termination_by t
decreasing_by exact i.isLt

theorem freshRun_spec (input : Stage3Case024.Stream) (t : ℕ) :
    freshRun input t ∈ core ∧
      (∀ i : Fin (t + 1), input i ≠ freshRun input t) ∧
      (∀ i : Fin t, freshRun input i ≠ freshRun input t) := by
  rw [freshRun]
  exact freshCoreAt_spec t (fun i => input i) (fun i => freshRun input i)

theorem freshRun_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshGenerator input (freshRun input) := by
  intro t
  rw [freshRun]
  rfl

theorem freshRun_novel (input : Stage3Case024.Stream) (K : Set ℕ)
    (hcore : core ⊆ K) :
    GenLimit.NovelGeneratesInLimit input (freshRun input) K := by
  refine ⟨0, ?_⟩
  intro t _ht
  have hspec := freshRun_spec input t
  refine ⟨hcore hspec.1, ?_, ?_⟩
  · intro hsample
    obtain ⟨s, hs, hsequal⟩ := GenLimit.mem_sample_iff.mp hsample
    exact hspec.2.1 ⟨s, hs⟩ hsequal
  · intro s hs hsequal
    exact hspec.2.2 ⟨s, hs⟩ hsequal

theorem nestedFamily_globallyFeasible (r : ℕ) :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨freshGenerator, ?_⟩
  intro input _hlegal
  refine ⟨freshRun input, freshRun_follows input, ?_⟩
  intro j
  exact freshRun_novel input (nestedFamily r j) (core_subset_nestedFamily r j)

theorem nestedFamily_obstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonStream := by
  intro Ω _ μ _ gen output _hfollow _hmeas _hintegrable hvalid
  let first : Fin r := ⟨0, by omega⟩
  have hvalidCore := hvalid first
  rw [nestedFamily_zero hr] at hvalidCore
  have hzero :
      Stage3Case024.expectedUpperDensity μ Set.univ commonStream output = 0 :=
    expected_univ_eq_zero_of_eventual_core μ commonStream output hvalidCore
  let last : Fin r := ⟨r - 1, Nat.sub_lt (by omega) Nat.zero_lt_one⟩
  refine ⟨last, ?_⟩
  change Stage3Case024.expectedUpperDensity μ
      (nestedFamily r last) commonStream output = 0
  rw [nestedFamily_last (by omega)]
  exact hzero

theorem nestedFamily_witness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonStream := by
  refine ⟨nestedFamily_strictlyNested hr, ?_,
    nestedFamily_globallyFeasible r, nestedFamily_obstruction hr⟩
  intro j
  exact commonStream_legal_of_core_subset
    (nestedFamily_infinite r j) (core_subset_nestedFamily r j)

end Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  refine ⟨?_, ?_⟩
  · refine ⟨Case024Proof.core, Set.univ, Case024Proof.commonStream,
      Case024Proof.core_ssubset_univ, ?_, ?_, Case024Proof.pair_obstruction⟩
    · exact Case024Proof.commonStream_legal_of_core_subset
        Case024Proof.core_infinite Set.Subset.rfl
    · exact Case024Proof.commonStream_legal_of_core_subset
        Set.infinite_univ (Set.subset_univ _)
  · intro r hr
    exact ⟨Case024Proof.nestedFamily r, Case024Proof.commonStream,
      Case024Proof.nestedFamily_witness hr⟩
