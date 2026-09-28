import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology

namespace Case024

open GenLimit.InfiniteContamination

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

def Core : Language := {n | SparseSquare n}

theorem core_infinite : Core.Infinite := by
  have hmono : StrictMono (fun n : ℕ => n * n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    nlinarith
  exact (Set.infinite_range_of_injective hmono.injective).mono (by
    rintro _ ⟨n, rfl⟩
    exact sparseSquare_mul_self n)

theorem core_compl_infinite : Coreᶜ.Infinite := by
  simpa [Core, SparseNonSquare] using sparseNonSquare_infinite

noncomputable def commonInput : Stream :=
  squareSparseMerge Core Coreᶜ core_infinite core_compl_infinite

theorem commonInput_injective : Function.Injective commonInput := by
  apply squareSparseMerge_injective core_infinite core_compl_infinite
  exact disjoint_compl_right

theorem commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_squareSparseMerge core_infinite core_compl_infinite]
  exact Set.union_compl_self Core

theorem legal_of_core_subset {K : Language} (hcore : Core ⊆ K)
    (hK : K.Infinite) : Stage3Case024.Legal commonInput K := by
  refine ⟨hK, commonInput_injective, ?_, ?_⟩
  · intro x hx
    rw [commonInput_range]
    exact Set.mem_univ x
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      core_infinite core_compl_infinite hcore

theorem prefixCount_mono {A B : Language} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  exact Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hx.1, h hx.2⟩)

@[simp] theorem prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Language) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

theorem prefixCount_core (n : ℕ) :
    GenLimit.PatientScope.prefixCount Core n = Nat.count SparseSquare n := by
  classical
  letI : DecidablePred SparseSquare := Classical.decPred _
  rw [Nat.count_eq_card_filter_range]
  rfl

theorem core_ratio_tendsto :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount Core n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Language) n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero'
      (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / n)
  · exact Eventually.of_forall fun n => div_nonneg (by positivity) (by positivity)
  · exact Eventually.of_forall fun n => by
      rw [prefixCount_core, prefixCount_univ]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast count_sparseSquare_le_sqrt_add_one n
      · positivity
  · exact tendsto_sparseSqrt_add_one_div

theorem finite_range_diff_of_eventual_mem {output : Stream} {K : Language}
    (h : ∃ T, ∀ t, T ≤ t → output t ∈ K) :
    (Set.range output \ K).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_range (fun t : Fin T => output t)).subset
  rintro x ⟨⟨t, rfl⟩, htK⟩
  have ht : t < T := by
    by_contra hnot
    exact htK (hT t (Nat.le_of_not_gt hnot))
  exact ⟨⟨t, ht⟩, rfl⟩

theorem generatorFirst_subset_range (input output : Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, ht, -⟩
  exact ⟨t, ht⟩

theorem prefixCount_le_core_add_finite {A : Language}
    (hfinite : (A \ Core).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount Core n + hfinite.toFinset.card := by
  classical
  let a := GenLimit.PatientScope.prefixFinset A n
  let c := GenLimit.PatientScope.prefixFinset Core n
  have hsub : a ⊆ c ∪ hfinite.toFinset := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hc : x ∈ Core
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hc⟩)
    · exact Finset.mem_union_right _
        (Set.Finite.mem_toFinset hfinite |>.2 ⟨hx'.2, hc⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem ratio_tendsto_zero_of_finite_diff {A : Language}
    (hfinite : (A \ Core).Finite) :
    Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Set.univ : Language) n : ℝ))
      atTop (𝓝 0) := by
  let B := hfinite.toFinset.card
  apply squeeze_zero'
      (g := fun n : ℕ =>
        ((GenLimit.PatientScope.prefixCount Core n : ℝ) + B) / n)
  · exact Eventually.of_forall fun n => div_nonneg (by positivity) (by positivity)
  · exact Eventually.of_forall fun n => by
      rw [prefixCount_univ]
      simp only [Set.inter_univ]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast prefixCount_le_core_add_finite hfinite n
      · positivity
  · have hcore := core_ratio_tendsto
    simp only [prefixCount_univ] at hcore
    have hB : Tendsto (fun n : ℕ => (B : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa [add_div] using hcore.add hB

theorem relativeUpperDensity_univ_eq_zero_of_finite_diff {A : Language}
    (hfinite : (A \ Core).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  exact (ratio_tendsto_zero_of_finite_diff hfinite).limsup_eq

theorem relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  have hpoint : ∀ n : ℕ,
      (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
          GenLimit.PatientScope.prefixCount K n ≤ 1 := by
    intro n
    have hcount := prefixCount_mono (Set.inter_subset_right : A ∩ K ⊆ K) n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)]
      exact_mod_cast hcount
  have h := limsup_le_limsup (Eventually.of_forall hpoint)
    (isCoboundedUnder_le_of_le atTop (fun n => by positivity))
    (isBoundedUnder_of ⟨1, fun _ => le_rfl⟩)
  simpa using h.trans_eq (tendsto_const_nhds.limsup_eq)

end Case024

namespace Case024

noncomputable def freshCoreChoice {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : ℕ :=
  Classical.choose (core_infinite.exists_notMem_finite
    ((Set.finite_range input).union (Set.finite_range output)))

 theorem freshCoreChoice_mem {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshCoreChoice input output ∈ Core := by
  exact (Classical.choose_spec (core_infinite.exists_notMem_finite
    ((Set.finite_range input).union (Set.finite_range output)))).1

 theorem freshCoreChoice_not_input {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (i : Fin (t + 1)) :
    freshCoreChoice input output ≠ input i := by
  intro h
  have hnot := (Classical.choose_spec (core_infinite.exists_notMem_finite
    ((Set.finite_range input).union (Set.finite_range output)))).2
  apply hnot
  exact Set.mem_union_left _ ⟨i, h.symm⟩

 theorem freshCoreChoice_not_output {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (i : Fin t) :
    freshCoreChoice input output ≠ output i := by
  intro h
  have hnot := (Classical.choose_spec (core_infinite.exists_notMem_finite
    ((Set.finite_range input).union (Set.finite_range output)))).2
  apply hnot
  exact Set.mem_union_right _ ⟨i, h.symm⟩

noncomputable def coreGenerator : Stage3Case024.OnlineGenerator :=
  fun _ input output => freshCoreChoice input output

noncomputable def coreRun (input : Stream) (t : ℕ) : ℕ :=
  coreGenerator t (fun i => input i) (fun i => coreRun input i)
termination_by t

 theorem coreRun_follows (input : Stream) :
    Stage3Case024.Follows coreGenerator input (coreRun input) := by
  intro t
  rw [coreRun]

 theorem coreRun_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (coreRun input) Core := by
  refine ⟨0, ?_⟩
  intro t _
  rw [coreRun]
  refine ⟨freshCoreChoice_mem _ _, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, hvalue⟩ := hsample
    exact freshCoreChoice_not_input _ _ ⟨s, hs⟩ hvalue.symm
  · intro s hs
    simpa only [coreGenerator] using
      (freshCoreChoice_not_output
        (input := fun i : Fin (t + 1) => input i)
        (output := fun i : Fin t => coreRun input i) ⟨s, hs⟩).symm

 theorem globallyFeasible_of_core_subset {r : ℕ} (family : Fin r → Language)
    (hcore : ∀ j, Core ⊆ family j) :
    Stage3Case024.GloballyFeasible family := by
  refine ⟨coreGenerator, fun input _ => ⟨coreRun input, coreRun_follows input, ?_⟩⟩
  intro j
  obtain ⟨T, hT⟩ := coreRun_novel input
  exact ⟨T, fun t ht => by
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    exact ⟨hcore j hmem, hfresh, hnovel⟩⟩

end Case024

namespace Case024

open GenLimit.InfiniteContamination

def Added (j : ℕ) : Language :=
  Set.range (fun k : Fin j => sparseBetweenSquares k)

 theorem added_mono {i j : ℕ} (hij : i ≤ j) : Added i ⊆ Added j := by
  rintro x ⟨k, rfl⟩
  exact ⟨⟨k, lt_of_lt_of_le k.isLt hij⟩, rfl⟩

 theorem between_mem_added {i j : ℕ} (hij : i < j) :
    sparseBetweenSquares i ∈ Added j := by
  exact ⟨⟨i, hij⟩, rfl⟩

 theorem between_not_mem_added (i : ℕ) :
    sparseBetweenSquares i ∉ Added i := by
  rintro ⟨k, hk⟩
  have := sparseBetweenSquares_strictMono.injective hk
  omega

 theorem between_not_mem_core (i : ℕ) :
    sparseBetweenSquares i ∉ Core := by
  exact sparseBetweenSquares_nonsquare i

noncomputable def family (r : ℕ) (i : Fin r) : Language :=
  if i.1 + 1 = r then Set.univ else Core ∪ Added i.1

 theorem family_core_subset (r : ℕ) (i : Fin r) :
    Core ⊆ family r i := by
  intro x hx
  unfold family
  split
  · exact Set.mem_univ x
  · exact Set.mem_union_left _ hx

 theorem family_infinite (r : ℕ) (i : Fin r) :
    (family r i).Infinite :=
  core_infinite.mono (family_core_subset r i)

 theorem family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (family r) := by
  intro i j hij
  have hiNotLast : i.1 + 1 ≠ r := by omega
  by_cases hjLast : j.1 + 1 = r
  · have hsub : family r i ⊆ family r j := by
      simp [family, hiNotLast, hjLast]
    apply (Set.ssubset_iff_of_subset hsub).2
    refine ⟨sparseBetweenSquares i.1, ?_, ?_⟩
    · simp [family, hjLast]
    · simp only [family, hiNotLast, ↓reduceIte, Set.mem_union]
      exact not_or_intro (between_not_mem_core i.1) (between_not_mem_added i.1)
  · have hsub : family r i ⊆ family r j := by
      simp only [family, hiNotLast, hjLast, ↓reduceIte]
      exact Set.union_subset_union_right _ (added_mono (Nat.le_of_lt hij))
    apply (Set.ssubset_iff_of_subset hsub).2
    refine ⟨sparseBetweenSquares i.1, ?_, ?_⟩
    · simp only [family, hjLast, ↓reduceIte, Set.mem_union]
      exact Or.inr (between_mem_added hij)
    · simp only [family, hiNotLast, ↓reduceIte, Set.mem_union]
      exact not_or_intro (between_not_mem_core i.1) (between_not_mem_added i.1)

def lastIndex (r : ℕ) (hr : 0 < r) : Fin r :=
  ⟨r - 1, by omega⟩

 theorem family_last_univ {r : ℕ} (hr : 0 < r) :
    family r (lastIndex r hr) = Set.univ := by
  unfold family lastIndex
  simp [Nat.sub_add_cancel (by omega : 1 ≤ r)]

 theorem family_legal (r : ℕ) (i : Fin r) :
    Stage3Case024.Legal commonInput (family r i) :=
  legal_of_core_subset (family_core_subset r i) (family_infinite r i)

end Case024

namespace Case024

 theorem density_zero_of_novel {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output Core) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := h
  have hrange : (Set.range output \ Core).Finite :=
    finite_range_diff_of_eventual_mem ⟨T, fun t ht => (hT t ht).1⟩
  apply relativeUpperDensity_univ_eq_zero_of_finite_diff
  exact hrange.subset (by
    intro x hx
    exact ⟨generatorFirst_subset_range input output hx.1, hx.2⟩)

 theorem expected_univ_eq_zero {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (input : Stream) (output : Ω → Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ Core input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) =
        ∫ _ : Ω, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hvalid] with ω hω
          exact density_zero_of_novel hω
    _ = 0 := integral_zero Ω ℝ

 theorem expected_density_le_one {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Language) (input : Stream) (output : Ω → Stream)
    (hint : Stage3Case024.DensityIntegrable μ K input output) :
    Stage3Case024.expectedUpperDensity μ K input output ≤ 1 := by
  unfold Stage3Case024.expectedUpperDensity Stage3Case024.DensityIntegrable at *
  have hle := integral_mono_ae hint (integrable_const (1 : ℝ))
    (Filter.Eventually.of_forall fun ω =>
      relativeUpperDensity_le_one (GenLimit.GeneratorFirst input (output ω)) K)
  simpa using hle

 theorem pairObstruction :
    Stage3Case024.PairObstruction Core Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hintCore _ hvalidCore _
  have hzero := expected_univ_eq_zero μ commonInput output hvalidCore
  have hle := expected_density_le_one μ Core commonInput output hintCore
  constructor
  · rw [hzero, add_zero]
    exact hle
  · rintro ⟨hcore, huniv⟩
    rw [hzero] at huniv
    norm_num at huniv

 theorem family_zero_core {r : ℕ} (hr : 2 ≤ r) :
    family r ⟨0, by omega⟩ = Core := by
  unfold family Added
  simp [show 1 ≠ r by omega]

 theorem manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (family r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last := lastIndex r (by omega)
  have hvalidCore : Stage3Case024.EventuallyFreshValid μ Core commonInput output := by
    simpa [first, family_zero_core hr] using hvalid first
  refine ⟨last, ?_⟩
  rw [show family r last = Set.univ by
    simpa [last] using family_last_univ (r := r) (by omega)]
  exact expected_univ_eq_zero μ commonInput output hvalidCore

 theorem manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (family r) commonInput := by
  refine ⟨family_strictlyNested hr, ?_, ?_, manyTargetObstruction hr⟩
  · exact fun j => family_legal r j
  · exact globallyFeasible_of_core_subset (family r) (family_core_subset r)

end Case024
