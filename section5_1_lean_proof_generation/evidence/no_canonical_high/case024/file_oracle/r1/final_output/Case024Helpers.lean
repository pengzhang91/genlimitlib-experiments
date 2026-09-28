import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof

namespace IC
abbrev SparseSquare := GenLimit.InfiniteContamination.SparseSquare
abbrev SparseNonSquare := GenLimit.InfiniteContamination.SparseNonSquare
abbrev sparseBetweenSquares := GenLimit.InfiniteContamination.sparseBetweenSquares
end IC

abbrev core : Set ℕ := {n | IC.SparseSquare n}

noncomputable local instance : DecidablePred IC.SparseSquare := Classical.decPred _

lemma core_infinite : core.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => n * n) := by
    intro a b hab
    nlinarith
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact ⟨n, rfl⟩

lemma between_not_core (k : ℕ) : IC.sparseBetweenSquares k ∉ core :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare k

noncomputable abbrev commonStream : Stage3Case024.Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation core coreᶜ core_infinite

lemma commonStream_injective : Function.Injective commonStream := by
  apply GenLimit.InfiniteContamination.sparseMergePresentation_injective core_infinite
  exact Set.disjoint_compl_right_iff_subset.mpr Set.Subset.rfl

lemma commonStream_range : Set.range commonStream = Set.univ := by
  rw [GenLimit.InfiniteContamination.range_sparseMergePresentation core_infinite]
  exact Set.union_compl_self core

lemma commonStream_legal {K : Set ℕ} (hcore : core ⊆ K) (hK : K.Infinite) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨hK, commonStream_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonStream_range]
    exact Set.subset_univ K
  · exact GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
      core_infinite hcore

noncomputable def markers (i : ℕ) : Set ℕ :=
  ↑((Finset.range i).image IC.sparseBetweenSquares)

abbrev lowerTarget (i : ℕ) : Set ℕ := core ∪ markers i

lemma marker_not_lower (i : ℕ) : IC.sparseBetweenSquares i ∉ lowerTarget i := by
  intro h
  rcases h with hcore | hmark
  · exact between_not_core i hcore
  · simp only [markers, Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hmark
    obtain ⟨k, hk, heq⟩ := hmark
    have : k = i := GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective heq
    omega

lemma lowerTarget_mono {i j : ℕ} (hij : i ≤ j) : lowerTarget i ⊆ lowerTarget j := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · right
    simp only [markers, Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

lemma lowerTarget_ssubset {i j : ℕ} (hij : i < j) : lowerTarget i ⊂ lowerTarget j := by
  refine ⟨lowerTarget_mono hij.le, ?_⟩
  intro hrev
  exact marker_not_lower i (hrev (Or.inr (by
    simp only [markers, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨i, hij, rfl⟩)))

noncomputable def family (r : ℕ) (i : Fin r) : Set ℕ :=
  if i.1 + 1 = r then Set.univ else lowerTarget i.1

lemma family_zero {r : ℕ} (hr : 2 ≤ r) : family r ⟨0, by omega⟩ = core := by
  have hne : 0 + 1 ≠ r := by omega
  simp [family, hne, lowerTarget, markers]

lemma family_last {r : ℕ} (hr : 1 ≤ r) :
    family r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [family]
  omega

lemma core_subset_family {r : ℕ} (i : Fin r) : core ⊆ family r i := by
  unfold family
  split_ifs
  · exact Set.subset_univ _
  · exact Set.subset_union_left

lemma family_infinite {r : ℕ} (i : Fin r) : (family r i).Infinite :=
  core_infinite.mono (core_subset_family i)

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (family r) := by
  intro i j hij
  unfold family
  split_ifs with hi hj
  · omega
  · exact (hj (by omega)).elim
  · refine ⟨Set.subset_univ _, ?_⟩
    intro hrev
    exact marker_not_lower i.1 (hrev (Set.mem_univ _))
  · exact lowerTarget_ssubset hij

lemma commonStream_legal_family {r : ℕ} (i : Fin r) :
    Stage3Case024.Legal commonStream (family r i) :=
  commonStream_legal (core_subset_family i) (family_infinite i)

end Case024Proof

namespace Case024Proof

open GenLimit.PatientScope

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n := by
  unfold prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_core_le (n : ℕ) :
    prefixCount core n ≤ Nat.sqrt n + 1 := by
  classical
  have h := GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n
  rw [Nat.count_eq_card_filter_range] at h
  simpa [prefixCount, prefixFinset, core] using h

lemma prefixCount_subset_core_union_finset
    {A : Set ℕ} (E : Finset ℕ) (hA : A ⊆ core ∪ (E : Set ℕ)) (n : ℕ) :
    prefixCount A n ≤ Nat.sqrt n + 1 + E.card := by
  calc
    prefixCount A n ≤ prefixCount (core ∪ (E : Set ℕ)) n := prefixCount_mono hA n
    _ ≤ prefixCount core n + E.card := by
      unfold prefixCount
      calc
        (prefixFinset (core ∪ (E : Set ℕ)) n).card ≤
            (prefixFinset core n ∪ E).card := by
          apply Finset.card_le_card
          intro x hx
          rw [mem_prefixFinset] at hx
          rcases hx.2 with hxcore | hxE
          · exact Finset.mem_union_left _ (mem_prefixFinset.mpr ⟨hx.1, hxcore⟩)
          · exact Finset.mem_union_right _ hxE
        _ ≤ (prefixFinset core n).card + E.card := Finset.card_union_le _ _
    _ ≤ Nat.sqrt n + 1 + E.card :=
      Nat.add_le_add_right (prefixCount_core_le n) E.card

lemma tendsto_sparse_bound (E : Finset ℕ) :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 + E.card : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hfinite : Tendsto (fun n : ℕ => (E.card : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have hm : Tendsto (fun n : ℕ => (E.card : ℝ) * (n : ℝ)⁻¹) atTop
        (𝓝 ((E.card : ℝ) * 0)) :=
      tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv] using hm
  have hsum := GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.add hfinite
  convert hsum using 1 <;> norm_num [Nat.cast_add, add_div]

@[simp] lemma prefixCount_univ (n : ℕ) : prefixCount (Set.univ : Set ℕ) n = n := by
  simp [prefixCount, prefixFinset]

lemma relativeUpperDensity_zero_of_subset_core_union_finset
    {A : Set ℕ} (E : Finset ℕ) (hA : A ⊆ core ∪ (E : Set ℕ)) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  simp only [Set.inter_univ, prefixCount_univ]
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero
    (fun n => div_nonneg (by positivity) (by positivity))
    (fun n => by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast prefixCount_subset_core_union_finset E hA n
      · positivity)
    (tendsto_sparse_bound E)

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n =>
      div_nonneg (by positivity) (by positivity))
  · apply Eventually.of_forall
    intro n
    by_cases hzero : prefixCount K n = 0
    · have hnum : prefixCount (A ∩ K) n = 0 :=
        Nat.eq_zero_of_le_zero (hzero ▸ prefixCount_mono Set.inter_subset_right n)
      simp [hzero, hnum]
    · have hpos : (0 : ℝ) < prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      rw [div_le_one hpos]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n

lemma generatorFirst_subset_core_union_early
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output core) :
    ∃ E : Finset ℕ, GenLimit.GeneratorFirst input output ⊆ core ∪ (E : Set ℕ) := by
  obtain ⟨T, hT⟩ := hvalid
  let E := (Finset.range T).image output
  refine ⟨E, ?_⟩
  intro x hx
  obtain ⟨t, htx, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Or.inl (htx ▸ (hT t ht).1)
  · right
    simp only [E, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨t, Nat.lt_of_not_ge ht, htx⟩

lemma generatorFirst_density_univ_zero
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output core) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨E, hE⟩ := generatorFirst_subset_core_union_early hvalid
  exact relativeUpperDensity_zero_of_subset_core_union_finset E hE

end Case024Proof

namespace Case024Proof

noncomputable def freshCoreGenerator : Stage3Case024.OnlineGenerator :=
  fun _ input previous =>
    Classical.choose <| core_infinite.exists_not_mem_finset
      ((Finset.univ.image input) ∪ (Finset.univ.image previous))

lemma freshCoreGenerator_spec (t : ℕ) (input : Fin (t + 1) → ℕ)
    (previous : Fin t → ℕ) :
    freshCoreGenerator t input previous ∈ core ∧
      freshCoreGenerator t input previous ∉ Finset.univ.image input ∧
      freshCoreGenerator t input previous ∉ Finset.univ.image previous := by
  have h := Classical.choose_spec <| core_infinite.exists_not_mem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image previous))
  refine ⟨h.1, ?_, ?_⟩
  · intro hmem
    exact h.2 (Finset.mem_union_left _ hmem)
  · intro hmem
    exact h.2 (Finset.mem_union_right _ hmem)

noncomputable def followOutput (gen : Stage3Case024.OnlineGenerator)
    (input : Stage3Case024.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => followOutput gen input i)
termination_by t

lemma followOutput_follows (gen : Stage3Case024.OnlineGenerator)
    (input : Stage3Case024.Stream) :
    Stage3Case024.Follows gen input (followOutput gen input) := by
  intro t
  rw [followOutput]

lemma freshCoreGenerator_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input
      (followOutput freshCoreGenerator input) core := by
  refine ⟨0, ?_⟩
  intro t _
  have hspec := freshCoreGenerator_spec t (fun i => input i)
    (fun i => followOutput freshCoreGenerator input i)
  rw [followOutput]
  refine ⟨hspec.1, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hst, hvalue⟩ := hsample
    apply hspec.2.1
    rw [Finset.mem_image]
    exact ⟨⟨s, hst⟩, Finset.mem_univ _, hvalue⟩
  · intro s hst heq
    apply hspec.2.2
    rw [Finset.mem_image]
    exact ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩

lemma family_globallyFeasible {r : ℕ} :
    Stage3Case024.GloballyFeasible (family r) := by
  refine ⟨freshCoreGenerator, ?_⟩
  intro input _
  refine ⟨followOutput freshCoreGenerator input,
    followOutput_follows freshCoreGenerator input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshCoreGenerator_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  exact ⟨core_subset_family j hcore, hfresh, hnovel⟩

end Case024Proof

namespace Case024Proof

lemma expected_core_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (input : Stage3Case024.Stream) (output : Ω → Stage3Case024.Stream)
    (hint : Stage3Case024.DensityIntegrable μ core input output) :
    Stage3Case024.expectedUpperDensity μ core input output ≤ 1 := by
  unfold Stage3Case024.expectedUpperDensity
  have hle := integral_mono_ae hint (integrable_const (1 : ℝ))
    (Eventually.of_forall fun ω =>
      relativeUpperDensity_le_one
        (GenLimit.GeneratorFirst input (output ω)) core)
  simpa using hle

lemma expected_univ_zero
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : Stage3Case024.Stream) (output : Ω → Stage3Case024.Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ core input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.expectedUpperDensity
  apply integral_eq_zero_of_ae
  filter_upwards [hvalid] with ω hω
  exact generatorFirst_density_univ_zero hω

lemma pairObstruction : Stage3Case024.PairObstruction core Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hintCore _ hvalidCore _
  have hcore := expected_core_le_one μ commonStream output hintCore
  have huniv := expected_univ_zero μ commonStream output hvalidCore
  constructor
  · rw [huniv]
    linarith
  · intro hhalf
    rw [huniv] at hhalf
    linarith

lemma core_ssubset_univ : core ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  exact between_not_core 0 (h (Set.mem_univ _))

lemma manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (family r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hvalidCore : Stage3Case024.EventuallyFreshValid μ core commonStream output := by
    simpa [first, family_zero hr] using hvalid first
  refine ⟨last, ?_⟩
  rw [show family r last = Set.univ by simpa [last] using family_last (show 1 ≤ r by omega)]
  exact expected_univ_zero μ commonStream output hvalidCore

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (family r) commonStream := by
  refine ⟨family_strictlyNested hr, ?_, family_globallyFeasible,
    manyTargetObstruction hr⟩
  intro j
  exact commonStream_legal_family j

end Case024Proof
