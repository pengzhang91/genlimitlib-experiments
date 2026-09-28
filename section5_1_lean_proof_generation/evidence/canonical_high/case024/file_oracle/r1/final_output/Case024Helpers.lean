import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Data.Nat.Pairing

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024

namespace IC
abbrev SparseSquare := GenLimit.InfiniteContamination.SparseSquare
abbrev SparseNonSquare := GenLimit.InfiniteContamination.SparseNonSquare
end IC

noncomputable def core : Set ℕ := {n | IC.SparseSquare n}

noncomputable def exceptional : Set ℕ := coreᶜ

lemma core_infinite : core.Infinite := by
  apply (Set.infinite_range_of_injective (f := fun n : ℕ => n * n) (by
    intro a b hab
    nlinarith)).mono
  rintro _ ⟨n, rfl⟩
  exact ⟨n, rfl⟩

lemma exceptional_infinite : exceptional.Infinite := by
  simpa [exceptional, core, IC.SparseNonSquare] using
    GenLimit.InfiniteContamination.sparseNonSquare_infinite

noncomputable def commonStream : Stage3Case024.Stream :=
  GenLimit.InfiniteContamination.squareSparseMerge
    core exceptional core_infinite exceptional_infinite

lemma commonStream_injective : Function.Injective commonStream := by
  apply GenLimit.InfiniteContamination.squareSparseMerge_injective
    core_infinite exceptional_infinite
  exact Set.disjoint_compl_right_iff_subset.mpr Set.Subset.rfl

lemma commonStream_range : Set.range commonStream = Set.univ := by
  rw [commonStream,
    GenLimit.InfiniteContamination.range_squareSparseMerge
      core_infinite exceptional_infinite]
  exact Set.union_compl_self core

lemma commonStream_legal {K : Set ℕ} (hcore : core ⊆ K)
    (hK : K.Infinite) : Stage3Case024.Legal commonStream K := by
  refine ⟨hK, commonStream_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonStream_range]
    exact Set.subset_univ K
  · exact
      GenLimit.InfiniteContamination.squareSparseMerge_vanishingNoise_of_core_subset
        core_infinite exceptional_infinite hcore

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  have h := Finset.card_union_le
    ((Finset.range n).filter (fun x => x ∈ A))
    ((Finset.range n).filter (fun x => x ∈ B))
  rw [← Finset.filter_or] at h
  simpa only [Set.mem_union] using h

lemma prefixCount_finite_le_card {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  simpa using hx.2

lemma prefixCount_core_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n ≤ Nat.sqrt n + 1 := by
  classical
  simpa [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, core,
    Nat.count_eq_card_filter_range] using
      GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le (hf :=
    Filter.isCoboundedUnder_le_of_le atTop (fun n => by positivity))
  exact Eventually.of_forall fun n => by
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono (Set.inter_subset_right) n

lemma relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall fun n => by positivity
  · apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    exact Eventually.of_forall fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · apply (div_le_one (by positivity)).2
        exact_mod_cast prefixCount_mono (Set.inter_subset_right) n

lemma generatorFirst_subset_range (input output : ℕ → ℕ) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, ht, -⟩
  exact ⟨t, ht⟩

lemma range_subset_core_union_early {output : ℕ → ℕ} {T : ℕ}
    (hT : ∀ t, T ≤ t → output t ∈ core) :
    Set.range output ⊆ core ∪ Set.range (fun i : Fin T => output i) := by
  rintro x ⟨t, rfl⟩
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (hT t ht)
  · exact Set.mem_union_right _ ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩

lemma tendsto_sparse_bound (T : ℕ) :
    Tendsto (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + T) / n)
      atTop (𝓝 0) := by
  have hT : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  convert GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.add hT using 1 <;>
    simp [add_div]

lemma relativeUpperDensity_univ_eq_zero_of_eventually_core
    {output : ℕ → ℕ} {T : ℕ}
    (hT : ∀ t, T ≤ t → output t ∈ core) (input : ℕ → ℕ) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  let early : Set ℕ := Set.range (fun i : Fin T => output i)
  have hearly : early.Finite := Set.finite_range _
  have hsubset : GenLimit.GeneratorFirst input output ⊆ core ∪ early :=
    (generatorFirst_subset_range input output).trans
      (range_subset_core_union_early hT)
  have hbound (n : ℕ) :
      GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output) n ≤
        Nat.sqrt n + 1 + T := by
    calc
      GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output) n ≤
          GenLimit.PatientScope.prefixCount (core ∪ early) n :=
        prefixCount_mono hsubset n
      _ ≤ GenLimit.PatientScope.prefixCount core n +
          GenLimit.PatientScope.prefixCount early n :=
        prefixCount_union_le core early n
      _ ≤ (Nat.sqrt n + 1) + hearly.toFinset.card :=
        Nat.add_le_add (prefixCount_core_le n)
          (prefixCount_finite_le_card hearly n)
      _ ≤ Nat.sqrt n + 1 + T := by
        apply Nat.add_le_add_left
        simpa [early] using (Finset.card_image_le :
          (Finset.univ.image (fun i : Fin T => output i)).card ≤
            (Finset.univ : Finset (Fin T)).card)
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero'
    (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + T) / n)
  · exact Eventually.of_forall fun n => by positivity
  · exact Eventually.of_forall fun n => by
      simp only [Set.inter_univ]
      simp [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset]
      by_cases hn : n = 0
      · simp [hn]
      · apply div_le_div_of_nonneg_right
        · exact_mod_cast hbound n
        · positivity
  · exact tendsto_sparse_bound T

lemma relativeUpperDensity_univ_eq_zero_of_novel
    {input output : ℕ → ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output core) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := h
  exact relativeUpperDensity_univ_eq_zero_of_eventually_core
    (fun t ht => (hT t ht).1) input

noncomputable def freshSquareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ =>
    let m := Nat.pair t (∑ i, input i) + 1
    m * m

lemma freshSquareGenerator_spec (t : ℕ)
    (input : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) :
    freshSquareGenerator t input previous ∈ core ∧
      (∀ i, freshSquareGenerator t input previous ≠ input i) := by
  classical
  let inputSum := ∑ i, input i
  let m := Nat.pair t inputSum + 1
  have hmpos : 0 < m := by omega
  have hmle : m ≤ m * m := by nlinarith
  have hinput (i : Fin (t + 1)) : input i < m := by
    have hi : input i ≤ inputSum := by
      apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hpair := Nat.right_le_pair t inputSum
    omega
  change m * m ∈ core ∧ (∀ i, m * m ≠ input i)
  refine ⟨⟨m, rfl⟩, ?_⟩
  intro i heq
  have := hinput i
  omega

noncomputable def freshSquareOutput (input : Stage3Case024.Stream) :
    Stage3Case024.Stream := fun t =>
  freshSquareGenerator t (fun i => input i) (fun _ => 0)

lemma freshSquare_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshSquareGenerator input (freshSquareOutput input) := by
  intro t
  rfl

lemma freshSquareOutput_injective (input : Stage3Case024.Stream) :
    Function.Injective (freshSquareOutput input) := by
  intro s t hst
  unfold freshSquareOutput freshSquareGenerator at hst
  have hroot :
      Nat.pair s (∑ i : Fin (s + 1), input i) + 1 =
        Nat.pair t (∑ i : Fin (t + 1), input i) + 1 := by
    nlinarith
  have hpair :
      Nat.pair s (∑ i : Fin (s + 1), input i) =
        Nat.pair t (∑ i : Fin (t + 1), input i) := by omega
  exact (Nat.pair_eq_pair.mp hpair).1

lemma freshSquare_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (freshSquareOutput input) core := by
  refine ⟨0, ?_⟩
  intro t _
  have hs := freshSquareGenerator_spec t
    (fun i => input i) (fun _ : Fin t => 0)
  refine ⟨hs.1, ?_, ?_⟩
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hst, hsval⟩ := hmem
    exact hs.2 ⟨s, hst⟩ hsval.symm
  · intro s hst
    exact fun heq => hst.ne (freshSquareOutput_injective input heq)


lemma core_ssubset_univ : core ⊂ (Set.univ : Set ℕ) := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨Set.subset_univ _, ?_⟩
  intro heq
  have hmem : GenLimit.InfiniteContamination.sparseBetweenSquares 0 ∈ core := by
    rw [heq]
    trivial
  exact GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare 0 hmem

lemma novel_mono {input output : ℕ → ℕ} {K L : Set ℕ}
    (hKL : K ⊆ L) (h : GenLimit.NovelGeneratesInLimit input output K) :
    GenLimit.NovelGeneratesInLimit input output L := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hKL hmem, hfresh, hnovel⟩

lemma expected_density_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : Set ℕ) (input : ℕ → ℕ) (output : Ω → ℕ → ℕ)
    (hint : Stage3Case024.DensityIntegrable μ K input output) :
    Stage3Case024.expectedUpperDensity μ K input output ≤ 1 := by
  unfold Stage3Case024.DensityIntegrable at hint
  unfold Stage3Case024.expectedUpperDensity
  have hmono := integral_mono hint (integrable_const (1 : ℝ))
    (fun ω => relativeUpperDensity_le_one
      (GenLimit.GeneratorFirst input (output ω)) K)
  simpa [integral_const, measureReal_univ_eq_one] using hmono

lemma expected_univ_eq_zero_of_eventually_core
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : ℕ → ℕ) (output : Ω → ℕ → ℕ)
    (hvalid : Stage3Case024.EventuallyFreshValid μ core input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.EventuallyFreshValid at hvalid
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae]
  · exact integral_zero Ω ℝ
  · filter_upwards [hvalid] with ω hω
    exact relativeUpperDensity_univ_eq_zero_of_novel hω

lemma pairObstruction :
    Stage3Case024.PairObstruction core Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hintCore hintUniv hvalidCore _
  have hzero :
      Stage3Case024.expectedUpperDensity μ Set.univ commonStream output = 0 :=
    expected_univ_eq_zero_of_eventually_core μ commonStream output hvalidCore
  have hle :
      Stage3Case024.expectedUpperDensity μ core commonStream output ≤ 1 :=
    expected_density_le_one μ core commonStream output hintCore
  constructor
  · rw [hzero, add_zero]
    exact hle
  · intro hboth
    rw [hzero] at hboth
    norm_num at hboth

noncomputable def extras (n : ℕ) : Set ℕ :=
  Set.range (fun k : Fin n =>
    GenLimit.InfiniteContamination.sparseBetweenSquares k)

lemma extras_finite (n : ℕ) : (extras n).Finite := Set.finite_range _

lemma extras_mono {i j : ℕ} (hij : i ≤ j) : extras i ⊆ extras j := by
  rintro x ⟨k, rfl⟩
  exact ⟨⟨k, lt_of_lt_of_le k.isLt hij⟩, rfl⟩

lemma special_mem_extras {i j : ℕ} (hij : i < j) :
    GenLimit.InfiniteContamination.sparseBetweenSquares i ∈ extras j := by
  exact ⟨⟨i, hij⟩, rfl⟩

lemma special_not_core (i : ℕ) :
    GenLimit.InfiniteContamination.sparseBetweenSquares i ∉ core :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare i

lemma special_not_extras_self (i : ℕ) :
    GenLimit.InfiniteContamination.sparseBetweenSquares i ∉ extras i := by
  rintro ⟨k, hk⟩
  have heq : (k : ℕ) = i :=
    GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective hk
  exact (Nat.ne_of_lt k.isLt) heq

noncomputable def nestedFamily (r : ℕ) : Fin r → Set ℕ := fun j =>
  if (j : ℕ) + 1 = r then Set.univ else core ∪ extras j

lemma core_subset_nestedFamily (r : ℕ) (j : Fin r) :
    core ⊆ nestedFamily r j := by
  unfold nestedFamily
  split_ifs
  · exact Set.subset_univ _
  · exact Set.subset_union_left

lemma nestedFamily_infinite (r : ℕ) (j : Fin r) :
    (nestedFamily r j).Infinite :=
  core_infinite.mono (core_subset_nestedFamily r j)

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, lt_of_lt_of_le (by decide) hr⟩ = core := by
  unfold nestedFamily extras
  simp [show (1 : ℕ) ≠ r by omega]

noncomputable def lastIndex (r : ℕ) (hr : 1 ≤ r) : Fin r :=
  ⟨r - 1, Nat.sub_lt (by omega) (by decide)⟩

lemma lastIndex_value (r : ℕ) (hr : 1 ≤ r) :
    ((lastIndex r hr : Fin r) : ℕ) + 1 = r := by
  change (r - 1) + 1 = r
  exact Nat.sub_add_cancel hr

lemma nestedFamily_last (r : ℕ) (hr : 1 ≤ r) :
    nestedFamily r (lastIndex r hr) = Set.univ := by
  simp [nestedFamily, lastIndex_value r hr]

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hilast : (i : ℕ) + 1 ≠ r := by
    intro hi
    have hjlt : (j : ℕ) < r := j.isLt
    omega
  have hiEq : nestedFamily r i = core ∪ extras i := by
    simp [nestedFamily, hilast]
  by_cases hjlast : (j : ℕ) + 1 = r
  · have hjEq : nestedFamily r j = Set.univ := by
      simp [nestedFamily, hjlast]
    rw [hiEq, hjEq, Set.ssubset_iff_subset_ne]
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hw : GenLimit.InfiniteContamination.sparseBetweenSquares i ∈
        core ∪ extras i := by
      rw [heq]
      trivial
    rcases hw with hw | hw
    · exact special_not_core i hw
    · exact special_not_extras_self i hw
  · have hjEq : nestedFamily r j = core ∪ extras j := by
      simp [nestedFamily, hjlast]
    rw [hiEq, hjEq, Set.ssubset_iff_subset_ne]
    refine ⟨Set.union_subset_union_right core
      (extras_mono (Nat.le_of_lt hij)), ?_⟩
    intro heq
    have hwj : GenLimit.InfiniteContamination.sparseBetweenSquares i ∈
        core ∪ extras j :=
      Set.mem_union_right _ (special_mem_extras hij)
    have hwi : GenLimit.InfiniteContamination.sparseBetweenSquares i ∈
        core ∪ extras i := by
      rw [heq]
      exact hwj
    rcases hwi with hwi | hwi
    · exact special_not_core i hwi
    · exact special_not_extras_self i hwi

lemma nestedFamily_legal (r : ℕ) (j : Fin r) :
    Stage3Case024.Legal commonStream (nestedFamily r j) :=
  commonStream_legal (core_subset_nestedFamily r j)
    (nestedFamily_infinite r j)

lemma nestedFamily_globallyFeasible (r : ℕ) :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨freshSquareGenerator, ?_⟩
  intro input _
  refine ⟨freshSquareOutput input, freshSquare_follows input, ?_⟩
  intro j
  exact novel_mono (core_subset_nestedFamily r j) (freshSquare_novel input)

lemma nestedFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let zero : Fin r := ⟨0, lt_of_lt_of_le (by decide) hr⟩
  let last : Fin r := lastIndex r (by omega)
  have hvalidCore : Stage3Case024.EventuallyFreshValid μ core commonStream output := by
    simpa [zero, nestedFamily_zero hr] using hvalid zero
  refine ⟨last, ?_⟩
  have hzero := expected_univ_eq_zero_of_eventually_core
    μ commonStream output hvalidCore
  simpa [last, nestedFamily_last r (by omega)] using hzero

lemma manyTargetWitness (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonStream := by
  exact ⟨nestedFamily_strict hr, nestedFamily_legal r,
    nestedFamily_globallyFeasible r,
    nestedFamily_manyTargetObstruction hr⟩

end Case024
