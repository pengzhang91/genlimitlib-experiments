import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof

open Stage3Case024
open GenLimit.InfiniteContamination

abbrev Squares : Set ℕ := {n | SparseSquare n}

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

@[simp] lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

lemma relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  refine Filter.limsup_le_of_le (hf := ?_) ?_
  · apply isCoboundedUnder_le_of_le atTop
    intro n
    positivity
  · filter_upwards [] with n
    let a := GenLimit.PatientScope.prefixCount (A ∩ K) n
    let b := GenLimit.PatientScope.prefixCount K n
    have hab : a ≤ b := prefixCount_mono Set.inter_subset_right n
    by_cases hb : b = 0
    · have ha : a = 0 := Nat.eq_zero_of_le_zero (hb ▸ hab)
      simp [a, b, ha, hb]
    · have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
      rw [div_le_one hbpos]
      exact_mod_cast hab

lemma generatorFirst_subset_squares_early
    {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output Squares) :
    ∃ T, GenLimit.GeneratorFirst input output ⊆
      Squares ∪ (↑((Finset.range T).image output) : Set ℕ) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  intro x hx
  obtain ⟨t, hout, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (hout ▸ (hT t ht).1)
  · apply Set.mem_union_right
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨t, Finset.mem_range.mpr (Nat.lt_of_not_ge ht), hout⟩

lemma prefixCount_generatorFirst_le
    {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output Squares) :
    ∃ T, ∀ n,
      GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output) n ≤
        Nat.sqrt n + 1 + T := by
  classical
  obtain ⟨T, hsub⟩ := generatorFirst_subset_squares_early h
  refine ⟨T, fun n => ?_⟩
  calc
    GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output) n ≤
      GenLimit.PatientScope.prefixCount
        (Squares ∪ (↑((Finset.range T).image output) : Set ℕ)) n :=
      prefixCount_mono hsub n
    _ ≤ GenLimit.PatientScope.prefixCount Squares n +
        ((Finset.range T).image output).card := by
      unfold GenLimit.PatientScope.prefixCount
      apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
      intro x hx
      rw [GenLimit.PatientScope.mem_prefixFinset] at hx
      rcases hx.2 with hxSquare | hxEarly
      · exact Finset.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx.1, hxSquare⟩)
      · exact Finset.mem_union_right _ hxEarly
    _ ≤ (Nat.sqrt n + 1) + T := by
      apply Nat.add_le_add
      · simpa [GenLimit.PatientScope.prefixCount,
          GenLimit.PatientScope.prefixFinset,
          Nat.count_eq_card_filter_range] using
          count_sparseSquare_le_sqrt_add_one n
      · simpa using
          (Finset.card_image_le :
            ((Finset.range T).image output).card ≤ (Finset.range T).card)

lemma tendsto_sparse_bound (T : ℕ) :
    Tendsto (fun n : ℕ => (((Nat.sqrt n + 1 + T : ℕ) : ℝ) / n))
      atTop (𝓝 0) := by
  have hT : Tendsto (fun n : ℕ => (T : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := tendsto_sparseSqrt_add_one_div.add hT
  convert h using 1 <;> norm_num [Nat.cast_add, add_div]

lemma relativeUpperDensity_univ_eq_zero_of_eventual_squares
    {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output Squares) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hcount⟩ := prefixCount_generatorFirst_le h
  unfold relativeUpperDensity
  have hnonneg : ∀ n : ℕ, 0 ≤
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ) := by
    intro n
    positivity
  have hle : ∀ n : ℕ,
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ Set.univ) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ) ≤
      ((Nat.sqrt n + 1 + T : ℕ) : ℝ) / n := by
    intro n
    simp only [Set.inter_univ, prefixCount_univ]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount n)
      (Nat.cast_nonneg n)
  exact (squeeze_zero' (Eventually.of_forall hnonneg)
    (Eventually.of_forall hle) (tendsto_sparse_bound T)).limsup_eq

end Stage3Case024Proof

namespace Stage3Case024Proof

open Stage3Case024
open GenLimit.InfiniteContamination

lemma squareMap_strictMono : StrictMono (fun n : ℕ => n * n) := by
  apply strictMono_nat_of_lt_succ
  intro n
  nlinarith

lemma squares_infinite : Squares.Infinite := by
  apply (Set.infinite_range_of_injective squareMap_strictMono.injective).mono
  rintro _ ⟨n, rfl⟩
  exact sparseSquare_mul_self n

noncomputable def commonInput : Stream :=
  sparseMergePresentation Squares Squaresᶜ squares_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply sparseMergePresentation_injective squares_infinite
  exact Set.disjoint_left.2 (by simp)

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation squares_infinite]
  exact Set.union_compl_self Squares

lemma legal_commonInput {K : Language} (hs : Squares ⊆ K) :
    Legal commonInput K := by
  constructor
  · exact squares_infinite.mono hs
  · refine ⟨commonInput_injective, ?_, ?_⟩
    · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
      exact Set.subset_univ K
    · exact sparseMergePresentation_vanishingNoise_of_core_subset
        squares_infinite hs

abbrev Markers (i : ℕ) : Set ℕ :=
  ↑((Finset.range i).image sparseBetweenSquares)

lemma marker_mem_markers {i j : ℕ} (hij : i < j) :
    sparseBetweenSquares i ∈ Markers j := by
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨i, Finset.mem_range.mpr hij, rfl⟩

lemma marker_not_mem_markers (i : ℕ) :
    sparseBetweenSquares i ∉ Markers i := by
  intro h
  rw [Finset.mem_coe, Finset.mem_image] at h
  obtain ⟨k, hk, heq⟩ := h
  have hki : k = i := sparseBetweenSquares_strictMono.injective heq
  subst k
  exact (Nat.not_lt_of_ge (Nat.le_refl i)) (Finset.mem_range.mp hk)

lemma markers_mono {i j : ℕ} (hij : i ≤ j) : Markers i ⊆ Markers j := by
  intro x hx
  rw [Finset.mem_coe, Finset.mem_image] at hx ⊢
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hij), rfl⟩

noncomputable def family (r : ℕ) (i : Fin r) : Language :=
  if i.1 + 1 = r then Set.univ else Squares ∪ Markers i.1

lemma squares_subset_family (r : ℕ) (i : Fin r) : Squares ⊆ family r i := by
  intro x hx
  simp only [family]
  split
  · exact Set.mem_univ x
  · exact Set.mem_union_left _ hx

lemma family_strictlyNested {r : ℕ} : StrictlyNested (family r) := by
  intro i j hij
  have hji : i.1 < j.1 := hij
  have hiNotLast : i.1 + 1 ≠ r := by omega
  constructor
  · intro x hx
    simp only [family, hiNotLast, if_false] at hx
    by_cases hjLast : j.1 + 1 = r
    · simp [family, hjLast]
    · simp only [family, hjLast, if_false]
      rcases hx with hxS | hxM
      · exact Set.mem_union_left _ hxS
      · exact Set.mem_union_right _ (markers_mono (Nat.le_of_lt hji) hxM)
  · intro hsub
    have hwj : sparseBetweenSquares i.1 ∈ family r j := by
      by_cases hjLast : j.1 + 1 = r
      · simp [family, hjLast]
      · simp only [family, hjLast, if_false]
        exact Set.mem_union_right _ (marker_mem_markers hji)
    have hwi := hsub hwj
    simp only [family, hiNotLast, if_false, Set.mem_union] at hwi
    rcases hwi with hSquare | hMarker
    · exact sparseBetweenSquares_nonsquare i.1 hSquare
    · exact marker_not_mem_markers i.1 hMarker

noncomputable def generatorSum (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ :=
  Finset.univ.sum xs

noncomputable def streamSum (input : Stream) (t : ℕ) : ℕ :=
  Finset.univ.sum (fun i : Fin (t + 1) => input i)

noncomputable def squareGenerator : OnlineGenerator :=
  fun t xs _ =>
    let b := generatorSum t xs + t + 1
    b * b

noncomputable def squareOutput (input : Stream) : Stream :=
  fun t =>
    let b := streamSum input t + t + 1
    b * b

lemma squareOutput_follows (input : Stream) :
    Follows squareGenerator input (squareOutput input) := by
  intro t
  simp [squareGenerator, squareOutput, generatorSum, streamSum]

lemma streamSum_le_succ (input : Stream) (t : ℕ) :
    streamSum input t ≤ streamSum input (t + 1) := by
  calc
    streamSum input t = Finset.univ.sum (fun i : Fin (t + 1) => input i) := rfl
    _ ≤ Finset.univ.sum (fun i : Fin (t + 1) => input i) + input (t + 1) :=
      Nat.le_add_right _ _
    _ = streamSum input (t + 1) := by
      unfold streamSum
      conv_rhs => rw [Fin.sum_univ_castSucc]
      rfl

lemma streamSum_mono {input : Stream} {s t : ℕ} (hst : s ≤ t) :
    streamSum input s ≤ streamSum input t := by
  exact Nat.le_induction (Nat.le_refl _) (fun n _ ih =>
    ih.trans (streamSum_le_succ input n)) t hst

lemma squareOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) Squares := by
  refine ⟨0, ?_⟩
  intro t _
  let total := streamSum input t
  let b := total + t + 1
  have hbpos : 0 < b := by omega
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨b, ?_⟩
    simp [b, total, squareOutput]
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hst, hs⟩ := hmem
    have hsle : input s ≤ total := by
      let i : Fin (t + 1) := ⟨s, hst⟩
      have hi := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin (t + 1) => input j)
        (fun _ _ => Nat.zero_le _) (by simp : i ∈ Finset.univ)
      simpa [i, total, streamSum] using hi
    have houtgt : total < squareOutput input t := by
      simp only [squareOutput, total]
      nlinarith
    exact (not_le_of_gt houtgt) (hs ▸ hsle)
  · intro s hst heq
    have hsum := streamSum_mono (input := input) (Nat.le_of_lt hst)
    have hbase : streamSum input s + s + 1 < streamSum input t + t + 1 := by
      omega
    simp only [squareOutput] at heq
    exact (squareMap_strictMono hbase).ne heq

lemma globallyFeasible_family {r : ℕ} : GloballyFeasible (family r) := by
  refine ⟨squareGenerator, ?_⟩
  intro input _
  refine ⟨squareOutput input, squareOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := squareOutput_novel input
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨squares_subset_family r j hmem, hfresh, hnovel⟩

end Stage3Case024Proof

namespace Stage3Case024Proof

open Stage3Case024
open GenLimit.InfiniteContamination

lemma squares_ssubset_univ : Squares ⊂ (Set.univ : Language) := by
  constructor
  · exact Set.subset_univ _
  · intro h
    have hx : sparseBetweenSquares 0 ∈ Squares := h (Set.mem_univ _)
    exact sparseBetweenSquares_nonsquare 0 hx

lemma expected_univ_eq_zero
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {input : Stream} {output : Ω → Stream}
    (h : EventuallyFreshValid μ Squares input output) :
    expectedUpperDensity μ Set.univ input output = 0 := by
  unfold expectedUpperDensity
  apply integral_eq_zero_of_ae
  filter_upwards [h] with ω hω
  exact relativeUpperDensity_univ_eq_zero_of_eventual_squares hω

lemma expected_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : Language) (input : Stream) (output : Ω → Stream)
    (hint : DensityIntegrable μ K input output) :
    expectedUpperDensity μ K input output ≤ 1 := by
  unfold DensityIntegrable at hint
  unfold expectedUpperDensity
  have hle := integral_mono_ae hint (integrable_const (1 : ℝ))
    (Eventually.of_forall fun ω =>
      relativeUpperDensity_le_one
        (GenLimit.GeneratorFirst input (output ω)) K)
  simpa [integral_const, IsProbabilityMeasure.measure_univ] using hle

lemma pairObstruction : PairObstruction Squares Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hint0 _ hvalid0 _
  have hzero : expectedUpperDensity μ Set.univ commonInput output = 0 :=
    expected_univ_eq_zero μ hvalid0
  have hle : expectedUpperDensity μ Squares commonInput output ≤ 1 :=
    expected_le_one μ Squares commonInput output hint0
  constructor
  · rw [hzero, add_zero]
    exact hle
  · intro hboth
    rw [hzero] at hboth
    linarith

lemma family_zero {r : ℕ} (hr : 2 ≤ r) :
    family r ⟨0, by omega⟩ = Squares := by
  rw [family]
  rw [if_neg (by simp; omega)]
  simp [Markers]

def lastIndex (r : ℕ) (hr : 2 ≤ r) : Fin r := ⟨r - 1, by omega⟩

lemma family_last {r : ℕ} (hr : 2 ≤ r) :
    family r (lastIndex r hr) = Set.univ := by
  simp [family, lastIndex]
  omega

lemma manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (family r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let zero : Fin r := ⟨0, by omega⟩
  have hz := hvalid zero
  have hzSquares : EventuallyFreshValid μ Squares commonInput output := by
    simpa [zero, family_zero hr] using hz
  refine ⟨lastIndex r hr, ?_⟩
  rw [family_last hr]
  exact expected_univ_eq_zero μ hzSquares

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (family r) commonInput := by
  refine ⟨family_strictlyNested, ?_, globallyFeasible_family,
    manyTargetObstruction hr⟩
  intro j
  exact legal_commonInput (squares_subset_family r j)

end Stage3Case024Proof
