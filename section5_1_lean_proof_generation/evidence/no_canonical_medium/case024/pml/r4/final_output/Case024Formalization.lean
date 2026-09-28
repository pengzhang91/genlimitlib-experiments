import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

open Filter MeasureTheory
open scoped Topology

namespace Stage3Case024Proof
open Stage3Case024

open GenLimit.InfiniteContamination
open GenLimit.PatientScope

noncomputable def core (r : ℕ) : Set ℕ :=
  Set.range (fun k => (r + k) * (r + k))

lemma core_infinite (r : ℕ) : (core r).Infinite := by
  apply Set.infinite_range_of_injective
  intro a b h
  have : r + a = r + b := by nlinarith
  omega

lemma core_subset_sparseSquare (r : ℕ) : core r ⊆ {n | SparseSquare n} := by
  rintro _ ⟨k, rfl⟩
  exact ⟨r + k, rfl⟩

noncomputable def commonStream (r : ℕ) : Stream :=
  sparseMergePresentation (core r) (Set.univ \ core r) (core_infinite r)

lemma commonStream_range (r : ℕ) : Set.range (commonStream r) = Set.univ := by
  rw [commonStream, range_sparseMergePresentation (core_infinite r)]
  exact Set.union_diff_cancel (Set.subset_univ _)

lemma commonStream_legal_of_core_subset {r : ℕ} {K : Language}
    (hsub : core r ⊆ K) (hK : K.Infinite) : Legal (commonStream r) K := by
  refine ⟨hK, ?_⟩
  refine ⟨sparseMergePresentation_injective (core_infinite r) Set.disjoint_sdiff_right,
    ?_, sparseMergePresentation_vanishingNoise_of_core_subset (core_infinite r) hsub⟩
  rw [GenLimit.InfiniteContamination.NoOmissions, commonStream_range]
  exact Set.subset_univ _

noncomputable def family (r : ℕ) (j : Fin r) : Language :=
  if (j : ℕ) + 1 = r then Set.univ else core r ∪ Set.Iio (j : ℕ)

lemma core_subset_family {r : ℕ} (j : Fin r) : core r ⊆ family r j := by
  intro x hx
  by_cases hj : (j : ℕ) + 1 = r
  · simp [family, hj]
  · simp only [family, hj, if_false]
    exact Set.mem_union_left _ hx

lemma family_infinite {r : ℕ} (j : Fin r) : (family r j).Infinite :=
  (core_infinite r).mono (core_subset_family j)

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) : StrictlyNested (family r) := by
  intro i j hij
  have hir : (i : ℕ) + 1 < r := by omega
  constructor
  · intro x hx
    by_cases hj : (j : ℕ) + 1 = r
    · simp [family, hj]
    · have hi : (i : ℕ) + 1 ≠ r := by omega
      simp only [family, hi, hj, Set.mem_union, Set.mem_Iio] at hx ⊢
      exact hx.elim Or.inl (fun h => Or.inr (lt_trans h hij))
  · intro hsub
    have hmemj : (i : ℕ) ∈ family r j := by
      by_cases hj : (j : ℕ) + 1 = r
      · simp [family, hj]
      · simp [family, hj, hij]
    have hnoti : (i : ℕ) ∉ family r i := by
      have hi : (i : ℕ) + 1 ≠ r := by omega
      simp only [family, hi, if_false, Set.mem_union, Set.mem_Iio]
      push_neg
      constructor
      · rintro ⟨k, hk⟩
        have hi_lt : (i : ℕ) < r := i.isLt
        have hlarge : r ≤ (r + k) * (r + k) := by nlinarith [hr]
        have hk' : (r + k) * (r + k) = (i : ℕ) := by simpa using hk
        rw [hk'] at hlarge
        omega
      · exact Nat.le_refl _
    exact hnoti (hsub hmemj)

noncomputable def freshValue (K : Language) (hK : K.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (past : Fin t → ℕ) : ℕ :=
  Classical.choose (hK.exists_not_mem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image past)))

lemma freshValue_spec (K : Language) (hK : K.Infinite)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (past : Fin t → ℕ) :
    freshValue K hK t input past ∈ K ∧
      freshValue K hK t input past ∉ Finset.univ.image input ∪ Finset.univ.image past :=
  Classical.choose_spec (hK.exists_not_mem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image past)))

noncomputable def feasibleGenerator (r : ℕ) : OnlineGenerator :=
  fun t input past => freshValue (core r) (core_infinite r) t input past

lemma feasibleGenerator_valid (r : ℕ) (input output : Stream)
    (hfollow : Follows (feasibleGenerator r) input output) (j : Fin r) :
    EventuallyFreshValidPath (family r j) input output := by
  refine ⟨0, fun t _ => ?_⟩
  rw [hfollow t]
  have hs := freshValue_spec (core r) (core_infinite r) t
    (fun i => input i) (fun i => output i)
  refine ⟨core_subset_family j hs.1, ?_, ?_⟩
  · intro hsample
    rcases Finset.mem_image.mp hsample with ⟨s, hst, hsval⟩
    let q : Fin (t + 1) := ⟨s, Finset.mem_range.mp hst⟩
    exact hs.2 (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hsval⟩))
  · intro s hst heq
    let q : Fin t := ⟨s, hst⟩
    exact hs.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩))

noncomputable def runGenerator (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => runGenerator gen input i)
termination_by t

lemma runGenerator_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (runGenerator gen input) := by
  intro t
  rw [runGenerator]

lemma family_globallyFeasible (r : ℕ) : GloballyFeasible (family r) := by
  refine ⟨feasibleGenerator r, fun input _ =>
    ⟨runGenerator (feasibleGenerator r) input,
      runGenerator_follows _ _, fun j => ?_⟩⟩
  exact feasibleGenerator_valid r input _ (runGenerator_follows _ _) j

lemma generatorFirst_subset_core_union_range_fin
    {input output : Stream} {r T : ℕ}
    (hvalid : ∀ t, T ≤ t → output t ∈ core r) :
    GenLimit.GeneratorFirst input output ⊆
      core r ∪ Set.range (fun t : Fin T => output t) := by
  rintro x ⟨t, rfl, -⟩
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (hvalid t ht)
  · exact Set.mem_union_right _ ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩

lemma prefixCount_sparseSquare_le (n : ℕ) :
    prefixCount {x | SparseSquare x} n ≤ Nat.sqrt n + 1 := by
  classical
  simpa [prefixCount, prefixFinset, Nat.count_eq_card_filter_range]
    using count_sparseSquare_le_sqrt_add_one n

lemma tendsto_sparse_bound (c : ℕ) :
    Tendsto (fun n : ℕ => (((Nat.sqrt n + 1 + c : ℕ) : ℝ) / n)) atTop (𝓝 0) := by
  have h₁ := tendsto_sparseSqrt_add_one_div
  have h₂ : Tendsto (fun n : ℕ => (c : ℝ) / n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  convert h₁.add h₂ using 1 <;> simp [Nat.cast_add, add_div]

lemma relativeUpperDensity_univ_eq_zero_of_subset
    {A : Language} {r T : ℕ} {f : Fin T → ℕ}
    (hA : A ⊆ core r ∪ Set.range f) :
    relativeUpperDensity A Set.univ = 0 := by
  apply Tendsto.limsup_eq
  apply squeeze_zero'
    (g := fun n : ℕ => (((Nat.sqrt n + 1 + T : ℕ) : ℝ) / n))
  · exact Eventually.of_forall fun n => by positivity
  · exact Eventually.of_forall fun n => by
      rw [show prefixCount Set.univ n = n by simp [prefixCount, prefixFinset]]
      by_cases hn : n = 0
      · simp [hn]
      · apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
        exact_mod_cast calc
          prefixCount (A ∩ Set.univ) n ≤ prefixCount A n :=
            prefixCount_mono Set.inter_subset_left n
          _ ≤ prefixCount (core r ∪ Set.range f) n := prefixCount_mono hA n
          _ ≤ prefixCount (core r) n + prefixCount (Set.range f) n := by
            classical
            change (prefixFinset (core r ∪ Set.range f) n).card ≤
              (prefixFinset (core r) n).card + (prefixFinset (Set.range f) n).card
            exact (Finset.card_le_card (by
              intro x hx
              rw [Finset.mem_union]
              have hx' := mem_prefixFinset.mp hx
              exact hx'.2.elim
                (fun h => Or.inl (mem_prefixFinset.mpr ⟨hx'.1, h⟩))
                (fun h => Or.inr (mem_prefixFinset.mpr ⟨hx'.1, h⟩)))).trans
                (Finset.card_union_le _ _)
          _ ≤ prefixCount {x | SparseSquare x} n + T := by
            apply Nat.add_le_add
            · exact prefixCount_mono (core_subset_sparseSquare r) n
            · classical
              calc
                prefixCount (Set.range f) n ≤ (Finset.univ.image f).card := by
                  unfold prefixCount
                  apply Finset.card_le_card
                  intro x hx
                  have hx' := mem_prefixFinset.mp hx
                  obtain ⟨i, rfl⟩ := hx'.2
                  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
                _ ≤ Finset.univ.card := Finset.card_image_le
                _ = T := by simp
          _ ≤ Nat.sqrt n + 1 + T := Nat.add_le_add_right (prefixCount_sparseSquare_le n) T
  · exact tendsto_sparse_bound T

lemma relativeUpperDensity_le_one (A K : Language) :
    relativeUpperDensity A K ≤ 1 := by
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n =>
      div_nonneg (by positivity) (by positivity))
  · filter_upwards [] with n
    by_cases hzero : prefixCount K n = 0
    · simp [hzero]
    · rw [div_le_one (by positivity : (0 : ℝ) < prefixCount K n)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n

lemma path_density_univ_zero {input output : Stream} {r : ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output (core r)) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := hvalid
  apply relativeUpperDensity_univ_eq_zero_of_subset
    (f := fun t : Fin T => output t)
  exact generatorFirst_subset_core_union_range_fin (fun t ht => (hT t ht).1)

lemma pair_obstruction (r : ℕ) :
    PairObstruction (core r) Set.univ (commonStream r) := by
  intro Ω _ μ _ gen output _ _ hInt0 _ hcore _
  have hz : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst (commonStream r) (output ω)) Set.univ = 0 :=
    hcore.mono (fun ω hω => path_density_univ_zero hω)
  have hint : expectedUpperDensity μ Set.univ (commonStream r) output = 0 := by
    unfold expectedUpperDensity
    exact integral_eq_zero_of_ae hz
  have hle : expectedUpperDensity μ (core r) (commonStream r) output ≤ 1 := by
    unfold expectedUpperDensity
    calc
      ∫ ω, relativeUpperDensity (GenLimit.GeneratorFirst (commonStream r) (output ω)) (core r) ∂μ
          ≤ ∫ _ω, (1 : ℝ) ∂μ := integral_mono_ae hInt0 (integrable_const 1)
            (Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _)
      _ = 1 := by simp
  constructor
  · simpa [hint] using hle
  · rw [hint]
    norm_num

lemma many_obstruction {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (family r) (commonStream r) := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hlast : family r last = Set.univ := by
    simp only [family, last]
    rw [if_pos (by omega)]
  rw [hlast]
  have hcore := hvalid ⟨0, by omega⟩
  have hzero : ∀ᵐ ω ∂μ,
      relativeUpperDensity (GenLimit.GeneratorFirst (commonStream r) (output ω)) Set.univ = 0 := by
    apply hcore.mono
    intro ω hω
    have hfamily0 : family r ⟨0, by omega⟩ = core r := by
      simp [family]
      omega
    rw [hfamily0] at hω
    exact path_density_univ_zero hω
  unfold expectedUpperDensity
  exact integral_eq_zero_of_ae hzero

end Stage3Case024Proof

open Stage3Case024
open Stage3Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨core 2, Set.univ, commonStream 2, ?_,
      commonStream_legal_of_core_subset (Set.Subset.rfl) (core_infinite 2),
      commonStream_legal_of_core_subset (Set.subset_univ _) Set.infinite_univ,
      pair_obstruction 2⟩
    constructor
    · exact Set.subset_univ _
    · intro hsub
      have hone := hsub (Set.mem_univ 1)
      rcases hone with ⟨k, hk⟩
      have : 4 ≤ (2 + k) * (2 + k) := by nlinarith
      nlinarith
  · intro r hr
    refine ⟨family r, commonStream r, family_strictlyNested hr,
      fun j => commonStream_legal_of_core_subset (core_subset_family j) (family_infinite j),
      family_globallyFeasible r, many_obstruction hr⟩
