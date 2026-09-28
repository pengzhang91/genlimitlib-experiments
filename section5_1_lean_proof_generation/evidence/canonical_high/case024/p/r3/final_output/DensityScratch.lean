import Helpers

open Filter MeasureTheory
open scoped Topology

namespace Case024Formalization

open Stage3Case024

noncomputable section

lemma generatorFirst_prefixCount_le (input output : Stream) (K : Language) (T n : ℕ)
    (hvalid : ∀ t, T ≤ t → output t ∈ K) :
    pcount (GenLimit.GeneratorFirst input output) n ≤ pcount K n + T := by
  classical
  let early : Finset ℕ := (Finset.range T).image output
  have hsub : GenLimit.PatientScope.prefixFinset
      (GenLimit.GeneratorFirst input output) n ⊆
      GenLimit.PatientScope.prefixFinset K n ∪ early := by
    intro x hx
    have hxmem := (Finset.mem_filter.1 hx).2
    have hxlt := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    rcases hxmem with ⟨t, houtput, hfirst⟩
    apply Finset.mem_union.2
    by_cases ht : T ≤ t
    · apply Or.inl
      apply Finset.mem_filter.2
      exact ⟨Finset.mem_range.2 hxlt, by simpa [houtput] using hvalid t ht⟩
    · apply Or.inr
      apply Finset.mem_image.2
      exact ⟨t, Finset.mem_range.2 (by omega), houtput⟩
  calc
    pcount (GenLimit.GeneratorFirst input output) n ≤
        (GenLimit.PatientScope.prefixFinset K n ∪ early).card :=
      Finset.card_le_card hsub
    _ ≤ (GenLimit.PatientScope.prefixFinset K n).card + early.card :=
      Finset.card_union_le _ _
    _ ≤ pcount K n + T := by
      unfold pcount GenLimit.PatientScope.prefixCount
      exact Nat.add_le_add_left (by simpa [early] using (Finset.card_image_le (f := output) (s := Finset.range T))) _

lemma generatorFirst_tendsto_zero_of_eventual_sparse
    (input output : Stream) {K : Language} (hK : SparseCore K)
    (hvalid : GenLimit.NovelGeneratesInLimit input output K) :
    Tendsto (fun n : ℕ => (pcount (GenLimit.GeneratorFirst input output) n : ℝ) / n)
      atTop (𝓝 0) := by
  rcases hvalid with ⟨T, hT⟩
  have hconst : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper : Tendsto
      (fun n : ℕ => (pcount K n : ℝ) / n + (T : ℝ) / n) atTop (𝓝 0) := by
    simpa using hK.2.2.add hconst
  apply squeeze_zero'
      (f := fun n : ℕ => (pcount (GenLimit.GeneratorFirst input output) n : ℝ) / n)
      (g := fun n : ℕ => (pcount K n : ℝ) / n + (T : ℝ) / n)
  · filter_upwards with n
    positivity
  · filter_upwards with n
    by_cases hn : n = 0
    · subst n
      simp
    · have hcount := generatorFirst_prefixCount_le input output K T n
          (fun t ht => (hT t ht).1)
      have hcast : (pcount (GenLimit.GeneratorFirst input output) n : ℝ) ≤
          (pcount K n : ℝ) + T := by exact_mod_cast hcount
      rw [← add_div]
      exact div_le_div_of_nonneg_right hcast (by positivity)
  · exact hupper

lemma relativeUpperDensity_univ_eq_zero_of_eventual_sparse
    (input output : Stream) {K : Language} (hK : SparseCore K)
    (hvalid : GenLimit.NovelGeneratesInLimit input output K) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  unfold relativeUpperDensity
  have ht := generatorFirst_tendsto_zero_of_eventual_sparse input output hK hvalid
  apply Filter.Tendsto.limsup_eq
  simpa [pcount, pcount_univ] using ht

lemma relativeUpperDensity_le_one (A K : Language) : relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  apply limsup_le_of_le (hf := isCoboundedUnder_le_of_le atTop (fun n => by positivity))
  filter_upwards with n
  have hcount : pcount (A ∩ K) n ≤ pcount K n := pcount_mono Set.inter_subset_right n
  by_cases hz : pcount K n = 0
  · simp [hz]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast hcount

lemma relativeUpperDensity_nonneg (A K : Language) : 0 ≤ relativeUpperDensity A K := by
  unfold relativeUpperDensity
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (pcount (A ∩ K) n : ℝ) / (pcount K n : ℝ)) := by
    refine ⟨(1 : ℝ), ?_⟩
    change ∀ᶠ n : ℕ in atTop,
      (pcount (A ∩ K) n : ℝ) / (pcount K n : ℝ) ≤ 1
    filter_upwards with n
    have hcount : pcount (A ∩ K) n ≤ pcount K n := pcount_mono Set.inter_subset_right n
    by_cases hz : pcount K n = 0
    · simp [hz]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast hcount
  apply le_limsup_of_le (hf := hbounded)
  intro b hb
  rcases hb.exists with ⟨n, hn⟩
  exact le_trans (by positivity : 0 ≤ (pcount (A ∩ K) n : ℝ) / (pcount K n : ℝ)) hn

lemma expectedUpperDensity_univ_eq_zero_of_ae_eventual_sparse
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : Stream) (output : Ω → Stream) {K : Language} (hK : SparseCore K)
    (hvalid : EventuallyFreshValid μ K input output) :
    expectedUpperDensity μ Set.univ input output = 0 := by
  unfold expectedUpperDensity
  calc
    (∫ ω, relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) = ∫ _ : Ω, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hvalid] with ω hω
        exact relativeUpperDensity_univ_eq_zero_of_eventual_sparse input (output ω) hK hω
    _ = 0 := integral_zero Ω ℝ

lemma expectedUpperDensity_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Language) (input : Stream) (output : Ω → Stream)
    (hint : DensityIntegrable μ K input output) :
    expectedUpperDensity μ K input output ≤ 1 := by
  unfold expectedUpperDensity
  have hmono := integral_mono_ae hint (integrable_const (1 : ℝ))
    (Filter.Eventually.of_forall (fun ω => relativeUpperDensity_le_one
      (GenLimit.GeneratorFirst input (output ω)) K))
  simpa using hmono

end

end Case024Formalization

namespace Case024Formalization

open Stage3Case024

noncomputable section

lemma pairObstruction_quadratic :
    PairObstruction quadraticCore Set.univ
      (swapPerm quadraticCore quadraticCore_sparse.1 quadraticCore_sparse.2.1) := by
  intro Ω _ μ _ gen output hfollow hmeas hintCore hintUniv hvalidCore hvalidUniv
  have hzero : expectedUpperDensity μ Set.univ
      (swapPerm quadraticCore quadraticCore_sparse.1 quadraticCore_sparse.2.1) output = 0 :=
    expectedUpperDensity_univ_eq_zero_of_ae_eventual_sparse μ _ output
      quadraticCore_sparse hvalidCore
  constructor
  · rw [hzero, add_zero]
    exact expectedUpperDensity_le_one μ quadraticCore _ output hintCore
  · intro hboth
    rw [hzero] at hboth
    norm_num at hboth

lemma gap_injective : Function.Injective (fun k : ℕ => k * (k + 1) + 1) := by
  intro a b hab
  apply quadratic_strictMono.injective
  exact Nat.add_right_cancel hab

def gapPrefix (j : ℕ) : Set ℕ :=
  {x | ∃ k < j, x = k * (k + 1) + 1}

lemma gap_mem_gapPrefix {k j : ℕ} (hkj : k < j) :
    k * (k + 1) + 1 ∈ gapPrefix j := ⟨k, hkj, rfl⟩

lemma gap_not_mem_gapPrefix (j : ℕ) : j * (j + 1) + 1 ∉ gapPrefix j := by
  rintro ⟨k, hkj, hk⟩
  have : k = j := gap_injective hk.symm
  omega

def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if j.1 + 1 = r then Set.univ else quadraticCore ∪ gapPrefix j.1

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = quadraticCore := by
  change (if 0 + 1 = r then Set.univ else quadraticCore ∪ gapPrefix 0) = quadraticCore
  rw [if_neg (by omega)]
  ext x
  simp [gapPrefix]

lemma nestedFamily_last {r : ℕ} (hr : 1 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [nestedFamily, Nat.sub_add_cancel hr]

lemma nestedFamily_infinite {r : ℕ} (j : Fin r) : (nestedFamily r j).Infinite := by
  by_cases hj : j.1 + 1 = r
  · simpa [nestedFamily, hj] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  · apply quadraticCore_infinite.mono
    simp [nestedFamily, hj]

lemma nestedFamily_strict {r : ℕ} : StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiNotLast : i.1 + 1 ≠ r := by omega
  refine Set.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
  · intro x hx
    simp only [nestedFamily, hiNotLast, if_false] at hx
    by_cases hjLast : j.1 + 1 = r
    · simp [nestedFamily, hjLast]
    · simp only [nestedFamily, hjLast, if_false]
      rcases hx with hx | ⟨k, hki, hk⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, lt_trans hki hij, hk⟩
  · intro heq
    have hwit : i.1 * (i.1 + 1) + 1 ∈ nestedFamily r j := by
      by_cases hjLast : j.1 + 1 = r
      · simp [nestedFamily, hjLast]
      · simp [nestedFamily, hjLast, gap_mem_gapPrefix hij]
    have hnot : i.1 * (i.1 + 1) + 1 ∉ nestedFamily r i := by
      simp only [nestedFamily, hiNotLast, if_false, Set.mem_union]
      exact fun h => h.elim (gap_not_quadratic i.1) (gap_not_mem_gapPrefix i.1)
    exact hnot (heq ▸ hwit)

lemma noiseCount_mono {input : Stream} {K L : Language} (hKL : K ⊆ L) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input L n ≤
      GenLimit.InfiniteContamination.noiseCount input K n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun hk => ht.2 (hKL hk)⟩

lemma legal_swap_superset {K L : Language} (hK : SparseCore K) (hKL : K ⊆ L)
    (hL : L.Infinite) : Legal (swapPerm K hK.1 hK.2.1) L := by
  refine ⟨hL, (swapPerm K hK.1 hK.2.1).injective, ?_, ?_⟩
  · intro x hx
    exact (swapPerm K hK.1 hK.2.1).surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply squeeze_zero'
      (f := GenLimit.InfiniteContamination.empiricalNoiseRate
        (swapPerm K hK.1 hK.2.1) L)
      (g := GenLimit.InfiniteContamination.empiricalNoiseRate
        (swapPerm K hK.1 hK.2.1) K)
    · filter_upwards with n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split <;> positivity
    · filter_upwards with n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split
      · simp
      · apply div_le_div_of_nonneg_right
        · exact_mod_cast noiseCount_mono hKL n
        · positivity
    · exact (legal_swap_core hK).2.2.2

lemma legal_nestedFamily (r : ℕ) (j : Fin r) :
    Legal (swapPerm quadraticCore quadraticCore_sparse.1 quadraticCore_sparse.2.1)
      (nestedFamily r j) := by
  apply legal_swap_superset quadraticCore_sparse
  · intro x hx
    by_cases hj : j.1 + 1 = r
    · simp [nestedFamily, hj]
    · simpa [nestedFamily, hj] using (Or.inl hx : x ∈ quadraticCore ∨ x ∈ gapPrefix j.1)
  · exact nestedFamily_infinite (r := r) j

noncomputable def freshCoreGenerator (K : Language) (hK : K.Infinite) : OnlineGenerator :=
  fun t inputPrefix outputPrefix =>
    Classical.choose (hK.exists_not_mem_finset
      ((Finset.univ.image inputPrefix) ∪ (Finset.univ.image outputPrefix)))

lemma freshCoreGenerator_spec (K : Language) (hK : K.Infinite) (t : ℕ)
    (inputPrefix : Fin (t + 1) → ℕ) (outputPrefix : Fin t → ℕ) :
    freshCoreGenerator K hK t inputPrefix outputPrefix ∈ K ∧
      freshCoreGenerator K hK t inputPrefix outputPrefix ∉ Finset.univ.image inputPrefix ∧
      freshCoreGenerator K hK t inputPrefix outputPrefix ∉ Finset.univ.image outputPrefix := by
  have hs := Classical.choose_spec (hK.exists_not_mem_finset
    ((Finset.univ.image inputPrefix) ∪ (Finset.univ.image outputPrefix)))
  exact ⟨hs.1, fun h => hs.2 (Finset.mem_union_left _ h),
    fun h => hs.2 (Finset.mem_union_right _ h)⟩

noncomputable def followOutput (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => WellFounded.fix Nat.lt_wfRel.wf
    (fun t rec => gen t (fun i => input i) (fun i => rec i i.isLt)) t

lemma followOutput_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    followOutput gen input t =
      gen t (fun i => input i) (fun i => followOutput gen input i) := by
  rw [followOutput, WellFounded.fix_eq]
  congr 1

lemma freshCoreGenerator_follows (K : Language) (hK : K.Infinite) (input : Stream) :
    Follows (freshCoreGenerator K hK) input
      (followOutput (freshCoreGenerator K hK) input) := by
  intro t
  exact followOutput_eq _ _ t

lemma freshCoreGenerator_valid (K : Language) (hK : K.Infinite) (input : Stream) :
    GenLimit.NovelGeneratesInLimit input
      (followOutput (freshCoreGenerator K hK) input) K := by
  refine ⟨0, fun t ht => ?_⟩
  have hs := freshCoreGenerator_spec K hK t (fun i => input i)
    (fun i => followOutput (freshCoreGenerator K hK) input i)
  rw [followOutput_eq]
  refine ⟨hs.1, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.sample] at hsample
    rcases Finset.mem_image.1 hsample with ⟨i, hi, hieq⟩
    exact hs.2.1 (Finset.mem_image.2
      ⟨⟨i, by simpa using Finset.mem_range.1 hi⟩, Finset.mem_univ _, hieq⟩)
  · intro s hst heq
    exact hs.2.2 (Finset.mem_image.2 ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩)

lemma globallyFeasible_nestedFamily (r : ℕ) : GloballyFeasible (nestedFamily r) := by
  refine ⟨freshCoreGenerator quadraticCore quadraticCore_infinite, fun input hlegal => ?_⟩
  refine ⟨followOutput (freshCoreGenerator quadraticCore quadraticCore_infinite) input,
    freshCoreGenerator_follows quadraticCore quadraticCore_infinite input, ?_⟩
  intro j
  rcases freshCoreGenerator_valid quadraticCore quadraticCore_infinite input with ⟨T, hT⟩
  refine ⟨T, fun t ht => ?_⟩
  have h := hT t ht
  refine ⟨?_, h.2.1, h.2.2⟩
  by_cases hj : j.1 + 1 = r
  · simp [nestedFamily, hj]
  · simpa [nestedFamily, hj] using
      (Or.inl h.1 : _ ∈ quadraticCore ∨ _ ∈ gapPrefix j.1)

end

end Case024Formalization

namespace Case024Formalization

open Stage3Case024

noncomputable section

lemma manyTargetObstruction_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r)
      (swapPerm quadraticCore quadraticCore_sparse.1 quadraticCore_sparse.2.1) := by
  intro Ω _ μ _ gen output hfollow hmeas hint hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hvalidCore : EventuallyFreshValid μ quadraticCore
      (swapPerm quadraticCore quadraticCore_sparse.1 quadraticCore_sparse.2.1) output := by
    simpa [first, nestedFamily_zero hr] using hvalid first
  have hzero : expectedUpperDensity μ Set.univ
      (swapPerm quadraticCore quadraticCore_sparse.1 quadraticCore_sparse.2.1) output = 0 :=
    expectedUpperDensity_univ_eq_zero_of_ae_eventual_sparse μ _ output
      quadraticCore_sparse hvalidCore
  refine ⟨last, ?_⟩
  simpa [last, nestedFamily_last (by omega : 1 ≤ r)] using hzero

lemma quadraticCore_ssubset_univ : quadraticCore ⊂ (Set.univ : Set ℕ) := by
  refine Set.ssubset_iff_subset_ne.2 ⟨Set.subset_univ _, ?_⟩
  intro heq
  have hmem : 1 ∈ quadraticCore := heq ▸ Set.mem_univ 1
  simpa using (gap_not_quadratic 0 hmem)

lemma mainClaim : MainClaim := by
  constructor
  · refine ⟨quadraticCore, Set.univ,
      swapPerm quadraticCore quadraticCore_sparse.1 quadraticCore_sparse.2.1,
      quadraticCore_ssubset_univ, legal_swap_core quadraticCore_sparse,
      legal_swap_univ quadraticCore_sparse, pairObstruction_quadratic⟩
  · intro r hr
    refine ⟨nestedFamily r,
      swapPerm quadraticCore quadraticCore_sparse.1 quadraticCore_sparse.2.1, ?_⟩
    exact ⟨nestedFamily_strict, legal_nestedFamily r,
      globallyFeasible_nestedFamily r, manyTargetObstruction_nestedFamily hr⟩

end

end Case024Formalization
