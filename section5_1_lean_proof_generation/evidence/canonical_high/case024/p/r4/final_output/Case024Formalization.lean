import Helpers

open Filter MeasureTheory
open scoped Topology

namespace Case024

lemma generatorFirst_subset_core_union_image_of_novel
    (input output : Stage3Case024.Stream)
    (h : GenLimit.NovelGeneratesInLimit input output core) :
    GenLimit.GeneratorFirst input output ⊆
      core ∪ ((Finset.range h.choose).image output : Set ℕ) := by
  intro x hx
  rcases hx with ⟨t, rfl, htfirst⟩
  by_cases ht : h.choose ≤ t
  · exact Or.inl ((h.choose_spec t ht).1)
  · exact Or.inr (by
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨t, Nat.lt_of_not_ge ht, rfl⟩)

lemma expected_univ_eq_zero {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (input : Stage3Case024.Stream) (output : Ω → Stage3Case024.Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ core input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.EventuallyFreshValid at hvalid
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) =
        ∫ _ : Ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hvalid] with ω hω
      exact relativeUpperDensity_univ_eq_zero _ _
        (generatorFirst_subset_core_union_image_of_novel input (output ω) hω)
    _ = 0 := by simp

lemma expected_density_le_one {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Set ℕ) (input : Stage3Case024.Stream) (output : Ω → Stage3Case024.Stream)
    (hint : Stage3Case024.DensityIntegrable μ K input output) :
    Stage3Case024.expectedUpperDensity μ K input output ≤ 1 := by
  unfold Stage3Case024.DensityIntegrable at hint
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst input (output ω)) K ∂μ) ≤
        ∫ _ : Ω, (1 : ℝ) ∂μ := by
      apply integral_mono_ae hint (integrable_const 1)
      exact Filter.Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
    _ = 1 := by simp

lemma pair_obstruction :
    Stage3Case024.PairObstruction core Set.univ swapStream := by
  intro Ω _ μ _ gen output hfollows hmeas hintcore hintuniv hvalidcore hvaliduniv
  have huniv : Stage3Case024.expectedUpperDensity μ Set.univ swapStream output = 0 :=
    expected_univ_eq_zero μ swapStream output hvalidcore
  have hcore : Stage3Case024.expectedUpperDensity μ core swapStream output ≤ 1 :=
    expected_density_le_one μ core swapStream output hintcore
  constructor
  · linarith
  · intro h
    linarith [h.2]

end Case024

namespace Case024

lemma noiseCount_mono_target {K L : Set ℕ} (hKL : K ⊆ L) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount swapStream L n ≤
      GenLimit.InfiniteContamination.noiseCount swapStream K n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun hK => ht.2 (hKL hK)⟩

lemma vanishingNoise_of_core_subset (K : Set ℕ) (hcore : core ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise swapStream K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  refine squeeze_zero' ?_ ?_ vanishingNoise_core
  · exact Filter.Eventually.of_forall fun n => by
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split <;> positivity
  · exact Filter.Eventually.of_forall fun n => by
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast noiseCount_mono_target hcore n) (by positivity)

lemma legal_of_core_subset (K : Set ℕ) (hcore : core ⊆ K) :
    Stage3Case024.Legal swapStream K := by
  refine ⟨core_infinite.mono hcore, swap_injective,
    noOmissions_of_surjective K, vanishingNoise_of_core_subset K hcore⟩

def extraPoint (k : ℕ) : ℕ := Nat.pair (k + 1) 0

lemma extraPoint_injective : Function.Injective extraPoint := by
  intro a b h
  simp [extraPoint] at h
  omega

lemma extraPoint_not_mem_core (k : ℕ) : extraPoint k ∉ core := by
  simpa [extraPoint] using not_mem_core_pair_succ k 0

def targetFamily (r : ℕ) (i : Fin r) : Set ℕ :=
  if i.val + 1 = r then Set.univ
  else core ∪ {n | ∃ k, k < i.val ∧ n = extraPoint k}

lemma core_subset_targetFamily (r : ℕ) (i : Fin r) :
    core ⊆ targetFamily r i := by
  intro x hx
  unfold targetFamily
  split
  · simp
  · exact Or.inl hx

lemma targetFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    targetFamily r ⟨0, by omega⟩ = core := by
  have hne : (0 : ℕ) + 1 ≠ r := by omega
  ext x
  simp [targetFamily, hne]

lemma targetFamily_last {r : ℕ} (hr : 2 ≤ r) :
    targetFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  have heq : r - 1 + 1 = r := by omega
  simp [targetFamily, heq]

lemma strictlyNested_targetFamily {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  intro i j hij
  have hi_not_last : i.val + 1 ≠ r := by omega
  have hsubset : targetFamily r i ⊆ targetFamily r j := by
    intro x hx
    simp only [targetFamily, hi_not_last, ↓reduceIte] at hx
    unfold targetFamily
    by_cases hjlast : j.val + 1 = r
    · simp [hjlast]
    · simp only [hjlast, ↓reduceIte]
      rcases hx with hxcore | ⟨k, hki, rfl⟩
      · exact Or.inl hxcore
      · exact Or.inr ⟨k, hki.trans hij, rfl⟩
  refine Set.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
  intro heq
  have hjmem : extraPoint i.val ∈ targetFamily r j := by
    unfold targetFamily
    by_cases hjlast : j.val + 1 = r
    · simp [hjlast]
    · simp only [hjlast, ↓reduceIte]
      exact Or.inr ⟨i.val, hij, rfl⟩
  have himem : extraPoint i.val ∈ targetFamily r i := heq ▸ hjmem
  simp only [targetFamily, hi_not_last, ↓reduceIte] at himem
  rcases himem with hcore | ⟨k, hki, hk⟩
  · exact extraPoint_not_mem_core i.val hcore
  · have : i.val = k := extraPoint_injective hk
    omega

lemma legal_targetFamily (r : ℕ) (i : Fin r) :
    Stage3Case024.Legal swapStream (targetFamily r i) :=
  legal_of_core_subset _ (core_subset_targetFamily r i)

end Case024

namespace Case024

def coreGenerator : Stage3Case024.OnlineGenerator :=
  fun t inputHistory _ =>
    Nat.pair 0 (Nat.pair t (1 + ∑ i, inputHistory i))

def coreOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => Nat.pair 0 (Nat.pair t (1 + ∑ i : Fin (t + 1), input i))

lemma coreOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows coreGenerator input (coreOutput input) := by
  intro t
  rfl

lemma coreOutput_novel (input : Stage3Case024.Stream) (K : Set ℕ)
    (hcore : core ⊆ K) :
    GenLimit.NovelGeneratesInLimit input (coreOutput input) K := by
  refine ⟨0, ?_⟩
  intro t ht
  have hmemcore : coreOutput input t ∈ core := by
    simp [coreOutput, core]
  refine ⟨hcore hmemcore, ?_, ?_⟩
  · intro hsample
    unfold GenLimit.sample at hsample
    rw [Finset.mem_image] at hsample
    rcases hsample with ⟨s, hs, hsequal⟩
    simp only [Finset.mem_range] at hs
    let sf : Fin (t + 1) := ⟨s, hs⟩
    have hle : input s ≤ ∑ i : Fin (t + 1), input i := by
      simpa [sf] using
        (Finset.single_le_sum (s := Finset.univ)
          (fun (i : Fin (t + 1)) _ => Nat.zero_le (input i)) (Finset.mem_univ sf))
    have hlt : input s < coreOutput input t := by
      have h₁ : input s < 1 + ∑ i : Fin (t + 1), input i := by omega
      have h₂ : 1 + ∑ i : Fin (t + 1), input i ≤
          Nat.pair t (1 + ∑ i : Fin (t + 1), input i) :=
        Nat.right_le_pair _ _
      have h₃ : Nat.pair t (1 + ∑ i : Fin (t + 1), input i) ≤
          coreOutput input t := by
        exact Nat.right_le_pair _ _
      exact h₁.trans_le (h₂.trans h₃)
    rw [hsequal] at hlt
    exact (Nat.lt_irrefl _ hlt)
  · intro s hst hequal
    have hinner :
        Nat.pair s (1 + ∑ i : Fin (s + 1), input i) =
          Nat.pair t (1 + ∑ i : Fin (t + 1), input i) := by
      exact (Nat.pair_eq_pair.mp hequal).2
    have hst_eq : s = t := (Nat.pair_eq_pair.mp hinner).1
    omega

lemma globallyFeasible_targetFamily {r : ℕ} :
    Stage3Case024.GloballyFeasible (targetFamily r) := by
  refine ⟨coreGenerator, ?_⟩
  intro input hlegal
  refine ⟨coreOutput input, coreOutput_follows input, ?_⟩
  intro j
  exact coreOutput_novel input _ (core_subset_targetFamily r j)

end Case024

namespace Case024

lemma manyTargetObstruction_targetFamily {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) swapStream := by
  intro Ω _ μ _ gen output hfollows hmeas hint hvalid
  let izero : Fin r := ⟨0, by omega⟩
  let ilast : Fin r := ⟨r - 1, by omega⟩
  have hvalidcore :
      Stage3Case024.EventuallyFreshValid μ core swapStream output := by
    have hz := hvalid izero
    simpa [izero, targetFamily_zero hr] using hz
  have huniv :
      Stage3Case024.expectedUpperDensity μ Set.univ swapStream output = 0 :=
    expected_univ_eq_zero μ swapStream output hvalidcore
  refine ⟨ilast, ?_⟩
  simpa [ilast, targetFamily_last hr] using huniv

lemma core_ssubset_univ : core ⊂ (Set.univ : Set ℕ) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
  intro heq
  have : extraPoint 0 ∈ core := by rw [heq]; simp
  exact extraPoint_not_mem_core 0 this

end Case024

open Case024

 theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨core, Set.univ, swapStream, core_ssubset_univ,
      legal_core, legal_univ, pair_obstruction⟩
  · intro r hr
    refine ⟨targetFamily r, swapStream, strictlyNested_targetFamily hr,
      ?_, globallyFeasible_targetFamily,
      manyTargetObstruction_targetFamily hr⟩
    intro j
    exact legal_targetFamily r j
