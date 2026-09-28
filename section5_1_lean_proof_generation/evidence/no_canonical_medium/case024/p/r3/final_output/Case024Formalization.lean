import Stage3Model
import Mathlib

open Filter MeasureTheory Set
open scoped Topology

namespace Case024Proof

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

noncomputable def core : Language := Set.range (fun k : ℕ => 2 ^ (k + 1))

lemma core_infinite : core.Infinite := by
  apply Set.infinite_range_of_injective
  apply (Nat.pow_right_injective (by omega : 2 ≤ 2)).comp
  intro a b h
  exact Nat.add_right_cancel h

lemma prefixCount_core_le_log (n : ℕ) :
    GenLimit.PatientScope.prefixCount core n ≤ Nat.log 2 n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset core
  let s := (Finset.range (Nat.log 2 n)).image (fun k : ℕ => 2 ^ (k + 1))
  calc
    ((Finset.range n).filter fun x => x ∈ Set.range (fun k : ℕ => 2 ^ (k + 1))).card ≤ s.card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range] at hx
      rcases hx with ⟨hxn, k, rfl⟩
      simp only [s, Finset.mem_image]
      refine ⟨k, ?_, rfl⟩
      rw [Finset.mem_range]
      have hp : 2 ^ (k + 1) ≤ n := Nat.le_of_lt hxn
      exact (Nat.le_log_of_pow_le (by omega) hp)
    _ ≤ Nat.log 2 n := by
      exact Finset.card_image_le.trans (by simp [s])

lemma tendsto_log_ratio :
    Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ) / n) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.logb 2 x / x) atTop (𝓝 0) := by
    simpa [Real.logb, div_eq_mul_inv, mul_comm, mul_left_comm] using
      (Real.isLittleO_log_id_atTop.const_mul_left (Real.log 2)⁻¹).tendsto_div_nhds_zero
  have hcomp := hreal.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (g := fun n : ℕ => Real.logb 2 n / n)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (Real.natLog_le_logb n 2) (by positivity)
  · simpa using hcomp

lemma tendsto_core_ratio :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount core n : ℝ) / n) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun n : ℕ => (Nat.log 2 n : ℝ) / n)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (mod_cast prefixCount_core_le_log n) (by positivity)
  · exact tendsto_log_ratio

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Language) n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma core_relative_zero (A : Language) (hA : A ⊆ core) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  have hle : ∀ n, GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n ≤
      GenLimit.PatientScope.prefixCount core n := by
    intro n
    unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff, Set.mem_univ,
      and_true] at hx ⊢
    exact ⟨hx.1, hA hx.2⟩
  apply squeeze_zero' (g := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount core n : ℝ) / n)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [prefixCount_univ]
    exact div_le_div_of_nonneg_right (mod_cast hle n) (by positivity)
  · exact tendsto_core_ratio

lemma core_compl_infinite : coreᶜ.Infinite := by
  let f : ℕ → ℕ := fun n => 2 * n + 1
  have hf : Function.Injective f := by
    intro a b h
    simp only [f] at h
    omega
  apply (Set.infinite_range_of_injective hf).mono
  intro x hx
  rcases hx with ⟨n, rfl⟩
  simp only [Set.mem_compl_iff, core, Set.mem_range, not_exists]
  intro k hk
  have he : Even (2 ^ (k + 1)) := (Nat.even_pow.2 ⟨by simp, by omega⟩)
  rw [hk] at he
  exact (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one n)) he

noncomputable def coreSwap : {n : ℕ // n ∈ core} ≃ {n : ℕ // n ∈ coreᶜ} := by
  letI : Infinite {n : ℕ // n ∈ core} := core_infinite.to_subtype
  letI : Infinite {n : ℕ // n ∈ coreᶜ} := core_compl_infinite.to_subtype
  exact Classical.choice nonempty_equiv_of_countable

noncomputable def input : Stream := by
  classical
  exact fun n =>
    if h : n ∈ core then (coreSwap ⟨n, h⟩ : ℕ)
    else (coreSwap.symm ⟨n, by simpa⟩ : ℕ)

lemma input_core_iff (n : ℕ) : input n ∈ core ↔ n ∉ core := by
  classical
  rw [input]
  split_ifs with h
  · constructor
    · intro hi
      have hc : (coreSwap ⟨n, h⟩ : ℕ) ∉ core := by
        simpa only [Set.mem_compl_iff] using (coreSwap ⟨n, h⟩).property
      exact (hc hi).elim
    · intro hn
      exact (hn h).elim
  · constructor
    · intro hi
      exact h
    · intro hn
      exact (coreSwap.symm ⟨n, by simpa using h⟩).property

lemma input_involutive : Function.Involutive input := by
  intro n
  classical
  by_cases h : n ∈ core
  · have ho : (coreSwap ⟨n, h⟩ : ℕ) ∉ core := by
      simpa only [Set.mem_compl_iff] using (coreSwap ⟨n, h⟩).property
    simpa [input, h, ho] using congrArg Subtype.val (coreSwap.symm_apply_apply ⟨n, h⟩)
  · have hi : (coreSwap.symm ⟨n, by simpa using h⟩ : ℕ) ∈ core :=
      (coreSwap.symm ⟨n, by simpa using h⟩).property
    simpa [input, h, hi] using
      congrArg Subtype.val (coreSwap.apply_symm_apply ⟨n, by simpa using h⟩)

lemma input_bijective : Function.Bijective input := input_involutive.bijective

lemma noise_le_core (K : Language) (hcore : core ⊆ K) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input K n ≤
      GenLimit.PatientScope.prefixCount core n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
    GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  refine ⟨ht.1, ?_⟩
  by_contra hn
  exact ht.2 (hcore ((input_core_iff t).mpr hn))

lemma vanishingNoise_of_core_subset (K : Language) (hcore : core ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise input K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  apply squeeze_zero' (g := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount core n : ℝ) / n)
  · filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split_ifs
    · simp
    · positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [GenLimit.InfiniteContamination.empiricalNoiseRate, if_neg hn.ne']
    exact div_le_div_of_nonneg_right (mod_cast noise_le_core K hcore n) (by positivity)
  · exact tendsto_core_ratio

lemma legal_of_core_subset (K : Language) (hcore : core ⊆ K) (hinf : K.Infinite) :
    Stage3Case024.Legal input K := by
  refine ⟨hinf, input_bijective.1, ?_, vanishingNoise_of_core_subset K hcore⟩
  intro x hx
  exact input_bijective.2 x

lemma relative_zero_of_subset_core_union_finset (A : Language) (F : Finset ℕ)
    (hA : A ⊆ core ∪ (↑F : Set ℕ)) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  simp only [Set.inter_univ]
  apply Filter.Tendsto.limsup_eq
  have hcount : ∀ n, GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount core n + F.card := by
    intro n
    classical
    unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
    let left := (Finset.range n).filter fun x => x ∈ A
    let right := ((Finset.range n).filter fun x => x ∈ core) ∪ F
    have hsub : left ⊆ right := by
      intro x hx
      simp only [left, Finset.mem_filter, Finset.mem_range] at hx
      simp only [right, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      rcases hA hx.2 with hc | hf
      · exact Or.inl ⟨hx.1, hc⟩
      · exact Or.inr hf
    dsimp only [left] at hsub ⊢
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hfinite : Tendsto (fun n : ℕ => (F.card : ℝ) / n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (g := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount core n : ℝ) / n + (F.card : ℝ) / n)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [prefixCount_univ]
    calc
      (GenLimit.PatientScope.prefixCount A n : ℝ) / n ≤
          ((GenLimit.PatientScope.prefixCount core n + F.card : ℕ) : ℝ) / n :=
        div_le_div_of_nonneg_right (mod_cast hcount n) (by positivity)
      _ = (GenLimit.PatientScope.prefixCount core n : ℝ) / n + (F.card : ℝ) / n := by
        rw [Nat.cast_add, add_div]
  · simpa using tendsto_core_ratio.add hfinite

lemma generatorFirst_subset_after
    (output : Stream) (T : ℕ)
    (hvalid : ∀ t, T ≤ t → output t ∈ core) :
    GenLimit.GeneratorFirst input output ⊆
      core ∪ (↑((Finset.range T).image output) : Set ℕ) := by
  intro x hx
  rcases hx with ⟨t, rfl, ht⟩
  by_cases hT : T ≤ t
  · exact Or.inl (hvalid t hT)
  · exact Or.inr (by simp; exact ⟨t, by omega, rfl⟩)

lemma density_univ_zero_of_novel (output : Stream)
    (h : GenLimit.NovelGeneratesInLimit input output core) :
    Stage3Case024.relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  rcases h with ⟨T, hT⟩
  apply relative_zero_of_subset_core_union_finset _ ((Finset.range T).image output)
  exact generatorFirst_subset_after output T (fun t ht => (hT t ht).1)

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n => by positivity))
  filter_upwards with n
  by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hz]
  · apply (div_le_one (by positivity)).2
    norm_cast
    classical
    unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff] at hx ⊢
    exact ⟨hx.1, hx.2.2⟩

lemma core_ssubset_univ : core ⊂ (Set.univ : Language) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have h0 : (0 : ℕ) ∈ core := h (Set.mem_univ 0)
  rcases h0 with ⟨k, hk⟩
  have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
  exact (Nat.ne_of_gt hp) hk

lemma expected_univ_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (output : Ω → Stream)
    (hev : Stage3Case024.EventuallyFreshValid μ core input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.EventuallyFreshValid at hev
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) = ∫ _ω, (0 : ℝ) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hev] with ω hω
        exact density_univ_zero_of_novel (output ω) hω
    _ = 0 := integral_zero Ω ℝ

lemma expected_le_one {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : Language) (output : Ω → Stream)
    (hint : Stage3Case024.DensityIntegrable μ K input output) :
    Stage3Case024.expectedUpperDensity μ K input output ≤ 1 := by
  unfold Stage3Case024.DensityIntegrable at hint
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) K ∂μ) ≤ ∫ _ω, (1 : ℝ) ∂μ := by
        apply MeasureTheory.integral_mono_ae hint (integrable_const 1)
        filter_upwards with ω
        exact relativeUpperDensity_le_one _ _
    _ = 1 := by simp

lemma pairObstruction : Stage3Case024.PairObstruction core Set.univ input := by
  intro Ω _ μ _ gen output hfollow hmeas hint0 hint1 hev0 hev1
  have hz := expected_univ_zero μ output hev0
  have hu := expected_le_one μ core output hint0
  constructor
  · rw [hz, add_zero]
    exact hu
  · intro hboth
    rw [hz] at hboth
    linarith


private def oddExtra (n : ℕ) : ℕ := 2 * n + 1

private lemma oddExtra_injective : Function.Injective oddExtra := by
  intro a b h
  unfold oddExtra at h
  omega

private lemma oddExtra_not_core (n : ℕ) : oddExtra n ∉ core := by
  intro h
  rcases h with ⟨k, hk⟩
  have he : Even (2 ^ (k + 1)) := Nat.even_pow.2 ⟨by simp, by omega⟩
  change 2 ^ (k + 1) = oddExtra n at hk
  rw [hk] at he
  exact (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one n)) he

private def extrasBefore (j : ℕ) : Language :=
  {x | ∃ k < j, x = oddExtra k}

noncomputable def targetFamily (r : ℕ) (j : Fin r) : Language :=
  if j.1 + 1 = r then Set.univ else core ∪ extrasBefore j.1

lemma core_subset_targetFamily (r : ℕ) (j : Fin r) : core ⊆ targetFamily r j := by
  intro x hx
  unfold targetFamily
  split_ifs
  · exact Set.mem_univ x
  · exact Or.inl hx

lemma targetFamily_infinite (r : ℕ) (j : Fin r) : (targetFamily r j).Infinite :=
  core_infinite.mono (core_subset_targetFamily r j)

lemma targetFamily_strictlyNested (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  intro i j hij
  have hi : i.1 + 1 ≠ r := by omega
  by_cases hj : j.1 + 1 = r
  · rw [targetFamily, if_neg hi, targetFamily, if_pos hj]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hsub
    have hw : oddExtra i.1 ∈ core ∪ extrasBefore i.1 := hsub (Set.mem_univ _)
    rcases hw with hw | hw
    · exact oddExtra_not_core i.1 hw
    · rcases hw with ⟨k, hk, heq⟩
      have : k = i.1 := oddExtra_injective heq.symm
      omega
  · rw [targetFamily, if_neg hi, targetFamily, if_neg hj]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | ⟨k, hk, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, by omega, rfl⟩
    · intro hsub
      have hw : oddExtra i.1 ∈ core ∪ extrasBefore i.1 :=
        hsub (Or.inr ⟨i.1, hij, rfl⟩)
      rcases hw with hw | hw
      · exact oddExtra_not_core i.1 hw
      · rcases hw with ⟨k, hk, heq⟩
        have : k = i.1 := oddExtra_injective heq.symm
        omega

noncomputable def freshCoreGen : Stage3Case024.OnlineGenerator :=
  fun _t xs ys => Classical.choose
    (core_infinite.exists_not_mem_finset
      ((Finset.univ.image xs) ∪ (Finset.univ.image ys)))

lemma freshCoreGen_spec (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    freshCoreGen t xs ys ∈ core ∧
      freshCoreGen t xs ys ∉ (Finset.univ.image xs) ∪ (Finset.univ.image ys) := by
  exact Classical.choose_spec
    (core_infinite.exists_not_mem_finset
      ((Finset.univ.image xs) ∪ (Finset.univ.image ys)))

noncomputable def runGenerator (gen : Stage3Case024.OnlineGenerator)
    (presented : Stream) : Stream :=
  (measure id).wf.fix (C := fun _ => ℕ) (fun t rec =>
    gen t (fun i => presented i) (fun i => rec i (by exact i.isLt)))

lemma runGenerator_eq (gen : Stage3Case024.OnlineGenerator)
    (presented : Stream) (t : ℕ) :
    runGenerator gen presented t =
      gen t (fun i => presented i) (fun i => runGenerator gen presented i) := by
  rw [runGenerator, WellFounded.fix_eq]

lemma runFresh_novel_core (presented : Stream) :
    GenLimit.NovelGeneratesInLimit presented (runGenerator freshCoreGen presented) core := by
  refine ⟨0, ?_⟩
  intro t _ht
  rw [runGenerator_eq]
  have hs := freshCoreGen_spec t (fun i => presented i)
    (fun i => runGenerator freshCoreGen presented i)
  refine ⟨hs.1, ?_, ?_⟩
  · intro hmem
    apply hs.2
    simp only [Finset.mem_union, Finset.mem_image]
    left
    rw [GenLimit.sample] at hmem
    rcases Finset.mem_image.mp hmem with ⟨s, hslt, heq⟩
    exact ⟨⟨s, by simpa using hslt⟩, Finset.mem_univ _, heq⟩
  · intro s hst heq
    apply hs.2
    simp only [Finset.mem_union, Finset.mem_image]
    right
    exact ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩

lemma targetFamily_globallyFeasible (r : ℕ) :
    Stage3Case024.GloballyFeasible (targetFamily r) := by
  refine ⟨freshCoreGen, ?_⟩
  intro presented _hlegal
  refine ⟨runGenerator freshCoreGen presented, ?_, ?_⟩
  · intro t
    exact runGenerator_eq freshCoreGen presented t
  · intro j
    rcases runFresh_novel_core presented with ⟨T, hT⟩
    exact ⟨T, fun t ht =>
      ⟨core_subset_targetFamily r j (hT t ht).1, (hT t ht).2.1, (hT t ht).2.2⟩⟩

lemma targetFamily_obstruction (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) input := by
  intro Ω _ μ _ gen output hfollow hmeas hint hev
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hzero := expected_univ_zero μ output (by
    have hcore := hev ⟨0, by omega⟩
    have hne : 1 ≠ r := by omega
    simpa [targetFamily, extrasBefore, hne] using hcore)
  have hlast : targetFamily r last = Set.univ := by
    simp [targetFamily, last]
    omega
  simpa [hlast] using hzero

lemma manyTargetWitness (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (targetFamily r) input := by
  refine ⟨targetFamily_strictlyNested r hr, ?_, targetFamily_globallyFeasible r,
    targetFamily_obstruction r hr⟩
  intro j
  exact legal_of_core_subset _ (core_subset_targetFamily r j) (targetFamily_infinite r j)

end Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · exact ⟨Case024Proof.core, Set.univ, Case024Proof.input, Case024Proof.core_ssubset_univ,
      Case024Proof.legal_of_core_subset _ (fun _ h => h) Case024Proof.core_infinite,
      Case024Proof.legal_of_core_subset _ (Set.subset_univ _) Set.infinite_univ,
      Case024Proof.pairObstruction⟩
  · intro r hr
    exact ⟨Case024Proof.targetFamily r, Case024Proof.input,
      Case024Proof.manyTargetWitness r hr⟩
