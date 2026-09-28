import Stage3Model
import Mathlib

open Filter MeasureTheory
open scoped Topology

namespace Case024Helpers

open Stage3Case024

noncomputable section

def core : Set ℕ := Set.range (fun n : ℕ => n ^ 2)

abbrev Core := {n : ℕ // n ∈ core}
abbrev Outside := {n : ℕ // n ∉ core}

lemma square_injective : Function.Injective (fun n : ℕ => n ^ 2) := by
  intro a b h
  nlinarith

lemma core_infinite : core.Infinite := by
  exact Set.infinite_range_of_injective square_injective

lemma nonsquare (n : ℕ) : (n + 1) ^ 2 + 1 ∉ core := by
  rintro ⟨k, hk⟩
  by_cases hle : k ≤ n + 1
  · have hs : k ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left hle 2
    nlinarith
  · have hs : (n + 2) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith

lemma core_compl_infinite : {n : ℕ | n ∉ core}.Infinite := by
  let f : ℕ → ℕ := fun n => (n + 1) ^ 2 + 1
  have hf : Function.Injective f := by
    intro a b h
    dsimp [f] at h
    have hs : (a + 1) ^ 2 = (b + 1) ^ 2 := by omega
    have hab : a + 1 = b + 1 := square_injective hs
    omega
  have hrange : Set.range f ⊆ {n : ℕ | n ∉ core} := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact nonsquare n
  exact (Set.infinite_range_of_injective hf).mono hrange

noncomputable def coreEquiv : Core ≃ ℕ := by
  letI : Denumerable Core :=
    Classical.choice (Set.countable_infinite_iff_nonempty_denumerable.1
      ⟨Set.to_countable core, core_infinite⟩)
  exact Denumerable.eqv Core

noncomputable def outsideEquiv : Outside ≃ ℕ := by
  letI : Denumerable Outside :=
    Classical.choice (Set.countable_infinite_iff_nonempty_denumerable.1
      ⟨Set.to_countable {n : ℕ | n ∉ core}, core_compl_infinite⟩)
  exact Denumerable.eqv Outside

noncomputable def input : ℕ → ℕ := by
  classical
  exact fun t =>
    if ht : t ∈ core then
      ((outsideEquiv.symm (coreEquiv ⟨t, ht⟩)) : ℕ)
    else
      ((coreEquiv.symm (outsideEquiv ⟨t, ht⟩)) : ℕ)

lemma input_mem_iff (t : ℕ) : input t ∈ core ↔ t ∉ core := by
  classical
  unfold input
  split_ifs with ht
  · exact ⟨fun h => False.elim ((outsideEquiv.symm (coreEquiv ⟨t, ht⟩)).property h),
      fun h => False.elim (h ht)⟩
  · exact ⟨fun _ => ht, fun _ => (coreEquiv.symm (outsideEquiv ⟨t, ht⟩)).property⟩

lemma input_injective : Function.Injective input := by
  classical
  intro a b hab
  by_cases ha : a ∈ core <;> by_cases hb : b ∈ core
  · simp only [input, ha, hb, ↓reduceDIte] at hab
    have hsub : outsideEquiv.symm (coreEquiv ⟨a, ha⟩) =
        outsideEquiv.symm (coreEquiv ⟨b, hb⟩) := Subtype.ext hab
    have h1 := outsideEquiv.symm.injective hsub
    have h2 := coreEquiv.injective h1
    exact congrArg Subtype.val h2
  · have hca : input a ∉ core := (input_mem_iff a).not.mpr (not_not.mpr ha)
    have hcb : input b ∈ core := (input_mem_iff b).mpr hb
    exact False.elim (hca (hab ▸ hcb))
  · have hca : input a ∈ core := (input_mem_iff a).mpr ha
    have hcb : input b ∉ core := (input_mem_iff b).not.mpr (not_not.mpr hb)
    exact False.elim (hcb (hab ▸ hca))
  · simp only [input, ha, hb, ↓reduceDIte] at hab
    have hsub : coreEquiv.symm (outsideEquiv ⟨a, ha⟩) =
        coreEquiv.symm (outsideEquiv ⟨b, hb⟩) := Subtype.ext hab
    have h1 := coreEquiv.symm.injective hsub
    have h2 := outsideEquiv.injective h1
    exact congrArg Subtype.val h2

lemma input_surjective : Function.Surjective input := by
  classical
  intro x
  by_cases hx : x ∈ core
  · let tsub : Outside := outsideEquiv.symm (coreEquiv ⟨x, hx⟩)
    refine ⟨tsub, ?_⟩
    have ht : (tsub : ℕ) ∉ core := tsub.property
    simp only [input, ht, ↓reduceDIte]
    have hout : (⟨(tsub : ℕ), ht⟩ : Outside) = tsub := Subtype.ext rfl
    rw [hout]
    exact congrArg Subtype.val (show coreEquiv.symm (outsideEquiv tsub) = ⟨x, hx⟩ from by simp [tsub])
  · let tsub : Core := coreEquiv.symm (outsideEquiv ⟨x, hx⟩)
    refine ⟨tsub, ?_⟩
    have ht : (tsub : ℕ) ∈ core := tsub.property
    simp only [input, ht, ↓reduceDIte]
    have hcore : (⟨(tsub : ℕ), ht⟩ : Core) = tsub := Subtype.ext rfl
    rw [hcore]
    exact congrArg Subtype.val (show outsideEquiv.symm (coreEquiv tsub) = ⟨x, hx⟩ from by simp [tsub])

open GenLimit.PatientScope

lemma mem_prefixFinset {S : Set ℕ} {n x : ℕ} :
    x ∈ prefixFinset S n ↔ x < n ∧ x ∈ S := by
  classical
  simp [prefixFinset]

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n := by
  classical
  unfold prefixCount prefixFinset
  exact Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨hx.1, hAB hx.2⟩)

lemma prefixCount_univ (n : ℕ) : prefixCount Set.univ n = n := by
  classical
  simp [prefixCount, prefixFinset]

lemma prefixCount_inter_le_right (A K : Set ℕ) (n : ℕ) :
    prefixCount (A ∩ K) n ≤ prefixCount K n :=
  prefixCount_mono Set.inter_subset_right n

lemma core_prefixCount_le (n : ℕ) : prefixCount core n ≤ n.sqrt + 1 := by
  classical
  let f : ℕ → ℕ := fun k => k ^ 2
  have hsub : prefixFinset core n ⊆ (Finset.range (n.sqrt + 1)).image f := by
    intro x hx
    rw [mem_prefixFinset] at hx
    rcases hx.2 with ⟨k, rfl⟩
    apply Finset.mem_image.2
    refine ⟨k, Finset.mem_range.2 ?_, rfl⟩
    exact Nat.lt_succ_iff.mpr ((Nat.le_sqrt').mpr (Nat.le_of_lt hx.1))
  calc
    prefixCount core n = (prefixFinset core n).card := rfl
    _ ≤ ((Finset.range (n.sqrt + 1)).image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (n.sqrt + 1)).card := Finset.card_image_le
    _ = n.sqrt + 1 := by simp

lemma tendsto_real_sqrt_nat_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨m : ℕ, hm : b ≤ m⟩ := exists_nat_ge b
  refine eventually_atTop.2 ⟨m ^ 2, ?_⟩
  intro n hn
  calc
    b ≤ (m : ℝ) := hm
    _ = Real.sqrt ((m ^ 2 : ℕ) : ℝ) := by simp
    _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn)

lemma tendsto_sqrt_add_one_div :
    Tendsto (fun n : ℕ => ((n.sqrt + 1 : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  have hsqrtInv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_real_sqrt_nat_atTop
  have hreal : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / n) atTop (𝓝 0) := by
    apply hsqrtInv.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_div_self.symm
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1)
  have hsum : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / n + 1 / n) atTop (𝓝 0) := by
    simpa using hreal.add hone
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (by positivity) (Nat.cast_nonneg n)) ?_
      hsum
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Nat.cast_add, Nat.cast_one, add_div]
  gcongr
  exact Real.nat_sqrt_le_real_sqrt

lemma noiseCount_le_core (K : Set ℕ) (hcore : core ⊆ K) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input K n ≤ prefixCount core n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount prefixCount prefixFinset
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  refine ⟨ht.1, ?_⟩
  have hnotcore : input t ∉ core := fun h => ht.2 (hcore h)
  have : t ∈ core := by
    simpa using (not_congr (input_mem_iff t)).mp hnotcore
  exact this

lemma vanishingNoise_of_core_subset (K : Set ℕ) (hcore : core ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise input K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  refine squeeze_zero'
    (f := GenLimit.InfiniteContamination.empiricalNoiseRate input K)
    (g := fun n : ℕ => ((n.sqrt + 1 : ℕ) : ℝ) / n) ?_ ?_ tendsto_sqrt_add_one_div
  · exact Eventually.of_forall fun n => by
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split_ifs
      · exact le_rfl
      · positivity
  · exact Eventually.of_forall fun n => by
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split_ifs with hn
      · simp [hn]
      · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        exact_mod_cast (noiseCount_le_core K hcore n).trans (core_prefixCount_le n)

lemma legal_of_core_subset (K : Set ℕ) (hKinf : K.Infinite) (hcore : core ⊆ K) :
    Legal input K := by
  refine ⟨hKinf, input_injective, ?_, vanishingNoise_of_core_subset K hcore⟩
  intro x hx
  exact input_surjective x

lemma prefixRatio_le_one (A K : Set ℕ) (n : ℕ) :
    (prefixCount (A ∩ K) n : ℝ) / prefixCount K n ≤ 1 := by
  by_cases hzero : prefixCount K n = 0
  · simp [hzero]
  · rw [div_le_one (by positivity)]
    exact_mod_cast prefixCount_inter_le_right A K n

lemma relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ relativeUpperDensity A K := by
  unfold relativeUpperDensity
  let seq : ℕ → ℝ := fun n => (prefixCount (A ∩ K) n : ℝ) / prefixCount K n
  have hnonneg : ∀ n, 0 ≤ seq n := fun n => by dsimp [seq]; positivity
  have hle : ∀ n, seq n ≤ 1 := fun n => by
    dsimp [seq]
    exact prefixRatio_le_one A K n
  have hb : atTop.IsBoundedUnder (· ≤ ·) seq := isBoundedUnder_of_eventually_le (Eventually.of_forall hle)
  rw [← limsup_const (f := atTop (α := ℕ)) (0 : ℝ)]
  exact limsup_le_limsup (Eventually.of_forall hnonneg)
    (isCoboundedUnder_le_of_le atTop fun _ => le_rfl) hb

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    relativeUpperDensity A K ≤ 1 := by
  unfold relativeUpperDensity
  let seq : ℕ → ℝ := fun n => (prefixCount (A ∩ K) n : ℝ) / prefixCount K n
  have hnonneg : ∀ n, 0 ≤ seq n := fun n => by dsimp [seq]; positivity
  have hle : ∀ n, seq n ≤ 1 := fun n => by
    dsimp [seq]
    exact prefixRatio_le_one A K n
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hnonneg) (Eventually.of_forall hle)

lemma relativeUpperDensity_univ_eq (A : Set ℕ) :
    relativeUpperDensity A Set.univ =
      limsup (fun n : ℕ => (prefixCount A n : ℝ) / n) atTop := by
  unfold relativeUpperDensity
  apply limsup_congr
  exact Eventually.of_forall fun n => by
    rw [Set.inter_univ, prefixCount_univ]

lemma prefixCount_subset_core_union_finset (A : Set ℕ) (F : Finset ℕ)
    (hA : A ⊆ core ∪ (F : Set ℕ)) (n : ℕ) :
    prefixCount A n ≤ prefixCount core n + F.card := by
  classical
  unfold prefixCount
  calc
    (prefixFinset A n).card ≤ ((prefixFinset core n) ∪ F).card := by
      apply Finset.card_le_card
      intro x hx
      rw [mem_prefixFinset] at hx
      rcases hA hx.2 with hcore | hF
      · exact Finset.mem_union_left _ ((mem_prefixFinset).2 ⟨hx.1, hcore⟩)
      · exact Finset.mem_union_right _ hF
    _ ≤ (prefixFinset core n).card + F.card := Finset.card_union_le _ _

lemma tendsto_sqrt_add_const_div (c : ℕ) :
    Tendsto (fun n : ℕ => ((n.sqrt + 1 + c : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ => (c : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have hsum : Tendsto (fun n : ℕ => ((n.sqrt + 1 : ℕ) : ℝ) / n + (c : ℝ) / n) atTop (𝓝 0) := by
    simpa using tendsto_sqrt_add_one_div.add hc
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  push_cast
  ring

lemma relativeUpperDensity_univ_zero_of_subset_core_union_finset
    (A : Set ℕ) (F : Finset ℕ) (hA : A ⊆ core ∪ (F : Set ℕ)) :
    relativeUpperDensity A Set.univ = 0 := by
  rw [relativeUpperDensity_univ_eq]
  apply Filter.Tendsto.limsup_eq
  refine squeeze_zero'
    (f := fun n : ℕ => (prefixCount A n : ℝ) / n)
    (g := fun n : ℕ => ((n.sqrt + 1 + F.card : ℕ) : ℝ) / n) ?_ ?_
      (tendsto_sqrt_add_const_div F.card)
  · exact Eventually.of_forall fun n => by positivity
  · exact Eventually.of_forall fun n => by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast (prefixCount_subset_core_union_finset A F hA n).trans
        (Nat.add_le_add_right (core_prefixCount_le n) F.card)

lemma generatorFirst_subset_range (adversary output : ℕ → ℕ) :
    GenLimit.GeneratorFirst adversary output ⊆ Set.range output := by
  intro x hx
  rcases hx with ⟨t, ht, _⟩
  exact ⟨t, ht⟩

lemma output_range_subset_core_union_finset_of_novel
    (output : ℕ → ℕ) (h : GenLimit.NovelGeneratesInLimit input output core) :
    ∃ F : Finset ℕ, Set.range output ⊆ core ∪ (F : Set ℕ) := by
  classical
  rcases h with ⟨T, hT⟩
  refine ⟨(Finset.range T).image output, ?_⟩
  intro x hx
  rcases hx with ⟨t, rfl⟩
  by_cases ht : T ≤ t
  · exact Or.inl (hT t ht).1
  · exact Or.inr (Finset.mem_image.2 ⟨t, Finset.mem_range.2 (by omega), rfl⟩)

lemma generatorFirst_univ_density_zero_of_novel
    (output : ℕ → ℕ) (h : GenLimit.NovelGeneratesInLimit input output core) :
    relativeUpperDensity (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  rcases output_range_subset_core_union_finset_of_novel output h with ⟨F, hF⟩
  exact relativeUpperDensity_univ_zero_of_subset_core_union_finset _ F
    (generatorFirst_subset_range input output |>.trans hF)

lemma expected_univ_zero_of_eventually_core
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (output : Ω → Stream)
    (h : EventuallyFreshValid μ core input output) :
    expectedUpperDensity μ Set.univ input output = 0 := by
  unfold expectedUpperDensity
  rw [MeasureTheory.integral_congr_ae]
  · exact MeasureTheory.integral_zero Ω ℝ
  · filter_upwards [h] with ω hω
    exact generatorFirst_univ_density_zero_of_novel (output ω) hω

lemma expected_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Set ℕ) (output : Ω → Stream)
    (hInt : DensityIntegrable μ K input output) :
    expectedUpperDensity μ K input output ≤ 1 := by
  unfold DensityIntegrable at hInt
  unfold expectedUpperDensity
  have hle := MeasureTheory.integral_mono_ae hInt (MeasureTheory.integrable_const 1)
    (ae_of_all _ fun ω => relativeUpperDensity_le_one
      (GenLimit.GeneratorFirst input (output ω)) K)
  simpa using hle

lemma pairObstruction_core_univ : PairObstruction core Set.univ input := by
  intro Ω _ μ _ gen output _ _ hIntCore hIntUniv hCore hUniv
  have hzero : expectedUpperDensity μ Set.univ input output = 0 :=
    expected_univ_zero_of_eventually_core μ output hCore
  have hle : expectedUpperDensity μ core input output ≤ 1 :=
    expected_le_one μ core output hIntCore
  constructor
  · linarith
  · intro hboth
    rcases hboth with ⟨_, huniv⟩
    rw [hzero] at huniv
    norm_num at huniv

open scoped BigOperators

def freshBase (stream : Stream) (t : ℕ) : ℕ :=
  t + 1 + ∑ i ∈ Finset.range (t + 1), stream i

def freshOutput (stream : Stream) (t : ℕ) : ℕ := (freshBase stream t) ^ 2

def freshGenerator : OnlineGenerator := fun t inputHistory _ =>
  (t + 1 + ∑ i : Fin (t + 1), inputHistory i) ^ 2

lemma freshOutput_follows (stream : Stream) :
    Follows freshGenerator stream (freshOutput stream) := by
  intro t
  simp only [freshOutput, freshGenerator, freshBase]
  rw [Fin.sum_univ_eq_sum_range]

lemma sum_prefix_mono (stream : Stream) {s t : ℕ} (hst : s ≤ t) :
    (∑ i ∈ Finset.range (s + 1), stream i) ≤
      ∑ i ∈ Finset.range (t + 1), stream i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hst 1)
  · intro i _ _
    exact Nat.zero_le _

lemma freshBase_lt (stream : Stream) {s t : ℕ} (hst : s < t) :
    freshBase stream s < freshBase stream t := by
  unfold freshBase
  have hsum := sum_prefix_mono stream (Nat.le_of_lt hst)
  omega

lemma input_lt_freshOutput (stream : Stream) {s t : ℕ} (hst : s < t + 1) :
    stream s < freshOutput stream t := by
  have hmem : s ∈ Finset.range (t + 1) := Finset.mem_range.2 hst
  have hterm : stream s ≤ ∑ i ∈ Finset.range (t + 1), stream i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  have hbase : stream s < freshBase stream t := by
    unfold freshBase
    omega
  have hbasepos : 1 ≤ freshBase stream t := by
    unfold freshBase
    omega
  unfold freshOutput
  have hsq : freshBase stream t ≤ freshBase stream t ^ 2 := by nlinarith
  omega

lemma freshOutput_novel_core (stream : Stream) :
    GenLimit.NovelGeneratesInLimit stream (freshOutput stream) core := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨⟨freshBase stream t, rfl⟩, ?_, ?_⟩
  · intro hmem
    rcases Finset.mem_image.1 hmem with ⟨s, hs, heq⟩
    have hlt : stream s < freshOutput stream t := input_lt_freshOutput stream (Finset.mem_range.1 hs)
    omega
  · intro s hst heq
    have hb := freshBase_lt stream hst
    unfold freshOutput at heq
    exact (ne_of_lt hb) (square_injective heq)

lemma globallyFeasible_of_core_subset {r : ℕ} (family : Fin r → Language)
    (hcore : ∀ j, core ⊆ family j) : GloballyFeasible family := by
  refine ⟨freshGenerator, ?_⟩
  intro stream hlegal
  refine ⟨freshOutput stream, freshOutput_follows stream, ?_⟩
  intro j
  rcases freshOutput_novel_core stream with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  rcases hT t ht with ⟨hmem, hfresh, hrep⟩
  exact ⟨hcore j hmem, hfresh, hrep⟩

noncomputable def outsideVal (n : ℕ) : ℕ := (outsideEquiv.symm n : Outside).1

lemma outsideVal_not_core (n : ℕ) : outsideVal n ∉ core :=
  (outsideEquiv.symm n : Outside).2

lemma outsideVal_injective : Function.Injective outsideVal := by
  intro a b hab
  have hsub : outsideEquiv.symm a = outsideEquiv.symm b := Subtype.ext hab
  exact outsideEquiv.symm.injective hsub

noncomputable def extras (n : ℕ) : Finset ℕ :=
  (Finset.range n).image outsideVal

lemma outsideVal_mem_extras {i j : ℕ} (hij : i < j) : outsideVal i ∈ extras j := by
  classical
  exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hij, rfl⟩

lemma outsideVal_not_mem_extras (i : ℕ) : outsideVal i ∉ extras i := by
  classical
  intro h
  rcases Finset.mem_image.1 h with ⟨k, hk, heq⟩
  have hki : k = i := outsideVal_injective heq
  exact (Nat.ne_of_lt (Finset.mem_range.1 hk)) hki

lemma extras_mono {i j : ℕ} (hij : i ≤ j) : extras i ⊆ extras j := by
  classical
  intro x hx
  rcases Finset.mem_image.1 hx with ⟨k, hk, rfl⟩
  exact outsideVal_mem_extras (lt_of_lt_of_le (Finset.mem_range.1 hk) hij)

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if j.1 + 1 = r then Set.univ else core ∪ (extras j.1 : Set ℕ)

lemma nestedFamily_core_subset (r : ℕ) (j : Fin r) : core ⊆ nestedFamily r j := by
  intro x hx
  unfold nestedFamily
  split_ifs
  · trivial
  · exact Or.inl hx

lemma nestedFamily_infinite (r : ℕ) (j : Fin r) : (nestedFamily r j).Infinite :=
  core_infinite.mono (nestedFamily_core_subset r j)

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = core := by
  classical
  simp [nestedFamily, extras]
  omega

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [nestedFamily]
  omega

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) : StrictlyNested (nestedFamily r) := by
  classical
  intro i j hij
  have hi : i.1 + 1 ≠ r := by omega
  have hsubset : nestedFamily r i ⊆ nestedFamily r j := by
    unfold nestedFamily
    simp only [hi, ↓reduceIte]
    split_ifs with hj
    · exact Set.subset_univ _
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (extras_mono (Nat.le_of_lt hij) hx)
  refine ⟨hsubset, ?_⟩
  intro heq
  have hnoti : outsideVal i.1 ∉ nestedFamily r i := by
    simp only [nestedFamily, hi, ↓reduceIte, Set.mem_union, Set.mem_setOf_eq]
    exact fun h => h.elim (outsideVal_not_core i.1) (outsideVal_not_mem_extras i.1)
  have hmemj : outsideVal i.1 ∈ nestedFamily r j := by
    unfold nestedFamily
    split_ifs
    · trivial
    · exact Or.inr (outsideVal_mem_extras hij)
  exact hnoti (heq hmemj)

lemma nestedFamily_legal (r : ℕ) (j : Fin r) : Legal input (nestedFamily r j) :=
  legal_of_core_subset _ (nestedFamily_infinite r j) (nestedFamily_core_subset r j)

lemma manyTargetObstruction_nested {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetObstruction (nestedFamily r) input := by
  intro Ω _ μ _ gen output _ _ hInt hValid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hcore : EventuallyFreshValid μ core input output := by
    have h := hValid first
    simpa [first, nestedFamily_zero hr] using h
  have hzero : expectedUpperDensity μ Set.univ input output = 0 :=
    expected_univ_zero_of_eventually_core μ output hcore
  refine ⟨last, ?_⟩
  simpa [last, nestedFamily_last hr] using hzero

lemma manyTargetWitness_nested {r : ℕ} (hr : 2 ≤ r) :
    ManyTargetWitness (nestedFamily r) input := by
  refine ⟨nestedFamily_strict hr, nestedFamily_legal r,
    globallyFeasible_of_core_subset (nestedFamily r) (nestedFamily_core_subset r),
    manyTargetObstruction_nested hr⟩

lemma core_ssubset_univ : core ⊂ Set.univ := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  exact nonsquare 0 (h (Set.mem_univ _))

lemma mainClaim : MainClaim := by
  constructor
  · refine ⟨core, Set.univ, input, core_ssubset_univ, ?_, ?_, pairObstruction_core_univ⟩
    · exact legal_of_core_subset core core_infinite (Set.Subset.rfl)
    · exact legal_of_core_subset Set.univ Set.infinite_univ (Set.subset_univ _)
  · intro r hr
    exact ⟨nestedFamily r, input, manyTargetWitness_nested hr⟩

end

end Case024Helpers
