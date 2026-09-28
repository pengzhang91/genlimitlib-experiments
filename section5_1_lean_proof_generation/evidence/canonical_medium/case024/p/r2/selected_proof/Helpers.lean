import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter MeasureTheory
open scoped Topology

namespace Case024

noncomputable def mergeEnum (P K : Set ℕ) : ℕ → ℕ := by
  classical
  exact fun t =>
    if t ∈ P then Nat.nth (fun x => x ∉ K) (Nat.count (fun x => x ∈ P) t)
    else Nat.nth (fun x => x ∈ K) (Nat.count (fun x => x ∉ P) t)

lemma mergeEnum_mem_iff {P K : Set ℕ} (hK : K.Infinite) (hKc : Kᶜ.Infinite)
    (t : ℕ) : mergeEnum P K t ∈ K ↔ t ∉ P := by
  classical
  unfold mergeEnum
  split_ifs with ht
  · have hm := Nat.nth_mem_of_infinite hKc (Nat.count (fun x => x ∈ P) t)
    constructor
    · intro h; exact False.elim (hm h)
    · intro h; exact False.elim (h ht)
  · have hm := Nat.nth_mem_of_infinite hK (Nat.count (fun x => x ∉ P) t)
    constructor
    · intro _; exact ht
    · intro _; exact hm

lemma mergeEnum_injective {P K : Set ℕ} (hP : P.Infinite) (hPc : Pᶜ.Infinite)
    (hK : K.Infinite) (hKc : Kᶜ.Infinite) : Function.Injective (mergeEnum P K) := by
  classical
  intro a b hab
  by_cases ha : a ∈ P <;> by_cases hb : b ∈ P
  · unfold mergeEnum at hab
    simp only [ha, hb, if_pos] at hab
    have hc := (Nat.nth_injective hKc) hab
    exact Nat.count_injective ha hb hc
  · have hma : mergeEnum P K a ∉ K := fun h => ((mergeEnum_mem_iff hK hKc a).1 h) ha
    have hmb : mergeEnum P K b ∈ K := (mergeEnum_mem_iff hK hKc b).2 hb
    exact False.elim (hma (hab ▸ hmb))
  · have hmb : mergeEnum P K b ∉ K := fun h => ((mergeEnum_mem_iff hK hKc b).1 h) hb
    have hma : mergeEnum P K a ∈ K := (mergeEnum_mem_iff hK hKc a).2 ha
    exact False.elim (hmb (hab ▸ hma))
  · unfold mergeEnum at hab
    simp only [ha, hb, if_neg] at hab
    have hc := (Nat.nth_injective hK) hab
    exact Nat.count_injective ha hb hc

lemma mergeEnum_range {P K : Set ℕ} (hP : P.Infinite) (hPc : Pᶜ.Infinite)
    (hK : K.Infinite) (hKc : Kᶜ.Infinite) : Set.range (mergeEnum P K) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ K
  · obtain ⟨n, hn⟩ := Nat.subset_range_nth hx
    let t := Nat.nth (fun y => y ∉ P) n
    have ht : t ∉ P := Nat.nth_mem_of_infinite hPc n
    refine ⟨t, ?_⟩
    have hc : Nat.count (fun y => y ∉ P) t = n := Nat.count_nth_of_infinite hPc n
    simp only [mergeEnum, ht, if_false, hc]
    simpa only using hn
  · obtain ⟨n, hn⟩ := Nat.subset_range_nth (p := fun y => y ∉ K) hx
    let t := Nat.nth (fun y => y ∈ P) n
    have ht : t ∈ P := Nat.nth_mem_of_infinite hP n
    refine ⟨t, ?_⟩
    have hc : Nat.count (fun y => y ∈ P) t = n := Nat.count_nth_of_infinite hP n
    simp [mergeEnum, ht, hc, hn]


end Case024

namespace Case024

def Pow2 : Set ℕ := {n | ∃ k ≤ n, n = 2 ^ k}

noncomputable instance pow2DecidablePred : DecidablePred (fun x => x ∈ Pow2) := Classical.decPred _

lemma le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

lemma pow2_infinite : Pow2.Infinite := by
  apply (Set.infinite_range_of_injective (Nat.pow_right_injective (by omega : 2 ≤ 2))).mono
  rintro x ⟨k, rfl⟩
  exact ⟨k, le_two_pow k, rfl⟩

lemma odd_ge_three_not_pow2 (n : ℕ) : 2 * n + 3 ∉ Pow2 := by
  rintro ⟨k, _, hk⟩
  cases k with
  | zero => simp at hk
  | succ k =>
      rw [pow_succ] at hk
      omega

lemma pow2_compl_infinite : Pow2ᶜ.Infinite := by
  apply (Set.infinite_range_of_injective (by intro a b h; dsimp at h; omega : Function.Injective (fun n : ℕ => 2 * n + 3))).mono
  rintro x ⟨n, rfl⟩
  exact odd_ge_three_not_pow2 n

lemma pow2_count_le_log_add_one (n : ℕ) :
    Nat.count (fun x => x ∈ Pow2) n ≤ Nat.log 2 n + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let S := (Finset.range n).filter (fun x => x ∈ Pow2)
  let exponent (x : S) : ℕ := Nat.find (Finset.mem_filter.mp x.2).2
  have exponent_spec (x : S) : x.1 = 2 ^ exponent x :=
    (Nat.find_spec (Finset.mem_filter.mp x.2).2).2
  let f : S → Fin (Nat.log 2 n + 1) := fun x => by
    refine ⟨exponent x, Nat.lt_succ_iff.2 ?_⟩
    have hxn : x.1 < n := Finset.mem_range.mp (Finset.mem_filter.mp x.2).1
    have hn : n ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hxn)
    apply (Nat.pow_le_iff_le_log (by omega) hn).1
    rw [← exponent_spec x]
    exact Nat.le_of_lt hxn
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have he : exponent a = exponent b := Fin.ext_iff.mp hab
    rw [exponent_spec a, exponent_spec b, he]
  change S.card ≤ _
  rw [← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective f hf


end Case024

namespace Case024

lemma tendsto_pow2_count_ratio :
    Tendsto (fun n : ℕ => (Nat.count (fun x => x ∈ Pow2) n : ℝ) / n) atTop (nhds 0) := by
  apply squeeze_zero' (g := fun n : ℕ => ((Nat.log 2 n : ℕ) + 1 : ℝ) / n)
  · exact Filter.Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ne_atTop 0] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast pow2_count_le_log_add_one n
  · have hlog : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    apply squeeze_zero' (g := fun n : ℕ => (Real.logb 2 n + 1) / n)
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      apply div_nonneg _ (Nat.cast_nonneg _)
      have hnonneg : (0 : ℝ) ≤ Real.logb 2 n := le_trans (Nat.cast_nonneg _) (Real.natLog_le_logb n 2)
      linarith
    · filter_upwards [eventually_ne_atTop 0] with n hn
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      norm_num [Nat.cast_add]
      exact Real.natLog_le_logb n 2
    · simpa [add_div] using hlog.add hone

noncomputable def input : Stage3Case024.Stream := mergeEnum Pow2 Pow2

lemma input_injective : Function.Injective input :=
  mergeEnum_injective pow2_infinite pow2_compl_infinite pow2_infinite pow2_compl_infinite

lemma input_range : Set.range input = Set.univ :=
  mergeEnum_range pow2_infinite pow2_compl_infinite pow2_infinite pow2_compl_infinite

lemma input_not_mem_iff (t : ℕ) : input t ∉ Pow2 ↔ t ∈ Pow2 := by
  unfold input
  rw [not_congr (mergeEnum_mem_iff pow2_infinite pow2_compl_infinite t)]
  simp

lemma noiseCount_input_pow2 (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input Pow2 n = Nat.count (fun t => t ∈ Pow2) n := by
  classical
  simp only [GenLimit.InfiniteContamination.noiseCount, Nat.count_eq_card_filter_range]
  congr 1
  ext t
  simp [input_not_mem_iff]

lemma legal_pow2 : Stage3Case024.Legal input Pow2 := by
  refine ⟨pow2_infinite, input_injective, ?_, ?_⟩
  · intro x hx
    rw [input_range]
    trivial
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply tendsto_pow2_count_ratio.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [GenLimit.InfiniteContamination.empiricalNoiseRate, hn, noiseCount_input_pow2]

lemma legal_univ : Stage3Case024.Legal input Set.univ := by
  refine ⟨Set.infinite_univ, input_injective, ?_, ?_⟩
  · intro x hx
    rw [input_range]
    trivial
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)).congr'
    filter_upwards with n
    simp [GenLimit.InfiniteContamination.empiricalNoiseRate,
      GenLimit.InfiniteContamination.noiseCount]

end Case024

namespace Case024

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount Set.univ n = n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_pow2 (n : ℕ) :
    GenLimit.PatientScope.prefixCount Pow2 n = Nat.count (fun x => x ∈ Pow2) n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range]

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
      (isCoboundedUnder_le_of_le atTop
        (fun n : ℕ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) :
          ∀ n : ℕ, (0 : ℝ) ≤
            (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
              GenLimit.PatientScope.prefixCount K n))
  filter_upwards with n
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono (Set.inter_subset_right : A ∩ K ⊆ K) n

lemma generatorFirst_subset_output_range (stream output : ℕ → ℕ) :
    GenLimit.GeneratorFirst stream output ⊆ Set.range output := by
  rintro x ⟨t, ht, _⟩
  exact ⟨t, ht⟩

lemma prefixCount_le_pow2_add_of_eventual
    (stream output : ℕ → ℕ) (T : ℕ)
    (hvalid : ∀ t, T ≤ t → output t ∈ Pow2) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst stream output) n ≤
      GenLimit.PatientScope.prefixCount Pow2 n + T := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let early : Finset ℕ := (Finset.range T).image output
  have hsubset :
      (Finset.range n).filter (fun x => x ∈ GenLimit.GeneratorFirst stream output) ⊆
        (Finset.range n).filter (fun x => x ∈ Pow2) ∪ early := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    by_cases hp : x ∈ Pow2
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hx.1, hp⟩)
    · obtain ⟨t, rfl⟩ := generatorFirst_subset_output_range stream output hx.2
      have ht : t < T := by
        by_contra hnot
        exact hp (hvalid t (Nat.le_of_not_gt hnot))
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨t, Finset.mem_range.2 ht, rfl⟩)
  calc
    ((Finset.range n).filter (fun x => x ∈ GenLimit.GeneratorFirst stream output)).card
        ≤ ((Finset.range n).filter (fun x => x ∈ Pow2) ∪ early).card :=
          Finset.card_le_card hsubset
    _ ≤ ((Finset.range n).filter (fun x => x ∈ Pow2)).card + early.card :=
          Finset.card_union_le _ _
    _ ≤ ((Finset.range n).filter (fun x => x ∈ Pow2)).card + T := by
          gcongr
          show ((Finset.range T).image output).card ≤ T
          simpa using (Finset.card_image_le : ((Finset.range T).image output).card ≤ (Finset.range T).card)

lemma generatorFirst_univ_density_zero
    (stream output : ℕ → ℕ)
    (hgen : GenLimit.NovelGeneratesInLimit stream output Pow2) :
    Stage3Case024.relativeUpperDensity (GenLimit.GeneratorFirst stream output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := hgen
  have hratio : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst stream output ∩ Set.univ) n : ℝ) /
          GenLimit.PatientScope.prefixCount Set.univ n)
      atTop (nhds 0) := by
    apply squeeze_zero'
        (g := fun n : ℕ =>
          ((Nat.count (fun x => x ∈ Pow2) n : ℝ) + T) / n)
    · exact Filter.Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · filter_upwards [eventually_ne_atTop 0] with n hn
      rw [prefixCount_univ]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [Set.inter_univ]
      have hbound := prefixCount_le_pow2_add_of_eventual stream output T (fun t ht => (hT t ht).1) n
      rw [prefixCount_pow2] at hbound
      exact_mod_cast hbound
    · have hTzero : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat T
      simpa [add_div, prefixCount_pow2] using tendsto_pow2_count_ratio.add hTzero
  exact hratio.limsup_eq

end Case024

namespace Case024

lemma noiseCount_mono {K L : Set ℕ} (hKL : K ⊆ L) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount input L n ≤
      GenLimit.InfiniteContamination.noiseCount input K n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun h => ht.2 (hKL h)⟩

lemma legal_of_pow2_subset {K : Set ℕ} (hK : Pow2 ⊆ K) : Stage3Case024.Legal input K := by
  refine ⟨pow2_infinite.mono hK, input_injective, ?_, ?_⟩
  · intro x hx
    rw [input_range]
    trivial
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply squeeze_zero'
        (g := fun n : ℕ =>
          (GenLimit.InfiniteContamination.noiseCount input Pow2 n : ℝ) / n)
    · exact Filter.Eventually.of_forall (fun n => by
        simp [GenLimit.InfiniteContamination.empiricalNoiseRate]
        positivity)
    · filter_upwards with n
      by_cases hn : n = 0
      · simp [GenLimit.InfiniteContamination.empiricalNoiseRate, hn]
      · simp only [GenLimit.InfiniteContamination.empiricalNoiseRate, hn, if_false]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast noiseCount_mono hK n
    · have hp := legal_pow2.2.2.2
      apply hp.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      simp [GenLimit.InfiniteContamination.empiricalNoiseRate, hn]

lemma expected_univ_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (output : Ω → Stage3Case024.Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ Pow2 input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ)
        = ∫ _ : Ω, (0 : ℝ) ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hvalid] with ω hω
          exact generatorFirst_univ_density_zero input (output ω) hω
    _ = 0 := by simp

lemma expected_pow2_le_one {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (output : Ω → Stage3Case024.Stream)
    (hint : Stage3Case024.DensityIntegrable μ Pow2 input output) :
    Stage3Case024.expectedUpperDensity μ Pow2 input output ≤ 1 := by
  unfold Stage3Case024.expectedUpperDensity
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Pow2 ∂μ)
        ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
          apply MeasureTheory.integral_mono_ae hint hone
          exact Filter.Eventually.of_forall (fun ω =>
            relativeUpperDensity_le_one (GenLimit.GeneratorFirst input (output ω)) Pow2)
    _ = 1 := by simp

lemma pair_obstruction : Stage3Case024.PairObstruction Pow2 Set.univ input := by
  intro Ω _ μ _ gen output _ _ hint0 _ hvalid0 _
  have h0 := expected_pow2_le_one μ output hint0
  have h1 := expected_univ_zero μ output hvalid0
  constructor
  · rw [h1]
    linarith
  · intro h
    rw [h1] at h
    linarith


def addedOdds (i : ℕ) : Set ℕ := {x | ∃ k < i, x = 2 * k + 3}

def family (r : ℕ) (j : Fin r) : Set ℕ :=
  if j.1 + 1 = r then Set.univ else Pow2 ∪ addedOdds j.1

lemma addedOdds_mono {i j : ℕ} (hij : i ≤ j) : addedOdds i ⊆ addedOdds j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

lemma odd_marker_mem_addedOdds {i j : ℕ} (hij : i < j) : 2 * i + 3 ∈ addedOdds j :=
  ⟨i, hij, rfl⟩

lemma odd_marker_not_mem_addedOdds (i : ℕ) : 2 * i + 3 ∉ addedOdds i := by
  rintro ⟨k, hk, heq⟩
  omega

lemma pow2_subset_family {r : ℕ} (j : Fin r) : Pow2 ⊆ family r j := by
  intro x hx
  unfold family
  split_ifs
  · trivial
  · exact Set.mem_union_left _ hx

lemma family_zero {r : ℕ} (hr : 2 ≤ r) : family r ⟨0, by omega⟩ = Pow2 := by
  unfold family
  rw [if_neg (by change 1 ≠ r; omega)]
  ext x
  simp [addedOdds]

lemma family_last {r : ℕ} (hr : 2 ≤ r) : family r ⟨r - 1, by omega⟩ = Set.univ := by
  unfold family
  rw [if_pos (by change r - 1 + 1 = r; omega)]

lemma family_strictlyNested {r : ℕ} (hr : 2 ≤ r) : Stage3Case024.StrictlyNested (family r) := by
  intro i j hij
  have hjle : j.1 + 1 ≤ r := j.2
  have hnotlast : i.1 + 1 ≠ r := by omega
  constructor
  · intro x hx
    unfold family at hx ⊢
    simp only [hnotlast, if_false] at hx
    split_ifs with hjlast
    · trivial
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (addedOdds_mono (Nat.le_of_lt hij) hx)
  · intro hback
    have hmj : 2 * i.1 + 3 ∈ family r j := by
      unfold family
      split_ifs with hjlast
      · trivial
      · exact Set.mem_union_right _ (odd_marker_mem_addedOdds hij)
    have hmi := hback hmj
    unfold family at hmi
    simp only [hnotlast, if_false, Set.mem_union] at hmi
    exact hmi.elim (odd_ge_three_not_pow2 i.1) (odd_marker_not_mem_addedOdds i.1)

lemma family_legal {r : ℕ} (j : Fin r) : Stage3Case024.Legal input (family r j) :=
  legal_of_pow2_subset (pow2_subset_family j)

end Case024

namespace Case024

open scoped BigOperators

noncomputable def freshGen : Stage3Case024.OnlineGenerator := fun _ inp out =>
  2 ^ (1 + (∑ i, inp i) + ∑ i, out i)

noncomputable def runGenerator (gen : Stage3Case024.OnlineGenerator)
    (stream : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => Nat.strongRec (motive := fun _ => ℕ)
    (fun t ih => gen t (fun i => stream i) (fun i => ih i.1 i.2)) t

lemma runGenerator_eq (gen : Stage3Case024.OnlineGenerator)
    (stream : Stage3Case024.Stream) (t : ℕ) :
    runGenerator gen stream t =
      gen t (fun i => stream i) (fun i => runGenerator gen stream i) := by
  rw [runGenerator, Nat.strongRec_eq]
  rfl

lemma freshGen_mem_pow2 (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ) :
    freshGen t inp out ∈ Pow2 := by
  let e := 1 + (∑ i, inp i) + ∑ i, out i
  exact ⟨e, le_two_pow e, rfl⟩

lemma freshGen_gt_input (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ)
    (i : Fin (t + 1)) : inp i < freshGen t inp out := by
  have hsum : inp i ≤ ∑ j, inp j := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    simp
  have he : inp i < 1 + (∑ j, inp j) + ∑ j, out j := by omega
  have hp := le_two_pow (1 + (∑ j, inp j) + ∑ j, out j)
  unfold freshGen
  omega

lemma freshGen_gt_output (t : ℕ) (inp : Fin (t + 1) → ℕ) (out : Fin t → ℕ)
    (i : Fin t) : out i < freshGen t inp out := by
  have hsum : out i ≤ ∑ j, out j := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    simp
  have he : out i < 1 + (∑ j, inp j) + ∑ j, out j := by omega
  have hp := le_two_pow (1 + (∑ j, inp j) + ∑ j, out j)
  unfold freshGen
  omega

lemma run_follows (stream : Stage3Case024.Stream) :
    Stage3Case024.Follows freshGen stream (runGenerator freshGen stream) := by
  intro t
  exact runGenerator_eq freshGen stream t

lemma run_novel (stream : Stage3Case024.Stream) {K : Set ℕ} (hK : Pow2 ⊆ K) :
    GenLimit.NovelGeneratesInLimit stream (runGenerator freshGen stream) K := by
  refine ⟨0, fun t _ => ⟨?_, ?_, ?_⟩⟩
  · apply hK
    rw [runGenerator_eq]
    exact freshGen_mem_pow2 t _ _
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨i, hi, heq⟩ := hmem
    have hlt := freshGen_gt_input t (fun j : Fin (t + 1) => stream j)
      (fun j : Fin t => runGenerator freshGen stream j) ⟨i, hi⟩
    rw [← runGenerator_eq freshGen stream t, heq] at hlt
    exact (Nat.lt_irrefl _) hlt
  · intro s hs heq
    have hlt := freshGen_gt_output t (fun j : Fin (t + 1) => stream j)
      (fun j : Fin t => runGenerator freshGen stream j) ⟨s, hs⟩
    rw [← runGenerator_eq freshGen stream t, heq] at hlt
    exact (Nat.lt_irrefl _) hlt

lemma family_globallyFeasible {r : ℕ} : Stage3Case024.GloballyFeasible (family r) := by
  refine ⟨freshGen, fun stream _ => ⟨runGenerator freshGen stream, run_follows stream, ?_⟩⟩
  intro j
  exact run_novel stream (pow2_subset_family j)

lemma family_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (family r) input := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  rw [family_last hr]
  apply expected_univ_zero μ output
  have hf := hvalid first
  rwa [family_zero hr] at hf

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (family r) input := by
  exact ⟨family_strictlyNested hr, family_legal, family_globallyFeasible,
    family_manyTargetObstruction hr⟩

end Case024
