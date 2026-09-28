import Stage3Model
import Mathlib

open Filter MeasureTheory
open scoped Topology

namespace Case024Proof

noncomputable section

def square (n : ℕ) : Prop := ∃ k : ℕ, n = k * k

instance : DecidablePred square := Classical.decPred _

lemma square_infinite : Set.Infinite {n : ℕ | square n} := by
  have hi : Function.Injective (fun n : ℕ => n * n) := by
    intro a b h
    nlinarith
  have heq : {n : ℕ | square n} = Set.range (fun n : ℕ => n * n) := by
    ext n
    simp [square, eq_comm]
  rw [heq]
  exact Set.infinite_range_of_injective hi

lemma nonsquare_infinite : Set.Infinite {n : ℕ | ¬ square n} := by
  let f : ℕ → ℕ := fun k => (k + 1) * (k + 1) + (k + 1)
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    nlinarith
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro n ⟨k, rfl⟩ ⟨m, hm⟩
  let a := k + 1
  have hlo : a * a < a * a + a := by omega
  have hhi : a * a + a < (a + 1) * (a + 1) := by nlinarith
  have hm' : a * a + a = m * m := by simpa [a] using hm
  by_cases hma : m ≤ a
  · have hsq := Nat.mul_self_le_mul_self hma
    omega
  · have hsq := Nat.mul_self_le_mul_self (show a + 1 ≤ m by omega)
    omega

def swappedEnumeration (t : ℕ) : ℕ :=
  if square t then
    Nat.nth (fun n => ¬ square n) (Nat.count square t)
  else
    Nat.nth square (Nat.count (fun n => ¬ square n) t)

lemma swappedEnumeration_square_iff (t : ℕ) :
    square (swappedEnumeration t) ↔ ¬ square t := by
  unfold swappedEnumeration
  by_cases ht : square t
  · simp only [ht, if_pos, not_true_eq_false, iff_false]
    exact Nat.nth_mem_of_infinite nonsquare_infinite _
  · simp only [ht, if_neg, not_false_eq_true, iff_true]
    exact Nat.nth_mem_of_infinite square_infinite _

lemma swappedEnumeration_injective : Function.Injective swappedEnumeration := by
  intro a b hab
  by_cases ha : square a <;> by_cases hb : square b
  · have hc : Nat.count square a = Nat.count square b :=
      (Nat.nth_injective nonsquare_infinite) (by simpa [swappedEnumeration, ha, hb] using hab)
    calc
      a = Nat.nth square (Nat.count square a) := (Nat.nth_count ha).symm
      _ = Nat.nth square (Nat.count square b) := by rw [hc]
      _ = b := Nat.nth_count hb
  · have hs : square (swappedEnumeration b) := (swappedEnumeration_square_iff b).2 hb
    exact False.elim ((swappedEnumeration_square_iff a).1 (hab ▸ hs) ha)
  · have hs : square (swappedEnumeration a) := (swappedEnumeration_square_iff a).2 ha
    exact False.elim ((swappedEnumeration_square_iff b).1 (hab ▸ hs) hb)
  · have hc : Nat.count (fun n => ¬ square n) a =
        Nat.count (fun n => ¬ square n) b :=
      (Nat.nth_injective square_infinite) (by simpa [swappedEnumeration, ha, hb] using hab)
    calc
      a = Nat.nth (fun n => ¬ square n)
          (Nat.count (fun n => ¬ square n) a) := (Nat.nth_count ha).symm
      _ = Nat.nth (fun n => ¬ square n)
          (Nat.count (fun n => ¬ square n) b) := by rw [hc]
      _ = b := Nat.nth_count hb

lemma swappedEnumeration_surjective : Function.Surjective swappedEnumeration := by
  intro x
  by_cases hx : square x
  · let t := Nat.nth (fun n => ¬ square n) (Nat.count square x)
    have ht : ¬ square t := Nat.nth_mem_of_infinite nonsquare_infinite _
    refine ⟨t, ?_⟩
    simp [swappedEnumeration, t, ht, Nat.count_nth_of_infinite nonsquare_infinite,
      Nat.nth_count hx]
  · let t := Nat.nth square (Nat.count (fun n => ¬ square n) x)
    have ht : square t := Nat.nth_mem_of_infinite square_infinite _
    refine ⟨t, ?_⟩
    simp [swappedEnumeration, t, ht, Nat.count_nth_of_infinite square_infinite,
      Nat.nth_count (p := fun n => ¬ square n) hx]


lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  apply Finset.card_le_card
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma square_prefixCount_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount {x : ℕ | square x} n ≤ Nat.sqrt n + 1 := by
  classical
  let source := Finset.range (Nat.sqrt n + 1)
  let target := GenLimit.PatientScope.prefixFinset {x : ℕ | square x} n
  have hsub : target ⊆ source.image (fun k => k * k) := by
    intro x hx
    simp only [target, GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range, Set.mem_setOf_eq] at hx
    rcases hx.2 with ⟨k, rfl⟩
    have hk : k ≤ Nat.sqrt n := (Nat.le_sqrt).2 (Nat.le_of_lt hx.1)
    simp only [source, Finset.mem_image]
    exact ⟨k, by simp [source, Nat.lt_succ_iff.mpr hk], rfl⟩
  calc
    GenLimit.PatientScope.prefixCount {x : ℕ | square x} n = target.card := rfl
    _ ≤ (source.image (fun k => k * k)).card := Finset.card_le_card hsub
    _ ≤ source.card := Finset.card_image_le
    _ = Nat.sqrt n + 1 := by simp [source]

lemma tendsto_sqrt_add_one_div :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hmain : Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ) + 1 / (n : ℝ))
      atTop (𝓝 0) := by
    convert (Filter.Tendsto.const_div_atTop hsqrtTop 1).add
      (tendsto_const_div_atTop_nhds_zero_nat 1) using 1 <;> norm_num
  have hreal : Tendsto (fun n : ℕ =>
      (Real.sqrt (n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    apply hmain.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hs0 : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
    field_simp
    nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  refine squeeze_zero'
    (f := fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / (n : ℝ))
    (g := fun n : ℕ => (Real.sqrt (n : ℝ) + 1) / (n : ℝ)) ?_ ?_ hreal
  · exact Filter.Eventually.of_forall fun n => by positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hsle : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      simpa [pow_two] using (show ((Nat.sqrt n * Nat.sqrt n : ℕ) : ℝ) ≤ (n : ℝ) by
        exact_mod_cast Nat.sqrt_le n)
    norm_num
    gcongr

lemma square_density_zero :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount {x : ℕ | square x} n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity) ?_ tendsto_sqrt_add_one_div
  exact Filter.Eventually.of_forall fun n => by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast square_prefixCount_le n


abbrev Kcore : Set ℕ := {n : ℕ | square n}

lemma noiseCount_swapped (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount swappedEnumeration Kcore n =
      GenLimit.PatientScope.prefixCount Kcore n := by
  classical
  simp only [GenLimit.InfiniteContamination.noiseCount,
    GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  congr 1
  ext t
  simp [swappedEnumeration_square_iff]

lemma legal_core : Stage3Case024.Legal swappedEnumeration Kcore := by
  refine ⟨square_infinite, swappedEnumeration_injective, ?_, ?_⟩
  · intro x hx
    exact swappedEnumeration_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply square_density_zero.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp [GenLimit.InfiniteContamination.empiricalNoiseRate, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn),
      noiseCount_swapped]

lemma legal_superset (K : Set ℕ) (hcore : Kcore ⊆ K) (hinf : K.Infinite) :
    Stage3Case024.Legal swappedEnumeration K := by
  refine ⟨hinf, swappedEnumeration_injective, ?_, ?_⟩
  · intro x hx
    exact swappedEnumeration_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    have hzero : Tendsto (fun n : ℕ =>
        (GenLimit.InfiniteContamination.noiseCount swappedEnumeration K n : ℝ) / (n : ℝ))
        atTop (𝓝 0) := by
      refine squeeze_zero'
        (Filter.Eventually.of_forall fun n => by positivity) ?_ square_density_zero
      exact Filter.Eventually.of_forall fun n => by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (show GenLimit.InfiniteContamination.noiseCount swappedEnumeration K n ≤
            GenLimit.PatientScope.prefixCount Kcore n by
          classical
          simp only [GenLimit.InfiniteContamination.noiseCount,
            GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
          refine ⟨ht.1, ?_⟩
          by_contra hns
          exact ht.2 (hcore ((swappedEnumeration_square_iff t).2 hns)))
    apply hzero.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp [GenLimit.InfiniteContamination.empiricalNoiseRate, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)]

lemma prefixCount_union_finite_le (A : Set ℕ) (E : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ (E : Set ℕ)) n ≤
      GenLimit.PatientScope.prefixCount A n + E.card := by
  classical
  simp only [GenLimit.PatientScope.prefixCount]
  calc
    (GenLimit.PatientScope.prefixFinset (A ∪ (E : Set ℕ)) n).card ≤
        (GenLimit.PatientScope.prefixFinset A n ∪ E).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
            Finset.mem_range, Set.mem_union, Finset.mem_union, Finset.mem_coe] at hx ⊢
          rcases hx.2 with hxA | hxE
          · exact Or.inl ⟨hx.1, hxA⟩
          · exact Or.inr hxE
    _ ≤ (GenLimit.PatientScope.prefixFinset A n).card + E.card := Finset.card_union_le _ _

lemma density_zero_of_subset_core_finite {A : Set ℕ} {E : Finset ℕ}
    (hA : A ⊆ Kcore ∪ (E : Set ℕ)) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  have hratio : Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n : ℕ =>
        ((GenLimit.PatientScope.prefixCount Kcore n : ℝ) + E.card) / (n : ℝ))
        atTop (𝓝 0) := by
      convert square_density_zero.add (tendsto_const_div_atTop_nhds_zero_nat E.card) using 1
      · funext n
        ring
      · norm_num
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun n => by positivity) ?_ hupper
    exact Filter.Eventually.of_forall fun n => by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (le_trans (prefixCount_mono hA n)
        (prefixCount_union_finite_le Kcore E n))
  unfold Stage3Case024.relativeUpperDensity
  rw [show (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
        (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ)) =
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ)) by
        funext n
        simp [prefixCount_univ]]
  exact hratio.limsup_eq

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  refine Filter.limsup_le_of_le (u := fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) (a := 1) (hf := by
        apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
        exact (Filter.Eventually.of_forall fun n => by positivity).frequently) (h := ?_)
  exact Filter.Eventually.of_forall fun n => by
    have hc : GenLimit.PatientScope.prefixCount (A ∩ K) n ≤
        GenLimit.PatientScope.prefixCount K n := prefixCount_mono Set.inter_subset_right n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · have hnum : GenLimit.PatientScope.prefixCount (A ∩ K) n = 0 := by omega
      simp [hz, hnum]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      apply (div_le_one hpos).2
      exact_mod_cast hc

lemma generatorFirst_subset_core_finite {output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit swappedEnumeration output Kcore) :
    ∃ E : Finset ℕ, GenLimit.GeneratorFirst swappedEnumeration output ⊆
      Kcore ∪ (E : Set ℕ) := by
  rcases hvalid with ⟨T, hT⟩
  refine ⟨(Finset.range T).image output, ?_⟩
  intro z hz
  rcases hz with ⟨t, rfl, ht⟩
  by_cases hlt : t < T
  · exact Or.inr (by simp; exact ⟨t, hlt, rfl⟩)
  · exact Or.inl (hT t (by omega)).1

lemma expected_univ_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (output : Ω → Stage3Case024.Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ Kcore swappedEnumeration output) :
    Stage3Case024.expectedUpperDensity μ Set.univ swappedEnumeration output = 0 := by
  unfold Stage3Case024.EventuallyFreshValid at hvalid
  unfold Stage3Case024.expectedUpperDensity
  apply integral_eq_zero_of_ae
  filter_upwards [hvalid] with ω hω
  rcases generatorFirst_subset_core_finite hω with ⟨E, hE⟩
  exact density_zero_of_subset_core_finite hE

lemma expected_core_le_one {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (output : Ω → Stage3Case024.Stream)
    (hint : Stage3Case024.DensityIntegrable μ Kcore swappedEnumeration output) :
    Stage3Case024.expectedUpperDensity μ Kcore swappedEnumeration output ≤ 1 := by
  unfold Stage3Case024.DensityIntegrable at hint
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst swappedEnumeration (output ω)) Kcore ∂μ) ≤
        ∫ _ : Ω, (1 : ℝ) ∂μ := by
          apply integral_mono hint (integrable_const 1)
          intro ω
          exact relativeUpperDensity_le_one _ _
    _ = 1 := by simp

noncomputable def freshGenerator (K : Set ℕ) (hK : K.Infinite) :
    Stage3Case024.OnlineGenerator := fun t input output =>
  Classical.choose (hK.exists_notMem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image output)))

lemma freshGenerator_spec (K : Set ℕ) (hK : K.Infinite) (t : ℕ)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshGenerator K hK t input output ∈ K ∧
      (∀ s : Fin (t + 1), input s ≠ freshGenerator K hK t input output) ∧
      ∀ s : Fin t, output s ≠ freshGenerator K hK t input output := by
  classical
  unfold freshGenerator
  have h := Classical.choose_spec (hK.exists_notMem_finset
    ((Finset.univ.image input) ∪ (Finset.univ.image output)))
  refine ⟨h.1, ?_, ?_⟩
  · intro s heq
    apply h.2
    apply Finset.mem_union_left
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨s, heq⟩
  · intro s heq
    apply h.2
    apply Finset.mem_union_right
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨s, heq⟩

noncomputable def followFresh (K : Set ℕ) (hK : K.Infinite)
    (input : Stage3Case024.Stream) : Stage3Case024.Stream
  | t => freshGenerator K hK t (fun i => input i) (fun i => followFresh K hK input i)

lemma followFresh_follows (K : Set ℕ) (hK : K.Infinite)
    (input : Stage3Case024.Stream) :
    Stage3Case024.Follows (freshGenerator K hK) input (followFresh K hK input) := by
  intro t
  rw [followFresh]

lemma followFresh_valid (K : Set ℕ) (hK : K.Infinite)
    (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (followFresh K hK input) K := by
  refine ⟨0, fun t _ => ?_⟩
  rw [followFresh]
  have hs := freshGenerator_spec K hK t (fun i => input i)
    (fun i => followFresh K hK input i)
  refine ⟨hs.1, ?_, ?_⟩
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
    rcases hmem with ⟨s, hst, heq⟩
    exact hs.2.1 ⟨s, by omega⟩ heq
  · intro s hst
    exact hs.2.2 ⟨s, hst⟩


lemma novel_mono {input output : Stage3Case024.Stream} {A B : Set ℕ}
    (hAB : A ⊆ B) (hvalid : GenLimit.NovelGeneratesInLimit input output A) :
    GenLimit.NovelGeneratesInLimit input output B := by
  rcases hvalid with ⟨T, hT⟩
  refine ⟨T, fun t ht => ?_⟩
  rcases hT t ht with ⟨hA, hfresh, hnovel⟩
  exact ⟨hAB hA, hfresh, hnovel⟩

noncomputable def marker (k : ℕ) : ℕ :=
  Nat.nth (fun n => ¬ square n) k

lemma marker_nonsquare (k : ℕ) : ¬ square (marker k) := by
  exact Nat.nth_mem_of_infinite nonsquare_infinite k

lemma marker_injective : Function.Injective marker := by
  exact Nat.nth_injective nonsquare_infinite

noncomputable def finiteExtras (j : ℕ) : Finset ℕ :=
  (Finset.range j).image marker

lemma marker_not_mem_finiteExtras (i : ℕ) : marker i ∉ finiteExtras i := by
  intro hmem
  rcases Finset.mem_image.1 hmem with ⟨k, hk, heq⟩
  have hki : k = i := marker_injective heq
  have hlt : k < i := Finset.mem_range.1 hk
  omega

noncomputable def targetFamily {r : ℕ} (j : Fin r) : Set ℕ :=
  if (j : ℕ) + 1 = r then Set.univ else Kcore ∪ (finiteExtras j : Set ℕ)

lemma targetFamily_core_subset {r : ℕ} (j : Fin r) :
    Kcore ⊆ targetFamily j := by
  intro x hx
  unfold targetFamily
  by_cases hlast : (j : ℕ) + 1 = r
  · simp [hlast]
  · simp [hlast, hx]

lemma targetFamily_strict {r : ℕ} (i j : Fin r) (hij : (i : ℕ) < (j : ℕ)) :
    targetFamily i ⊂ targetFamily j := by
  rw [Set.ssubset_iff_exists]
  have hiNotLast : (i : ℕ) + 1 ≠ r := by
    intro hi
    have hjlt := j.isLt
    omega
  have hsub : targetFamily i ⊆ targetFamily j := by
    intro x hx
    unfold targetFamily at hx ⊢
    by_cases hjLast : (j : ℕ) + 1 = r
    · simp [hjLast]
    · simp only [hiNotLast, hjLast, if_false, Set.mem_union, Finset.mem_coe] at hx ⊢
      rcases hx with hxcore | hxextra
      · exact Or.inl hxcore
      · exact Or.inr (Finset.image_mono marker (Finset.range_mono (Nat.le_of_lt hij)) hxextra)
  refine ⟨hsub, marker i, ?_, ?_⟩
  · unfold targetFamily
    by_cases hjLast : (j : ℕ) + 1 = r
    · simp [hjLast]
    · simp only [hjLast, if_false, Set.mem_union, Finset.mem_coe]
      exact Or.inr (by
        simp only [finiteExtras, Finset.mem_image, Finset.mem_range]
        exact ⟨i, hij, rfl⟩)
  · unfold targetFamily
    simp only [hiNotLast, if_false, Set.mem_union, Finset.mem_coe, not_or]
    exact ⟨marker_nonsquare i, marker_not_mem_finiteExtras i⟩

end

end Case024Proof

open Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · have hstrict : Kcore ⊂ (Set.univ : Set ℕ) := by
      rw [Set.ssubset_iff_exists]
      exact ⟨Set.subset_univ Kcore, marker 0, Set.mem_univ _, marker_nonsquare 0⟩
    refine ⟨Kcore, Set.univ, swappedEnumeration, hstrict, legal_core,
      legal_superset Set.univ (Set.subset_univ Kcore) Set.infinite_univ, ?_⟩
    unfold Stage3Case024.PairObstruction
    intro Ω _ μ _ gen output hfollow hmeas hintCore hintUniv hvalidCore hvalidUniv
    have hcore := expected_core_le_one μ output hintCore
    have huniv := expected_univ_zero μ output hvalidCore
    constructor
    · rw [huniv]
      linarith
    · rintro ⟨hhalfCore, hhalfUniv⟩
      rw [huniv] at hhalfUniv
      norm_num at hhalfUniv
  · intro r hr
    refine ⟨fun j : Fin r => targetFamily j, swappedEnumeration, ?_⟩
    unfold Stage3Case024.ManyTargetWitness
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact targetFamily_strict i j hij
    · intro j
      exact legal_superset (targetFamily j) (targetFamily_core_subset j)
        (square_infinite.mono (targetFamily_core_subset j))
    · refine ⟨freshGenerator Kcore square_infinite, ?_⟩
      intro input hlegal
      refine ⟨followFresh Kcore square_infinite input,
        followFresh_follows Kcore square_infinite input, ?_⟩
      intro j
      exact novel_mono (targetFamily_core_subset j)
        (followFresh_valid Kcore square_infinite input)
    · unfold Stage3Case024.ManyTargetObstruction
      intro Ω _ μ _ gen output hfollow hmeas hint hvalid
      let first : Fin r := ⟨0, by omega⟩
      let last : Fin r := ⟨r - 1, by omega⟩
      refine ⟨last, ?_⟩
      have hvalidCore : Stage3Case024.EventuallyFreshValid μ Kcore swappedEnumeration output := by
        have hfirst := hvalid first
        simpa [first, targetFamily, finiteExtras, show (1 : ℕ) ≠ r by omega] using hfirst
      have huniv := expected_univ_zero μ output hvalidCore
      simpa [last, targetFamily, show r - 1 + 1 = r by omega] using huniv
