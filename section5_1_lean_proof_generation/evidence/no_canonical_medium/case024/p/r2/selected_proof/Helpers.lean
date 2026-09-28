import Stage3Model
import Mathlib

open Filter MeasureTheory Set
open scoped Topology

namespace Case024

abbrev Language := Stage3Case024.Language

def squares : Language := Set.range (fun n : ℕ => n * n)

lemma squares_infinite : squares.Infinite := by
  apply Set.infinite_range_of_injective
  intro a b h
  nlinarith

lemma squares_compl_infinite : squaresᶜ.Infinite := by
  let f : ℕ → ℕ := fun n => (2 * n + 1) * (2 * n + 1) + 1
  apply Set.infinite_of_injective_forall_mem (s := squaresᶜ) (f := f)
  · intro a b h
    simp only [f] at h
    nlinarith
  · intro n
    change f n ∉ squares
    simp only [squares, Set.mem_range]
    rintro ⟨m, hm⟩
    simp only [f] at hm
    by_cases hle : m ≤ 2 * n + 1
    · have hsq := Nat.mul_self_le_mul_self hle
      nlinarith
    · have hle' : 2 * n + 2 ≤ m := by omega
      have hsq := Nat.mul_self_le_mul_self hle'
      nlinarith

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  apply Finset.card_le_card
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma squares_prefix_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n ≤ Nat.sqrt n + 1 := by
  let f : Finset ℕ := (Finset.range (Nat.sqrt n + 1)).image (fun k => k * k)
  calc
    GenLimit.PatientScope.prefixCount squares n ≤ f.card := by
      apply Finset.card_le_card
      intro x hx
      simp only [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
        Finset.mem_filter, Finset.mem_range, squares, Set.mem_range] at hx
      obtain ⟨hxlt, k, rfl⟩ := hx
      simp only [f, Finset.mem_image]
      refine ⟨k, ?_, rfl⟩
      simp only [Finset.mem_range]
      exact Nat.lt_succ_iff.mpr ((Nat.le_sqrt).2 (Nat.le_of_lt hxlt))
    _ ≤ Nat.sqrt n + 1 := by
      simpa [f] using
        (Finset.card_image_le :
          ((Finset.range (Nat.sqrt n + 1)).image (fun k : ℕ => k * k)).card ≤
            (Finset.range (Nat.sqrt n + 1)).card)

lemma tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with a ha
  exact (Nat.le_sqrt).2 ha

lemma tendsto_sqrt_ratio_zero :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hs : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_sqrt_atTop
  have hinv : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hs
  have htwo : Tendsto (fun n : ℕ => 2 * (Nat.sqrt n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n : ℕ => (2 : ℝ) * (Nat.sqrt n : ℝ)⁻¹) atTop (nhds ((2 : ℝ) * 0)))
  apply squeeze_zero'
    (f := fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / (n : ℝ))
    (g := fun n : ℕ => 2 * (Nat.sqrt n : ℝ)⁻¹)
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    have hspos : (0 : ℝ) < Nat.sqrt n := by
      exact_mod_cast (Nat.sqrt_pos.2 hn)
    have hsq : ((Nat.sqrt n : ℝ) * Nat.sqrt n) ≤ n := by
      exact_mod_cast Nat.sqrt_le n
    rw [show ((Nat.sqrt n + 1 : ℕ) : ℝ) = (Nat.sqrt n : ℝ) + 1 by norm_num]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n)]
    have hsone : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast (Nat.sqrt_pos.2 hn)
    calc
      (Nat.sqrt n : ℝ) + 1 ≤ 2 * Nat.sqrt n := by linarith
      _ ≤ (2 * (Nat.sqrt n : ℝ)⁻¹) * n := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [le_inv_mul_iff₀ hspos]
        exact hsq
  · exact htwo

lemma squares_density_zero :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / n) atTop (nhds 0) := by
  apply squeeze_zero'
    (f := fun n : ℕ => (GenLimit.PatientScope.prefixCount squares n : ℝ) / n)
    (g := fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n)
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
    exact div_le_div_of_nonneg_right (by exact_mod_cast (squares_prefix_le n)) (by positivity)
  · exact tendsto_sqrt_ratio_zero


def tag (n : ℕ) : ℕ := (2 * n + 1) * (2 * n + 1) + 1

lemma tag_injective : Function.Injective tag := by
  intro a b h
  simp only [tag] at h
  nlinarith

lemma tag_not_square (n : ℕ) : tag n ∉ squares := by
  simp only [tag, squares, Set.mem_range]
  rintro ⟨m, hm⟩
  by_cases hle : m ≤ 2 * n + 1
  · have hsq := Nat.mul_self_le_mul_self hle
    nlinarith
  · have hle' : 2 * n + 2 ≤ m := by omega
    have hsq := Nat.mul_self_le_mul_self hle'
    nlinarith

noncomputable def squareSwap : {x : ℕ // x ∈ squares} ≃ {x : ℕ // x ∈ squaresᶜ} := by
  letI : Infinite {x : ℕ // x ∈ squares} := infinite_coe_iff.mpr squares_infinite
  letI : Infinite {x : ℕ // x ∈ squaresᶜ} := infinite_coe_iff.mpr squares_compl_infinite
  exact Classical.choice inferInstance

noncomputable def commonStream : ℕ → ℕ := by
  classical
  exact fun n =>
    if h : n ∈ squares then squareSwap ⟨n, h⟩ else squareSwap.symm ⟨n, h⟩

lemma commonStream_mem_iff (n : ℕ) : commonStream n ∈ squares ↔ n ∉ squares := by
  classical
  by_cases h : n ∈ squares
  · have hout : commonStream n ∉ squares := by
      rw [commonStream]
      simp only [dif_pos h]
      exact (squareSwap ⟨n, h⟩).property
    simp [h, hout]
  · have hout : commonStream n ∈ squares := by
      rw [commonStream]
      simp only [dif_neg h]
      exact (squareSwap.symm ⟨n, h⟩).property
    simp [h, hout]

lemma commonStream_involutive (n : ℕ) : commonStream (commonStream n) = n := by
  classical
  by_cases h : n ∈ squares
  · have hnval : commonStream n = (squareSwap ⟨n, h⟩ : ℕ) := by
      simp [commonStream, h]
    rw [hnval]
    have hc : (squareSwap ⟨n, h⟩ : ℕ) ∉ squares := (squareSwap ⟨n, h⟩).property
    simp [commonStream, hc]
  · have hnval : commonStream n = (squareSwap.symm ⟨n, h⟩ : ℕ) := by
      simp [commonStream, h]
    rw [hnval]
    have hc : (squareSwap.symm ⟨n, h⟩ : ℕ) ∈ squares := (squareSwap.symm ⟨n, h⟩).property
    simp [commonStream, hc]

lemma commonStream_injective : Function.Injective commonStream := by
  intro a b h
  simpa only [commonStream_involutive] using congrArg commonStream h

lemma commonStream_surjective : Function.Surjective commonStream := by
  intro n
  exact ⟨commonStream n, commonStream_involutive n⟩

lemma commonStream_noiseCount (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount commonStream squares n =
      GenLimit.PatientScope.prefixCount squares n := by
  classical
  simp only [GenLimit.InfiniteContamination.noiseCount,
    GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  congr 1
  ext t
  simp [commonStream_mem_iff]

lemma commonStream_vanishingNoise_squares :
    GenLimit.InfiniteContamination.VanishingNoise commonStream squares := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  apply squares_density_zero.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
  have hn0 : n ≠ 0 := by omega
  rw [GenLimit.InfiniteContamination.empiricalNoiseRate, if_neg hn0, commonStream_noiseCount]

lemma commonStream_legal_squares : Stage3Case024.Legal commonStream squares := by
  refine ⟨squares_infinite, commonStream_injective, ?_, commonStream_vanishingNoise_squares⟩
  intro x hx
  exact commonStream_surjective x

lemma commonStream_vanishingNoise_mono {K : Language} (hsub : squares ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise commonStream K := by
  unfold GenLimit.InfiniteContamination.VanishingNoise
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  apply squeeze_zero'
    (f := GenLimit.InfiniteContamination.empiricalNoiseRate commonStream K)
    (g := GenLimit.InfiniteContamination.empiricalNoiseRate commonStream squares)
  · filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    positivity
  · filter_upwards with n
    unfold GenLimit.InfiniteContamination.empiricalNoiseRate
    split_ifs with hn
    · simp
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
        exact ⟨ht.1, fun hmem => ht.2 (hsub hmem)⟩)
  · exact commonStream_vanishingNoise_squares

lemma commonStream_legal_of_superset (K : Language) (hinf : K.Infinite) (hsub : squares ⊆ K) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨hinf, commonStream_injective, ?_, commonStream_vanishingNoise_mono hsub⟩
  intro x hx
  exact commonStream_surjective x

noncomputable def squareGenerator : Stage3Case024.OnlineGenerator := fun t input _ =>
  let base := 1 + t + ∑ i, input i
  base * base

lemma squareGenerator_success (input : Stage3Case024.Stream) :
    ∃ output : Stage3Case024.Stream,
      Stage3Case024.Follows squareGenerator input output ∧
      Stage3Case024.EventuallyFreshValidPath squares input output := by
  let output : Stage3Case024.Stream := fun t =>
    let base := 1 + t + ∑ i : Fin (t + 1), input i
    base * base
  have sum_mono : ∀ {s t : ℕ}, s ≤ t →
      (∑ i : Fin (s + 1), input i) ≤ ∑ i : Fin (t + 1), input i := by
    intro s t hst
    induction hst with
    | refl => exact le_rfl
    | @step t hst ih =>
        rw [Fin.sum_univ_castSucc (fun i : Fin (t + 2) => input i)]
        exact le_add_right ih
  refine ⟨output, ?_, ?_⟩
  · intro t
    rfl
  · refine ⟨0, fun t _ => ?_⟩
    let base := 1 + t + ∑ i : Fin (t + 1), input i
    refine ⟨⟨base, rfl⟩, ?_, ?_⟩
    · simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range, not_exists, not_and]
      intro s hst
      have hle' : input (⟨s, hst⟩ : Fin (t + 1)) ≤ ∑ i : Fin (t + 1), input i := by
        apply Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin (t + 1) => input i)
        · intro i _
          exact Nat.zero_le _
        · exact Finset.mem_univ _
      have hle : input s ≤ ∑ i : Fin (t + 1), input i := hle'
      dsimp [output, base]
      have hb : input s < base := by simp [base]; omega
      exact ne_of_lt (lt_of_lt_of_le hb (Nat.le_mul_self base))
    · intro s hst
      let baseS := 1 + s + ∑ i : Fin (s + 1), input i
      have hsum := sum_mono (Nat.le_of_lt hst)
      have hlt : baseS < base := by simp [baseS, base]; omega
      dsimp [output, baseS, base]
      exact ne_of_lt (Nat.mul_self_lt_mul_self hlt)


lemma generatorFirst_subset_range (input output : Stage3Case024.Stream) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, ht, _⟩
  exact ⟨t, ht⟩

lemma generatorFirst_diff_squares_finite {input output : Stage3Case024.Stream}
    (hvalid : Stage3Case024.EventuallyFreshValidPath squares input output) :
    (GenLimit.GeneratorFirst input output \ squares).Finite := by
  obtain ⟨T, hT⟩ := hvalid
  refine ((Finset.range T).image output).finite_toSet.subset ?_
  rintro x ⟨hx, hnot⟩
  obtain ⟨t, ht⟩ := generatorFirst_subset_range input output hx
  have hlt : t < T := by
    by_contra h
    have hsquare := (hT t (Nat.le_of_not_gt h)).1
    exact hnot (ht ▸ hsquare)
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  exact ⟨t, hlt, ht⟩

lemma prefixCount_le_squares_add {A : Language} (hfin : (A \ squares).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount squares n + hfin.toFinset.card := by
  classical
  let fa := GenLimit.PatientScope.prefixFinset A n
  let fs := GenLimit.PatientScope.prefixFinset squares n
  have hsub : fa ⊆ fs ∪ hfin.toFinset := by
    intro x hx
    have hx' : x < n ∧ x ∈ A := by
      simpa [fa, GenLimit.PatientScope.prefixFinset] using hx
    by_cases hs : x ∈ squares
    · apply Finset.mem_union_left
      simpa [fs, GenLimit.PatientScope.prefixFinset] using ⟨hx'.1, hs⟩
    · apply Finset.mem_union_right
      exact hfin.mem_toFinset.mpr ⟨hx'.2, hs⟩
  calc
    GenLimit.PatientScope.prefixCount A n = fa.card := rfl
    _ ≤ (fs ∪ hfin.toFinset).card := Finset.card_le_card hsub
    _ ≤ fs.card + hfin.toFinset.card := Finset.card_union_le _ _
    _ = GenLimit.PatientScope.prefixCount squares n + hfin.toFinset.card := rfl

lemma density_univ_zero_of_finite_diff {A : Language} (hfin : (A \ squares).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  have hconst : Tendsto (fun n : ℕ => (hfin.toFinset.card : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop) _
  have hadd := squares_density_zero.add hconst
  have hratio : Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
        (GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero'
      (g := fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount squares n : ℝ) / n +
          (hfin.toFinset.card : ℝ) / n)
    · filter_upwards with n
      positivity
    · filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with n hn
      rw [Set.inter_univ, prefixCount_univ]
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_le_squares_add hfin n)
        (by positivity)
    · simpa using hadd
  exact hratio.limsup_eq

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.limsup_le_of_le
    (hf := Filter.isCoboundedUnder_le_of_eventually_le atTop
      (Filter.Eventually.of_forall (fun n => by positivity)))
  filter_upwards with n
  by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hz]
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)]
    exact_mod_cast prefixCount_mono Set.inter_subset_right n

lemma eventually_generatorFirst_finite_diff {input output : Stage3Case024.Stream}
    (hvalid : Stage3Case024.EventuallyFreshValidPath squares input output) :
    ((GenLimit.GeneratorFirst input output) \ squares).Finite :=
  generatorFirst_diff_squares_finite hvalid

lemma ae_density_univ_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : Stage3Case024.Stream) (output : Ω → Stage3Case024.Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ squares input output) :
    ∀ᵐ ω ∂μ, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Set.univ = 0 := by
  filter_upwards [hvalid] with ω hω
  exact density_univ_zero_of_finite_diff (generatorFirst_diff_squares_finite hω)

end Case024
