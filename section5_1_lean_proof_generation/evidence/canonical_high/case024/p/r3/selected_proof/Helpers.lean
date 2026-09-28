import Stage3Model
import Mathlib

open Filter MeasureTheory
open scoped Topology

namespace Case024Formalization

open Stage3Case024

noncomputable section

abbrev pcount := GenLimit.PatientScope.prefixCount

def SparseCore (K : Set ℕ) : Prop :=
  K.Infinite ∧ Kᶜ.Infinite ∧
    Tendsto (fun n : ℕ => (pcount K n : ℝ) / n) atTop (𝓝 0)

def quadraticCore : Set ℕ := Set.range (fun k : ℕ => k * (k + 1))

lemma quadratic_strictMono : StrictMono (fun k : ℕ => k * (k + 1)) := by
  intro a b hab
  nlinarith [Nat.mul_self_lt_mul_self hab]

lemma quadraticCore_infinite : quadraticCore.Infinite := by
  exact Set.infinite_range_of_injective quadratic_strictMono.injective

lemma gap_not_quadratic (k : ℕ) : k * (k + 1) + 1 ∉ quadraticCore := by
  rintro ⟨j, hj⟩
  by_cases hjk : j ≤ k
  · have hle := quadratic_strictMono.monotone hjk
    have hbad : j * (j + 1) < j * (j + 1) := by
      calc
        j * (j + 1) ≤ k * (k + 1) := hle
        _ < k * (k + 1) + 1 := Nat.lt_succ_self _
        _ = j * (j + 1) := hj.symm
    exact (Nat.lt_irrefl _ hbad)
  · have hkj : k + 1 ≤ j := by omega
    have hle := quadratic_strictMono.monotone hkj
    have hgap : k * (k + 1) + 1 < (k + 1) * ((k + 1) + 1) := by
      nlinarith
    have hbad : j * (j + 1) < j * (j + 1) := by
      calc
        j * (j + 1) = k * (k + 1) + 1 := hj
        _ < (k + 1) * ((k + 1) + 1) := hgap
        _ ≤ j * (j + 1) := hle
    exact (Nat.lt_irrefl _ hbad)

lemma quadraticCore_compl_infinite : quadraticCoreᶜ.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => k * (k + 1) + 1)
  · intro a b h
    apply quadratic_strictMono.injective
    exact Nat.add_right_cancel h
  · intro k
    exact gap_not_quadratic k

lemma pcount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) : pcount A n ≤ pcount B n := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [pcount, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma pcount_univ (n : ℕ) : pcount Set.univ n = n := by
  simp [pcount, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

lemma pcount_quadratic_le (n : ℕ) : pcount quadraticCore n ≤ Nat.sqrt n + 1 := by
  classical
  let f : ℕ → ℕ := fun k => k * (k + 1)
  have hsub : GenLimit.PatientScope.prefixFinset quadraticCore n ⊆
      (Finset.range (Nat.sqrt n + 1)).image f := by
    intro x hx
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range] at hx
    rcases hx.2 with ⟨k, rfl⟩
    apply Finset.mem_image.2
    refine ⟨k, ?_, rfl⟩
    have hkn : k * k < n := by
      calc
        k * k ≤ k * (k + 1) := Nat.mul_le_mul_left k (Nat.le_succ k)
        _ < n := hx.1
    have hks : k ≤ Nat.sqrt n := Nat.le_sqrt.2 (Nat.le_of_lt hkn)
    exact Finset.mem_range.2 (by simpa using Nat.lt_succ_of_le hks)
  calc
    pcount quadraticCore n ≤ ((Finset.range (Nat.sqrt n + 1)).image f).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.sqrt n + 1)).card := Finset.card_image_le
    _ = Nat.sqrt n + 1 := Finset.card_range _

lemma sqrt_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 / ε) 1)
  refine ⟨N * N, fun n hn => ?_⟩
  have hNpos : (0 : ℕ) < N := by
    have : (1 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) (by exact_mod_cast hN)
    exact_mod_cast (lt_trans zero_lt_one this)
  have hnpos : (0 : ℕ) < n := lt_of_lt_of_le (Nat.mul_pos hNpos hNpos) hn
  have hNsqrt : N ≤ Nat.sqrt n := Nat.le_sqrt.2 hn
  have hspos : (0 : ℕ) < Nat.sqrt n := lt_of_lt_of_le hNpos hNsqrt
  have htwo : (2 : ℝ) < ε * N := by
    have hreal : (2 : ℝ) / ε < N := lt_of_le_of_lt (le_max_left _ _) (by exact_mod_cast hN)
    simpa [mul_comm] using (div_lt_iff₀ hε).1 hreal
  have hnum : ((Nat.sqrt n + 1 : ℕ) : ℝ) < ε * n := by
    have h1 : ((Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 2 * Nat.sqrt n := by
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      exact_mod_cast (show Nat.sqrt n + 1 ≤ 2 * Nat.sqrt n by omega)
    have h2 : (2 : ℝ) * Nat.sqrt n < (ε * N) * Nat.sqrt n := by
      exact mul_lt_mul_of_pos_right htwo (by exact_mod_cast hspos)
    have hNreal : (N : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hNsqrt
    have hsreal : (0 : ℝ) ≤ Nat.sqrt n := by positivity
    have h3 : (ε * N) * Nat.sqrt n ≤ ε * (Nat.sqrt n * Nat.sqrt n) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hNreal hsreal) hε.le
    have h4 : ε * (Nat.sqrt n * Nat.sqrt n : ℝ) ≤ ε * n := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      exact_mod_cast Nat.sqrt_le n
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (h3.trans h4))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact (div_lt_iff₀ (by exact_mod_cast hnpos)).2 hnum
  · positivity

lemma quadraticCore_sparse : SparseCore quadraticCore := by
  refine ⟨quadraticCore_infinite, quadraticCore_compl_infinite, ?_⟩
  apply squeeze_zero' (f := fun n : ℕ => (pcount quadraticCore n : ℝ) / n)
    (g := fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n)
  · filter_upwards with n
    positivity
  · filter_upwards with n
    by_cases hn : n = 0
    · subst n
      simp
    · apply div_le_div_of_nonneg_right
      · exact_mod_cast pcount_quadratic_le n
      · positivity
  · exact sqrt_ratio_tendsto_zero


noncomputable def swapPerm (K : Set ℕ) (hK : K.Infinite) (hKc : Kᶜ.Infinite) : ℕ ≃ ℕ := by
  classical
  letI : Infinite (↥K) := hK.to_subtype
  letI : Infinite (↥(Kᶜ)) := hKc.to_subtype
  let e : (↥K) ≃ (↥(Kᶜ)) := nonempty_equiv_of_countable.some
  exact (Equiv.Set.sumCompl K).symm |>.trans
    ((Equiv.sumCongr e e.symm).trans
      ((Equiv.sumComm (↥(Kᶜ)) (↥K)).trans (Equiv.Set.sumCompl K)))

lemma swapPerm_mem_iff (K : Set ℕ) (hK : K.Infinite) (hKc : Kᶜ.Infinite) (n : ℕ) :
    swapPerm K hK hKc n ∈ K ↔ n ∉ K := by
  classical
  letI : Infinite (↥K) := hK.to_subtype
  letI : Infinite (↥(Kᶜ)) := hKc.to_subtype
  by_cases hn : n ∈ K
  · simp only [swapPerm, Equiv.trans_apply]
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hn]
    simp only [Equiv.sumCongr_apply, Equiv.sumComm_apply, Equiv.Set.sumCompl_apply_inr]
    constructor
    · intro hout
      exact fun _ => ((nonempty_equiv_of_countable (α := ↥K) (β := ↥(Kᶜ))).some
        ⟨n, hn⟩).property hout
    · intro hnot
      exact (hnot hn).elim
  · simp only [swapPerm, Equiv.trans_apply]
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hn]
    simp only [Equiv.sumCongr_apply, Equiv.sumComm_apply, Equiv.Set.sumCompl_apply_inl]
    constructor
    · intro _
      exact hn
    · intro _
      exact (((nonempty_equiv_of_countable (α := ↥K) (β := ↥(Kᶜ))).some).symm
        ⟨n, hn⟩).property

lemma noiseCount_swapPerm (K : Set ℕ) (hK : K.Infinite) (hKc : Kᶜ.Infinite) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount (swapPerm K hK hKc) K n = pcount K n := by
  classical
  simp only [GenLimit.InfiniteContamination.noiseCount, pcount,
    GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  congr 1
  ext t
  simp [swapPerm_mem_iff K hK hKc]

lemma legal_swap_core {K : Set ℕ} (hK : SparseCore K) :
    Legal (swapPerm K hK.1 hK.2.1) K := by
  refine ⟨hK.1, (swapPerm K hK.1 hK.2.1).injective, ?_, ?_⟩
  · intro x hx
    exact (swapPerm K hK.1 hK.2.1).surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    have hsparse := hK.2.2
    apply hsparse.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [GenLimit.InfiniteContamination.empiricalNoiseRate, hn,
      noiseCount_swapPerm K hK.1 hK.2.1]

lemma legal_swap_univ {K : Set ℕ} (hK : SparseCore K) :
    Legal (swapPerm K hK.1 hK.2.1) Set.univ := by
  refine ⟨Set.infinite_univ, (swapPerm K hK.1 hK.2.1).injective, ?_, ?_⟩
  · intro x hx
    exact (swapPerm K hK.1 hK.2.1).surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    have : GenLimit.InfiniteContamination.empiricalNoiseRate
        (swapPerm K hK.1 hK.2.1) Set.univ = fun _ => 0 := by
      funext n
      simp [GenLimit.InfiniteContamination.empiricalNoiseRate,
        GenLimit.InfiniteContamination.noiseCount]
    rw [this]
    exact tendsto_const_nhds

end

end Case024Formalization
