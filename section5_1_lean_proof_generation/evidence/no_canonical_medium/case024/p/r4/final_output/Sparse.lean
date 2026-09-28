import Stage3Model
import Mathlib

open Filter
open scoped Topology

namespace Case024

abbrev squares : Set ℕ := Set.range (fun k : ℕ => k^2)

lemma prefixCount_univ (n : ℕ) : GenLimit.PatientScope.prefixCount Set.univ n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n ≤ Nat.sqrt n + 1 := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let F := (Finset.range (Nat.sqrt n + 1)).image (fun k : ℕ => k^2)
  calc
    ((Finset.range n).filter fun x => x ∈ squares).card ≤ F.card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      rcases hx.2 with ⟨k, rfl⟩
      apply Finset.mem_image.2
      refine ⟨k, ?_, rfl⟩
      simp only [Finset.mem_range]
      have hkn : k^2 ≤ n := le_of_lt hx.1
      exact Nat.lt_succ_iff.mpr (Nat.le_sqrt'.2 hkn)
    _ ≤ Nat.sqrt n + 1 := by
      exact (Finset.card_image_le.trans_eq (Finset.card_range _))

end Case024

namespace Case024

lemma tendsto_real_sqrt_nat_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (Nat.ceil (max b 0 ^ 2))] with n hn
  have hb0 : 0 ≤ max b 0 := le_max_right _ _
  have hceil : max b 0 ^ 2 ≤ (Nat.ceil (max b 0 ^ 2) : ℝ) := Nat.le_ceil _
  have hnreal : (Nat.ceil (max b 0 ^ 2) : ℝ) ≤ n := by exact_mod_cast hn
  have hsquare : max b 0 ^ 2 ≤ (n : ℝ) := hceil.trans hnreal
  have hroot : max b 0 ≤ Real.sqrt (n : ℝ) := (Real.le_sqrt hb0 (Nat.cast_nonneg _)).2 hsquare
  exact (le_max_left b 0).trans hroot

lemma tendsto_sqrt_ratio_zero :
    Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hinvroot : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_real_sqrt_nat_atTop
  have hinvn : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hbound : ∀ n : ℕ, ((Nat.sqrt n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
      (Real.sqrt (n : ℝ))⁻¹ + ((n : ℝ))⁻¹ := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).2
      rw [← Nat.cast_pow]
      exact_mod_cast Nat.sqrt_le' n
    rw [Nat.cast_add, Nat.cast_one, add_div]
    apply add_le_add
    · calc
        (Nat.sqrt n : ℝ) / n ≤ Real.sqrt (n : ℝ) / n :=
          div_le_div_of_nonneg_right hsqrt hnpos.le
        _ = (Real.sqrt (n : ℝ))⁻¹ := Real.sqrt_div_self
    · simp [one_div]
  apply squeeze_zero
  · intro n; positivity
  · exact hbound
  · simpa using hinvroot.add hinvn

lemma tendsto_square_prefix_ratio_zero :
    Tendsto (fun n : ℕ =>
      (GenLimit.PatientScope.prefixCount squares n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n; positivity
  · intro n
    have hcast : (GenLimit.PatientScope.prefixCount squares n : ℝ) ≤
        ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
      exact_mod_cast prefixCount_squares_le n
    exact div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
  · exact tendsto_sqrt_ratio_zero

end Case024
