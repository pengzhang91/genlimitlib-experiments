import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open Set Filter
open scoped Topology
namespace Stage3Proof
open Stage3S2B
lemma sq_le_two_pow_succ (k : ℕ) : k * k ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      by_cases hk : k ≤ 2
      · have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> norm_num
      · have hk2 : 2 * k + 1 ≤ k * k := by nlinarith
        calc
          (k + 1) * (k + 1) ≤ 2 * (k * k) := by nlinarith
          _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (k + 1) * 2 := Nat.mul_comm _ _

noncomputable def coreExponent (z : ℕ) : ℕ := by
  classical
  exact if hz : z ∈ core then Classical.choose hz else 0

lemma pow_coreExponent {z : ℕ} (hz : z ∈ core) : 2 ^ coreExponent z = z := by
  classical
  simp only [coreExponent, dif_pos hz]
  exact Classical.choose_spec hz

lemma coreExponent_injOn : Set.InjOn coreExponent core := by
  intro z hz w hw he
  rw [← pow_coreExponent hz, ← pow_coreExponent hw, he]

noncomputable def coreCount (M : ℕ) : ℕ := by
  classical
  exact Nat.count (fun z => z ∈ core) (M + 1)

lemma count_core_le_sqrt (M : ℕ) :
    coreCount M ≤ Nat.sqrt (2 * M) + 1 := by
  classical
  rw [coreCount, Nat.count_eq_card_filter_range]
  let s := (Finset.range (M + 1)).filter (fun z => z ∈ core)
  have hcard : (s.image coreExponent).card = s.card := by
    rw [Finset.card_image_iff]
    intro z hz w hw he
    have hz' : z < M + 1 ∧ z ∈ core := by simpa [s] using hz
    have hw' : w < M + 1 ∧ w ∈ core := by simpa [s] using hw
    exact coreExponent_injOn hz'.2 hw'.2 he
  rw [← hcard]
  calc
    (s.image coreExponent).card ≤ (Finset.range (Nat.sqrt (2 * M) + 1)).card := by
      apply Finset.card_le_card
      rw [Finset.image_subset_iff]
      intro z hz
      simp only [Finset.mem_range]
      have hz' : z < M + 1 ∧ z ∈ core := by simpa [s] using hz
      have hsq : coreExponent z * coreExponent z ≤ 2 * M := by
        calc
          coreExponent z * coreExponent z ≤ 2 ^ (coreExponent z + 1) := sq_le_two_pow_succ _
          _ = 2 * z := by rw [pow_succ, pow_coreExponent hz'.2]; omega
          _ ≤ 2 * M := by omega
      exact Nat.lt_succ_iff.mpr (Nat.le_sqrt.mpr hsq)
    _ = Nat.sqrt (2 * M) + 1 := Finset.card_range _
end Stage3Proof
