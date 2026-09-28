import Stage3Model
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic

open Stage3Case019
open scoped BigOperators

namespace Case019Formalization

private noncomputable def historyWeight {t : ℕ} (history : Fin t → ℤ) : ℕ :=
  t + ∑ i, Int.natAbs (history i) + 1

private noncomputable def positiveEscape {t : ℕ} (history : Fin t → ℤ) : ℤ :=
  (historyWeight history : ℤ)

private noncomputable def negativeEscape {t : ℕ} (history : Fin t → ℤ) : ℤ :=
  -(historyWeight history : ℤ)

private theorem natAbs_le_historyWeight {t : ℕ} (history : Fin t → ℤ) (i : Fin t) :
    Int.natAbs (history i) < historyWeight history := by
  unfold historyWeight
  have hle : Int.natAbs (history i) ≤ ∑ j, Int.natAbs (history j) := by
    exact Finset.single_le_sum (f := fun j => Int.natAbs (history j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

private theorem history_lt_positiveEscape {t : ℕ} (history : Fin t → ℤ) (i : Fin t) :
    history i < positiveEscape history := by
  unfold positiveEscape
  have h := natAbs_le_historyWeight history i
  have habs : history i ≤ (Int.natAbs (history i) : ℤ) := Int.le_natAbs
  have hcast : (Int.natAbs (history i) : ℤ) < (historyWeight history : ℤ) := by
    exact Int.ofNat_lt.mpr h
  exact lt_of_le_of_lt habs hcast

private theorem negativeEscape_lt_history {t : ℕ} (history : Fin t → ℤ) (i : Fin t) :
    negativeEscape history < history i := by
  unfold negativeEscape
  have h := natAbs_le_historyWeight history i
  have hcast : (Int.natAbs (history i) : ℤ) < (historyWeight history : ℤ) := by
    exact Int.ofNat_lt.mpr h
  by_cases hx : 0 ≤ history i
  · have habs_nonneg : 0 ≤ (Int.natAbs (history i) : ℤ) :=
      Int.ofNat_zero_le _
    omega
  · have hxneg : history i < 0 := lt_of_not_ge hx
    rcases Int.natAbs_eq (history i) with hpos | hneg
    · have habs_nonneg : 0 ≤ (Int.natAbs (history i) : ℤ) :=
        Int.ofNat_zero_le _
      omega
    · omega

private theorem positiveEscape_not_mem_sequenceSample {t : ℕ} (history : Fin t → ℤ) :
    positiveEscape history ∉ GenLimit.Generic.sequenceSample history := by
  classical
  simp only [GenLimit.Generic.sequenceSample, Finset.mem_image, Finset.mem_univ, true_and,
    not_exists]
  intro i
  exact ne_of_lt (history_lt_positiveEscape history i)

private theorem negativeEscape_not_mem_sequenceSample {t : ℕ} (history : Fin t → ℤ) :
    negativeEscape history ∉ GenLimit.Generic.sequenceSample history := by
  classical
  simp only [GenLimit.Generic.sequenceSample, Finset.mem_image, Finset.mem_univ, true_and,
    not_exists]
  intro i
  exact ne_of_gt (negativeEscape_lt_history history i)

/-- The two escape directions used by the adjacent-noise construction are
fresh relative to every finite input history. -/
theorem escape_values_are_fresh {t : ℕ} (history : Fin t → ℤ) :
    positiveEscape history ∉ GenLimit.Generic.sequenceSample history ∧
      negativeEscape history ∉ GenLimit.Generic.sequenceSample history := by
  exact ⟨positiveEscape_not_mem_sequenceSample history,
    negativeEscape_not_mem_sequenceSample history⟩


end Case019Formalization
