import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open Filter
open scoped Topology

example (S : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n =
      ∑ k ∈ Finset.range n, S.indicator (fun _ => (1 : ℕ)) k := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k ∈ S <;> simp [Set.indicator, h]
