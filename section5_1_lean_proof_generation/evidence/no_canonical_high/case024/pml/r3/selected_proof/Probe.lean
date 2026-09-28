import Stage3Model
import Mathlib.Tactic
open Stage3Case024
noncomputable def run (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => Nat.strongRec (motive := fun _ => ℕ)
    (fun n rec => gen n (fun i => input i) (fun i => rec i.1 i.2)) t

example (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  rw [run]
  rw [Nat.strongRec_eq]
  rfl
