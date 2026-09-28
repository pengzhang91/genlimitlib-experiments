import Case024Helpers
open Stage3Case024
noncomputable def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t
decreasing_by omega

theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  rw [run]
