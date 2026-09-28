import Stage3Model
open Stage3Case025
noncomputable def traj (g : OnlineGenerator) (x : Stream) (t : ℕ) : ℕ :=
  g t (fun i => x i) (fun i => traj g x i)
termination_by t
decreasing_by omega

theorem traj_follows (g : OnlineGenerator) (x : Stream) : Follows g x (traj g x) := by
  intro t
  rw [traj]
