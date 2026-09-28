import Stage3Model
noncomputable def traj (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => traj gen input i)
termination_by t
decreasing_by exact i.isLt
#print traj
#check traj.eq_def
#check traj.eq_1
#check traj._eq_1
example (gen : Stage3Case017.OnlineGenerator) (input : Stage3Case017.Stream) (t : ℕ) :
  traj gen input t = gen t (fun i => input i) (fun i => traj gen input i) := by
  unfold traj
