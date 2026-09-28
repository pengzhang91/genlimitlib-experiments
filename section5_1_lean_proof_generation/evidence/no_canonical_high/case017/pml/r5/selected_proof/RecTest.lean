import Stage3Model
open Stage3Case017
noncomputable def traj {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) : ℕ :=
  onlineGen t (fun i => input i) (fun i => traj family input i)
termination_by t
where
  onlineGen : OnlineGenerator := fun _ _ _ => 0
