import Stage3Model
#check WellFounded.fix
#check WellFounded.fix_eq
#check Nat.lt_wfRel
#check Nat.find
#check Set.Infinite.exists_not_mem_finset
#check Set.Infinite.exists_not_mem_finset
#check Set.Finite.toFinset

namespace X
abbrev OG := (t : ℕ) → (Fin (t+1) → ℕ) → (Fin t → ℕ) → ℕ
noncomputable def traj (g : OG) (x : ℕ → ℕ) : ℕ → ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf fun t rec =>
    g t (fun i => x i) (fun i => rec i i.isLt)

theorem traj_eq (g : OG) (x : ℕ → ℕ) (t : ℕ) :
    traj g x t = g t (fun i => x i) (fun i => traj g x i) := by
  rw [traj, WellFounded.fix_eq]
