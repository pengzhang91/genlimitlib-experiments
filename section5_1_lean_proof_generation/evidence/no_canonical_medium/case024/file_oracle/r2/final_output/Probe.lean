import Stage3Model
noncomputable def foo (gen : Stage3Case024.OnlineGenerator) (input : Stage3Case024.Stream) : Stage3Case024.Stream := by
  let rec output (t : ℕ) : ℕ := gen t (fun i => input i) (fun i => output i)
  termination_by t
  decreasing_by exact i.isLt
  exact output
#print foo
#print foo.output
#check foo.output.eq_def
#check foo.output.eq_1
#check foo.output.eq_2
