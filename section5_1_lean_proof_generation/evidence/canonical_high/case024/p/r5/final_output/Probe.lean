import Stage3Model
import Mathlib.Tactic
namespace X
abbrev Stream := Stage3Case024.Stream
abbrev OnlineGenerator := Stage3Case024.OnlineGenerator
noncomputable def gen : OnlineGenerator := fun t inp out => 0
noncomputable def out (input : Stream) : Stream :=
  Nat.lt_wfRel.wf.fix (fun t rec => gen t (fun i => input i) (fun i => rec i i.isLt))
lemma out_eq (input : Stream) (t : ℕ) :
  out input t = gen t (fun i => input i) (fun i => out input i) := by
  rw [out]
  rw [WellFounded.fix_eq]
end X
