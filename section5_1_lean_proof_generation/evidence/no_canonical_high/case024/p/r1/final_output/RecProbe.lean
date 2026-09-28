import Helpers
namespace X
noncomputable def f (g : ℕ → ℕ) (t : ℕ) : ℕ :=
  t + f g (g ⟨t-1, by omega⟩)
termination_by t
#check f.eq_1
#print f.eq_1
end X
