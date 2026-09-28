import Section4.StaircaseFrontier

namespace Section4.Staircase.Family
variable (F : Family)

@[simp] theorem errorIndices_all_false (i : ℕ) : errorIndices (fun _ => false) i = {i} := by
  ext k
  simp [mem_errorIndices,Charged]

@[simp] theorem errorIndices_all_true (i : ℕ) : errorIndices (fun _ => true) i = Finset.range i := by
  ext k
  simp [mem_errorIndices,Charged]

@[simp] theorem mistakeCount_all_false (i : ℕ) : mistakeCount (fun _ => false) i = 1 := by
  simp [mistakeCount]

@[simp] theorem mistakeCount_all_true (i : ℕ) : mistakeCount (fun _ => true) i = i := by
  simp [mistakeCount]

@[simp] theorem deadline_all_false (i : ℕ) : F.deadline (fun _ => false) i = F.size i + 1 := by
  simp [deadline]

@[simp] theorem deadline_all_true_zero : F.deadline (fun _ => true) 0 = 0 := by
  simp [deadline]

@[simp] theorem deadline_all_true_succ (i : ℕ) : F.deadline (fun _ => true) (i+1) = F.size i+1 := by
  simp only [deadline,errorIndices_all_true]
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    exact Nat.add_le_add_right (F.increasing.monotone (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) 1
  · exact Finset.le_sup (f := fun k => F.size k+1) (by simp)

/-- The two extreme profiles quoted after the appendix proof. Target index
zero here is the manuscript's first target. -/
theorem extreme_profiles :
    (∀ i, F.worstMistakes (F.scheduleGenerator (fun _ => false)) i = 1 ∧
      F.worstDeadline (F.scheduleGenerator (fun _ => false)) i = (F.size i+1 : ℕ)) ∧
    (F.worstMistakes (F.scheduleGenerator (fun _ => true)) 0 = 0 ∧
      F.worstDeadline (F.scheduleGenerator (fun _ => true)) 0 = 0) ∧
    (∀ i, F.worstMistakes (F.scheduleGenerator (fun _ => true)) (i+1) = (i+1 : ℕ) ∧
      F.worstDeadline (F.scheduleGenerator (fun _ => true)) (i+1) = (F.size i+1 : ℕ)) := by
  simp [schedule_exact_mistakes,schedule_exact_deadline]

end Section4.Staircase.Family
