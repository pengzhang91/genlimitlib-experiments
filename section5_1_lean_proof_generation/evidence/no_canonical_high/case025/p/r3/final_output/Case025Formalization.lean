import Stage3Model

open Set

namespace Stage3Case025

/-- The distinct off-target values in an admissible presentation form a finite set. -/
theorem finite_contamination_values
    {input : Stream} {K : Language}
    (hp : CompleteFiniteOccurrencePresentation input K) :
    (Set.range input \ K).Finite := by
  rcases hp with ⟨_, hviol⟩
  refine (hviol.image input).subset ?_
  intro x hx
  rcases hx with ⟨⟨t, rfl⟩, htK⟩
  refine ⟨t, ?_, rfl⟩
  change ¬input t ∈ K
  exact htK

/-- The finite set of distinct off-target values occurring in a presentation. -/
noncomputable def contaminationValues
    (input : Stream) (K : Language)
    (hp : CompleteFiniteOccurrencePresentation input K) : Finset ℕ :=
  (finite_contamination_values hp).toFinset

theorem mem_contaminationValues_iff
    {input : Stream} {K : Language}
    (hp : CompleteFiniteOccurrencePresentation input K) (x : ℕ) :
    x ∈ contaminationValues input K hp ↔ x ∈ Set.range input ∧ x ∉ K := by
  simp [contaminationValues]

/-- An admissible noisy stream exactly presents the target enlarged by its
finite set of distinct contaminating values. -/
theorem presents_target_union_contamination
    {input : Stream} {K : Language}
    (hp : CompleteFiniteOccurrencePresentation input K) :
    GenLimit.Presents input (K ∪ (↑(contaminationValues input K hp) : Set ℕ)) := by
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ((mem_contaminationValues_iff hp x).2 ⟨hx, hxK⟩)
  · intro hx
    rcases hx with hxK | hxB
    · exact hp.1 hxK
    · exact ((mem_contaminationValues_iff hp x).1 hxB).1

/-- Finite occurrence contamination has a last bad round. -/
theorem eventually_input_mem_target
    {input : Stream} {K : Language}
    (hp : CompleteFiniteOccurrencePresentation input K) :
    ∃ T, ∀ t, T ≤ t → input t ∈ K := by
  rcases hp with ⟨_, hviol⟩
  rcases hviol.bddAbove with ⟨bound, hbound⟩
  refine ⟨bound + 1, ?_⟩
  intro t hbt
  by_contra htK
  have htViol : t ∈ GenLimit.Generic.ViolationIndices input (fun x => x ∈ K) := htK
  have htb : t ≤ bound := hbound htViol
  exact (Nat.not_succ_le_self bound) (by
    simpa [Nat.succ_eq_add_one] using hbt.trans htb)

theorem target_union_contamination_infinite
    {input : Stream} {K : Language}
    (hp : CompleteFiniteOccurrencePresentation input K) (hK : K.Infinite) :
    (K ∪ (↑(contaminationValues input K hp) : Set ℕ)).Infinite :=
  hK.mono Set.subset_union_left

end Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  sorry
