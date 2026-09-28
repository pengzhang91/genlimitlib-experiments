import Stage3Model

open Stage3Case025

namespace Stage3Case025

/-- Exact positive presentations are a special case of the allowed finitely
contaminated presentations. -/
theorem completeFiniteOccurrencePresentation_of_presents
    {input : Stream} {K : Language} (hinput : GenLimit.Presents input K) :
    CompleteFiniteOccurrencePresentation input K := by
  constructor
  · rw [← hinput]
  · rw [GenLimit.Generic.FinitelyManyViolations]
    have hall : ∀ t, input t ∈ K := by
      intro t
      rw [← hinput]
      exact ⟨t, rfl⟩
    have hempty :
        GenLimit.Generic.ViolationIndices input (fun x => x ∈ K) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact ht (hall t)
    rw [hempty]
    exact Set.finite_empty

/-- Finite occurrence contamination produces only finitely many distinct
values outside the target. -/
theorem finite_range_diff_of_completeFiniteOccurrencePresentation
    {input : Stream} {K : Language}
    (hinput : CompleteFiniteOccurrencePresentation input K) :
    (Set.range input \ K).Finite := by
  have hbad :
      (GenLimit.Generic.ViolationIndices input (fun x => x ∈ K)).Finite :=
    hinput.2
  apply (hbad.image input).subset
  intro x hx
  rcases hx.1 with ⟨t, rfl⟩
  exact ⟨t, hx.2, rfl⟩

/-- The local trace relation determines at most one output stream. -/
theorem follows_unique
    {gen : OnlineGenerator} {input output₁ output₂ : Stream}
    (h₁ : Follows gen input output₁) (h₂ : Follows gen input output₂) :
    output₁ = output₂ := by
  funext t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      rw [h₁ t, h₂ t]
      apply congrArg (gen t (fun i => input i))
      funext i
      exact ih i (Fin.isLt i)

end Stage3Case025
