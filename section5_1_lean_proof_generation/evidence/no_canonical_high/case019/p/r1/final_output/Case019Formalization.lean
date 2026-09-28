import Case019Partial

open Stage3Case019

/-- Checked partial result for Case 019: the explicit marker family is
uncountable, all its languages are infinite, and at noise level `q` one
semantic generator eventually produces valid, sample-fresh, nonrepeating
outputs on every legal presentation. -/
theorem stage3_separation_core :
    ∀ q : ℕ,
      ¬(Case019Partial.separationFamily q).Countable ∧
        (∀ K ∈ Case019Partial.separationFamily q, K.Infinite) ∧
        (∃ gen : Generator ℤ,
          ∀ K ∈ Case019Partial.separationFamily q, ∀ input : Stream ℤ,
            GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q →
              NovelGeneratesAfterInput input (outputAfterInput gen input) K) := by
  intro q
  exact Case019Partial.separationFamily_core q
