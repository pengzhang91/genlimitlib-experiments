import Case019Helpers

open Stage3Case019

/-- Checked partial milestone: the canonical marker family is extensionally
uncountable, all of its languages are infinite, and one semantic generator
novel-generates eventually on every level-`q` presentation. -/
theorem stage3_uncountable_level_q_novel_validity :
    ∀ q : ℕ, ∃ family : LanguageClass ℤ,
      ¬family.Countable ∧
      (∀ K ∈ family, K.Infinite) ∧
      ∃ gen : Generator ℤ,
        ∀ K ∈ family, ∀ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q →
            NovelGeneratesAfterInput input (outputAfterInput gen input) K := by
  intro q
  refine ⟨Case019.separationFamily q,
    Case019.separationFamily_uncountable q,
    Case019.separationFamily_infinite_languages q,
    Case019.markerGenerator q, ?_⟩
  intro K hK input hp
  exact Case019.markerGenerator_novel_limit q K input hK hp
