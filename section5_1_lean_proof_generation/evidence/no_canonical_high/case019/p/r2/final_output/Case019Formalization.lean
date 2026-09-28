import Helpers

open Stage3Case019

/-- Checked partial milestone for the natural-number side: once an infinite
semantic target is fixed, one prefix generator is valid, current-input fresh,
and nonrepeating from round zero on every input stream. -/
theorem stage3_known_nat_target_novel
    (K : Language ℕ) (hK : K.Infinite) :
    ∃ gen : Generator ℕ, ∀ input : Stream ℕ,
      GenLimit.NovelGeneratesInLimit
        input (outputAfterInput gen input) K := by
  refine ⟨Stage3Case019.Partial.knownTargetGenerator K hK, fun input => ?_⟩
  obtain ⟨T, hT⟩ := Stage3Case019.Partial.knownTarget_novel K hK input
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  refine ⟨hmem, ?_, hnovel⟩
  simpa [GenLimit.sample, GenLimit.Generic.sample] using hfresh

/-- Checked partial milestone for the integer side, in the exact polymorphic
novelty predicate used by the separation clause. -/
theorem stage3_known_int_target_novel
    (K : Language ℤ) (hK : K.Infinite) :
    ∃ gen : Generator ℤ, ∀ input : Stream ℤ,
      NovelGeneratesAfterInput input (outputAfterInput gen input) K := by
  exact ⟨Stage3Case019.Partial.knownTargetGenerator K hK,
    fun input => Stage3Case019.Partial.knownTarget_novel K hK input⟩
