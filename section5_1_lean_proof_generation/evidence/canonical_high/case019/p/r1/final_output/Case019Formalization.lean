import Helpers

open Stage3Case019
open Stage3Case019.Local

/-- The canonical marker-and-tail witness class is extensionally uncountable
and all of its languages are infinite. -/
theorem stage3_witness_family_structure (q : ℕ) :
    ¬(witnessFamily q).Countable ∧
      ∀ K ∈ witnessFamily q, K.Infinite := by
  exact ⟨witnessFamily_not_countable q, witnessFamily_infinite q⟩

/-- On the marker-free branch of the canonical witness class, the explicit
branch generator already has the full level-q eventual novelty guarantee
(in fact, from round zero). -/
theorem stage3_marker_free_positive
    (q : ℕ) (K : Language ℤ) (hK : K ∈ familyB q)
    (input : Stream ℤ)
    (hp : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput
      input (outputAfterInput (branchGenerator q) input) K := by
  exact branchGenerator_novel_familyB hK hp
