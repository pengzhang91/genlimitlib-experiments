import Stage3Model

open Set
open Stage3Case019

namespace Case019Formalization

variable {α : Type*}

/-- A legal value-contaminated presentation has range equal to the target
union its finite set of off-target values. -/
theorem range_eq_target_union_noise
    {input : Stream α} {K : Language α} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ∃ F : Finset α,
      F.card ≤ q ∧
      Set.range input = K ∪ (F : Set α) ∧
      (F : Set α) ∩ K = ∅ := by
  rcases h with ⟨_, hcover, F, hF, hcard⟩
  refine ⟨F, hcard, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr (hF ▸ ⟨hx, hxK⟩)
    · intro x hx
      rcases hx with hxK | hxF
      · exact hcover hxK
      · exact (hF ▸ hxF).1
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (hF ▸ hx.1).2 hx.2

/-- In particular, the range of a legal presentation of an infinite target is
infinite. -/
theorem presentation_range_infinite
    {input : Stream α} {K : Language α} {q : ℕ}
    (hK : K.Infinite)
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    (Set.range input).Infinite := by
  exact hK.mono h.2.1

end Case019Formalization
