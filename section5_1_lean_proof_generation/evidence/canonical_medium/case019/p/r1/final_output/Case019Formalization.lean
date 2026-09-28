import Stage3Model

open Stage3Case019

namespace Stage3Case019

theorem range_eq_target_union_contaminants {α : Type*}
    {input : Stream α} {K : Language α} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    Set.range input = K ∪ (Set.range input \ K) := by
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · intro hx
    rcases hx with hxK | hxOutside
    · exact h.2.1 hxK
    · exact hxOutside.1

theorem contaminants_finite {α : Type*}
    {input : Stream α} {K : Language α} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    (Set.range input \ K).Finite := by
  rcases h.2.2 with ⟨F, hF, _⟩
  rw [← hF]
  exact F.finite_toSet

theorem contaminant_finset_exists {α : Type*}
    {input : Stream α} {K : Language α} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ∃ F : Finset α, (F : Set α) = Set.range input \ K ∧ F.card ≤ q := by
  exact h.2.2

theorem target_infinite_of_presentation {α : Type*}
    {input : Stream α} {K : Language α} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    K.Infinite := by
  intro hK
  have hOutside := contaminants_finite h
  have hRange : (Set.range input).Finite := by
    rw [range_eq_target_union_contaminants h]
    exact hK.union hOutside
  exact (Set.infinite_range_of_injective h.1) hRange

theorem novel_after_input_implies_sample_fresh {α : Type*}
    {input output : Stream α} {K : Language α}
    (h : NovelGeneratesAfterInput input output K) :
    SampleFreshGeneratesAfterInput input output K := by
  rcases h with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  exact ⟨(hT t ht).1, (hT t ht).2.1⟩

theorem not_sample_fresh_iff {α : Type*}
    {input output : Stream α} {K : Language α} :
    ¬SampleFreshGeneratesAfterInput input output K ↔
      ∀ T, ∃ t, T ≤ t ∧
        (output t ∉ K ∨ output t ∈ GenLimit.Generic.sample input (t + 1)) := by
  constructor
  · intro h T
    by_contra hnone
    push_neg at hnone
    exact h ⟨T, hnone⟩
  · intro h hsuccess
    rcases hsuccess with ⟨T, hT⟩
    rcases h T with ⟨t, ht, hfail⟩
    rcases hfail with hout | hsample
    · exact hout (hT t ht).1
    · exact (hT t ht).2 hsample

theorem balanced_zero : balanced 0 = 0 := rfl

end Stage3Case019
