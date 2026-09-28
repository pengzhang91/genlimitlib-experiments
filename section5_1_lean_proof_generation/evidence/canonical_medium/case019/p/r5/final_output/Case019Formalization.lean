import Stage3Model

open Stage3Case019

namespace Stage3Case019

theorem range_eq_target_union_noise {α : Type*}
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
    rcases hx with hxK | hxNoise
    · exact h.2.1 hxK
    · exact hxNoise.1

theorem finite_noise_witness {α : Type*}
    {input : Stream α} {K : Language α} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    ∃ noise : Finset α,
      (noise : Set α) = Set.range input \ K ∧ noise.card ≤ q := by
  exact h.2.2

theorem finite_contaminant_bound {α : Type*} [DecidableEq α]
    {input : Stream α} {K : Language α} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q)
    (contaminants : Finset α)
    (hcontaminants : (contaminants : Set α) ⊆ Set.range input \ K) :
    contaminants.card ≤ q := by
  obtain ⟨noise, hnoise, hcard⟩ := finite_noise_witness h
  apply le_trans (Finset.card_le_card ?_) hcard
  intro x hx
  have hx' : x ∈ Set.range input \ K := hcontaminants hx
  rw [← hnoise] at hx'
  exact hx'

theorem too_many_contaminants_impossible {α : Type*} [DecidableEq α]
    {input : Stream α} {K : Language α} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q)
    (contaminants : Finset α)
    (hcontaminants : (contaminants : Set α) ⊆ Set.range input \ K)
    (hmany : q < contaminants.card) : False := by
  exact (Nat.not_lt_of_ge (finite_contaminant_bound h contaminants hcontaminants)) hmany

theorem not_sampleFresh_iff_frequently_fails {α : Type*}
    (input output : Stream α) (K : Language α) :
    ¬SampleFreshGeneratesAfterInput input output K ↔
      ∀ T, ∃ t, T ≤ t ∧
        (output t ∉ K ∨ output t ∈ GenLimit.Generic.sample input (t + 1)) := by
  simp only [SampleFreshGeneratesAfterInput]
  push_neg
  constructor
  · intro h T
    obtain ⟨t, ht, hfail⟩ := h T
    refine ⟨t, ht, ?_⟩
    by_cases hK : output t ∈ K
    · exact Or.inr (hfail hK)
    · exact Or.inl hK
  · intro h T
    obtain ⟨t, ht, hfail⟩ := h T
    refine ⟨t, ht, ?_⟩
    intro hK
    rcases hfail with hnotK | hsample
    · exact False.elim (hnotK hK)
    · exact hsample

theorem novel_after_input_implies_sample_fresh {α : Type*}
    {input output : Stream α} {K : Language α}
    (h : NovelGeneratesAfterInput input output K) :
    SampleFreshGeneratesAfterInput input output K := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun t ht => ⟨(hT t ht).1, (hT t ht).2.1⟩⟩

end Stage3Case019
