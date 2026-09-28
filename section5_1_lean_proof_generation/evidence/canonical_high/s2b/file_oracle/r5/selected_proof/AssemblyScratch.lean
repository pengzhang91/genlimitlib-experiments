import DensityScratch

open Set Filter
open Stage3S2B

namespace Stage3Proof

noncomputable def encodedTarget (A : Set ℕ) : Language :=
  core ∪ oddValue '' A

theorem encodedTarget_mem_class (A : Set ℕ) : encodedTarget A ∈ targetClass := by
  refine ⟨oddValue '' A, ?_, rfl⟩
  rintro z ⟨k, _, rfl⟩
  exact oddValue_not_core k

theorem oddValue_mem_encodedTarget (A : Set ℕ) (k : ℕ) :
    oddValue k ∈ encodedTarget A ↔ k ∈ A := by
  constructor
  · rintro (hkcore | ⟨j, hj, heq⟩)
    · exact (oddValue_not_core k hkcore).elim
    · exact (oddValue_injective heq).symm ▸ hj
  · intro hk
    exact Or.inr ⟨k, hk, rfl⟩

theorem encodedTarget_injective : Function.Injective encodedTarget := by
  intro A B hAB
  ext k
  rw [← oddValue_mem_encodedTarget A k, ← oddValue_mem_encodedTarget B k, hAB]

theorem targetClass_not_countable : ¬ targetClass.Countable := by
  intro hclass
  have hrange : (Set.range encodedTarget).Countable := by
    apply hclass.mono
    rintro K ⟨A, rfl⟩
    exact encodedTarget_mem_class A
  have hpreimage := hrange.preimage encodedTarget_injective
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    simpa using hpreimage
  letI : Countable (Set ℕ) := Set.countable_univ_iff.mp huniv
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ inferInstance

theorem uniformly_generatable : UniformlyGeneratableWithoutSamples := by
  refine ⟨fun t => 2 ^ t, Nat.pow_right_injective (by omega : 1 < (2 : ℕ)), 0, ?_⟩
  intro K hK t _
  rcases hK with ⟨A, hA, rfl⟩
  exact Or.inl ⟨t, rfl⟩

noncomputable def builtPresenter (gen : FeedbackGenerator) : CausalPresenter := {
  next := fun t _ _ _ _ => builtPresentation gen t
}

theorem presentedBy_built (gen : FeedbackGenerator) :
    PresentedBy (builtPresenter gen) (builtTranscript gen) := by
  intro t
  rfl

theorem scored_upperDensity_zero (gen : FeedbackGenerator) :
    (orderedTarget gen).upperDensity
      (scored (builtTarget gen) (builtPresentation gen) (builtOutput gen)) = 0 := by
  apply le_antisymm
  · calc
      (orderedTarget gen).upperDensity
          (scored (builtTarget gen) (builtPresentation gen) (builtOutput gen)) ≤
          (orderedTarget gen).upperDensity core :=
        (orderedTarget gen).upperDensity_mono (scored_subset_core gen)
      _ = 0 := core_upperDensity_zero gen
  · exact (orderedTarget gen).upperDensity_nonneg _

theorem faithful_built (gen : FeedbackGenerator) :
    FaithfulNegativeWitness gen (builtTarget gen) (builtPresenter gen)
      (builtTranscript gen) (orderedTarget gen) := by
  refine ⟨rfl, orderedTarget_strictMono gen, presentedBy_built gen,
    followsProtocol_built gen, ?_, builtPresentation_injective gen,
    builtPresentation_complete gen, scored_upperDensity_zero gen⟩
  exact presentation_mem_target gen

theorem negative_claim : NegativeClaim := by
  intro gen _
  exact ⟨builtTarget gen, builtTarget_mem_class gen, builtPresenter gen,
    builtTranscript gen, orderedTarget gen, faithful_built gen⟩

end Stage3Proof

example : Stage3S2B.MainClaim := by
  exact ⟨Stage3Proof.targetClass_not_countable,
    Stage3Proof.uniformly_generatable, Stage3Proof.negative_claim⟩
