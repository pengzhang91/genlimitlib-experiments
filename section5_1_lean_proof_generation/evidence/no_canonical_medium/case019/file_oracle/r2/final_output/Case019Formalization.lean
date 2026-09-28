import output.Helpers

open Stage3Case019

/-- Checked portion of the separation clause: the supplied finite-omission
class is extensionally uncountable, all its members are infinite, and every
semantic generator fails the required sample-fresh guarantee at the adjacent
noise level. -/
theorem stage3_separation_obstruction (q : ℕ) :
    let family : LanguageClass ℤ :=
      GenLimit.NoiseLossFeedback.finiteOmissionClass q
    ¬family.Countable ∧
      (∀ K ∈ family, K.Infinite) ∧
      (∀ gen : Generator ℤ,
        ∃ K ∈ family, ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K) := by
  dsimp
  exact ⟨Stage3Case019Proof.finiteOmissionClass_not_countable q,
    GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q,
    Stage3Case019Proof.finiteNoiseLevel_sampleFresh_failure q⟩
