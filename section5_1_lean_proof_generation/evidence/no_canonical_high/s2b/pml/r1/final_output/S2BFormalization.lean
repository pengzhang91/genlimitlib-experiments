import Helpers
import Density

namespace Stage3Work

open Stage3S2B

noncomputable def diagonalPresenter (gen : FeedbackGenerator) : CausalPresenter where
  next t _ _ _ _ := (diagonalTranscript gen).presentation t

theorem diagonal_presentedBy (gen : FeedbackGenerator) :
    PresentedBy (diagonalPresenter gen) (diagonalTranscript gen) := by
  intro t
  rfl

theorem diagonal_scored_subset_core (gen : FeedbackGenerator) :
    scored (diagonalTarget gen) (diagonalTranscript gen).presentation
      (diagonalTranscript gen).output ⊆ core := by
  intro z hz
  rcases hz with ⟨hzTarget, t, hy, hfresh⟩
  by_contra hzCore
  have hzOrdinary : z ∈ ordinary := hzCore
  exact (fresh_ordinary_output_not_mem_target gen hy hfresh hzOrdinary) hzTarget

theorem diagonal_scored_upperDensity_zero (gen : FeedbackGenerator) :
    (diagonalOrdered gen).upperDensity
      (scored (diagonalTarget gen) (diagonalTranscript gen).presentation
        (diagonalTranscript gen).output) = 0 := by
  apply le_antisymm
  · calc
      (diagonalOrdered gen).upperDensity
          (scored (diagonalTarget gen) (diagonalTranscript gen).presentation
            (diagonalTranscript gen).output) ≤
          (diagonalOrdered gen).upperDensity core :=
        (diagonalOrdered gen).upperDensity_mono (diagonal_scored_subset_core gen)
      _ = 0 := diagonal_core_upperDensity_zero gen
  · exact (diagonalOrdered gen).upperDensity_nonneg _

theorem negative_claim : NegativeClaim := by
  intro gen _
  refine ⟨diagonalTarget gen, diagonalTarget_mem gen,
    diagonalPresenter gen, diagonalTranscript gen, diagonalOrdered gen, ?_⟩
  refine ⟨rfl, diagonalOrdered_ambient gen, diagonal_presentedBy gen,
    diagonal_follows_protocol gen, diagonal_clean gen,
    diagonal_presentation_injective gen, diagonal_complete gen, ?_⟩
  exact diagonal_scored_upperDensity_zero gen

end Stage3Work

theorem stage3_result : Stage3S2B.MainClaim := by
  exact ⟨Stage3Work.targetClass_uncountable,
    Stage3Work.uniform_generation, Stage3Work.negative_claim⟩
