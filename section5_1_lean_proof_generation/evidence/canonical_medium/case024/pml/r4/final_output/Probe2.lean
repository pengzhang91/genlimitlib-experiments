import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
open Filter MeasureTheory
open scoped Topology
namespace X
abbrev squares : Set ℕ := {n | GenLimit.InfiniteContamination.SparseSquare n}
lemma sparseSquare_infinite : squares.Infinite := by
  exact Set.infinite_range_of_injective (f := fun n : ℕ => n * n) (by
    intro a b h
    nlinarith) |>.mono (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, rfl⟩)
end X
