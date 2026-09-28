import Stage3Model
import Develop

open Filter MeasureTheory
open scoped Topology

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨squares, Set.univ, swapStream, ?_, legal_swapStream_squares,
      legal_swapStream_of_superset (Set.subset_univ squares), pairObstruction_squares_univ⟩
    rw [Set.ssubset_iff_exists]
    refine ⟨(Set.subset_univ squares), marker 0, Set.mem_univ _, ?_⟩
    exact marker_not_square 0
  · intro r hr
    refine ⟨nestedFamily (r := r), swapStream, ?_⟩
    exact ⟨nestedFamily_strict hr,
      fun j => nestedFamily_legal j,
      nestedFamily_globallyFeasible,
      nestedFamily_manyTargetObstruction hr⟩
