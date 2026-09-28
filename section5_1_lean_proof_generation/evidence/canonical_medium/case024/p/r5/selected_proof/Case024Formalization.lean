import Family

open Filter MeasureTheory
open scoped Topology

noncomputable section
open Classical
open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Squares, Set.univ, input, ?_, legal_squares, legal_univ, ?_⟩
    · refine ⟨Set.subset_univ _, fun hreverse => ?_⟩
      exact gap_not_square 0 (hreverse (Set.mem_univ (gap 0)))
    · unfold Stage3Case024.PairObstruction
      intro Ω _ μ _ gen output hfollow hmeas hint0 hint1 hvalid0 hvalid1
      have hu := expected_univ_zero μ input output hvalid0
      have hle := expected_le_one μ Squares input output hint0
      constructor
      · rw [hu, add_zero]
        exact hle
      · intro hhalf
        rw [hu] at hhalf
        linarith
  · intro r hr
    exact ⟨family, input, manyTargetWitness hr⟩

end
