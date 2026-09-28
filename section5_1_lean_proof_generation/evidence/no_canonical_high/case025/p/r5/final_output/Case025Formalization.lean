import Helpers

open Stage3Case025

/-- Fully checked transfer from exact positive presentations to presentations
with finitely many off-target occurrence rounds. -/
theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hfamily
  obtain ⟨gen, hgen⟩ := hpositive (expandedFamily family)
    (expandedFamily_infinite family hfamily)
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  let F := badValueFinset input (family i) hpresentation.2
  have hpresents : GenLimit.Presents input
      (expandedFamily family (Encodable.encode (i, F.toList))) := by
    rw [expandedFamily_encode]
    exact presents_expanded_of_complete input (family i) hpresentation
  obtain ⟨output, hfollows, hnovel, hdensity⟩ :=
    hgen (Encodable.encode (i, F.toList)) input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · rcases hnovel with ⟨T, hT⟩
    obtain ⟨T', hT'⟩ := eventually_avoid_finset_of_novel hT F
    refine ⟨max T T', ?_⟩
    intro t htt
    have htT : T ≤ t := (le_max_left T T').trans htt
    have htT' : T' ≤ t := (le_max_right T T').trans htt
    have hout := hT t htT
    have hnotF := hT' t htT'
    rw [expandedFamily_encode] at hout
    exact ⟨hout.1.resolve_right hnotF, hout.2.1, hout.2.2⟩
  · rw [expandedFamily_encode] at hdensity
    apply relativeLowerDensity_finite_perturbation
      (A := GenLimit.GeneratorFirst input output ∩ family i)
      (A' := GenLimit.GeneratorFirst input output ∩ (family i ∪ (F : Set ℕ)))
      (K := family i) F (hfamily i)
    · exact Set.inter_subset_right
    · intro x hx
      rcases hx with ⟨hfirst, hxK | hxF⟩
      · exact Set.mem_union_left _ ⟨hfirst, hxK⟩
      · exact Set.mem_union_right _ hxF
    · exact hdensity
