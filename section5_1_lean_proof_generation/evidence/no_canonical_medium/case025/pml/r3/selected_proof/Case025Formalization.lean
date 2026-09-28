import «output».DensityTransfer

open GenLimit
open Stage3Case025

namespace Case025Helpers

open GenLimit.InfiniteContamination

private theorem exists_expansion_index
    (O : OracleFamily) (i : ℕ) (input : Stage3Case025.Stream)
    (hcover : O.language i ⊆ Set.range input)
    (hnoise : Generic.FinitelyManyViolations input (fun x => x ∈ O.language i)) :
    ∃ j,
      finiteExpansionBaseIndex j = i ∧
      Presents input ((finiteExpansionOracleFamily O).language j) := by
  let addFinite := displayedNoise_finite hnoise
  let data : FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm addFinite.toFinset,
      Finset.equivBitIndices.symm (∅ : Finset ℕ))
  let j := encodeFiniteExpansionCode data
  refine ⟨j, ?_, ?_⟩
  · simp [finiteExpansionBaseIndex, j, data]
  · change Set.range input = finiteExpansionLanguage O j
    have hadd :
        (↑addFinite.toFinset : Set ℕ) = displayedNoise input (O.language i) :=
      Set.Finite.coe_toFinset addFinite
    rw [finiteExpansionLanguage]
    simp only [j, data, finiteExpansionCode_encode, Equiv.apply_symm_apply]
    rw [hadd]
    simp only [finiteExpansion, Finset.coe_empty, Set.diff_empty]
    ext x
    simp only [displayedNoise, Set.mem_diff, Set.mem_union, Set.mem_range]
    constructor
    · intro hx
      by_cases hxL : x ∈ O.language i
      · exact Or.inl hxL
      · exact Or.inr ⟨hx, hxL⟩
    · rintro (hxL | ⟨hx, _⟩)
      · exact hcover hxL
      · exact hx

private theorem novel_transfer
    {input output : Stage3Case025.Stream} {K E : Set ℕ}
    (hP : Presents input E) (hfinite : (E \ K).Finite)
    (hNovel : NovelGeneratesInLimit input output E) :
    NovelGeneratesInLimit input output K := by
  obtain ⟨Tgenerate, hTgenerate⟩ := hNovel
  obtain ⟨Tseen, hTseen⟩ :=
    Generic.finset_eventually_subset_sample hP hfinite.toFinset (by
      intro x hx
      exact (Set.Finite.mem_toFinset hfinite |>.mp hx).1)
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have htGenerate : Tgenerate ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨hE, hfresh, hdistinct⟩ := hTgenerate t htGenerate
  refine ⟨?_, hfresh, hdistinct⟩
  by_contra hK
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hE, hK⟩
  have hseenAt : output t ∈ Generic.sample input Tseen := hTseen hbad
  have hsampleEq :
      sample input (t + 1) = Generic.sample input (t + 1) := by
    classical
    ext x
    simp only [sample, Generic.sample, Finset.mem_image, Finset.mem_range]
  exact hfresh (by
    rw [hsampleEq]
    exact Generic.sample_mono (htSeen.trans (Nat.le_succ t)) hseenAt)

 theorem finiteNoiseTransfer : FiniteNoiseTransferPrinciple := by
  intro _positiveEngine
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  let expanded := finiteExpansionOracleFamily O
  refine ⟨patientOnline expanded, ?_⟩
  intro i input hPresentation
  obtain ⟨j, hjBase, hP⟩ :=
    exists_expansion_index O i input hPresentation.1 hPresentation.2
  let output := PatientMachine.output expanded input
  obtain ⟨hNovelExpanded, hDensityExpanded⟩ :=
    PatientMachine.patientScope_generation_and_lowerDensity expanded input hP
  have hRange : expanded.language j = Set.range input := hP.symm
  have hfinite : (expanded.language j \ family i).Finite := by
    rw [hRange]
    exact displayedNoise_finite hPresentation.2
  have hNovelExpanded' :
      NovelGeneratesInLimit input output (expanded.language j) := by
    obtain ⟨T, hT⟩ := hNovelExpanded
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hinput, houtput⟩ := hT t ht
    refine ⟨hmem, ?_, houtput⟩
    intro hsample
    rw [mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact hinput s (Nat.lt_succ_iff.mp hs) heq
  refine ⟨output, patientOnline_follows expanded input, ?_, ?_⟩
  · exact novel_transfer hP hfinite hNovelExpanded'
  · apply relativeLowerDensity_finite_extension
      (GeneratorFirst input output) (family i) (expanded.language j)
      (hInfinite i)
    · intro x hx
      rw [hRange]
      exact hPresentation.1 hx
    · exact hfinite
    · exact hDensityExpanded

end Case025Helpers

 theorem stage3_result : Stage3Case025.MainClaim := by
  exact Case025Helpers.finiteNoiseTransfer Case025Helpers.positiveEngine
