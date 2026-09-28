import Stage3Model
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Stage3Case025

namespace Case025

open GenLimit

open GenLimit.InfiniteContamination

 theorem novelGeneratesInLimit_of_finite_extraneous
    {input output : Stream} {K E : GenLimit.Language}
    (hP : Presents input E) (hfinite : (E \ K).Finite)
    (hnovel : NovelGeneratesInLimit input output E) :
    NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hnovel
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hP hfinite.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hfinite).mp hx).1)
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have htGenerate : Tgenerate ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨hmemE, hfresh, hnovelOut⟩ := hTgenerate t htGenerate
  refine ⟨?_, hfresh, hnovelOut⟩
  by_contra hnotK
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hmemE, hnotK⟩
  have hseenAt : output t ∈ GenLimit.sample input Tseen := by
    simpa [GenLimit.Generic.sample, GenLimit.sample] using hTseen hbad
  exact hfresh (GenLimit.sample_mono (htSeen.trans (Nat.le_succ t)) hseenAt)

theorem transfer_test
    (hpositive : PositivePresentationHalfDensity)
    (hdensityTransfer : ∀ {A K E : Set ℕ}, K.Infinite → K ⊆ E → (E \ K).Finite →
      GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E ≤
        GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K) :
    PresentationDependentHalfDensity := by
  intro family hinfinite
  let O : OracleFamily :=
    { language := family
      infinite' := hinfinite
      query := fun i x => by
        classical
        exact if x ∈ family i then true else false
      query_spec := by
        classical
        intro i x
        simp }
  let expandedO := finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hpositive expandedO.language expandedO.infinite'
  refine ⟨gen, ?_⟩
  intro i input hcontam
  let noiseFinite := displayedNoise_finite hcontam.2
  let data : FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm noiseFinite.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := encodeFiniteExpansionCode data
  have hnoiseSet :
      (↑noiseFinite.toFinset : Set ℕ) = displayedNoise input (family i) :=
    Set.Finite.coe_toFinset noiseFinite
  have homissions : displayedOmissions input (family i) = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact hx.2 (hcontam.1 hx.1)
  have hP : Presents input (expandedO.language j) := by
    change Set.range input = finiteExpansionLanguage O j
    rw [finiteExpansionLanguage]
    simp only [j, data, finiteExpansionCode_encode, Equiv.apply_symm_apply]
    rw [hnoiseSet]
    simp only [Finset.coe_empty]
    rw [← homissions]
    exact (finiteExpansion_displayedNoise_displayedOmissions
      input (family i)).symm
  obtain ⟨output, hfollows, hnovel, hdenseExpanded⟩ := hgen j input hP
  refine ⟨output, hfollows, ?_, ?_⟩
  · have hfinite : (expandedO.language j \ family i).Finite := by
      rw [← hP]
      exact displayedNoise_finite hcontam.2
    exact novelGeneratesInLimit_of_finite_extraneous hP hfinite hnovel
  · have hKE : family i ⊆ expandedO.language j := by
      intro x hx
      rw [← hP]
      exact hcontam.1 hx
    have hfinite : (expandedO.language j \ family i).Finite := by
      rw [← hP]
      exact displayedNoise_finite hcontam.2
    exact hdenseExpanded.trans
      (hdensityTransfer (hinfinite i) hKE hfinite)

end Case025
