import Stage3Model
import Case025Helpers

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable section

 theorem finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let expanded : ℕ → Language := finiteAdditionLanguage family
  have hExpandedInfinite : ∀ j, (expanded j).Infinite :=
    finiteAdditionLanguage_infinite family hInfinite
  obtain ⟨gen, hgen⟩ := hpositive expanded hExpandedInfinite
  refine ⟨gen, ?_⟩
  intro i input hPresentation
  let K : Language := family i
  let R : Language := Set.range input
  have hKR : K ⊆ R := hPresentation.1
  have hNoise : (R \ K).Finite :=
    GenLimit.InfiniteContamination.displayedNoise_finite hPresentation.2
  let noiseCode : ℕ :=
    Finset.equivBitIndices.symm hNoise.toFinset
  let j : ℕ := encodeFiniteAddition i noiseCode
  have hPresents : GenLimit.Presents input (expanded j) := by
    change R = finiteAdditionLanguage family j
    rw [show j = encodeFiniteAddition i noiseCode from rfl]
    rw [finiteAdditionLanguage_encode]
    change R = K ∪ (Finset.equivBitIndices noiseCode : Set ℕ)
    rw [show Finset.equivBitIndices noiseCode = hNoise.toFinset by
      exact Equiv.apply_symm_apply Finset.equivBitIndices hNoise.toFinset]
    rw [show (↑hNoise.toFinset : Set ℕ) = R \ K from
      Set.Finite.coe_toFinset hNoise]
    exact (Set.union_diff_cancel hKR).symm
  obtain ⟨output, hFollows, hNovelExpanded, hDensityExpanded⟩ :=
    hgen j input hPresents
  have hExpandedEq : expanded j = R := hPresents.symm
  have hNovelRange : GenLimit.NovelGeneratesInLimit input output R := by
    rw [← hExpandedEq]
    exact hNovelExpanded
  have hDensityRange :
      (1 / 2 : ℝ) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ R) R := by
    rw [← hExpandedEq]
    exact hDensityExpanded
  refine ⟨output, hFollows, ?_, ?_⟩
  · classical
    obtain ⟨Tgenerate, hTgenerate⟩ := hNovelRange
    obtain ⟨Tseen, hTseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample
        (GenLimit.InfiniteContamination.stream_presents_range input)
        hNoise.toFinset (by
          intro x hx
          exact ((Set.Finite.mem_toFinset hNoise).mp hx).1)
    refine ⟨max Tgenerate Tseen, ?_⟩
    intro t ht
    have htGenerate : Tgenerate ≤ t := (Nat.le_max_left _ _).trans ht
    have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
    obtain ⟨hmemR, hfresh, hdistinct⟩ := hTgenerate t htGenerate
    refine ⟨?_, hfresh, hdistinct⟩
    by_contra hnotK
    have hbad : output t ∈ hNoise.toFinset :=
      (Set.Finite.mem_toFinset hNoise).mpr ⟨hmemR, hnotK⟩
    have hseen := hTseen hbad
    rw [GenLimit.Generic.mem_sample_iff] at hseen
    obtain ⟨s, hsTseen, hsOutput⟩ := hseen
    apply hfresh
    rw [GenLimit.mem_sample_iff]
    exact ⟨s, lt_of_lt_of_le hsTseen (htSeen.trans (Nat.le_succ t)), hsOutput⟩
  · exact hDensityRange.trans
      (relativeLowerDensity_enlargement_le
        (GenLimit.GeneratorFirst input output) K R
        (hInfinite i) hKR hNoise)

end

end Stage3Case025

open Stage3Case025

 theorem stage3_result : Stage3Case025.MainClaim := by
  exact finite_noise_transfer positive_engine
