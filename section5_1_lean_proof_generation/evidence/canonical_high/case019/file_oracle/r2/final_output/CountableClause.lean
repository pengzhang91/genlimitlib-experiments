import DensityTransfer

open Set Filter

namespace Stage3Case019

noncomputable section

private noncomputable def oracleOfFamily (family : LanguageFamily ℕ)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem finiteContamination_of_level
    {input : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
      input K := by
  refine ⟨h.1, ?_, ?_⟩
  · apply (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective h.1).mpr
    exact (GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
      (Set.range input) K q).mp h.2.2 |>.1
  · have hempty : K \ Set.range input = ∅ := by
      exact Set.diff_eq_empty.mpr h.2.1
    rw [GenLimit.InfiniteContamination.FiniteOmissions, hempty]
    exact Set.finite_empty

private theorem patient_novel_transfer
    (O : GenLimit.OracleFamily) (input : Stream ℕ) {j : ℕ}
    {K : Set ℕ}
    (hpatient :
      (∃ T, ∀ t, T ≤ t →
        GenLimit.PatientMachine.output O input t ∈ O.language j ∧
        (∀ s, s ≤ t → input s ≠ GenLimit.PatientMachine.output O input t) ∧
        (∀ s, s < t → GenLimit.PatientMachine.output O input s ≠
          GenLimit.PatientMachine.output O input t)))
    (hfinite : (O.language j \ K).Finite) :
    GenLimit.NovelGeneratesInLimit input
      (GenLimit.PatientMachine.output O input) K := by
  let badTimes : Set ℕ :=
    (GenLimit.PatientMachine.output O input) ⁻¹' (O.language j \ K)
  have hbad : badTimes.Finite := by
    exact hfinite.preimage
      (GenLimit.PatientMachine.output_injective O input).injOn
  let B := hbad.toFinset.sup id + 1
  obtain ⟨T, hT⟩ := hpatient
  refine ⟨max T B, ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (Nat.le_max_left _ _) ht
  obtain ⟨hE, hsamp, hnovel⟩ := hT t htT
  have hnotbad : t ∉ badTimes := by
    intro htb
    have hmem : t ∈ hbad.toFinset := hbad.mem_toFinset.mpr htb
    have hle : t ≤ hbad.toFinset.sup id := Finset.le_sup (f := id) hmem
    have hBt : B ≤ t := le_trans (Nat.le_max_right _ _) ht
    dsimp [B] at hBt
    omega
  refine ⟨?_, ?_, hnovel⟩
  · by_contra hK
    exact hnotbad ⟨hE, hK⟩
  · intro hs
    obtain ⟨s, hslt, hsi⟩ := GenLimit.mem_sample_iff.mp hs
    exact hsamp s (Nat.le_of_lt_succ hslt) hsi

/-- The countable-family half-density milestone. -/
theorem stage3_countable_half_density : CountableClause := by
  intro q family hinf
  let base := oracleOfFamily family hinf
  let expanded :=
    GenLimit.InfiniteContamination.finiteExpansionOracleFamily base
  refine ⟨patientGenerator expanded, ?_⟩
  intro i input hlevel
  have hcontam := finiteContamination_of_level hlevel
  obtain ⟨j, hj, hpresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream
      base hcontam
  have hpatient :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      expanded input hpresents
  have hKE : family i ⊆ expanded.language j := by
    rw [GenLimit.Generic.Presents] at hpresents
    rw [← hpresents]
    exact hlevel.2.1
  have hfinite : (expanded.language j \ family i).Finite := by
    rw [GenLimit.Generic.Presents] at hpresents
    rw [← hpresents]
    exact (GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
      (Set.range input) (family i) q).mp hlevel.2.2 |>.1
  constructor
  · rw [show outputAfterInput (patientGenerator expanded) input =
        GenLimit.PatientMachine.output expanded input by
      funext t
      exact patientGenerator_output expanded input t]
    exact patient_novel_transfer expanded input hpatient.1 hfinite
  · have hd := relativeLowerDensity_finiteExtension
      (A := GenLimit.GeneratorFirst input
        (GenLimit.PatientMachine.output expanded input) ∩ expanded.language j)
      (hinf i) hKE inter_subset_right hfinite
    have hset :
        ((GenLimit.GeneratorFirst input
            (GenLimit.PatientMachine.output expanded input) ∩ expanded.language j) ∩
          family i) =
        GenLimit.GeneratorFirst input
            (GenLimit.PatientMachine.output expanded input) ∩ family i := by
      ext x
      constructor
      · rintro ⟨⟨hx, _⟩, hxi⟩
        exact ⟨hx, hxi⟩
      · rintro ⟨hx, hxi⟩
        exact ⟨⟨hx, hKE hxi⟩, hxi⟩
    rw [hset] at hd
    have hhalf : (1 / 2 : ℝ) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input
              (GenLimit.PatientMachine.output expanded input) ∩
            expanded.language j)
          (expanded.language j) := hpatient.2
    rw [show outputAfterInput (patientGenerator expanded) input =
        GenLimit.PatientMachine.output expanded input by
      funext t
      exact patientGenerator_output expanded input t]
    exact hhalf.trans hd

end

end Stage3Case019
