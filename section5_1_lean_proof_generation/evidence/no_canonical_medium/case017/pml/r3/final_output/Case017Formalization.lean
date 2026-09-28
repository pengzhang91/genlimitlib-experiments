import Helpers

open Filter

namespace Stage3Case017

open GenLimit

noncomputable def oracleOfFinite {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (hinf : ∀ j, (family j).Infinite) :
    OracleFamily where
  language i := family ⟨i % m, Nat.mod_lt i hm⟩
  infinite' i := hinf ⟨i % m, Nat.mod_lt i hm⟩
  query i x := by
    classical
    exact decide (x ∈ family ⟨i % m, Nat.mod_lt i hm⟩)
  query_spec i x := by
    classical
    simp

@[simp] theorem oracleOfFinite_language_fin {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (hinf : ∀ j, (family j).Infinite)
    (j : Fin m) :
    (oracleOfFinite hm family hinf).language j = family j := by
  ext x
  simp [oracleOfFinite, Nat.mod_eq_of_lt j.isLt]

theorem relativeLowerDensity_mono {A B K : Language} (hAB : A ⊆ B)
    (hBK : B ⊆ K) :
    PatientScope.relativeLowerDensity A K ≤
      PatientScope.relativeLowerDensity B K := by
  unfold PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · filter_upwards with n
    gcongr
    exact PatientScope.prefixCount_mono hAB n
  · exact isBoundedUnder_of ⟨0, fun n => by positivity⟩
  · exact isCoboundedUnder_ge_of_le atTop (fun n => by
      have hcount := PatientScope.prefixCount_mono hBK n
      by_cases hzero : PatientScope.prefixCount K n = 0
      · have hBzero : PatientScope.prefixCount B n = 0 := by omega
        change (PatientScope.prefixCount B n : ℝ) /
          (PatientScope.prefixCount K n : ℝ) ≤ 1
        rw [hzero, hBzero]
        norm_num
      · have hpos : (0 : ℝ) < PatientScope.prefixCount K n := by
          exact_mod_cast Nat.pos_of_ne_zero hzero
        rw [div_le_one hpos]
        exact_mod_cast hcount)

theorem core_subset_closure_focus {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (hinf : ∀ j, (family j).Infinite)
    (input : Stream) (hP : Presents input (Set.range input))
    {j₀ : Fin m} (hsub₀ : Set.range input ⊆ family j₀) :
    ∃ T, ∀ t, T ≤ t →
      informationCore family input ⊆
        (PartialEnumeration.closure (oracleOfFinite hm family hinf)).language
          (PatientMachine.run
            (PartialEnumeration.closure (oracleOfFinite hm family hinf)) input t).focus := by
  let O := oracleOfFinite hm family hinf
  obtain ⟨T, hstable⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := O.language) hP m
  refine ⟨T, ?_⟩
  intro t ht x hx
  have hsubO : Set.range input ⊆ O.language j₀ := by
    simpa [O] using hsub₀
  have hOn : PatientMachine.OnModel (PartialEnumeration.closure O) input :=
    PartialEnumeration.closure_onModel O hP hsubO
  have hfocus := PatientMachine.run_focus_isFocus_of_onModel
    (PartialEnumeration.closure O) hOn t
  have hcon : Consistent (PartialEnumeration.closure O).language input t
      (PatientMachine.run (PartialEnumeration.closure O) input t).focus :=
    recursiveCritical_consistent hfocus.2.1
  rw [PartialEnumeration.closure_language]
  intro k hk
  have hkcon : Consistent O.language input t k := by
    intro y hy
    have hy' := hcon hy
    rw [PartialEnumeration.closure_language] at hy'
    exact hy' k hk
  let q : Fin m := ⟨k % m, Nat.mod_lt k hm⟩
  have hqcon : Consistent O.language input t q := by
    intro y hy
    have hy' := hkcon hy
    simpa [O, oracleOfFinite, q, Nat.mod_mod] using hy'
  have hrange : Set.range input ⊆ O.language q :=
    (hstable t ht q q.isLt).1 hqcon
  have hstream : Generic.StreamIn input (family q) := by
    rintro y ⟨s, rfl⟩
    have := hrange ⟨s, rfl⟩
    simpa [O] using this
  have hxq : x ∈ family q := hx q hstream
  simpa [O, oracleOfFinite, q, Nat.mod_mod] using hxq


theorem core_diff_range_subset_generatorFirst {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (hinf : ∀ j, (family j).Infinite)
    (input : Stream) {j₀ : Fin m} (hsub₀ : Set.range input ⊆ family j₀) :
    informationCore family input \ Set.range input ⊆
      GeneratorFirst input
        (PatientMachine.output
          (PartialEnumeration.closure (oracleOfFinite hm family hinf)) input) := by
  intro x hx
  let O := oracleOfFinite hm family hinf
  have hP : Presents input (Set.range input) := rfl
  obtain ⟨T, hcore⟩ :=
    core_subset_closure_focus hm family hinf input hP hsub₀
  have hexists : ∃ t,
      PatientMachine.output (PartialEnumeration.closure O) input t = x := by
    by_contra hnone
    let f : ℕ → ℕ := fun n =>
      PatientMachine.output (PartialEnumeration.closure O) input (T + n)
    have hfinj : Function.Injective f := by
      intro a b hab
      have htime := PatientMachine.output_injective
        (PartialEnumeration.closure O) input hab
      omega
    have hbound : Set.range f ⊆ Set.Iic x := by
      rintro y ⟨n, rfl⟩
      apply PatientMachine.output_minimal_post_focus
      refine ⟨?_, ?_, ?_⟩
      · exact hcore (T + n + 1) (by omega) hx.1
      · intro hxsample
        rw [mem_sample_iff] at hxsample
        obtain ⟨s, -, hs⟩ := hxsample
        exact hx.2 ⟨s, hs⟩
      · intro hxused
        rw [PatientMachine.run_used_eq_outputsBefore] at hxused
        rcases Finset.mem_image.mp hxused with ⟨s, hs, hsx⟩
        exact hnone ⟨s, hsx⟩
    exact (Set.infinite_range_of_injective hfinj)
      ((Set.finite_Iic x).subset hbound)
  obtain ⟨t, htx⟩ := hexists
  refine ⟨t, htx, ?_⟩
  intro s hs hinput
  exact hx.2 ⟨s, hinput⟩


theorem core_half_density {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (hinf : ∀ j, (family j).Infinite)
    (input : Stream) (hE : (Set.range input).Infinite)
    {j : Fin m} (hsub : Set.range input ⊆ family j) :
    (1 / 2 : ℝ) * PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      PatientScope.relativeLowerDensity
        (GeneratorFirst input
          (PatientMachine.output
            (PartialEnumeration.closure (oracleOfFinite hm family hinf)) input) ∩
          family j) (family j) := by
  let O := oracleOfFinite hm family hinf
  have hP : Presents input (Set.range input) := rfl
  have hsubO : Set.range input ⊆ O.language j := by
    simpa [O] using hsub
  obtain ⟨S⟩ := PartialEnumeration.stableTargetRun_nonempty
    O hP hE hsubO
  let P := S.partialCertificate hP hsubO
  have hPtarget : P.target = O.language j := rfl
  have hPenumerated : P.enumerated = Set.range input := rfl
  have hPdefender : P.defender =
      GeneratorFirst input
        (PatientMachine.output (PartialEnumeration.closure O) input) := rfl
  have hcoreTarget : informationCore family input ⊆ family j := by
    intro x hx
    exact hx j hsub
  let Q : PatientScope.PartialEnumerationCertificate :=
    { P with
      enumerated := informationCore family input
      enumerated_subset_target := by
        rw [hPtarget]
        simpa [O] using hcoreTarget
      enumerated_covered := by
        intro x hx
        by_cases hxr : x ∈ Set.range input
        · apply P.enumerated_covered
          rw [hPenumerated]
          exact hxr
        · apply Set.mem_union_right
          change x ∈ GeneratorFirst input
            (PatientMachine.output (PartialEnumeration.closure O) input)
          exact core_diff_range_subset_generatorFirst hm family hinf input hsub
            ⟨hx, hxr⟩ }
  have hInfinite : Q.target.Infinite := by
    rw [show Q.target = P.target from rfl, hPtarget]
    simpa [O] using hinf j
  have hlog : ∀ n, PatientScope.prefixCount Q.switchLoss n ≤
      Nat.log2 (Q.targetCount n) := by
    intro n
    simpa [Q] using S.partialCertificate_switch_log hP hsubO n
  have hdensity :=
    PatientScope.PartialEnumerationCertificate.theorem_3_17
      Q hInfinite hlog
  change (1 / 2 : ℝ) * PatientScope.relativeLowerDensity
      (informationCore family input) (O.language j) ≤
    PatientScope.relativeLowerDensity (P.defender ∩ O.language j) (O.language j)
    at hdensity
  rw [hPdefender] at hdensity
  simpa [O] using hdensity

end Stage3Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinf
  let O := Stage3Case017.oracleOfFinite hm family hinf
  refine ⟨Stage3Case017.patientOnlineGenerator O, ?_⟩
  intro input hinjective hexists hcoreInfinite
  let output := GenLimit.PatientMachine.output
    (GenLimit.PartialEnumeration.closure O) input
  refine ⟨output, ?_, ?_⟩
  · exact Stage3Case017.patientOnlineGenerator_follows O input
  · intro j hstream
    have hE : (Set.range input).Infinite :=
      Set.infinite_range_of_injective hinjective
    have hsub : Set.range input ⊆ family j := hstream
    have hsubO : Set.range input ⊆ O.language j := by
      simpa [O] using hsub
    obtain ⟨T, hgeneration⟩ :=
      GenLimit.PartialEnumeration.lemma_3_16_generation
        O (E := Set.range input) rfl hE hsubO
    have hnovel : GenLimit.NovelGeneratesInLimit input output (family j) := by
      refine ⟨T, ?_⟩
      intro t ht
      obtain ⟨hvalid, hfresh, hdistinct⟩ := hgeneration t ht
      refine ⟨?_, ?_, ?_⟩
      · simpa [output, O] using hvalid
      · intro hsample
        rw [GenLimit.mem_sample_iff] at hsample
        obtain ⟨s, hs, heq⟩ := hsample
        exact hfresh s (by omega) heq
      · intro s hs
        exact hdistinct s hs
    have hhalf := Stage3Case017.core_half_density
      hm family hinf input hE hsub
    have hmissing :
        GenLimit.PatientScope.relativeLowerDensity
            (Stage3Case017.informationCore family input \ Set.range input)
            (family j) ≤
          GenLimit.PatientScope.relativeLowerDensity
            (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
      apply Stage3Case017.relativeLowerDensity_mono
      · intro x hx
        refine ⟨?_, hx.1 j hstream⟩
        change x ∈ GenLimit.GeneratorFirst input
          (GenLimit.PatientMachine.output
            (GenLimit.PartialEnumeration.closure O) input)
        exact Stage3Case017.core_diff_range_subset_generatorFirst
          hm family hinf input hsub hx
      · exact Set.inter_subset_right
    refine ⟨hnovel, max_le ?_ hmissing⟩
    simpa [output, O] using hhalf
