import «output».Helpers

open Set Filter
open scoped Topology

namespace Stage3Case019

noncomputable def oracleOfFamily
    (family : LanguageFamily ℕ) (hinf : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

noncomputable def extendHistory {n : ℕ} (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if h : k < n then xs ⟨k, h⟩ else 0

noncomputable def patientGenerator (O : GenLimit.OracleFamily) : Generator ℕ :=
  fun n xs =>
    match n with
    | 0 => 0
    | t + 1 => GenLimit.PatientMachine.output O (extendHistory xs) t

theorem extendHistory_agrees {input : Stream ℕ} {n : ℕ} :
    AgreeBelow (extendHistory (fun i : Fin n => input i)) input n := by
  intro k hk
  simp [extendHistory, hk]

theorem patientGenerator_outputAfterInput
    (O : GenLimit.OracleFamily) (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (patientGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  unfold outputAfterInput GenLimit.Generic.output patientGenerator
  exact patient_output_eq_of_agreeBelow O extendHistory_agrees

theorem finiteContamination_of_atMost
    {input : Stream ℕ} {K : Language ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration input K := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective h.1]
    obtain ⟨F, hF, _⟩ := h.2.2
    rw [← hF]
    exact F.finite_toSet
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty



theorem relativeLowerDensity_transfer
    {D K E : Set ℕ} (hKinf : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (D ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  let output : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  have hEinf : E.Infinite := hKinf.mono hKE
  have herror : Tendsto error atTop (nhds 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.comp
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hEinf)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n := by
    have hKpos : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hKinf).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hKpos] with n hn
    have hEpos : 0 < GenLimit.PatientScope.prefixCount E n :=
      lt_of_lt_of_le hn (GenLimit.PatientScope.prefixCount_mono hKE n)
    have hcountDiff :
        GenLimit.PatientScope.prefixCount (D ∩ E) n ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n +
            hfinite.toFinset.card := by
      classical
      unfold GenLimit.PatientScope.prefixCount
      calc
        (GenLimit.PatientScope.prefixFinset (D ∩ E) n).card ≤
            (GenLimit.PatientScope.prefixFinset (D ∩ K) n ∪
              GenLimit.PatientScope.prefixFinset (E \ K) n).card := by
          apply Finset.card_le_card
          intro x hx
          rw [GenLimit.PatientScope.mem_prefixFinset] at hx
          rw [Finset.mem_union]
          by_cases hxK : x ∈ K
          · left
            rw [GenLimit.PatientScope.mem_prefixFinset]
            exact ⟨hx.1, hx.2.1, hxK⟩
          · right
            rw [GenLimit.PatientScope.mem_prefixFinset]
            exact ⟨hx.1, hx.2.2, hxK⟩
        _ ≤ (GenLimit.PatientScope.prefixFinset (D ∩ K) n).card +
              (GenLimit.PatientScope.prefixFinset (E \ K) n).card :=
          Finset.card_union_le _ _
        _ ≤ (GenLimit.PatientScope.prefixFinset (D ∩ K) n).card +
              hfinite.toFinset.card := by
          apply Nat.add_le_add_left
          apply Finset.card_le_card
          intro x hx
          rw [GenLimit.PatientScope.mem_prefixFinset] at hx
          exact Set.Finite.mem_toFinset hfinite |>.2 hx.2
    have hcountR :
        (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n +
            hfinite.toFinset.card := by exact_mod_cast hcountDiff
    have hden :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount E n := by
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hKE n
    have hnum : (0 : ℝ) ≤ GenLimit.PatientScope.prefixCount (D ∩ K) n := by positivity
    dsimp only [source, output, error]
    calc
      (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) /
          GenLimit.PatientScope.prefixCount E n ≤
        ((GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) +
          hfinite.toFinset.card) /
            GenLimit.PatientScope.prefixCount E n :=
        div_le_div_of_nonneg_right hcountR (by positivity)
      _ = (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount E n + error n := by
        rw [add_div]
      _ ≤ (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n + error n := by
        gcongr
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf source atTop ≤ liminf output atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (fun n => by
      dsimp [output]
      exact div_le_one_of_le₀ (by
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono
          (Set.inter_subset_right) n) (by positivity)))
    (isBoundedUnder_of ⟨0, fun n => by positivity⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, fun n => by dsimp [source]; positivity⟩)
  have herrEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrEventually, hprefix] with n hrs herr hp
  linarith


theorem finite_subset_range_eventually_seen
    {input : Stream ℕ} {F : Set ℕ} (hF : F.Finite)
    (hsub : F ⊆ Set.range input) :
    ∃ T, ∀ x ∈ F, ∃ s, s ≤ T ∧ input s = x := by
  classical
  induction F, hF using Set.Finite.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a F ha hF ih =>
      obtain ⟨ta, hta⟩ := hsub (Set.mem_insert a F)
      have hsubF : F ⊆ Set.range input := fun x hx =>
        hsub (Set.mem_insert_of_mem a hx)
      obtain ⟨T, hT⟩ := ih hsubF
      refine ⟨max ta T, ?_⟩
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hxF
      · exact ⟨ta, Nat.le_max_left _ _, hta⟩
      · obtain ⟨s, hs, hsx⟩ := hT x hxF
        exact ⟨s, hs.trans (Nat.le_max_right _ _), hsx⟩

theorem stage3_countable_half_density : CountableClause := by
  intro q family hinf
  let O := oracleOfFamily family hinf
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hcontam
  have hfiniteContam := finiteContamination_of_atMost hcontam
  obtain ⟨j, hjBase, hjPresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream
      O hfiniteContam
  have hrun :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      E input hjPresents
  have hKE : family i ⊆ E.language j := by
    intro x hx
    rw [← hjPresents]
    exact hcontam.2.1 hx
  have hdiff : (E.language j \ family i).Finite := by
    rw [← hjPresents]
    obtain ⟨F, hF, _⟩ := hcontam.2.2
    rw [← hF]
    exact F.finite_toSet
  obtain ⟨Tnoise, hnoiseSeen⟩ :=
    finite_subset_range_eventually_seen hdiff (by
      rw [← hjPresents]
      exact Set.diff_subset)
  have houtEq : outputAfterInput (patientGenerator E) input =
      GenLimit.PatientMachine.output E input := by
    funext t
    exact patientGenerator_outputAfterInput E input t
  constructor
  · obtain ⟨Tvalid, hvalid⟩ := hrun.1
    refine ⟨max Tvalid Tnoise, ?_⟩
    intro t ht
    have htValid : Tvalid ≤ t := (Nat.le_max_left _ _).trans ht
    have htNoise : Tnoise ≤ t := (Nat.le_max_right _ _).trans ht
    obtain ⟨houtE, hfresh, hnovel⟩ := hvalid t htValid
    have houtK : GenLimit.PatientMachine.output E input t ∈ family i := by
      by_contra houtNotK
      obtain ⟨s, hsT, hsout⟩ :=
        hnoiseSeen _ ⟨houtE, houtNotK⟩
      exact hfresh s (hsT.trans htNoise) hsout
    rw [houtEq]
    refine ⟨houtK, ?_, hnovel⟩
    intro hsample
    obtain ⟨s, hs, hsout⟩ := GenLimit.mem_sample_iff.mp hsample
    exact hfresh s (Nat.lt_succ_iff.mp hs) hsout
  · rw [houtEq]
    apply le_trans hrun.2
    exact relativeLowerDensity_transfer (hinf i) hKE hdiff

end Stage3Case019
