import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Stage3Case025Proof

open Stage3Case025

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hinf : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact decide (x ∈ family i)
  query_spec i x := by
    classical
    simp

noncomputable def extendPrefix {t : ℕ} (xs : Fin t → ℕ) : Stream :=
  fun n => if h : n < t then xs ⟨n, h⟩ else 0

@[simp] theorem extendPrefix_apply {t : ℕ} (xs : Fin t → ℕ)
    (n : ℕ) (hn : n < t) :
    extendPrefix xs n = xs ⟨n, hn⟩ := by
  simp [extendPrefix, hn]

private theorem sample_eq_of_eq_on_prefix
    {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

private theorem consistent_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t i : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.Consistent C stream₁ t i ↔ GenLimit.Consistent C stream₂ t i := by
  unfold GenLimit.Consistent
  rw [sample_eq_of_eq_on_prefix h]

private theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    ∀ i, GenLimit.RecursiveCritical C stream₁ t i ↔
      GenLimit.RecursiveCritical C stream₂ t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using
          consistent_congr C h (i := 0)
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨(consistent_congr C h).1 hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjcrit)
          · rintro ⟨hcon, hsub⟩
            refine ⟨(consistent_congr C h).2 hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjcrit)

private theorem consistentIndices_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.consistentIndices C stream₁ t scope =
      GenLimit.PatientMachine.consistentIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_congr C h]

private theorem criticalIndices_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.criticalIndices C stream₁ t scope =
      GenLimit.PatientMachine.criticalIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_congr C h i]

private theorem survivingCriticalIndices_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.survivingCriticalIndices C stream₁ t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr C
      (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t))) i,
    recursiveCritical_congr C h i]

private theorem highestCritical_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream}
    {t scope fallback : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.highestCritical C stream₁ t scope fallback =
      GenLimit.PatientMachine.highestCritical C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr C h]

private theorem highestSurvivor_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream}
    {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.highestSurvivor C stream₁ t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr C h]

private theorem lowestConsistentInScope_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream}
    {t scope fallback : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.lowestConsistentInScope C stream₁ t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr C h]

private theorem lowestConsistent_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream}
    {t fallback : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.lowestConsistent C stream₁ t fallback =
      GenLimit.PatientMachine.lowestConsistent C stream₂ t fallback := by
  classical
  by_cases h₁ : ∃ i, GenLimit.Consistent C stream₁ t i
  · have h₂ : ∃ i, GenLimit.Consistent C stream₂ t i := by
      obtain ⟨i, hi⟩ := h₁
      exact ⟨i, (consistent_congr C h).1 hi⟩
    rw [GenLimit.PatientMachine.lowestConsistent, dif_pos h₁,
      GenLimit.PatientMachine.lowestConsistent, dif_pos h₂]
    apply le_antisymm
    · exact Nat.find_min' h₁
        ((consistent_congr C h).2 (Nat.find_spec h₂))
    · exact Nat.find_min' h₂
        ((consistent_congr C h).1 (Nat.find_spec h₁))
  · have h₂ : ¬ ∃ i, GenLimit.Consistent C stream₂ t i := by
      intro hex
      obtain ⟨i, hi⟩ := hex
      exact h₁ ⟨i, (consistent_congr C h).2 hi⟩
    simp [GenLimit.PatientMachine.lowestConsistent, h₁, h₂]

private theorem stableDecision_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream}
    {t : ℕ} (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.stableDecision C stream₁ t old =
      GenLimit.PatientMachine.stableDecision C stream₂ t old := by
  classical
  simp only [GenLimit.PatientMachine.stableDecision]
  rw [highestCritical_congr C h]

private theorem backtrackDecision_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream}
    {t : ℕ} (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.backtrackDecision C stream₁ t old =
      GenLimit.PatientMachine.backtrackDecision C stream₂ t old := by
  classical
  have hconsistent := consistentIndices_congr C h
      (scope := old.scope)
  have hsurvivors := survivingCriticalIndices_congr C h
      (scope := old.scope)
  have hhighest := highestSurvivor_congr C h
      (scope := old.scope) (fallback := old.focus)
  have hlowestScope := lowestConsistentInScope_congr C h
      (scope := old.scope) (fallback := old.focus)
  have hlowest := lowestConsistent_congr C h (fallback := old.focus)
  have hex : (∃ j, GenLimit.Consistent C stream₁ (t + 1) j) ↔
      ∃ j, GenLimit.Consistent C stream₂ (t + 1) j := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (consistent_congr C h).1 hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (consistent_congr C h).2 hj⟩
  simp only [GenLimit.PatientMachine.backtrackDecision]
  rw [hconsistent, hsurvivors, hhighest, hlowestScope, hlowest, hex]

private theorem decide_congr
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream}
    {t : ℕ} (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.decide C stream₁ t old =
      GenLimit.PatientMachine.decide C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [consistent_congr C h]
  split
  · exact stableDecision_congr C old h
  · exact backtrackDecision_congr C old h

private theorem leastAvailable_congr
    (C : GenLimit.LanguageFamily) (hinf : ∀ i, (C i).Infinite)
    {stream₁ stream₂ : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.leastAvailable C hinf stream₁ t used focus =
      GenLimit.PatientMachine.leastAvailable C hinf stream₂ t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply le_antisymm
  · apply Nat.find_min'
      (GenLimit.PatientMachine.available_exists C hinf stream₁ t used focus)
    simpa only [GenLimit.PatientMachine.Available,
      sample_eq_of_eq_on_prefix h] using
      Nat.find_spec
        (GenLimit.PatientMachine.available_exists C hinf stream₂ t used focus)
  · apply Nat.find_min'
      (GenLimit.PatientMachine.available_exists C hinf stream₂ t used focus)
    simpa only [GenLimit.PatientMachine.Available,
      sample_eq_of_eq_on_prefix h] using
      Nat.find_spec
        (GenLimit.PatientMachine.available_exists C hinf stream₁ t used focus)

private theorem run_congr
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} :
    ∀ t, (∀ n, n < t → stream₁ n = stream₂ n) →
      GenLimit.PatientMachine.run O stream₁ t =
        GenLimit.PatientMachine.run O stream₂ t := by
  intro t h
  induction t with
  | zero => rfl
  | succ t ih =>
      have hold : GenLimit.PatientMachine.run O stream₁ t =
          GenLimit.PatientMachine.run O stream₂ t :=
        ih (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t)))
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, hold]
      have hdecide := decide_congr O.language
        (GenLimit.PatientMachine.run O stream₂ t) h
      have hleast := leastAvailable_congr O.language O.infinite'
        (GenLimit.PatientMachine.run O stream₂ t).used
        (GenLimit.PatientMachine.decide O.language stream₂ t
          (GenLimit.PatientMachine.run O stream₂ t)).focus h
      simp only [GenLimit.PatientMachine.processRound]
      simp only [hdecide, hleast]

private theorem output_congr
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr O (t + 1) h]

noncomputable def onlineOfOracle (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t inputPrefix _ =>
    GenLimit.PatientMachine.output O (extendPrefix inputPrefix) t

private theorem follows_onlineOfOracle
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlineOfOracle O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_congr O
  intro n hn
  simp [extendPrefix, hn]

private theorem novel_of_patient
    (O : GenLimit.OracleFamily) (input : Stream) {i : ℕ}
    (hP : GenLimit.Presents input (O.language i)) :
    GenLimit.NovelGeneratesInLimit input
      (GenLimit.PatientMachine.output O input) (O.language i) := by
  obtain ⟨hgen, _⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
  obtain ⟨T, hT⟩ := hgen
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  refine ⟨hmem, ?_, hnovel⟩
  intro hs
  rw [GenLimit.mem_sample_iff] at hs
  obtain ⟨s, hs, heq⟩ := hs
  exact hfresh s (Nat.le_of_lt_succ hs) heq

private theorem density_of_patient
    (O : GenLimit.OracleFamily) (input : Stream) {i : ℕ}
    (hP : GenLimit.Presents input (O.language i)) :
    (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity
      (GenLimit.GeneratorFirst input (GenLimit.PatientMachine.output O input) ∩
        O.language i) (O.language i) := by
  simpa [GenLimit.PatientMachine.patientLowerDensity] using
    GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP

theorem positive_engine : PositivePresentationHalfDensity := by
  intro family hinf
  let O := oracleOfFamily family hinf
  refine ⟨onlineOfOracle O, ?_⟩
  intro i input hP
  refine ⟨GenLimit.PatientMachine.output O input, ?_, ?_, ?_⟩
  · exact follows_onlineOfOracle O input
  · exact novel_of_patient O input hP
  · exact density_of_patient O input hP

private theorem exists_addOnlyExpansion_index
    (O : GenLimit.OracleFamily) {i : ℕ} {input : Stream}
    (hcomplete : CompleteFiniteOccurrencePresentation input (O.language i)) :
    ∃ j,
      GenLimit.Presents input
        ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) ∧
      O.language i ⊆
        (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j ∧
      ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j \
        O.language i).Finite := by
  classical
  let noiseFinite :=
    GenLimit.InfiniteContamination.displayedNoise_finite hcomplete.2
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm noiseFinite.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  have hnoiseCoe :
      (↑noiseFinite.toFinset : Set ℕ) =
        GenLimit.InfiniteContamination.displayedNoise input (O.language i) :=
    Set.Finite.coe_toFinset noiseFinite
  have hjLanguage :
      (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j =
        O.language i ∪
          GenLimit.InfiniteContamination.displayedNoise input (O.language i) := by
    change GenLimit.InfiniteContamination.finiteExpansionLanguage O j = _
    rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
    simp only [j, data,
      GenLimit.InfiniteContamination.finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    rw [hnoiseCoe]
    simp [GenLimit.InfiniteContamination.finiteExpansion]
  refine ⟨j, ?_, ?_, ?_⟩
  · change Set.range input = _
    rw [hjLanguage]
    ext x
    constructor
    · intro hx
      by_cases hxK : x ∈ O.language i
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    · rintro (hxK | hxNoise)
      · exact hcomplete.1 hxK
      · exact hxNoise.1
  · rw [hjLanguage]
    exact Set.subset_union_left
  · rw [hjLanguage]
    apply noiseFinite.subset
    intro x hx
    exact hx.1.resolve_left hx.2

private theorem novel_of_finite_extraneous
    {input output : Stream} {K expanded : Language}
    (hpresents : GenLimit.Presents input expanded)
    (hextraneous : (expanded \ K).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output expanded) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hnovel
  have hpresentsGeneric : GenLimit.Generic.Presents input expanded := hpresents
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hpresentsGeneric
      hextraneous.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hextraneous).mp hx).1)
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have htGenerate : Tgenerate ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨hExpanded, hFresh, hUnique⟩ := hTgenerate t htGenerate
  refine ⟨?_, hFresh, hUnique⟩
  by_contra hnotK
  have hbad : output t ∈ hextraneous.toFinset :=
    (Set.Finite.mem_toFinset hextraneous).mpr ⟨hExpanded, hnotK⟩
  have hseen : output t ∈ GenLimit.sample input Tseen := by
    simpa [GenLimit.sample, GenLimit.Generic.sample] using hTseen hbad
  exact hFresh (GenLimit.sample_mono
    (htSeen.trans (Nat.le_succ t)) hseen)

private theorem prefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := GenLimit.PatientScope.prefixFinset A n
  let bPrefix := GenLimit.PatientScope.prefixFinset B n
  let diffPrefix := GenLimit.PatientScope.prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hcard : aPrefix.card ≤ bPrefix.card + diffPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2
      (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
  exact hcard.trans (Nat.add_le_add_left hdiff _)

private theorem prefixRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

private theorem prefixRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n

private theorem liminf_le_of_le_add_vanishing
    (source output error : ℕ → ℝ)
    (hsourceNonneg : ∀ n, 0 ≤ source n)
    (houtputNonneg : ∀ n, 0 ≤ output n)
    (houtputLeOne : ∀ n, output n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n) :
    liminf source atTop ≤ liminf output atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop houtputLeOne)
    (isBoundedUnder_of ⟨0, houtputNonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrSource⟩ := exists_between hy
  have hsourceEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrSource
      (isBoundedUnder_of ⟨0, hsourceNonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := sub_pos.mpr hyr
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hsourceEventually, herrorEventually, hcompare] with
      n hsource hsmall hle
  linarith

private theorem density_transfer
    {D K expanded : Set ℕ}
    (hK : K.Infinite) (hsubset : K ⊆ expanded)
    (hextraneous : (expanded \ K).Finite)
    (hdensity : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ expanded) expanded) :
    (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ expanded) n : ℝ) /
      (GenLimit.PatientScope.prefixCount expanded n : ℝ)
  let output : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hextraneous.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcastCountK : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcastCountK
  have hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n := by
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      hcountK.eventually (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdenomNat := GenLimit.PatientScope.prefixCount_mono hsubset n
    have hdenomR :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount expanded n := by
      exact_mod_cast hdenomNat
    have hextraDiff : ((D ∩ expanded) \ (D ∩ K)).Finite := by
      apply hextraneous.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hnumNat := prefixCount_le_add_ncard_diff hextraDiff n
    have hdiffSubset : (D ∩ expanded) \ (D ∩ K) ⊆ expanded \ K := by
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hcardLe : hextraDiff.toFinset.card ≤ hextraneous.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      exact Set.Finite.mem_toFinset hextraneous |>.2
        (hdiffSubset (Set.Finite.mem_toFinset hextraDiff |>.1 hx))
    have hnumNat' :
        GenLimit.PatientScope.prefixCount (D ∩ expanded) n ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n +
            hextraneous.toFinset.card :=
      hnumNat.trans (Nat.add_le_add_left hcardLe _)
    have hnumR :
        (GenLimit.PatientScope.prefixCount (D ∩ expanded) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n +
            hextraneous.toFinset.card := by
      exact_mod_cast hnumNat'
    have hexpandedPos :
        (0 : ℝ) < GenLimit.PatientScope.prefixCount expanded n :=
      lt_of_lt_of_le hnR hdenomR
    change
      (GenLimit.PatientScope.prefixCount (D ∩ expanded) n : ℝ) /
          (GenLimit.PatientScope.prefixCount expanded n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) +
          (hextraneous.toFinset.card : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ)
    rw [← add_div]
    rw [div_le_div_iff₀ hexpandedPos hnR]
    calc
      (GenLimit.PatientScope.prefixCount (D ∩ expanded) n : ℝ) *
          GenLimit.PatientScope.prefixCount K n
        ≤ (GenLimit.PatientScope.prefixCount (D ∩ K) n +
            hextraneous.toFinset.card : ℝ) *
            GenLimit.PatientScope.prefixCount K n :=
          mul_le_mul_of_nonneg_right hnumR (le_of_lt hnR)
      _ ≤ (GenLimit.PatientScope.prefixCount (D ∩ K) n +
            hextraneous.toFinset.card : ℝ) *
            GenLimit.PatientScope.prefixCount expanded n :=
          mul_le_mul_of_nonneg_left hdenomR (by positivity)
  have hliminf : liminf source atTop ≤ liminf output atTop :=
    liminf_le_of_le_add_vanishing source output error
      (fun n => prefixRatio_nonneg _ _ n)
      (fun n => prefixRatio_nonneg _ _ n)
      (fun n => prefixRatio_le_one Set.inter_subset_right n)
      herror hcompare
  unfold GenLimit.PatientScope.relativeLowerDensity at hdensity ⊢
  exact hdensity.trans (by simpa [source, output] using hliminf)

 theorem finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinf
  let O := oracleOfFamily family hinf
  let expandedO :=
    GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hpositive expandedO.language expandedO.infinite'
  refine ⟨gen, ?_⟩
  intro i input hcomplete
  have hcompleteO : CompleteFiniteOccurrencePresentation input (O.language i) :=
    hcomplete
  obtain ⟨j, hjPresents, hjSubset, hjFinite⟩ :=
    exists_addOnlyExpansion_index O hcompleteO
  obtain ⟨output, hfollow, hnovel, hdensity⟩ := hgen j input hjPresents
  refine ⟨output, hfollow, ?_, ?_⟩
  · exact novel_of_finite_extraneous hjPresents hjFinite hnovel
  · exact density_transfer (hinf i) hjSubset hjFinite hdensity

end Stage3Case025Proof

open Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025Proof.finite_noise_transfer
    Stage3Case025Proof.positive_engine
