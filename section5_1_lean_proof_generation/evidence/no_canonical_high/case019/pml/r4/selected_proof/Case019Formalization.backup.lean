import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper39_DenseGeneration.Partial.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper02_LearningTheory.Common.FiniteHistory

open Set Filter
open scoped Topology

namespace Case019Formalization

noncomputable section

open GenLimit
open GenLimit.Generic
open GenLimit.InfiniteContamination
open GenLimit.LiRamanTewari.Common

def oracleOfFamily
    (family : Stage3Case019.LanguageFamily ℕ)
    (hinfinite : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := by classical exact if x ∈ family i then true else false
  query_spec i x := by classical simp

private theorem consistent_iff_of_sample_eq
    (C : LanguageFamily) {a b : ℕ → ℕ} {t i : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    Consistent C a t i ↔ Consistent C b t i := by
  simp only [Consistent, h]

private theorem recursiveCritical_iff_of_sample_eq
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    ∀ i, RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [RecursiveCritical] using
            consistent_iff_of_sample_eq C h (i := 0)
      | succ i =>
          simp only [RecursiveCritical]
          rw [consistent_iff_of_sample_eq C h]
          constructor
          · rintro ⟨hc, hall⟩
            refine ⟨hc, ?_⟩
            intro j hj hjc
            exact hall j hj ((ih j (by omega)).mpr hjc)
          · rintro ⟨hc, hall⟩
            refine ⟨hc, ?_⟩
            intro j hj hjc
            exact hall j hj ((ih j (by omega)).mp hjc)

private theorem decide_eq_of_samples
    (O : OracleFamily) {a b : ℕ → ℕ} (n : ℕ)
    (old : PatientMachine.State)
    (hn : GenLimit.sample a n = GenLimit.sample b n)
    (hn1 : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1)) :
    PatientMachine.decide O.language a n old =
      PatientMachine.decide O.language b n old := by
  classical
  have hcon (i : ℕ) :
      Consistent O.language a (n + 1) i ↔
        Consistent O.language b (n + 1) i :=
    consistent_iff_of_sample_eq O.language hn1
  have hcrit (i : ℕ) :
      RecursiveCritical O.language a n i ↔
        RecursiveCritical O.language b n i :=
    recursiveCritical_iff_of_sample_eq O.language hn i
  have hcrit1 (i : ℕ) :
      RecursiveCritical O.language a (n + 1) i ↔
        RecursiveCritical O.language b (n + 1) i :=
    recursiveCritical_iff_of_sample_eq O.language hn1 i
  have hconsistent (scope : ℕ) :
      PatientMachine.consistentIndices O.language a (n + 1) scope =
        PatientMachine.consistentIndices O.language b (n + 1) scope := by
    ext i
    simp [hcon]
  have hcritical (scope : ℕ) :
      PatientMachine.criticalIndices O.language a (n + 1) scope =
        PatientMachine.criticalIndices O.language b (n + 1) scope := by
    ext i
    simp [hcrit1]
  have hsurviving (scope : ℕ) :
      PatientMachine.survivingCriticalIndices O.language a n scope =
        PatientMachine.survivingCriticalIndices O.language b n scope := by
    ext i
    simp [hcrit, hcrit1]
  have hhighest (scope fallback : ℕ) :
      PatientMachine.highestCritical O.language a (n + 1) scope fallback =
        PatientMachine.highestCritical O.language b (n + 1) scope fallback := by
    unfold PatientMachine.highestCritical
    rw [hcritical]
  have hsurvivor (scope fallback : ℕ) :
      PatientMachine.highestSurvivor O.language a n scope fallback =
        PatientMachine.highestSurvivor O.language b n scope fallback := by
    unfold PatientMachine.highestSurvivor
    rw [hsurviving]
  have hlowestScope (scope fallback : ℕ) :
      PatientMachine.lowestConsistentInScope O.language a (n + 1) scope fallback =
        PatientMachine.lowestConsistentInScope O.language b (n + 1) scope fallback := by
    unfold PatientMachine.lowestConsistentInScope
    rw [hconsistent]
  have hlowest (fallback : ℕ) :
      PatientMachine.lowestConsistent O.language a (n + 1) fallback =
        PatientMachine.lowestConsistent O.language b (n + 1) fallback := by
    unfold PatientMachine.lowestConsistent
    have hexists :
        (∃ i, Consistent O.language a (n + 1) i) ↔
          ∃ i, Consistent O.language b (n + 1) i := by
      exact exists_congr hcon
    split <;> rename_i ha
    · have hb := hexists.mp ha
      simp only [dif_pos hb]
      apply Nat.find_congr (Nat.find_spec ha)
      intro i _
      exact hcon i
    · have hb : ¬∃ i, Consistent O.language b (n + 1) i :=
        fun hb => ha (hexists.mpr hb)
      simp only [dif_neg hb]
  have hstable :
      PatientMachine.stableDecision O.language a n old =
        PatientMachine.stableDecision O.language b n old := by
    unfold PatientMachine.stableDecision
    split
    · simp only [hhighest]
    · rfl
  have hbacktrack :
      PatientMachine.backtrackDecision O.language a n old =
        PatientMachine.backtrackDecision O.language b n old := by
    unfold PatientMachine.backtrackDecision
    simp only [hconsistent, hsurviving, hsurvivor, hlowestScope, hlowest,
      propext (exists_congr hcon)]
  unfold PatientMachine.decide
  rw [propext (hcon old.focus)]
  split
  · exact hstable
  · exact hbacktrack

private theorem processRound_eq_of_samples
    (O : OracleFamily) {a b : ℕ → ℕ} (n : ℕ)
    (old : PatientMachine.State)
    (hn : GenLimit.sample a n = GenLimit.sample b n)
    (hn1 : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1)) :
    PatientMachine.processRound O a n old =
      PatientMachine.processRound O b n old := by
  classical
  have hdecide := decide_eq_of_samples O n old hn hn1
  have hleast (focus : ℕ) :
      PatientMachine.leastAvailable O.language O.infinite' a (n + 1) old.used focus =
        PatientMachine.leastAvailable O.language O.infinite' b (n + 1) old.used focus := by
    unfold PatientMachine.leastAvailable
    apply Nat.find_congr (Nat.find_spec
      (PatientMachine.available_exists O.language O.infinite' a
        (n + 1) old.used focus))
    intro x _
    simp only [PatientMachine.Available, hn1]
  unfold PatientMachine.processRound
  simp only [hdecide, hleast]

private theorem base_sample_eq_of_prefix
    {a b : ℕ → ℕ} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, hx⟩
  · exact ⟨k, hk, (h k hk).symm ▸ hx⟩
  · exact ⟨k, hk, h k hk ▸ hx⟩

private theorem patient_run_eq_of_prefix
    (O : OracleFamily) {a b : ℕ → ℕ} :
    ∀ n, (∀ k, k < n → a k = b k) →
      PatientMachine.run O a n = PatientMachine.run O b n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hab
      rw [PatientMachine.run_succ, PatientMachine.run_succ, ih]
      · apply processRound_eq_of_samples
        · apply base_sample_eq_of_prefix
          exact fun i hi => hab i (hi.trans (Nat.lt_succ_self n))
        · apply base_sample_eq_of_prefix
          exact fun i hi => hab i hi
      · exact fun k hk => hab k (hk.trans (Nat.lt_succ_self n))

def patientGenerator (O : OracleFamily) : Generator ℕ :=
  fun t xs =>
    if ht : t = 0 then 0
    else PatientMachine.output O (extendHistory xs) (t - 1)

private theorem patientGenerator_output
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) stream t =
      PatientMachine.output O stream t := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output patientGenerator
  simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceDIte,
    Nat.add_sub_cancel]
  unfold PatientMachine.output
  congr 2
  apply patient_run_eq_of_prefix
  intro k hk
  exact extendHistory_apply_of_lt _ hk

private theorem contaminated_of_level
    {stream : ℕ → ℕ} {K : Set ℕ} {q : ℕ}
    (h : InjectiveValueContaminatedPresentationAtMost stream K q) :
    FiniteNoiseFiniteOmissionEnumeration stream K := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [finiteNoise_iff_valuesOutside_finite_of_injective h.1]
    exact ((setDifferenceAtMost_iff_finite_ncard_le _ _ _).mp h.2.2).1
  · change (K \ Set.range stream).Finite
    rw [Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty


private theorem liminf_le_of_eventually_le_add_vanishing
    (f g error : ℕ → ℝ)
    (hf_nonneg : ∀ n, 0 ≤ f n) (hf_le_one : ∀ n, f n ≤ 1)
    (hg_nonneg : ∀ n, 0 ≤ g n) (hg_le_one : ∀ n, g n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hcompare : ∀ᶠ n in atTop, f n ≤ g n + error n) :
    liminf f atTop ≤ liminf g atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop hg_le_one)
    (isBoundedUnder_of ⟨0, hg_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrf⟩ := exists_between hy
  have hrEventually : ∀ᶠ n in atTop, r < f n :=
    eventually_lt_of_lt_liminf hrf
      (isBoundedUnder_of ⟨0, hf_nonneg⟩)
  have herrorEventually : ∀ᶠ n in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hcompare] with n hrf' herr hfg
  linarith

private theorem prefixCount_le_add_of_diff_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    PatientScope.prefixCount A n ≤
      PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold PatientScope.prefixCount
  let aPrefix := (Finset.range n).filter fun x => x ∈ A
  let bPrefix := (Finset.range n).filter fun x => x ∈ B
  let diffPrefix := (Finset.range n).filter fun x => x ∈ A \ B
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    simp only [aPrefix, bPrefix, diffPrefix, Finset.mem_filter,
      Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [diffPrefix, Finset.mem_filter] at hx
    exact Set.Finite.mem_toFinset hfinite |>.2 hx.2
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hdiff _))

private theorem relativeLowerDensity_transfer_finite_expansion
    {A K E : Set ℕ} (hK : K.Infinite) (hAE : A ⊆ E)
    (hKE : K ⊆ E) (hfinite : (E \ K).Finite) :
    PatientScope.relativeLowerDensity A E ≤
      PatientScope.relativeLowerDensity (A ∩ K) K := by
  let f : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount A n : ℝ) /
      (PatientScope.prefixCount E n : ℝ)
  let g : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  have hdiff : (A \ (A ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hAE hx.1, fun hxK => hx.2 ⟨hx.1, hxK⟩⟩
  let error : ℕ → ℝ := fun n =>
    (hdiff.toFinset.card : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  have hdenNat := PatientScope.tendsto_prefixCount_atTop hK
  have hdenReal :
      Tendsto (fun n => (PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdenNat
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hdenReal
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hf_le_one : ∀ n, f n ≤ 1 := by
    intro n
    by_cases hzero : PatientScope.prefixCount E n = 0
    · simp [f, hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast PatientScope.prefixCount_mono hAE n
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hg_le_one : ∀ n, g n ≤ 1 := by
    intro n
    by_cases hzero : PatientScope.prefixCount K n = 0
    · simp [g, hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast PatientScope.prefixCount_mono Set.inter_subset_right n
  have hpositive : ∀ᶠ n in atTop, 0 < PatientScope.prefixCount K n :=
    hdenNat.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n in atTop, f n ≤ g n + error n := by
    filter_upwards [hpositive] with n hn
    have hkR : (0 : ℝ) < PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have heR : (0 : ℝ) < PatientScope.prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn (PatientScope.prefixCount_mono hKE n)
    have hden :
        (PatientScope.prefixCount K n : ℝ) ≤
          PatientScope.prefixCount E n := by
      exact_mod_cast PatientScope.prefixCount_mono hKE n
    have hnum :
        (PatientScope.prefixCount A n : ℝ) ≤
          PatientScope.prefixCount (A ∩ K) n + hdiff.toFinset.card := by
      exact_mod_cast prefixCount_le_add_of_diff_finite hdiff n
    calc
      f n ≤ (PatientScope.prefixCount A n : ℝ) /
          PatientScope.prefixCount K n := by
        exact div_le_div_of_nonneg_left (by positivity) hkR hden
      _ ≤ (PatientScope.prefixCount (A ∩ K) n +
            hdiff.toFinset.card : ℝ) /
          PatientScope.prefixCount K n := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt hkR)
      _ = g n + error n := by
        simp only [f, g, error]
        rw [add_div]
  change liminf f atTop ≤ liminf g atTop
  exact liminf_le_of_eventually_le_add_vanishing
    f g error hf_nonneg hf_le_one hg_nonneg hg_le_one herror hcompare


private theorem stage3_countable_half_density : Stage3Case019.CountableClause := by
  intro q family hinfinite
  let O := oracleOfFamily family hinfinite
  let expanded := finiteExpansionOracleFamily O
  refine ⟨patientGenerator expanded, ?_⟩
  intro i input hinput
  have hcontam :
      FiniteNoiseFiniteOmissionEnumeration input (O.language i) :=
    contaminated_of_level hinput
  obtain ⟨j, hjBase, hjPresents⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity
    expanded input hjPresents
  have houtput :
      Stage3Case019.outputAfterInput (patientGenerator expanded) input =
        PatientMachine.output expanded input := by
    funext t
    exact patientGenerator_output expanded input t
  constructor
  · obtain ⟨Tvalid, hvalid⟩ := hrun.1
    have hextraFinite : (expanded.language j \ O.language i).Finite := by
      rw [← hjPresents]
      exact displayedNoise_finite hcontam.2.1
    let extra := hextraFinite.toFinset
    have hextraSet : (↑extra : Set ℕ) = expanded.language j \ O.language i := by
      exact Set.Finite.coe_toFinset hextraFinite
    obtain ⟨Tseen, hseenGeneric⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample
        hjPresents extra (by
          intro x hx
          rw [hextraSet] at hx
          exact hx.1)
    have hseen : extra ⊆ GenLimit.sample input Tseen := by
      intro x hx
      have hx' := hseenGeneric hx
      rw [GenLimit.Generic.mem_sample_iff] at hx'
      rw [GenLimit.mem_sample_iff]
      exact hx'
    refine ⟨max Tvalid Tseen, ?_⟩
    intro t ht
    have htValid : Tvalid ≤ t := (Nat.le_max_left _ _).trans ht
    have htSeen : Tseen ≤ t + 1 := by
      omega
    have hout := hvalid t htValid
    rw [houtput]
    refine ⟨?_, ?_, hout.2.2⟩
    · by_contra hnotTarget
      have hbadSet :
          PatientMachine.output expanded input t ∈ (↑extra : Set ℕ) := by
        rw [hextraSet]
        exact ⟨hout.1, hnotTarget⟩
      have hbad : PatientMachine.output expanded input t ∈ extra := hbadSet
      have hsample :
          PatientMachine.output expanded input t ∈
            GenLimit.sample input (t + 1) :=
        GenLimit.sample_mono htSeen (hseen hbad)
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hout.2.1 s (Nat.le_of_lt_succ hs) heq
    · intro hsample
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hout.2.1 s (Nat.le_of_lt_succ hs) heq
  · rw [houtput]
    have hKE : O.language i ⊆ expanded.language j := by
      intro x hx
      rw [← hjPresents]
      exact hinput.2.1 hx
    have hfinite : (expanded.language j \ O.language i).Finite := by
      rw [← hjPresents]
      exact displayedNoise_finite hcontam.2.1
    have htransfer := relativeLowerDensity_transfer_finite_expansion
      (A := GeneratorFirst input (PatientMachine.output expanded input) ∩
        expanded.language j)
      (K := O.language i) (E := expanded.language j)
      (hinfinite i) Set.inter_subset_right hKE hfinite
    have hdensity :
        (1 / 2 : ℝ) ≤
          PatientScope.relativeLowerDensity
            ((GeneratorFirst input (PatientMachine.output expanded input) ∩
                expanded.language j) ∩ O.language i)
            (O.language i) :=
      hrun.2.trans htransfer
    have hset :
        (GeneratorFirst input (PatientMachine.output expanded input) ∩
            expanded.language j) ∩ O.language i =
          GeneratorFirst input (PatientMachine.output expanded input) ∩
            O.language i := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
      · intro hx
        exact ⟨⟨hx.1, hKE hx.2⟩, hx.2⟩
    rw [hset] at hdensity
    simpa only [O, oracleOfFamily] using hdensity


private def universalFamily : Stage3Case019.LanguageFamily ℕ := fun _ => Set.univ

private theorem universalFamily_infinite (i : ℕ) :
    (universalFamily i).Infinite := by
  exact Set.infinite_univ

private def universalOracle : OracleFamily :=
  oracleOfFamily universalFamily universalFamily_infinite

private def partialUniversalOracle : OracleFamily :=
  PartialEnumeration.closure universalOracle

private def positiveProjection : ℤ → ℕ
  | Int.ofNat 0 => 0
  | Int.ofNat (n + 1) => n
  | Int.negSucc _ => 0

private def negativeProjection : ℤ → ℕ
  | Int.negSucc n => n
  | Int.ofNat _ => 0

@[simp] private theorem positiveProjection_positiveCode (n : ℕ) :
    positiveProjection (GenLimit.UnionClosedness.positiveCode n) = n := by
  cases n <;> rfl

@[simp] private theorem negativeProjection_negativeCode (n : ℕ) :
    negativeProjection (GenLimit.UnionClosedness.negativeCode n) = n := by
  rfl

private theorem positiveProjection_eq_of_positiveCode_eq {z : ℤ} {n : ℕ}
    (h : positiveProjection z = n)
    (hz : z = GenLimit.UnionClosedness.positiveCode n) : z =
      GenLimit.UnionClosedness.positiveCode n := hz

private def projectedStream (proj : ℤ → ℕ)
    (input : Stage3Case019.Stream ℤ) : Stage3Case019.Stream ℕ :=
  fun t => proj (input t)

private def liftedPatientGenerator
    (proj : ℤ → ℕ) (code : ℕ → ℤ) : Stage3Case019.Generator ℤ :=
  fun t xs => code (patientGenerator partialUniversalOracle t (fun k => proj (xs k)))

private theorem liftedPatientGenerator_output
    (proj : ℤ → ℕ) (code : ℕ → ℤ)
    (input : Stage3Case019.Stream ℤ) (t : ℕ) :
    Stage3Case019.outputAfterInput (liftedPatientGenerator proj code) input t =
      code (PatientMachine.output partialUniversalOracle
        (projectedStream proj input) t) := by
  change code (patientGenerator partialUniversalOracle (t + 1)
      (fun k : Fin (t + 1) => proj (input k))) = _
  rw [← patientGenerator_output partialUniversalOracle
    (projectedStream proj input) t]
  rfl

private def separationGenerator (q : ℕ) : Stage3Case019.Generator ℤ :=
  fun t xs =>
    if GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sequenceSample xs then
      liftedPatientGenerator positiveProjection
        GenLimit.UnionClosedness.positiveCode t xs
    else
      liftedPatientGenerator negativeProjection
        GenLimit.UnionClosedness.negativeCode t xs

private theorem separationGenerator_output_positive
    {q : ℕ} {input : Stage3Case019.Stream ℤ} {t : ℕ}
    (hmark : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.NoiseLossFeedback.observedThrough input t) :
    Stage3Case019.outputAfterInput (separationGenerator q) input t =
      GenLimit.UnionClosedness.positiveCode
        (PatientMachine.output partialUniversalOracle
          (projectedStream positiveProjection input) t) := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output separationGenerator
  rw [GenLimit.Generic.sequenceSample_prefix, if_pos hmark]
  exact liftedPatientGenerator_output positiveProjection
    GenLimit.UnionClosedness.positiveCode input t

private theorem separationGenerator_output_negative
    {q : ℕ} {input : Stage3Case019.Stream ℤ} {t : ℕ}
    (hmark : ¬GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.NoiseLossFeedback.observedThrough input t) :
    Stage3Case019.outputAfterInput (separationGenerator q) input t =
      GenLimit.UnionClosedness.negativeCode
        (PatientMachine.output partialUniversalOracle
          (projectedStream negativeProjection input) t) := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output separationGenerator
  rw [GenLimit.Generic.sequenceSample_prefix, if_neg hmark]
  exact liftedPatientGenerator_output negativeProjection
    GenLimit.UnionClosedness.negativeCode input t

private def firstEncodedLanguage (q : ℕ) (A : Set ℕ) : Set ℤ :=
  (GenLimit.NoiseLossFeedback.omissionMarkerFinset q : Set ℤ) ∪
    GenLimit.UnionClosedness.positiveIntegers ∪
      GenLimit.UnionClosedness.negativeCode '' A

private theorem firstEncodedLanguage_mem (q : ℕ) (A : Set ℕ) :
    firstEncodedLanguage q A ∈
      GenLimit.NoiseLossFeedback.finiteOmissionClass q := by
  left
  refine ⟨?_, 0, ?_⟩
  · intro z hz
    exact Or.inl (Or.inl hz)
  · rintro z ⟨k, rfl⟩
    exact Or.inl (Or.inr (GenLimit.UnionClosedness.positiveCode_mem _))

private theorem firstEncodedLanguage_injective (q : ℕ) :
    Function.Injective (firstEncodedLanguage q) := by
  intro A B hAB
  ext n
  have hprobe := Set.ext_iff.mp hAB
    (GenLimit.UnionClosedness.negativeCode n)
  have hneg : GenLimit.UnionClosedness.negativeCode n ∉
      GenLimit.UnionClosedness.positiveIntegers := by
    exact Int.not_lt_of_ge (le_of_lt
      (GenLimit.UnionClosedness.negativeCode_mem n))
  have hmarker := GenLimit.NoiseLossFeedback.negativeCode_not_marker q n
  change (((GenLimit.UnionClosedness.negativeCode n ∈
      (GenLimit.NoiseLossFeedback.omissionMarkerFinset q : Set ℤ)) ∨
      GenLimit.UnionClosedness.negativeCode n ∈
        GenLimit.UnionClosedness.positiveIntegers) ∨
      GenLimit.UnionClosedness.negativeCode n ∈
        GenLimit.UnionClosedness.negativeCode '' A ↔
    ((GenLimit.UnionClosedness.negativeCode n ∈
      (GenLimit.NoiseLossFeedback.omissionMarkerFinset q : Set ℤ)) ∨
      GenLimit.UnionClosedness.negativeCode n ∈
        GenLimit.UnionClosedness.positiveIntegers) ∨
      GenLimit.UnionClosedness.negativeCode n ∈
        GenLimit.UnionClosedness.negativeCode '' B) at hprobe
  have himageA : GenLimit.UnionClosedness.negativeCode n ∈
      GenLimit.UnionClosedness.negativeCode '' A ↔ n ∈ A := by
    constructor
    · rintro ⟨m, hm, heq⟩
      exact GenLimit.UnionClosedness.negativeCode_injective heq ▸ hm
    · exact fun hn => ⟨n, hn, rfl⟩
  have himageB : GenLimit.UnionClosedness.negativeCode n ∈
      GenLimit.UnionClosedness.negativeCode '' B ↔ n ∈ B := by
    constructor
    · rintro ⟨m, hm, heq⟩
      exact GenLimit.UnionClosedness.negativeCode_injective heq ▸ hm
    · exact fun hn => ⟨n, hn, rfl⟩
  rw [himageA, himageB] at hprobe
  simpa [hmarker, hneg] using hprobe

private theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → GenLimit.NoiseLossFeedback.finiteOmissionClass q :=
    fun A => ⟨firstEncodedLanguage q A, firstEncodedLanguage_mem q A⟩
  have hf : Function.Injective f := by
    intro A B h
    apply firstEncodedLanguage_injective q
    exact congrArg Subtype.val h
  letI : Countable (GenLimit.NoiseLossFeedback.finiteOmissionClass q) :=
    hcountable.to_subtype
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hf.countable

private theorem finiteNoise_negative_clause (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stage3Case019.Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬Stage3Case019.SampleFreshGeneratesAfterInput
              input (Stage3Case019.outputAfterInput gen input) K := by
  intro gen
  by_contra h
  push_neg at h
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  obtain ⟨T, hT⟩ := h K hK input hinput
  exact ⟨T, fun t ht => hT t ht⟩


end

end Case019Formalization
