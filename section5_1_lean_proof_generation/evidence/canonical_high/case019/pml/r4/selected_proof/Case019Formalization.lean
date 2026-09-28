import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper02_LearningTheory.Common.FiniteHistory
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Logic.Equiv.Finset

open Stage3Case019

namespace Case019

open GenLimit
open Filter

noncomputable def oracleOfFamily (family : GenLimit.Generic.LanguageFamily ℕ)
    (hinf : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hinf
  query i x := by classical exact if x ∈ family i then true else false
  query_spec i x := by classical simp

lemma consistent_congr_sample {C : GenLimit.Generic.LanguageFamily ℕ}
    {a b : GenLimit.Generic.Stream ℕ} {t i : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    Consistent C a t i ↔ Consistent C b t i := by
  simp only [Consistent]
  rw [h]

lemma recursiveCritical_congr_sample {C : GenLimit.Generic.LanguageFamily ℕ}
    {a b : GenLimit.Generic.Stream ℕ} {t : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    ∀ i, RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [RecursiveCritical] using consistent_congr_sample (C := C) (i := 0) h
      | succ i =>
          simp only [RecursiveCritical]
          constructor
          · rintro ⟨hc, hs⟩
            refine ⟨(consistent_congr_sample h).mp hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjc)
          · rintro ⟨hc, hs⟩
            refine ⟨(consistent_congr_sample h).mpr hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjc)

lemma consistentIndices_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} {t scope : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    PatientMachine.consistentIndices C a t scope =
      PatientMachine.consistentIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_consistentIndices]
  rw [consistent_congr_sample h]

lemma criticalIndices_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} {t scope : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    PatientMachine.criticalIndices C a t scope =
      PatientMachine.criticalIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_congr_sample h i]

lemma survivingIndices_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} {t scope : ℕ}
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    PatientMachine.survivingCriticalIndices C a t scope =
      PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr_sample h0 i, recursiveCritical_congr_sample h1 i]

lemma highestCritical_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} {t scope fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    PatientMachine.highestCritical C a t scope fallback =
      PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold PatientMachine.highestCritical
  rw [criticalIndices_congr C h]

lemma highestSurvivor_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} {t scope fallback : ℕ}
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    PatientMachine.highestSurvivor C a t scope fallback =
      PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold PatientMachine.highestSurvivor
  rw [survivingIndices_congr C h0 h1]

lemma lowestConsistentInScope_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} {t scope fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    PatientMachine.lowestConsistentInScope C a t scope fallback =
      PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr C h]

lemma lowestConsistent_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} {t fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    PatientMachine.lowestConsistent C a t fallback =
      PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold PatientMachine.lowestConsistent
  by_cases ha : ∃ i, Consistent C a t i
  · have hb : ∃ i, Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_congr_sample h).mp hi⟩
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr' (consistent_congr_sample h)
  · have hb : ¬ ∃ i, Consistent C b t i := by
      intro hb
      obtain ⟨i, hi⟩ := hb
      exact ha ⟨i, (consistent_congr_sample h).mpr hi⟩
    rw [dif_neg ha, dif_neg hb]

lemma leastAvailable_congr (O : OracleFamily)
    {a b : GenLimit.Generic.Stream ℕ} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  classical
  unfold PatientMachine.leastAvailable
  apply Nat.find_congr'
  intro x
  simp only [PatientMachine.Available]
  rw [h]

lemma stableDecision_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} (t : ℕ) (old : PatientMachine.State)
    (h : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    PatientMachine.stableDecision C a t old =
      PatientMachine.stableDecision C b t old := by
  classical
  unfold PatientMachine.stableDecision
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp only [dif_pos hwait]
    rw [highestCritical_congr C h]
  · simp only [dif_neg hwait]

lemma backtrackDecision_congr (C : GenLimit.Generic.LanguageFamily ℕ)
    {a b : GenLimit.Generic.Stream ℕ} (t : ℕ) (old : PatientMachine.State)
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    PatientMachine.backtrackDecision C a t old =
      PatientMachine.backtrackDecision C b t old := by
  classical
  have hc := consistentIndices_congr C h1 (scope := old.scope)
  have hs := survivingIndices_congr C h0 h1 (scope := old.scope)
  have hall : (∃ j, Consistent C a (t + 1) j) ↔
      ∃ j, Consistent C b (t + 1) j := by
    constructor <;> rintro ⟨j, hj⟩
    · exact ⟨j, (consistent_congr_sample h1).mp hj⟩
    · exact ⟨j, (consistent_congr_sample h1).mpr hj⟩
  unfold PatientMachine.backtrackDecision
  simp only [hc]
  by_cases hcon : (PatientMachine.consistentIndices C b (t + 1) old.scope).Nonempty
  · simp only [dif_pos hcon]
    rw [hs]
    by_cases hsurv : (PatientMachine.survivingCriticalIndices C b t old.scope).Nonempty
    · simp only [if_pos hsurv]
      rw [highestSurvivor_congr C h0 h1]
    · simp only [if_neg hsurv]
      rw [lowestConsistentInScope_congr C h1]
  · simp only [dif_neg hcon]
    dsimp
    rw [lowestConsistent_congr C h1]
    by_cases ha : ∃ j, Consistent C a (t + 1) j
    · have hb := hall.mp ha
      rw [if_pos ha, if_pos hb]
    · have hb : ¬ ∃ j, Consistent C b (t + 1) j := fun hb => ha (hall.mpr hb)
      rw [if_neg ha, if_neg hb]

lemma decide_congr (O : OracleFamily)
    {a b : GenLimit.Generic.Stream ℕ} (t : ℕ) (old : PatientMachine.State)
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    PatientMachine.decide O.language a t old =
      PatientMachine.decide O.language b t old := by
  classical
  unfold PatientMachine.decide
  have hp : Consistent O.language a (t + 1) old.focus =
      Consistent O.language b (t + 1) old.focus :=
    propext (consistent_congr_sample h1)
  rw [hp]
  split
  · exact stableDecision_congr O.language t old h1
  · exact backtrackDecision_congr O.language t old h0 h1

lemma processRound_congr (O : OracleFamily)
    {a b : GenLimit.Generic.Stream ℕ} (t : ℕ) (old : PatientMachine.State)
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    PatientMachine.processRound O a t old = PatientMachine.processRound O b t old := by
  classical
  unfold PatientMachine.processRound
  rw [decide_congr O t old h0 h1]
  dsimp
  rw [leastAvailable_congr O old.used
    (PatientMachine.decide O.language b t old).focus h1]

lemma run_congr_prefix (O : OracleFamily) {a b : GenLimit.Generic.Stream ℕ} {n : ℕ}
    (h : ∀ r, r ≤ n → GenLimit.sample a r = GenLimit.sample b r) :
    PatientMachine.run O a n = PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      rw [ih (fun r hr => h r (hr.trans (Nat.le_succ n)))]
      exact processRound_congr O n (PatientMachine.run O b n)
        (h n (Nat.le_succ n)) (h (n + 1) le_rfl)

noncomputable def patientGenerator (O : OracleFamily) : GenLimit.Generic.Generator ℕ :=
  fun n xs =>
    if h : n = 0 then 0 else
      PatientMachine.output O (LiRamanTewari.Common.extendHistory xs) (n - 1)

lemma patientGenerator_output (O : OracleFamily)
    (stream : GenLimit.Generic.Stream ℕ) (t : ℕ) :
    outputAfterInput (patientGenerator O) stream t = PatientMachine.output O stream t := by
  unfold outputAfterInput GenLimit.Generic.output patientGenerator
  rw [dif_neg (Nat.succ_ne_zero t)]
  simp only [Nat.add_sub_cancel]
  have hsamp : ∀ r, r ≤ t + 1 →
      GenLimit.sample (LiRamanTewari.Common.extendHistory (fun i : Fin (t + 1) => stream i)) r =
        GenLimit.sample stream r := by
    intro r hr
    classical
    ext x
    simpa [GenLimit.sample, GenLimit.Generic.sample] using
      Finset.ext_iff.mp
        (LiRamanTewari.Common.sample_extendHistory_stream_eq
          (α := ℕ) (stream := stream) (t := t + 1) (r := r) hr) x
  unfold PatientMachine.output
  rw [run_congr_prefix O hsamp]


lemma relativeLowerDensity_transfer_finite_addition
    {A K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcastK : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcastK
  have hsource_nonneg : ∀ n, 0 ≤ source n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsource_le_one : ∀ n, source n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount R n = 0
    · simp [source, hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (Set.inter_subset_right) n
  have htarget_nonneg : ∀ n, 0 ≤ target n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htarget_le_one : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [target, hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (Set.inter_subset_right) n
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      hcountK.eventually (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hkR : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hdiff : GenLimit.PatientScope.prefixCount (A ∩ R) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card := by
      classical
      unfold GenLimit.PatientScope.prefixCount
      let left := (Finset.range n).filter fun x => x ∈ A ∩ R
      let good := (Finset.range n).filter fun x => x ∈ A ∩ K
      let bad := (Finset.range n).filter fun x => x ∈ R \ K
      have hsub : left ⊆ good ∪ bad := by
        intro x hx
        simp only [left, good, bad, Finset.mem_filter, Finset.mem_union,
          Set.mem_inter_iff, Set.mem_diff] at hx ⊢
        by_cases hxK : x ∈ K
        · exact Or.inl ⟨hx.1, hx.2.1, hxK⟩
        · exact Or.inr ⟨hx.1, hx.2.2, hxK⟩
      have hbadSub : ∀ x : ℕ, x ∈ bad → x ∈ hfinite.toFinset := by
        intro x hx
        rw [Set.Finite.mem_toFinset]
        exact (Finset.mem_filter.mp hx).2
      have hbad : bad.card ≤ hfinite.toFinset.card :=
        Finset.card_le_card hbadSub
      simpa [GenLimit.PatientScope.prefixFinset, left, good] using
        (Finset.card_le_card hsub).trans
          ((Finset.card_union_le good bad).trans
            (Nat.add_le_add_left hbad good.card))
    have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hrpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n := by
      exact lt_of_lt_of_le hkpos (by exact_mod_cast hkR)
    have hdiffR :
        (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hdiff
    have hdenom :
        (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
            GenLimit.PatientScope.prefixCount R n ≤
          (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        hkpos (by exact_mod_cast hkR)
    dsimp [source, target, error]
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
          GenLimit.PatientScope.prefixCount R n ≤
        (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
          GenLimit.PatientScope.prefixCount K n := hdenom
      _ ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) +
          hfinite.toFinset.card) /
          GenLimit.PatientScope.prefixCount K n :=
        div_le_div_of_nonneg_right hdiffR hkpos.le
      _ = (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n +
          (hfinite.toFinset.card : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by rw [add_div]
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hrs herr hp
  linarith

theorem stage3_countable_half_density : Stage3Case019.CountableClause := by
  intro q family hinf
  let O := oracleOfFamily family hinf
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hinput
  have hcontam : GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
      input (O.language i) := by
    refine ⟨hinput.1, ?_, ?_⟩
    · exact (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
        hinput.1).mpr ((GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
          (Set.range input) (O.language i) q).mp hinput.2.2 |>.1)
    · unfold GenLimit.InfiniteContamination.FiniteOmissions
      exact Set.Finite.subset Set.finite_empty (by
        intro x hx
        exact False.elim (hx.2 (hinput.2.1 hx.1)))
  obtain ⟨j, hjbase, hjPresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hrun := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    E input hjPresents
  have houtput : outputAfterInput (patientGenerator E) input =
      GenLimit.PatientMachine.output E input := by
    funext t
    exact patientGenerator_output E input t
  constructor
  · rw [houtput]
    obtain ⟨Tvalid, hvalid⟩ := hrun.1
    have houtInjective : Function.Injective
        (GenLimit.PatientMachine.output E input) := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hablt | hbalt
      · exact GenLimit.PatientMachine.output_ne_of_lt E input hablt hab
      · exact GenLimit.PatientMachine.output_ne_of_lt E input hbalt hab.symm
    have hfiniteBad : (E.language j \ O.language i).Finite := by
      rw [← hjPresents]
      exact (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
        hinput.1).mp hcontam.2.1
    have hbadTimes : {t | GenLimit.PatientMachine.output E input t ∈
        E.language j \ O.language i}.Finite :=
      hfiniteBad.preimage houtInjective.injOn
    have heventuallyGood : ∀ᶠ t : ℕ in atTop,
        GenLimit.PatientMachine.output E input t ∉
          E.language j \ O.language i := by
      rw [← Nat.cofinite_eq_atTop]
      exact hbadTimes.compl_mem_cofinite
    obtain ⟨Tgood, hgood⟩ := (eventually_atTop.1 heventuallyGood)
    refine ⟨max Tvalid Tgood, ?_⟩
    intro t ht
    have hv := hvalid t ((Nat.le_max_left _ _).trans ht)
    have hg := hgood t ((Nat.le_max_right _ _).trans ht)
    exact ⟨by
      by_contra hnot
      exact hg ⟨hv.1, hnot⟩,
      by
        intro hsamp
        obtain ⟨s, hs, hseq⟩ := GenLimit.mem_sample_iff.mp hsamp
        exact hv.2.1 s (Nat.lt_succ_iff.mp hs) hseq,
      hv.2.2⟩
  · have hsubset : O.language i ⊆ E.language j := by
      rw [← hjPresents]
      exact hinput.2.1
    have hfinite : (E.language j \ O.language i).Finite := by
      rw [← hjPresents]
      exact (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
        hinput.1).mp hcontam.2.1
    have htransfer := relativeLowerDensity_transfer_finite_addition
      (A := GenLimit.GeneratorFirst input (GenLimit.PatientMachine.output E input))
      (hinf i) hsubset hfinite
    rw [houtput]
    exact hrun.2.trans htransfer


noncomputable def decodedFinset (i : ℕ) : Finset ℕ :=
  (Encodable.decode i : Option (Finset ℕ)).getD ∅

noncomputable def cofiniteAnchorFamily : GenLimit.LanguageFamily :=
  fun i => {n | n = 0 ∨ n ∉ decodedFinset i}

lemma cofiniteAnchorFamily_infinite (i : ℕ) :
    (cofiniteAnchorFamily i).Infinite := by
  exact (Set.Finite.infinite_compl (decodedFinset i).finite_toSet).mono (by
    intro n hn
    exact Or.inr hn)

noncomputable def cofiniteAnchorOracle : OracleFamily where
  language := cofiniteAnchorFamily
  infinite' := cofiniteAnchorFamily_infinite
  query i n := by classical exact decide (n ∈ cofiniteAnchorFamily i)
  query_spec i n := by classical simp

lemma exists_cofiniteAnchor_index {S : Set ℕ}
    (hzero : 0 ∈ S) (hfinite : Sᶜ.Finite) :
    ∃ i, cofiniteAnchorFamily i = S := by
  classical
  let F : Finset ℕ := hfinite.toFinset
  let i := Encodable.encode F
  refine ⟨i, ?_⟩
  have hdecode : decodedFinset i = F := by
    simp [decodedFinset, i, Encodable.encodek]
  ext n
  simp only [cofiniteAnchorFamily, Set.mem_setOf_eq, hdecode]
  constructor
  · intro hn
    rcases hn with rfl | hn
    · exact hzero
    · by_contra hnot
      exact hn (by simpa [F] using hnot)
  · intro hn
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    · exact Or.inr (by
        intro hnF
        have : n ∈ Sᶜ := by simpa [F] using hnF
        exact this hn)

abbrev negCode := GenLimit.UnionClosedness.negativeCode

def positiveCode0 (n : ℕ) : ℤ := Int.ofNat n

def positiveProject (z : ℤ) : ℕ := z.toNat

def negativeProject (z : ℤ) : ℕ :=
  if z < 0 then z.natAbs - 1 else 0

lemma positiveProject_positiveCode0 (n : ℕ) :
    positiveProject (positiveCode0 n) = n := by
  simp [positiveProject, positiveCode0]

lemma negativeProject_negCode (n : ℕ) :
    negativeProject (negCode n) = n := by
  simp [negativeProject, negCode, GenLimit.UnionClosedness.negativeCode]

lemma positiveCode0_injective : Function.Injective positiveCode0 := by
  intro a b h
  exact Int.ofNat_inj.mp h

lemma positiveCode0_nonnegative (n : ℕ) : (0 : ℤ) ≤ positiveCode0 n := by
  simp [positiveCode0]

lemma negCode_negative (n : ℕ) : negCode n < 0 :=
  GenLimit.UnionClosedness.negativeCode_mem n

noncomputable def sidePatientGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    if GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sequenceSample xs then
      positiveCode0 (patientGenerator cofiniteAnchorOracle n
        (fun k => positiveProject (xs k)))
    else
      negCode (patientGenerator cofiniteAnchorOracle n
        (fun k => negativeProject (xs k)))

lemma sidePatientGenerator_positive_output
    {q t : ℕ} {input : Stream ℤ}
    (hmarkers : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.Generic.sample input (t + 1)) :
    outputAfterInput (sidePatientGenerator q) input t =
      positiveCode0 (PatientMachine.output cofiniteAnchorOracle
        (fun s => positiveProject (input s)) t) := by
  unfold outputAfterInput GenLimit.Generic.output sidePatientGenerator
  have hsample : GenLimit.Generic.sequenceSample
      (fun k : Fin (t + 1) => input k) =
      GenLimit.Generic.sample input (t + 1) :=
    GenLimit.Generic.sequenceSample_prefix input (t + 1)
  rw [if_pos (by simpa [hsample] using hmarkers)]
  apply congrArg positiveCode0
  have h := patientGenerator_output cofiniteAnchorOracle
    (fun s => positiveProject (input s)) t
  exact h

lemma sidePatientGenerator_negative_output
    {q t : ℕ} {input : Stream ℤ}
    (hmarkers : ¬ GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.Generic.sample input (t + 1)) :
    outputAfterInput (sidePatientGenerator q) input t =
      negCode (PatientMachine.output cofiniteAnchorOracle
        (fun s => negativeProject (input s)) t) := by
  unfold outputAfterInput GenLimit.Generic.output sidePatientGenerator
  have hsample : GenLimit.Generic.sequenceSample
      (fun k : Fin (t + 1) => input k) =
      GenLimit.Generic.sample input (t + 1) :=
    GenLimit.Generic.sequenceSample_prefix input (t + 1)
  rw [if_neg (by simpa [hsample] using hmarkers)]
  apply congrArg negCode
  have h := patientGenerator_output cofiniteAnchorOracle
    (fun s => negativeProject (input s)) t
  exact h


def positiveRanks0 (K : Set ℤ) : Set ℕ := positiveCode0 ⁻¹' K

def negativeRanks0 (K : Set ℤ) : Set ℕ := negCode ⁻¹' K

lemma positive_project_range_zero
    {K : Set ℤ} {input : Stream ℤ}
    (hcover : K ⊆ Set.range input) (hzero : (0 : ℤ) ∈ K) :
    0 ∈ Set.range (fun s => positiveProject (input s)) := by
  obtain ⟨t, ht⟩ := hcover hzero
  refine ⟨t, ?_⟩
  simp [ht, positiveProject]

lemma positive_project_range_cofinite
    {K : Set ℤ} {input : Stream ℤ}
    (hcover : K ⊆ Set.range input)
    {j : ℕ} (htail : GenLimit.UnionClosedness.positiveTail j ⊆ K) :
    (Set.range (fun s => positiveProject (input s)))ᶜ.Finite := by
  apply Set.Finite.subset (Finset.finite_toSet (Finset.range (j + 1)))
  intro n hn
  simp only [Set.mem_compl_iff, Set.mem_range, not_exists] at hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hnot
  have hjn : j + 1 ≤ n := Nat.le_of_not_gt hnot
  let k := n - (j + 1)
  have hcode : positiveCode0 n ∈ GenLimit.UnionClosedness.positiveTail j := by
    refine ⟨k, ?_⟩
    simp only [positiveCode0, GenLimit.UnionClosedness.positiveCode]
    congr 1
    omega
  obtain ⟨t, ht⟩ := hcover (htail hcode)
  exact hn t (by simpa [positiveProject, positiveCode0] using congrArg positiveProject ht)

lemma negative_project_range_eq_univ
    {K : Set ℤ} {input : Stream ℤ}
    (hcover : K ⊆ Set.range input)
    (hnegative : GenLimit.UnionClosedness.negativeIntegers ⊆ K) :
    Set.range (fun s => negativeProject (input s)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  obtain ⟨t, ht⟩ := hcover (hnegative (negCode_negative n))
  refine ⟨t, ?_⟩
  simpa [ht] using negativeProject_negCode n

lemma positiveRanks0_subset_project_range
    {K : Set ℤ} {input : Stream ℤ}
    (hcover : K ⊆ Set.range input) :
    positiveRanks0 K ⊆ Set.range (fun s => positiveProject (input s)) := by
  intro n hn
  obtain ⟨t, ht⟩ := hcover hn
  refine ⟨t, ?_⟩
  simpa [ht] using positiveProject_positiveCode0 n

lemma project_range_difference_finite
    {K : Set ℤ} {input : Stream ℤ}
    (hinj : Function.Injective input) (hzero : (0 : ℤ) ∈ K)
    (hnoise : GenLimit.Generic.SetDifferenceAtMost (Set.range input) K q) :
    (Set.range (fun s => positiveProject (input s)) \ positiveRanks0 K).Finite := by
  have houtside : (Set.range input \ K).Finite :=
    (GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
      (Set.range input) K q).mp hnoise |>.1
  apply Set.Finite.subset (houtside.image positiveProject)
  intro n hn
  rcases hn.1 with ⟨t, rfl⟩
  refine ⟨input t, ⟨⟨t, rfl⟩, ?_⟩, rfl⟩
  intro hK
  apply hn.2
  change positiveCode0 (positiveProject (input t)) ∈ K
  by_cases hnonneg : 0 ≤ input t
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnonneg
    rw [hn] at hK ⊢
    simpa [positiveProject, positiveCode0] using hK
  · have hle : input t ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
    have heq : positiveProject (input t) = 0 :=
      Int.toNat_of_nonpos hle
    simpa [positiveCode0, heq] using hzero



lemma patient_output_injective (O : OracleFamily) (stream : ℕ → ℕ) :
    Function.Injective (PatientMachine.output O stream) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · exact PatientMachine.output_ne_of_lt O stream hablt hab
  · exact PatientMachine.output_ne_of_lt O stream hbalt hab.symm

lemma sidePatientGenerator_first_novel
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input K q) :
    NovelGeneratesAfterInput input (outputAfterInput (sidePatientGenerator q) input) K := by
  classical
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Td, hTd⟩ :=
    GenLimit.NoiseLossFeedback.allMarkers_eventually_observed hinput hmarkers
  let projected : ℕ → ℕ := fun s => positiveProject (input s)
  let R : Set ℕ := Set.range projected
  have hzeroK : (0 : ℤ) ∈ K := by
    apply hmarkers
    simp [GenLimit.NoiseLossFeedback.omissionMarkerFinset]
  have hzeroR : 0 ∈ R := positive_project_range_zero hinput.2.1 hzeroK
  have hcofiniteR : Rᶜ.Finite :=
    positive_project_range_cofinite hinput.2.1 htail
  obtain ⟨i, hi⟩ := exists_cofiniteAnchor_index hzeroR hcofiniteR
  change cofiniteAnchorOracle.language i = R at hi
  have hpresents : GenLimit.Presents projected (cofiniteAnchorOracle.language i) := by
    change Set.range projected = cofiniteAnchorOracle.language i
    exact hi.symm
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity
    cofiniteAnchorOracle projected hpresents
  let outN := PatientMachine.output cofiniteAnchorOracle projected
  have houtinj : Function.Injective outN :=
    patient_output_injective cofiniteAnchorOracle projected
  have hfiniteBad : (R \ positiveRanks0 K).Finite :=
    project_range_difference_finite hinput.1 hzeroK hinput.2.2
  have hbadTimes : {t | outN t ∈ R \ positiveRanks0 K}.Finite :=
    hfiniteBad.preimage houtinj.injOn
  have heventuallyGood : ∀ᶠ t : ℕ in atTop, outN t ∉ R \ positiveRanks0 K := by
    rw [← Nat.cofinite_eq_atTop]
    exact hbadTimes.compl_mem_cofinite
  obtain ⟨Tgood, hgood⟩ := eventually_atTop.1 heventuallyGood
  obtain ⟨Tvalid, hvalid⟩ := hrun.1
  refine ⟨max Td (max Tvalid Tgood), ?_⟩
  intro t ht
  have hdt : Td ≤ t := (Nat.le_max_left _ _).trans ht
  have hvt : Tvalid ≤ t :=
    (Nat.le_max_left Tvalid Tgood).trans ((Nat.le_max_right Td _).trans ht)
  have hgt : Tgood ≤ t :=
    (Nat.le_max_right Tvalid Tgood).trans ((Nat.le_max_right Td _).trans ht)
  have hmarkst := hTd t hdt
  have hout : outputAfterInput (sidePatientGenerator q) input t =
      positiveCode0 (outN t) :=
    sidePatientGenerator_positive_output hmarkst
  have hv := hvalid t hvt
  have hg := hgood t hgt
  have htargetRank : outN t ∈ positiveRanks0 K := by
    by_contra hnot
    have hvR : outN t ∈ R := by
      rw [← hi]
      exact hv.1
    exact hg ⟨hvR, hnot⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    exact htargetRank
  · rw [hout]
    intro hsamp
    obtain ⟨s, hs, hseq⟩ := GenLimit.Generic.mem_sample_iff.mp hsamp
    apply hv.2.1 s (Nat.lt_succ_iff.mp hs)
    change positiveProject (input s) = outN t
    rw [hseq, positiveProject_positiveCode0]
  · intro s hs
    by_cases hms : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sample input (s + 1)
    · rw [sidePatientGenerator_positive_output hms, hout]
      exact fun heq => hv.2.2 s hs (positiveCode0_injective heq)
    · rw [sidePatientGenerator_negative_output hms, hout]
      intro heq
      have hneg : negCode (PatientMachine.output cofiniteAnchorOracle
          (fun r => negativeProject (input r)) s) < 0 := negCode_negative _
      have hnonneg := positiveCode0_nonnegative (outN t)
      exact (Int.not_lt_of_ge hnonneg) (heq ▸ hneg)

lemma sidePatientGenerator_second_novel
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input K q) :
    NovelGeneratesAfterInput input (outputAfterInput (sidePatientGenerator q) input) K := by
  let projected : ℕ → ℕ := fun s => negativeProject (input s)
  have hrange : Set.range projected = Set.univ :=
    negative_project_range_eq_univ hinput.2.1 hK.1
  have hzero : 0 ∈ (Set.univ : Set ℕ) := Set.mem_univ 0
  have hfinite : ((Set.univ : Set ℕ)ᶜ).Finite := by simp
  obtain ⟨i, hi⟩ := exists_cofiniteAnchor_index hzero hfinite
  change cofiniteAnchorOracle.language i = Set.univ at hi
  have hpresents : GenLimit.Presents projected (cofiniteAnchorOracle.language i) := by
    change Set.range projected = cofiniteAnchorOracle.language i
    exact hrange.trans hi.symm
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity
    cofiniteAnchorOracle projected hpresents
  obtain ⟨Tvalid, hvalid⟩ := hrun.1
  refine ⟨Tvalid, ?_⟩
  intro t ht
  have hno := GenLimit.NoiseLossFeedback.not_allMarkers_observed_second hK hinput t
  have hout : outputAfterInput (sidePatientGenerator q) input t =
      negCode (PatientMachine.output cofiniteAnchorOracle projected t) :=
    sidePatientGenerator_negative_output hno
  have hv := hvalid t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    exact hK.1 (negCode_negative _)
  · rw [hout]
    intro hsamp
    obtain ⟨s, hs, hseq⟩ := GenLimit.Generic.mem_sample_iff.mp hsamp
    apply hv.2.1 s (Nat.lt_succ_iff.mp hs)
    change negativeProject (input s) = _
    rw [hseq, negativeProject_negCode]
  · intro s hs
    have hnos := GenLimit.NoiseLossFeedback.not_allMarkers_observed_second hK hinput s
    rw [sidePatientGenerator_negative_output hnos, hout]
    exact fun heq => hv.2.2 s hs
      (GenLimit.UnionClosedness.negativeCode_injective heq)



lemma relativeLowerDensity_remove_finite
    {A B K : Set ℕ} (hK : K.Infinite) (hAK : A ⊆ K)
    (hBA : B ⊆ A) (hfinite : (A \ B).Finite) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hBK : B ⊆ K := hBA.trans hAK
  have hsource_nonneg : ∀ n, 0 ≤ source n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsource_le_one : ∀ n, source n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [source, hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n
  have htarget_nonneg : ∀ n, 0 ≤ target n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htarget_le_one : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [target, hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcastK : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hcastK
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      hcountK.eventually (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hdiff : GenLimit.PatientScope.prefixCount A n ≤
        GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
      classical
      unfold GenLimit.PatientScope.prefixCount
      let left := GenLimit.PatientScope.prefixFinset A n
      let good := GenLimit.PatientScope.prefixFinset B n
      let bad := GenLimit.PatientScope.prefixFinset (A \ B) n
      have hsub : left ⊆ good ∪ bad := by
        intro x hx
        simp only [left, good, bad, GenLimit.PatientScope.mem_prefixFinset,
          Finset.mem_union, Set.mem_diff] at hx ⊢
        by_cases hxB : x ∈ B
        · exact Or.inl ⟨hx.1, hxB⟩
        · exact Or.inr ⟨hx.1, hx.2, hxB⟩
      have hbad : bad.card ≤ hfinite.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        rw [Set.Finite.mem_toFinset]
        exact (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
      exact (Finset.card_le_card hsub).trans
        ((Finset.card_union_le good bad).trans
          (Nat.add_le_add_left hbad good.card))
    have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    dsimp [source, target, error]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hdiff) hkpos.le
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrs : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herr : ∀ᶠ n : ℕ in atTop, error n < r - y :=
    herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrs, herr, hprefix] with n hrsn herrn hpn
  linarith

lemma relativeLowerDensity_cofinite_ambient
    {A K : Set ℕ} (hK : K.Infinite) (hAK : A ⊆ K)
    (hfinite : Kᶜ.Finite) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity A Set.univ := by
  classical
  unfold GenLimit.PatientScope.relativeLowerDensity
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hcountK)
  have hsnonneg : ∀ n, 0 ≤ source n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htnonneg : ∀ n, 0 ≤ target n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htle : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [target, hn]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast (GenLimit.PatientScope.prefixCount_mono hAK n).trans (by
        simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
          using Finset.card_filter_le (Finset.range n) (fun x => x ∈ K))
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    have hkpos : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      hcountK.eventually (eventually_gt_atTop 0)
    filter_upwards [hkpos] with n hn
    have hmissing : n ≤ GenLimit.PatientScope.prefixCount K n + hfinite.toFinset.card := by
      classical
      have hall : (Finset.range n).card ≤
          (GenLimit.PatientScope.prefixFinset K n ∪
            GenLimit.PatientScope.prefixFinset Kᶜ n).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_range, Finset.mem_union,
          GenLimit.PatientScope.mem_prefixFinset, Set.mem_compl_iff] at hx ⊢
        by_cases hxK : x ∈ K
        · exact Or.inl ⟨hx, hxK⟩
        · exact Or.inr ⟨hx, hxK⟩
      have hc : (GenLimit.PatientScope.prefixFinset Kᶜ n).card ≤
          hfinite.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        rw [Set.Finite.mem_toFinset]
        exact (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
      simpa [GenLimit.PatientScope.prefixCount] using hall.trans
        ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left hc _))
    have ha : GenLimit.PatientScope.prefixCount A n ≤
        GenLimit.PatientScope.prefixCount K n :=
      GenLimit.PatientScope.prefixCount_mono hAK n
    have hk : GenLimit.PatientScope.prefixCount K n ≤ n := by
      simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
        using Finset.card_filter_le (Finset.range n) (fun x => x ∈ K)
    have hnpos : (0 : ℝ) < n := by
      have : 0 < GenLimit.PatientScope.prefixCount K n := hn
      exact_mod_cast lt_of_lt_of_le this (by
        simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
          using Finset.card_filter_le (Finset.range n) (fun x => x ∈ K))
    have hkposR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    dsimp [source, target, error]
    let a := GenLimit.PatientScope.prefixCount A n
    let k := GenLimit.PatientScope.prefixCount K n
    let c := hfinite.toFinset.card
    have hdiff : n - k ≤ c := by dsimp [k, c]; omega
    have hprod : a * (n - k) ≤ k * c :=
      Nat.mul_le_mul ha hdiff
    have hnat : a * n ≤ a * k + n * c := by
      calc
        a * n = a * k + a * (n - k) := by
          rw [← Nat.mul_add]
          congr
          omega
        _ ≤ a * k + k * c := Nat.add_le_add_left hprod _
        _ ≤ a * k + n * c := Nat.add_le_add_left (Nat.mul_le_mul_right c hk) _
    have hreal : (a : ℝ) * n ≤ (a : ℝ) * k + (n : ℝ) * c := by
      exact_mod_cast hnat
    field_simp [hnpos.ne', hkposR.ne']
    exact hreal
  have hmain : liminf source atTop ≤ liminf target atTop := by
    apply (le_liminf_iff
      (isCoboundedUnder_ge_of_le atTop htle)
      (isBoundedUnder_of ⟨0, htnonneg⟩)).2
    intro y hy
    obtain ⟨r, hyr, hr⟩ := exists_between hy
    have hrs : ∀ᶠ n : ℕ in atTop, r < source n :=
      eventually_lt_of_lt_liminf hr (isBoundedUnder_of ⟨0, hsnonneg⟩)
    have herr : ∀ᶠ n : ℕ in atTop, error n < r - y :=
      herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
    filter_upwards [hrs, herr, hprefix] with n hrsn herrn hpn
    linarith
  simpa [source, target, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset] using hmain

lemma balanced_density_of_side
    {A B K : Set ℕ} {offset : ℕ} (hoffset : offset ≤ 1)
    (hBK : B ⊆ K)
    (hembed : ∀ n, n ∈ A → 2 * n + offset ∈ B)
    (hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A Set.univ) :
    (1 / 4 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity B K := by
  classical
  unfold GenLimit.PatientScope.relativeLowerDensity at hhalf ⊢
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n => 1 / (n : ℝ)
  have hsource_eq : liminf source atTop =
      liminf (fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount Set.univ n : ℝ)) atTop := by
    congr 1
    funext n
    simp [source, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]
  have hhalf' : (1 / 2 : ℝ) ≤ liminf source atTop := by
    rwa [← hsource_eq] at hhalf
  have hcomp : liminf (fun n => source (n / 2)) atTop = liminf source atTop := by
    rw [show (fun n => source (n / 2)) = source ∘ (fun n => n / 2) by rfl]
    rw [liminf_comp, Filter.map_div_atTop_eq_nat 2 (by omega)]
  have herror : Tendsto error atTop (nhds 0) := by
    dsimp [error]
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp tendsto_id)
  have hsource_nonneg : ∀ n, 0 ≤ source n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcomp_nonneg : ∀ n, 0 ≤ source (n / 2) := fun n => hsource_nonneg _
  have htarget_nonneg : ∀ n, 0 ≤ target n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htarget_le_one : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [target, hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  have hprefix : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) * source (N / 2) - error N ≤ target N := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    let n := N / 2
    have hn : 0 < n := by dsimp [n]; omega
    have hnN0 : 2 * n ≤ N := by dsimp [n]; omega
    have hcount : GenLimit.PatientScope.prefixCount A n ≤
        GenLimit.PatientScope.prefixCount B N := by
      unfold GenLimit.PatientScope.prefixCount
      apply Finset.card_le_card_of_injOn (fun x => 2 * x + offset)
      · intro x hx
        have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
        apply GenLimit.PatientScope.mem_prefixFinset.mpr
        refine ⟨?_, hembed x hx'.2⟩
        calc
          2 * x + offset ≤ 2 * x + 1 := Nat.add_le_add_left hoffset _
          _ < 2 * n := by omega
          _ ≤ N := hnN0
      · intro x _ y _ hxy
        have hmul : 2 * x = 2 * y := Nat.add_right_cancel hxy
        omega
    have ha : GenLimit.PatientScope.prefixCount A n ≤ n := by
      simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
        using Finset.card_filter_le (Finset.range n) (fun x => x ∈ A)
    have hk : GenLimit.PatientScope.prefixCount K N ≤ N := by
      simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
        using Finset.card_filter_le (Finset.range N) (fun x => x ∈ K)
    have hnN : 2 * n ≤ N := by dsimp [n]; omega
    have hNn : N ≤ 2 * n + 1 := by dsimp [n]; omega
    have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_trans Nat.zero_lt_one hN)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases hbzero : GenLimit.PatientScope.prefixCount B N = 0
    · have hazero : GenLimit.PatientScope.prefixCount A n = 0 :=
        Nat.eq_zero_of_le_zero (hbzero ▸ hcount)
      have hz : (1 / 2 : ℝ) * source n - error N ≤ 0 := by
        simp [source, error, hazero]
      exact hz.trans (htarget_nonneg N)
    · have hbpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount B N := by
        exact_mod_cast Nat.pos_of_ne_zero hbzero
      have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K N := by
        exact lt_of_lt_of_le hbpos (by exact_mod_cast
          GenLimit.PatientScope.prefixCount_mono hBK N)
      dsimp [source, target, error]
      have hratio1 :
          (GenLimit.PatientScope.prefixCount A n : ℝ) / (N : ℝ) ≤
            (GenLimit.PatientScope.prefixCount B N : ℝ) /
              (GenLimit.PatientScope.prefixCount K N : ℝ) := by
        calc
          _ ≤ (GenLimit.PatientScope.prefixCount B N : ℝ) / (N : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast hcount) hNR.le
          _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hkpos
            (by exact_mod_cast hk)
      have halgebra :
          (1 / 2 : ℝ) *
              ((GenLimit.PatientScope.prefixCount A n : ℝ) / (n : ℝ)) -
              1 / (N : ℝ) ≤
            (GenLimit.PatientScope.prefixCount A n : ℝ) / (N : ℝ) := by
        have haR : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤ n := by
          exact_mod_cast ha
        have hnNR : (2 : ℝ) * n ≤ N := by exact_mod_cast hnN
        have hNnR : (N : ℝ) ≤ 2 * n + 1 := by exact_mod_cast hNn
        field_simp [hnR.ne', hNR.ne']
        nlinarith
      exact halgebra.trans hratio1
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have h2r : 2 * r < liminf (fun n => source (n / 2)) atTop := by
    rw [hcomp]
    linarith
  have hrs : ∀ᶠ n : ℕ in atTop, 2 * r < source (n / 2) :=
    eventually_lt_of_lt_liminf h2r (isBoundedUnder_of ⟨0, hcomp_nonneg⟩)
  have herr : ∀ᶠ n : ℕ in atTop, error n < r - y :=
    herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrs, herr, hprefix] with n hrsn herrn hpn
  linarith

lemma balanced_even (n : ℕ) : balanced (2 * n) = positiveCode0 n := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp [balanced, positiveCode0] <;> omega

lemma balanced_odd (n : ℕ) : balanced (2 * n + 1) = negCode n := by
  rw [show 2 * n + 1 = (2 * n) + 1 by omega]
  simp [balanced, negCode, GenLimit.UnionClosedness.negativeCode] <;> omega


lemma positiveRanks0_infinite_of_tail
    {K : Set ℤ} {j : ℕ}
    (htail : GenLimit.UnionClosedness.positiveTail j ⊆ K) :
    (positiveRanks0 K).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n => n + (j + 1)) (by
      intro a b h
      exact Nat.add_right_cancel h)
  intro n
  change positiveCode0 (n + j + 1) ∈ K
  apply htail
  refine ⟨n, ?_⟩
  simp [positiveCode0, GenLimit.UnionClosedness.positiveCode, Nat.add_assoc]
  ring

lemma sidePatientGenerator_first_density
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input K q) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input (outputAfterInput (sidePatientGenerator q) input) ∩ K) K := by
  classical
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Td, hTd⟩ :=
    GenLimit.NoiseLossFeedback.allMarkers_eventually_observed hinput hmarkers
  let projected : ℕ → ℕ := fun s => positiveProject (input s)
  let R : Set ℕ := Set.range projected
  let outN := PatientMachine.output cofiniteAnchorOracle projected
  have hzeroK : (0 : ℤ) ∈ K := by
    apply hmarkers
    simp [GenLimit.NoiseLossFeedback.omissionMarkerFinset]
  have hzeroR : 0 ∈ R := positive_project_range_zero hinput.2.1 hzeroK
  have hcofiniteR : Rᶜ.Finite := positive_project_range_cofinite hinput.2.1 htail
  obtain ⟨i, hi⟩ := exists_cofiniteAnchor_index hzeroR hcofiniteR
  have hpresents : GenLimit.Presents projected (cofiniteAnchorOracle.language i) := by
    change Set.range projected = cofiniteAnchorOracle.language i
    exact hi.symm
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity
    cofiniteAnchorOracle projected hpresents
  have hlang : cofiniteAnchorOracle.language i = R := by
    exact hpresents.symm
  have hKR : positiveRanks0 K ⊆ R :=
    positiveRanks0_subset_project_range hinput.2.1
  have hfiniteBad : (R \ positiveRanks0 K).Finite :=
    project_range_difference_finite hinput.1 hzeroK hinput.2.2
  have hKpos : (positiveRanks0 K).Infinite := positiveRanks0_infinite_of_tail htail
  let A0 := GenLimit.GeneratorFirst projected outN ∩ positiveRanks0 K
  let early : Set ℕ := outN '' Set.Iio Td
  let A := A0 \ early
  have hbase : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst projected outN ∩ R) R := by
    simpa only [PatientMachine.patientLowerDensity, outN, hlang] using hrun.2
  have hhalf0 : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A0 (positiveRanks0 K) := by
    exact hbase.trans
      (relativeLowerDensity_transfer_finite_addition hKpos hKR hfiniteBad)
  have hearly : early.Finite := (Set.finite_Iio Td).image outN
  have hdiff : (A0 \ A).Finite := by
    apply hearly.subset
    intro n hn
    by_contra hnearly
    exact hn.2 ⟨hn.1, hnearly⟩
  have hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A Set.univ := by
    have hremove := relativeLowerDensity_remove_finite hKpos
      (Set.inter_subset_right : A0 ⊆ positiveRanks0 K)
      (Set.diff_subset : A ⊆ A0) hdiff
    have hAK : A ⊆ positiveRanks0 K := Set.diff_subset.trans Set.inter_subset_right
    have hKcomp : (positiveRanks0 K)ᶜ.Finite := by
      apply (hcofiniteR.union hfiniteBad).subset
      intro n hn
      by_cases hnR : n ∈ R
      · exact Or.inr ⟨hnR, hn⟩
      · exact Or.inl hnR
    exact hhalf0.trans (hremove.trans
      (relativeLowerDensity_cofinite_ambient hKpos hAK hKcomp))
  unfold balancedRelativeLowerDensity
  apply balanced_density_of_side (offset := 0) (by omega)
    (Set.inter_subset_right : balancedRanks
      (GeneratorFirstOn input (outputAfterInput (sidePatientGenerator q) input) ∩ K) ⊆
        balancedRanks K) _ hhalf
  intro n hn
  rcases hn.1.1 with ⟨t, hout, hfresh⟩
  have ht : Td ≤ t := by
    by_contra hnot
    apply hn.2
    exact ⟨t, Set.mem_Iio.mpr (Nat.lt_of_not_ge hnot), hout⟩
  have hmarkers_t := hTd t ht
  change balanced (2 * n) ∈
    GeneratorFirstOn input (outputAfterInput (sidePatientGenerator q) input) ∩ K
  rw [balanced_even]
  refine ⟨⟨t, ?_, ?_⟩, hn.1.2⟩
  · rw [sidePatientGenerator_positive_output hmarkers_t]
    exact congrArg positiveCode0 hout
  · intro s hs heq
    apply hfresh s hs
    change projected s = n
    dsimp [projected]
    rw [heq, positiveProject_positiveCode0]

lemma sidePatientGenerator_second_density
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      input K q) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input (outputAfterInput (sidePatientGenerator q) input) ∩ K) K := by
  classical
  let projected : ℕ → ℕ := fun s => negativeProject (input s)
  let outN := PatientMachine.output cofiniteAnchorOracle projected
  have hrange : Set.range projected = Set.univ :=
    negative_project_range_eq_univ hinput.2.1 hK.1
  have hzero : 0 ∈ (Set.univ : Set ℕ) := Set.mem_univ 0
  have hfinite : ((Set.univ : Set ℕ)ᶜ).Finite := by simp
  obtain ⟨i, hi⟩ := exists_cofiniteAnchor_index hzero hfinite
  have hpresents : GenLimit.Presents projected (cofiniteAnchorOracle.language i) := by
    change Set.range projected = cofiniteAnchorOracle.language i
    exact hrange.trans hi.symm
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity
    cofiniteAnchorOracle projected hpresents
  have hlang : cofiniteAnchorOracle.language i = Set.univ := by
    exact hpresents.symm.trans hrange
  have hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst projected outN) Set.univ := by
    simpa [PatientMachine.patientLowerDensity, outN, hlang] using hrun.2
  unfold balancedRelativeLowerDensity
  apply balanced_density_of_side (offset := 1) (by omega)
    (Set.inter_subset_right : balancedRanks
      (GeneratorFirstOn input (outputAfterInput (sidePatientGenerator q) input) ∩ K) ⊆
        balancedRanks K) _ hhalf
  intro n hn
  rcases hn with ⟨t, hout, hfresh⟩
  have hno := GenLimit.NoiseLossFeedback.not_allMarkers_observed_second hK hinput t
  change balanced (2 * n + 1) ∈
    GeneratorFirstOn input (outputAfterInput (sidePatientGenerator q) input) ∩ K
  rw [balanced_odd]
  refine ⟨⟨t, ?_, ?_⟩, hK.1 (negCode_negative n)⟩
  · rw [sidePatientGenerator_negative_output hno]
    exact congrArg negCode hout
  · intro s hs heq
    apply hfresh s hs
    change projected s = n
    dsimp [projected]
    rw [heq, negativeProject_negCode]



abbrev omissionMarkers (q : ℕ) : Set ℤ :=
  (GenLimit.NoiseLossFeedback.omissionMarkerFinset q : Set ℤ)

abbrev negCode' := GenLimit.UnionClosedness.negativeCode

def encodedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  omissionMarkers q ∪ GenLimit.UnionClosedness.positiveTail (q + 1) ∪
    negCode' '' S

lemma encodedLanguage_mem_first (q : ℕ) (S : Set ℕ) :
    encodedLanguage q S ∈
      GenLimit.NoiseLossFeedback.finiteOmissionFirstClass q := by
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · refine ⟨q + 1, ?_⟩
    intro z hz
    exact Or.inl (Or.inr hz)

lemma negCode_mem_encodedLanguage (q n : ℕ) (S : Set ℕ) :
    negCode' n ∈ encodedLanguage q S ↔ n ∈ S := by
  constructor
  · intro hn
    rcases hn with (hmarker | htail) | hcode
    · exact False.elim
        (GenLimit.NoiseLossFeedback.negativeCode_not_marker q n hmarker)
    · rcases htail with ⟨k, hk⟩
      change GenLimit.UnionClosedness.positiveCode (q + 1 + k) = negCode' n at hk
      have hpositive := GenLimit.UnionClosedness.positiveCode_mem (q + 1 + k)
      rw [hk] at hpositive
      exact False.elim
        ((Int.not_lt_of_ge (Int.le_of_lt hpositive))
          (GenLimit.UnionClosedness.negativeCode_mem n))
    · rcases hcode with ⟨m, hm, hmn⟩
      exact (GenLimit.UnionClosedness.negativeCode_injective hmn).symm ▸ hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

lemma encodedLanguage_injective (q : ℕ) :
    Function.Injective (encodedLanguage q) := by
  intro S T hST
  apply Set.ext
  intro n
  have hprobe := Set.ext_iff.mp hST (negCode' n)
  rw [negCode_mem_encodedLanguage, negCode_mem_encodedLanguage] at hprobe
  exact hprobe

lemma finiteOmissionClass_uncountable (q : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → GenLimit.NoiseLossFeedback.finiteOmissionClass q :=
    fun S => ⟨encodedLanguage q S,
      Set.mem_union_left _ (encodedLanguage_mem_first q S)⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply encodedLanguage_injective q
    exact congrArg Subtype.val hST
  letI : Countable (GenLimit.NoiseLossFeedback.finiteOmissionClass q) :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

lemma finiteOmission_adjacent_failure (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
        ∃ input : Stream ℤ,
          GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
              input K (q + 1) ∧
            ¬SampleFreshGeneratesAfterInput
              input (outputAfterInput gen input) K := by
  intro gen
  by_contra hnone
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  have hsuccess : SampleFreshGeneratesAfterInput
      input (outputAfterInput gen input) K := by
    by_contra hfailure
    apply hnone
    exact ⟨K, hK, input, hinput, hfailure⟩
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt] using hsuccess

theorem stage3_uncountable_separation :
    Stage3Case019.SeparationClause := by
  intro q
  refine ⟨GenLimit.NoiseLossFeedback.finiteOmissionClass q,
    finiteOmissionClass_uncountable q,
    GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q, ?_,
    finiteOmission_adjacent_failure q⟩
  refine ⟨sidePatientGenerator q, ?_⟩
  intro K hK input hinput
  rcases hK with hfirst | hsecond
  · exact ⟨sidePatientGenerator_first_novel hfirst hinput,
      sidePatientGenerator_first_density hfirst hinput⟩
  · exact ⟨sidePatientGenerator_second_novel hsecond hinput,
      sidePatientGenerator_second_density hsecond hinput⟩

end Case019

theorem stage3_result : Stage3Case019.MainClaim := by
  exact ⟨Case019.stage3_countable_half_density,
    Case019.stage3_uncountable_separation⟩
