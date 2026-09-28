import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Theorem41Cardinality
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Stage3Case019

noncomputable def familyOracle
    (family : LanguageFamily ℕ) (hinfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

theorem core_sample_eq_of_eq_on_prefix
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  classical
  unfold GenLimit.sample
  apply Finset.image_congr
  intro k hk
  exact h k (Finset.mem_range.mp hk)

theorem consistent_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (h : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t) :
    GenLimit.Consistent C stream₁ t i ↔
      GenLimit.Consistent C stream₂ t i := by
  classical
  unfold GenLimit.Consistent
  rw [h]

theorem recursiveCritical_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (h : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t) :
    GenLimit.RecursiveCritical C stream₁ t i ↔
      GenLimit.RecursiveCritical C stream₂ t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [GenLimit.RecursiveCritical] using
            consistent_congr_sample C (i := 0) h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_congr_sample C h]
          constructor
          · rintro ⟨hcon, hrest⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjcrit
            exact hrest j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hcon, hrest⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjcrit
            exact hrest j hj ((ih j (by omega)).mp hjcrit)

theorem consistentIndices_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t scope : ℕ}
    (h : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.consistentIndices C stream₁ t scope =
      GenLimit.PatientMachine.consistentIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_congr_sample C h]

theorem criticalIndices_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t scope : ℕ}
    (h : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.criticalIndices C stream₁ t scope =
      GenLimit.PatientMachine.criticalIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_congr_sample C h]

theorem survivingCriticalIndices_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t scope : ℕ}
    (ht : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t)
    (ht1 : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.survivingCriticalIndices C stream₁ t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr_sample C ht,
    recursiveCritical_congr_sample C ht1]

theorem highestCritical_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t scope fallback : ℕ}
    (h : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.highestCritical C stream₁ t scope fallback =
      GenLimit.PatientMachine.highestCritical C stream₂ t scope fallback := by
  classical
  let chooseMax := fun candidates : Finset ℕ =>
    if hne : candidates.Nonempty then candidates.max' hne else fallback
  have hc := criticalIndices_congr_sample C (scope := scope) h
  exact congrArg chooseMax hc

theorem highestSurvivor_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t scope fallback : ℕ}
    (ht : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t)
    (ht1 : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.highestSurvivor C stream₁ t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C stream₂ t scope fallback := by
  classical
  let chooseMax := fun candidates : Finset ℕ =>
    if hne : candidates.Nonempty then candidates.max' hne else fallback
  have hc := survivingCriticalIndices_congr_sample C
    (scope := scope) ht ht1
  exact congrArg chooseMax hc

theorem lowestConsistentInScope_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t scope fallback : ℕ}
    (h : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.lowestConsistentInScope C stream₁ t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C stream₂ t scope fallback := by
  classical
  let chooseMin := fun candidates : Finset ℕ =>
    if hne : candidates.Nonempty then candidates.min' hne else fallback
  have hc := consistentIndices_congr_sample C (scope := scope) h
  exact congrArg chooseMin hc

theorem lowestConsistent_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t fallback : ℕ}
    (h : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.lowestConsistent C stream₁ t fallback =
      GenLimit.PatientMachine.lowestConsistent C stream₂ t fallback := by
  classical
  let chooseMin := fun p : ℕ → Prop =>
    if hex : ∃ i, p i then Nat.find hex else fallback
  have hp : (fun i => GenLimit.Consistent C stream₁ t i) =
      fun i => GenLimit.Consistent C stream₂ t i := by
    funext i
    exact propext (consistent_congr_sample C h)
  exact congrArg chooseMin hp

theorem stableDecision_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (ht1 : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.stableDecision C stream₁ t old =
      GenLimit.PatientMachine.stableDecision C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp only [dif_pos hwait]
    rw [highestCritical_congr_sample C ht1]
  · simp only [dif_neg hwait]

theorem backtrackDecision_congr_sample
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (ht : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t)
    (ht1 : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.backtrackDecision C stream₁ t old =
      GenLimit.PatientMachine.backtrackDecision C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.backtrackDecision
  have hconsistent := consistentIndices_congr_sample C
    (scope := old.scope) ht1
  have hsurviving := survivingCriticalIndices_congr_sample C
    (scope := old.scope) ht ht1
  rw [hconsistent]
  by_cases hcon :
      (GenLimit.PatientMachine.consistentIndices C stream₂ (t + 1) old.scope).Nonempty
  · simp only [dif_pos hcon]
    rw [hsurviving]
    by_cases hsurv :
        (GenLimit.PatientMachine.survivingCriticalIndices C stream₂ t old.scope).Nonempty
    · simp only [if_pos hsurv]
      rw [highestSurvivor_congr_sample C ht ht1]
    · simp only [if_neg hsurv]
      rw [lowestConsistentInScope_congr_sample C ht1]
  · simp only [dif_neg hcon]
    rw [lowestConsistent_congr_sample C ht1]
    have hall : (∃ j, GenLimit.Consistent C stream₁ (t + 1) j) ↔
        ∃ j, GenLimit.Consistent C stream₂ (t + 1) j := by
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, (consistent_congr_sample C ht1).mp hj⟩
      · rintro ⟨j, hj⟩
        exact ⟨j, (consistent_congr_sample C ht1).mpr hj⟩
    rw [hall]

theorem decide_congr_prefix
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (ht : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t)
    (ht1 : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.decide C stream₁ t old =
      GenLimit.PatientMachine.decide C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [consistent_congr_sample C ht1]
  by_cases hcon : GenLimit.Consistent C stream₂ (t + 1) old.focus
  · simp only [if_pos hcon]
    exact stableDecision_congr_sample C old ht1
  · simp only [if_neg hcon]
    exact backtrackDecision_congr_sample C old ht ht1

theorem leastAvailable_congr_sample
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.leastAvailable C hInfinite stream₁ t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite stream₂ t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  apply propext
  unfold GenLimit.PatientMachine.Available
  rw [h]

theorem patient_run_congr_prefix
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : ℕ → ℕ} :
    ∀ t, (∀ k, k < t → stream₁ k = stream₂ k) →
      GenLimit.PatientMachine.run O stream₁ t =
        GenLimit.PatientMachine.run O stream₂ t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      have hrun := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      rw [hrun]
      have ht : GenLimit.sample stream₁ t =
          GenLimit.sample stream₂ t :=
        core_sample_eq_of_eq_on_prefix
          (fun k hk => h k (by omega))
      have ht1 : GenLimit.sample stream₁ (t + 1) =
          GenLimit.sample stream₂ (t + 1) :=
        core_sample_eq_of_eq_on_prefix
          (fun k hk => h k (by omega))
      unfold GenLimit.PatientMachine.processRound
      dsimp only
      rw [decide_congr_prefix O.language _ ht ht1]
      rw [leastAvailable_congr_sample O.language O.infinite' _ _ ht1]

theorem patient_output_congr_prefix
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : ℕ → ℕ} (t : ℕ)
    (h : ∀ k, k ≤ t → stream₁ k = stream₂ k) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  rw [GenLimit.PatientMachine.output_eq_leastAvailable,
    GenLimit.PatientMachine.output_eq_leastAvailable]
  have hrun := patient_run_congr_prefix O t
    (fun k hk => h k (Nat.le_of_lt hk))
  rw [hrun]
  have ht : GenLimit.sample stream₁ t =
      GenLimit.sample stream₂ t :=
    core_sample_eq_of_eq_on_prefix
      (fun k hk => h k (by omega))
  have ht1 : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1) :=
    core_sample_eq_of_eq_on_prefix
      (fun k hk => h k (by omega))
  have hd := decide_congr_prefix O.language
    (GenLimit.PatientMachine.run O stream₂ t) ht ht1
  rw [hd]
  exact leastAvailable_congr_sample O.language O.infinite' _ _ ht1

noncomputable def patientPrefixGenerator
    (O : GenLimit.OracleFamily) : Generator ℕ :=
  fun n xs =>
    if hn : n = 0 then 0 else
      GenLimit.PatientMachine.output O
        (fun k => if hk : k < n then xs ⟨k, hk⟩ else 0) (n - 1)

theorem outputAfterInput_patientPrefixGenerator
    (O : GenLimit.OracleFamily) (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (patientPrefixGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  unfold outputAfterInput GenLimit.Generic.output patientPrefixGenerator
  simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceDIte]
  apply patient_output_congr_prefix O
  intro k hk
  simp [show k < t + 1 by omega]

theorem prefixCount_le_finite_card
    {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  exact Set.Finite.mem_toFinset hF |>.2
    (GenLimit.PatientScope.mem_prefixFinset.mp hx).2

theorem relativeLowerDensity_mono_finite_extension
    {A B K R : Set ℕ}
    (hK : K.Infinite) (hKR : K ⊆ R)
    (hAR : A ⊆ R) (hAK : A ∩ K ⊆ B) (hBK : B ⊆ K)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity A R ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  let c := hfinite.toFinset.card
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let err : ℕ → ℝ := fun n =>
    (c : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hKtend := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herr : Tendsto err atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_iff.mpr hKtend)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + err n := by
    filter_upwards [hKtend.eventually (eventually_gt_atTop 0)] with n hn
    have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hden : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hnumNat : GenLimit.PatientScope.prefixCount A n ≤
        GenLimit.PatientScope.prefixCount B n + c := by
      classical
      let FA := GenLimit.PatientScope.prefixFinset A n
      let FB := GenLimit.PatientScope.prefixFinset B n
      let FF := GenLimit.PatientScope.prefixFinset (R \ K) n
      have hsub : FA ⊆ FB ∪ FF := by
        intro x hx
        have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
        by_cases hxK : x ∈ K
        · exact Finset.mem_union_left _ <|
            GenLimit.PatientScope.mem_prefixFinset.mpr
              ⟨hx'.1, hAK ⟨hx'.2, hxK⟩⟩
        · exact Finset.mem_union_right _ <|
            GenLimit.PatientScope.mem_prefixFinset.mpr
              ⟨hx'.1, hAR hx'.2, hxK⟩
      have hcard := (Finset.card_le_card hsub).trans
        (Finset.card_union_le FB FF)
      have hff : FF.card ≤ c := prefixCount_le_finite_card hfinite n
      exact hcard.trans (Nat.add_le_add_left hff _)
    have hnum : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
        GenLimit.PatientScope.prefixCount B n + c := by exact_mod_cast hnumNat
    dsimp [source, target, err]
    calc
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
          GenLimit.PatientScope.prefixCount R n
          ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
              GenLimit.PatientScope.prefixCount K n := by
                apply div_le_div_of_nonneg_left (by positivity) hkpos
                exact_mod_cast hden
      _ ≤ (GenLimit.PatientScope.prefixCount B n + c : ℝ) /
              GenLimit.PatientScope.prefixCount K n := by
                exact div_le_div_of_nonneg_right hnum hkpos.le
      _ = (GenLimit.PatientScope.prefixCount B n : ℝ) /
              GenLimit.PatientScope.prefixCount K n +
            (c : ℝ) / GenLimit.PatientScope.prefixCount K n := by
                rw [add_div]
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf source atTop ≤ liminf target atTop
  have htarget_le : ∀ n, target n ≤ 1 := by
    intro n
    dsimp [target]
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  have htarget_nonneg : ∀ n, (0 : ℝ) ≤ target n := by
    intro n
    dsimp [target]
    positivity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrsource⟩ := exists_between hy
  have hrevent : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrsource
      (isBoundedUnder_of ⟨0, fun n => by dsimp [source]; positivity⟩)
  have herrevent : ∀ᶠ n : ℕ in atTop, err n < r - y := by
    have : 0 < r - y := by linarith
    exact herr.eventually (Iio_mem_nhds this)
  filter_upwards [hrevent, herrevent, hprefix] with n hs he hp
  linarith

theorem stage3_countable_half_density : CountableClause := by
  intro q family hinfinite
  let O := familyOracle family hinfinite
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientPrefixGenerator E, ?_⟩
  intro i input hinput
  have hnoiseFinite : (Set.range input \ O.language i).Finite := by
    exact
      ((GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
        (Set.range input) (O.language i) q).mp hinput.2.2).1
  have hcontam :
      GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
        input (O.language i) := by
    refine ⟨hinput.1, ?_, ?_⟩
    · exact (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
        hinput.1).mpr hnoiseFinite
    · unfold GenLimit.InfiniteContamination.FiniteOmissions
      have hempty : O.language i \ Set.range input = ∅ :=
        Set.diff_eq_empty.mpr hinput.2.1
      rw [hempty]
      exact Set.finite_empty
  obtain ⟨j, _hj, hpresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hpatient :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      E input hpresents
  have houtfun : outputAfterInput (patientPrefixGenerator E) input =
      GenLimit.PatientMachine.output E input := by
    funext t
    exact outputAfterInput_patientPrefixGenerator E input t
  constructor
  · obtain ⟨T, hT⟩ := hpatient.1
    obtain ⟨S, hS⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample hpresents
        hnoiseFinite.toFinset (by
          intro x hx
          have hx' := (Set.Finite.mem_toFinset hnoiseFinite).mp hx
          exact hpresents.symm ▸ hx'.1)
    refine ⟨max T S, ?_⟩
    intro t ht
    have h := hT t ((Nat.le_max_left _ _).trans ht)
    rw [houtfun]
    refine ⟨?_, ?_, h.2.2⟩
    · by_contra hout
      have hnoise : GenLimit.PatientMachine.output E input t ∈
          (Set.range input \ O.language i) :=
        ⟨hpresents.symm ▸ h.1, hout⟩
      have hmem := hS ((Set.Finite.mem_toFinset hnoiseFinite).mpr hnoise)
      obtain ⟨s, hs, heq⟩ := GenLimit.Generic.mem_sample_iff.mp hmem
      exact h.2.1 s (by omega) heq
    · intro houtmem
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp houtmem
      exact h.2.1 s (by omega) heq
  · have hdens := hpatient.2
    unfold GenLimit.PatientMachine.patientLowerDensity at hdens
    rw [← houtfun] at hdens
    have hKR : O.language i ⊆ E.language j := by
      intro x hx
      exact hpresents ▸ hinput.2.1 hx
    have hfiniteE : (E.language j \ O.language i).Finite := by
      rw [← hpresents]
      exact hnoiseFinite
    apply hdens.trans
    apply relativeLowerDensity_mono_finite_extension
      (hinfinite i) hKR
      (fun _ hx => hx.2)
      (by rintro x ⟨⟨hxfirst, _⟩, hxK⟩; exact ⟨hxfirst, hxK⟩)
      (fun _ hx => hx.2)
      hfiniteE

def sweepCode (positive : Bool) (n : ℕ) : ℤ :=
  if positive then GenLimit.UnionClosedness.positiveCode n
  else GenLimit.UnionClosedness.negativeCode n

theorem sweepCode_injective (positive : Bool) :
    Function.Injective (sweepCode positive) := by
  cases positive
  · simpa [sweepCode] using
      GenLimit.UnionClosedness.negativeCode_injective
  · simpa [sweepCode] using
      GenLimit.UnionClosedness.positiveCode_injective

theorem sweepAvailable_infinite (positive : Bool) (sample : Finset ℤ) :
    {n : ℕ | sweepCode positive n ∉ sample}.Infinite := by
  classical
  have hbad : {n : ℕ | sweepCode positive n ∈ sample}.Finite := by
    apply Set.Finite.preimage (sweepCode_injective positive).injOn
    exact sample.finite_toSet
  simpa only [Set.mem_setOf_eq, Set.mem_compl_iff] using hbad.infinite_compl

noncomputable def rankedFreshIndex
    (positive : Bool) (n : ℕ) (sample : Finset ℤ) : ℕ :=
  Nat.nth (fun k => sweepCode positive k ∉ sample) n

noncomputable def rankedSweepGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    let positive := decide
      (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sequenceSample xs)
    sweepCode positive
      (rankedFreshIndex positive n (GenLimit.Generic.sequenceSample xs))

theorem rankedFreshIndex_fresh
    (positive : Bool) (n : ℕ) (sample : Finset ℤ) :
    sweepCode positive (rankedFreshIndex positive n sample) ∉ sample := by
  classical
  exact Nat.nth_mem_of_infinite
    (sweepAvailable_infinite positive sample) n

theorem rankedFreshIndex_le
    (positive : Bool) (n : ℕ) (sample : Finset ℤ) :
    rankedFreshIndex positive n sample ≤ n + sample.card := by
  classical
  let p : ℕ → Prop := fun k => sweepCode positive k ∉ sample
  let k := Nat.nth p n
  have hpinf : {k : ℕ | p k}.Infinite := by
    exact sweepAvailable_infinite positive sample
  have hcount : Nat.count p k = n :=
    Nat.count_nth_of_infinite hpinf n
  let good := (Finset.range k).filter p
  let bad := (Finset.range k).filter (fun j => ¬p j)
  have hgood : good.card = n := by
    simpa [good, Nat.count_eq_card_filter_range] using hcount
  have hpartition : good.card + bad.card = k := by
    simpa [good, bad] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := Finset.range k) p)
  have himage : (bad.image (sweepCode positive)).card = bad.card := by
    rw [Finset.card_image_iff]
    exact (sweepCode_injective positive).injOn
  have hsubset : bad.image (sweepCode positive) ⊆ sample := by
    intro z hz
    obtain ⟨j, hjbad, rfl⟩ := Finset.mem_image.mp hz
    have hjnot := (Finset.mem_filter.mp hjbad).2
    simpa [p] using hjnot
  have hbad : bad.card ≤ sample.card := by
    rw [← himage]
    exact Finset.card_le_card hsubset
  change k ≤ n + sample.card
  omega

theorem rankedSweepGenerator_spec
    (q n : ℕ) (xs : Fin n → ℤ) :
    let positive := decide
      (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sequenceSample xs)
    ∃ k ≤ 2 * n,
      rankedSweepGenerator q n xs = sweepCode positive k ∧
      rankedSweepGenerator q n xs ∉ GenLimit.Generic.sequenceSample xs := by
  dsimp [rankedSweepGenerator]
  let positive := decide
    (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.Generic.sequenceSample xs)
  refine ⟨rankedFreshIndex positive n (GenLimit.Generic.sequenceSample xs), ?_, rfl, ?_⟩
  · have heq : GenLimit.Generic.sequenceSample xs =
        Finset.univ.image xs := by
      ext z
      simp [GenLimit.Generic.mem_sequenceSample_iff]
    have hcard : (GenLimit.Generic.sequenceSample xs).card ≤ n := by
      rw [heq]
      exact (Finset.card_image_le.trans_eq (Finset.card_fin n))
    exact (rankedFreshIndex_le positive n _).trans (by omega)
  · exact rankedFreshIndex_fresh positive n _

theorem rankedFreshIndex_ge
    (positive : Bool) (n : ℕ) (sample : Finset ℤ) :
    n ≤ rankedFreshIndex positive n sample := by
  classical
  apply Nat.le_nth
  intro hfinite
  exact False.elim ((sweepAvailable_infinite positive sample) hfinite)

theorem rankedFreshIndex_ne_of_subset
    (positive : Bool) {m n : ℕ} {sample₁ sample₂ : Finset ℤ}
    (hmn : m < n) (hsub : sample₁ ⊆ sample₂) :
    rankedFreshIndex positive m sample₁ ≠
      rankedFreshIndex positive n sample₂ := by
  classical
  let p₁ : ℕ → Prop := fun k => sweepCode positive k ∉ sample₁
  let p₂ : ℕ → Prop := fun k => sweepCode positive k ∉ sample₂
  have hinf₁ : {k : ℕ | p₁ k}.Infinite :=
    sweepAvailable_infinite positive sample₁
  have hinf₂ : {k : ℕ | p₂ k}.Infinite :=
    sweepAvailable_infinite positive sample₂
  intro heq
  let k := Nat.nth p₁ m
  have hk : Nat.nth p₂ n = k := by
    exact heq.symm
  have hcount₁ : Nat.count p₁ k = m :=
    Nat.count_nth_of_infinite hinf₁ m
  have hcount₂ : Nat.count p₂ k = n := by
    rw [← hk]
    exact Nat.count_nth_of_infinite hinf₂ n
  have hfilter :
      (Finset.range k).filter p₂ ⊆ (Finset.range k).filter p₁ := by
    intro j hj
    have hjparts := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨hjparts.1, ?_⟩
    intro hjbad
    exact hjparts.2 (hsub hjbad)
  have hle : Nat.count p₂ k ≤ Nat.count p₁ k := by
    simpa [Nat.count_eq_card_filter_range] using
      Finset.card_le_card hfilter
  omega

theorem sample_prefix_subset
    (input : Stream ℤ) {m n : ℕ} (hmn : m ≤ n) :
    GenLimit.Generic.sample input m ⊆ GenLimit.Generic.sample input n := by
  intro z hz
  obtain ⟨j, hj, rfl⟩ := GenLimit.Generic.mem_sample_iff.mp hz
  exact GenLimit.Generic.mem_sample_iff.mpr ⟨j, lt_of_lt_of_le hj hmn, rfl⟩

theorem rankedSweep_output_ne
    (q : ℕ) (input : Stream ℤ) {s t : ℕ} (hst : s < t)
    (hbranch :
      decide (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sample input (s + 1)) =
      decide (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sample input (t + 1))) :
    outputAfterInput (rankedSweepGenerator q) input s ≠
      outputAfterInput (rankedSweepGenerator q) input t := by
  classical
  simp only [outputAfterInput, GenLimit.Generic.output,
    rankedSweepGenerator, GenLimit.Generic.sequenceSample_prefix]
  rw [hbranch]
  apply fun h => rankedFreshIndex_ne_of_subset
    (positive := decide
      (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sample input (t + 1)))
    (by omega)
    (sample_prefix_subset input (by omega))
    ((sweepCode_injective _ h))
theorem sweepCode_ne_of_bool_ne {a b : Bool} (hab : a ≠ b) (m n : ℕ) :
    sweepCode a m ≠ sweepCode b n := by
  cases a <;> cases b
  · exact False.elim (hab rfl)
  · intro h
    have hm := GenLimit.UnionClosedness.negativeCode_mem m
    have hn := GenLimit.UnionClosedness.positiveCode_mem n
    change GenLimit.UnionClosedness.negativeCode m < 0 at hm
    change 0 < GenLimit.UnionClosedness.positiveCode n at hn
    exact ne_of_lt (lt_trans hm hn) h
  · intro h
    have hm := GenLimit.UnionClosedness.positiveCode_mem m
    have hn := GenLimit.UnionClosedness.negativeCode_mem n
    change 0 < GenLimit.UnionClosedness.positiveCode m at hm
    change GenLimit.UnionClosedness.negativeCode n < 0 at hn
    exact ne_of_gt (lt_trans hn hm) h
  · exact False.elim (hab rfl)

theorem rankedSweep_output_ne_any
    (q : ℕ) (input : Stream ℤ) {s t : ℕ} (hst : s < t) :
    outputAfterInput (rankedSweepGenerator q) input s ≠
      outputAfterInput (rankedSweepGenerator q) input t := by
  classical
  let bs := decide (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
    GenLimit.Generic.sample input (s + 1))
  let bt := decide (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
    GenLimit.Generic.sample input (t + 1))
  by_cases hbranch : bs = bt
  · exact rankedSweep_output_ne q input hst hbranch
  · simp only [outputAfterInput, GenLimit.Generic.output,
      rankedSweepGenerator, GenLimit.Generic.sequenceSample_prefix]
    exact sweepCode_ne_of_bool_ne hbranch _ _

theorem rankedSweep_positive_clause (q : ℕ) :
    ∀ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
      ∀ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K q →
          NovelGeneratesAfterInput
            input (outputAfterInput (rankedSweepGenerator q) input) K := by
  intro K hK input hinput
  rcases hK with hfirst | hsecond
  · obtain ⟨hmarkers, j, htail⟩ := hfirst
    obtain ⟨Tmark, hTmark⟩ :=
      GenLimit.NoiseLossFeedback.allMarkers_eventually_observed
        hinput hmarkers
    refine ⟨max Tmark j, ?_⟩
    intro t ht
    have hdetect :
        GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
          GenLimit.Generic.sample input (t + 1) :=
      hTmark t ((Nat.le_max_left _ _).trans ht)
    let sample := GenLimit.Generic.sample input (t + 1)
    let k := rankedFreshIndex true (t + 1) sample
    have hkge : j ≤ k := by
      apply le_trans (le_trans (Nat.le_max_right _ _) ht)
      exact (Nat.le_succ t).trans
        (rankedFreshIndex_ge true (t + 1) sample)
    have hout : outputAfterInput (rankedSweepGenerator q) input t =
        GenLimit.UnionClosedness.positiveCode k := by
      simp [outputAfterInput, GenLimit.Generic.output, rankedSweepGenerator,
        GenLimit.Generic.sequenceSample_prefix, hdetect, k, sample, sweepCode]
    refine ⟨?_, ?_, ?_⟩
    · rw [hout]
      apply htail
      refine ⟨k - j, ?_⟩
      change GenLimit.UnionClosedness.positiveCode (j + (k - j)) = _
      rw [Nat.add_sub_of_le hkge]
    · rw [hout]
      simpa [sample, k, sweepCode] using
        rankedFreshIndex_fresh true (t + 1) sample
    · intro s hs
      exact rankedSweep_output_ne_any q input hs
  · refine ⟨0, ?_⟩
    intro t _ht
    have hnoDetect :
        ¬GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
          GenLimit.Generic.sample input (t + 1) :=
      GenLimit.NoiseLossFeedback.not_allMarkers_observed_second
        hsecond hinput t
    let sample := GenLimit.Generic.sample input (t + 1)
    let k := rankedFreshIndex false (t + 1) sample
    have hout : outputAfterInput (rankedSweepGenerator q) input t =
        GenLimit.UnionClosedness.negativeCode k := by
      simp [outputAfterInput, GenLimit.Generic.output, rankedSweepGenerator,
        GenLimit.Generic.sequenceSample_prefix, hnoDetect, k, sample, sweepCode]
    refine ⟨?_, ?_, ?_⟩
    · rw [hout]
      exact hsecond.1 (GenLimit.UnionClosedness.negativeCode_mem k)
    · rw [hout]
      simpa [sample, k, sweepCode] using
        rankedFreshIndex_fresh false (t + 1) sample
    · intro s hs
      exact rankedSweep_output_ne_any q input hs


theorem balanced_negativeCode (k : ℕ) :
    balanced (2 * k + 1) = GenLimit.UnionClosedness.negativeCode k := by
  simp [balanced, GenLimit.UnionClosedness.negativeCode]
  omega

theorem balanced_positiveCode (k : ℕ) :
    balanced (2 * k + 2) = GenLimit.UnionClosedness.positiveCode k := by
  simp [balanced, GenLimit.UnionClosedness.positiveCode]
  omega

theorem balanced_surjective : Function.Surjective balanced := by
  intro z
  cases z with
  | ofNat n =>
      cases n with
      | zero => exact ⟨0, rfl⟩
      | succ k => exact ⟨2 * k + 2, balanced_positiveCode k⟩
  | negSucc k => exact ⟨2 * k + 1, balanced_negativeCode k⟩

noncomputable def rankedSweepRank (q : ℕ) (input : Stream ℤ) (t : ℕ) : ℕ :=
  let positive := decide
    (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.Generic.sample input (t + 1))
  let k := rankedFreshIndex positive (t + 1)
    (GenLimit.Generic.sample input (t + 1))
  if positive then 2 * k + 2 else 2 * k + 1

theorem balanced_rankedSweepRank (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    balanced (rankedSweepRank q input t) =
      outputAfterInput (rankedSweepGenerator q) input t := by
  classical
  let positive := decide
    (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.Generic.sample input (t + 1))
  let k := rankedFreshIndex positive (t + 1)
    (GenLimit.Generic.sample input (t + 1))
  cases hpositive : positive
  · simp [rankedSweepRank, positive, hpositive, balanced_negativeCode,
      outputAfterInput, GenLimit.Generic.output, rankedSweepGenerator,
      GenLimit.Generic.sequenceSample_prefix, sweepCode]
  · simp [rankedSweepRank, positive, hpositive, balanced_positiveCode,
      outputAfterInput, GenLimit.Generic.output, rankedSweepGenerator,
      GenLimit.Generic.sequenceSample_prefix, sweepCode]

theorem rankedSweepRank_lt (q : ℕ) (input : Stream ℤ) (t : ℕ) :
    rankedSweepRank q input t < 4 * (t + 2) := by
  classical
  let positive := decide
    (GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.Generic.sample input (t + 1))
  let sample := GenLimit.Generic.sample input (t + 1)
  have heq : GenLimit.Generic.sequenceSample (fun i : Fin (t + 1) => input i) =
      Finset.univ.image (fun i : Fin (t + 1) => input i) := by
    ext z
    simp [GenLimit.Generic.mem_sequenceSample_iff]
  have hcard : sample.card ≤ t + 1 := by
    dsimp [sample]
    rw [← GenLimit.Generic.sequenceSample_prefix, heq]
    exact Finset.card_image_le.trans_eq (Finset.card_fin (t + 1))
  have hk : rankedFreshIndex positive (t + 1) sample ≤ 2 * (t + 1) := by
    exact (rankedFreshIndex_le positive (t + 1) sample).trans (by omega)
  change (if positive then
      2 * rankedFreshIndex positive (t + 1) sample + 2
    else 2 * rankedFreshIndex positive (t + 1) sample + 1) < 4 * (t + 2)
  cases hpositive : positive
  · have hkfalse : rankedFreshIndex false (t + 1) sample ≤ 2 * (t + 1) := by
      simpa [hpositive] using hk
    simp [hpositive]
    omega
  · have hktrue : rankedFreshIndex true (t + 1) sample ≤ 2 * (t + 1) := by
      simpa [hpositive] using hk
    simp [hpositive]
    omega

theorem rankedSweepRank_injective (q : ℕ) (input : Stream ℤ) :
    Function.Injective (rankedSweepRank q input) := by
  intro s t heq
  by_cases hst : s = t
  · exact hst
  · rcases lt_or_gt_of_ne hst with hlt | hgt
    · exfalso
      apply rankedSweep_output_ne_any q input hlt
      rw [← balanced_rankedSweepRank q input s,
        ← balanced_rankedSweepRank q input t, heq]
    · exfalso
      apply rankedSweep_output_ne_any q input hgt
      rw [← balanced_rankedSweepRank q input t,
        ← balanced_rankedSweepRank q input s, heq]

theorem lowerDensity_quarter_of_counting
    (A K : Set ℕ) (hK : K.Infinite) (hAK : A ⊆ K) (C : ℕ)
    (hcount : ∀ n,
      GenLimit.PatientScope.prefixCount K n ≤
        4 * GenLimit.PatientScope.prefixCount A n + C) :
    (1 / 4 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A K := by
  let N := GenLimit.PatientScope.prefixCount K
  let D := GenLimit.PatientScope.prefixCount A
  let g : ℕ → ℝ := fun n =>
    (1 / 4 : ℝ) - (C : ℝ) / (4 * (N n : ℝ))
  have hN : Tendsto N atTop atTop :=
    GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hg : Tendsto g atTop (𝓝 (1 / 4 : ℝ)) := by
    have hNR : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hN
    have hden : Tendsto (fun n => (4 : ℝ) * (N n : ℝ)) atTop atTop :=
      hNR.const_mul_atTop (by norm_num)
    have hInv : Tendsto
        (fun n => (C : ℝ) / ((4 : ℝ) * (N n : ℝ))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa [g] using tendsto_const_nhds.sub hInv
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      g n ≤ (D n : ℝ) / (N n : ℝ) := by
    filter_upwards [hNpos] with n hn
    have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
    have hcR : (N n : ℝ) ≤ 4 * (D n : ℝ) + C := by
      exact_mod_cast hcount n
    dsimp [g]
    rw [le_div_iff₀ hnR]
    field_simp [hnR.ne']
    nlinarith
  have hDle : ∀ n, D n ≤ N n := fun n =>
    GenLimit.PatientScope.prefixCount_mono hAK n
  have hratio : ∀ n, (D n : ℝ) / (N n : ℝ) ≤ 1 := by
    intro n
    by_cases hn : N n = 0
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast hDle n
  unfold GenLimit.PatientScope.relativeLowerDensity
  calc
    (1 / 4 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop :=
      liminf_le_liminf hcompare hg.isBoundedUnder_ge
        (isCoboundedUnder_ge_of_le atTop hratio)

theorem rankedSweep_density_clause (q : ℕ) :
    ∀ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
      ∀ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K q →
          (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
            (GeneratorFirstOn input
              (outputAfterInput (rankedSweepGenerator q) input) ∩ K) K := by
  classical
  intro K hK input hinput
  let A := balancedRanks
    (GeneratorFirstOn input
      (outputAfterInput (rankedSweepGenerator q) input) ∩ K)
  let KR := balancedRanks K
  have hnovel := rankedSweep_positive_clause q K hK input hinput
  obtain ⟨T, hT⟩ := hnovel
  have hAK : A ⊆ KR := by
    intro n hn
    exact hn.2
  have hKRinf : KR.Infinite := by
    have hKinf := GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q K hK
    intro hKRfin
    apply hKinf
    have hKeq : K = balanced '' KR := by
      ext z
      constructor
      · intro hz
        obtain ⟨n, rfl⟩ := balanced_surjective z
        refine ⟨n, ?_, rfl⟩
        simpa [KR, balancedRanks] using hz
      · rintro ⟨n, hn, rfl⟩
        simpa [KR, balancedRanks] using hn
    rw [hKeq]
    exact hKRfin.image balanced
  have hcount : ∀ n,
      GenLimit.PatientScope.prefixCount KR n ≤
        4 * GenLimit.PatientScope.prefixCount A n + 4 * (T + 3) := by
    intro n
    let r := n / 4
    let c := r - (T + 2)
    let times : Finset ℕ := Finset.range c
    let ranks : Finset ℕ := times.image (fun s => rankedSweepRank q input (T + s))
    have hrankInj : Function.Injective
        (fun s => rankedSweepRank q input (T + s)) := by
      intro a b hab
      exact Nat.add_left_cancel ((rankedSweepRank_injective q input) hab)
    have hranksCard : ranks.card = c := by
      simpa [ranks, times] using
        Finset.card_image_of_injective (Finset.range c) hrankInj
    have hranksSub : ranks ⊆ GenLimit.PatientScope.prefixFinset A n := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      have hslt : s < c := Finset.mem_range.mp hs
      have hranklt : rankedSweepRank q input (T + s) < n := by
        have h₁ := rankedSweepRank_lt q input (T + s)
        have h₂ : T + s + 2 < r := by
          dsimp [c, r] at hslt ⊢
          omega
        have h₃ : 4 * r ≤ n := by
          dsimp [r]
          omega
        omega
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      refine ⟨hranklt, ?_⟩
      have hout := hT (T + s) (by omega)
      change balanced (rankedSweepRank q input (T + s)) ∈
        GeneratorFirstOn input
          (outputAfterInput (rankedSweepGenerator q) input) ∩ K
      refine ⟨?_, ?_⟩
      · refine ⟨T + s, (balanced_rankedSweepRank q input (T + s)).symm, ?_⟩
        intro u hu heq
        have heq' : input u =
            outputAfterInput (rankedSweepGenerator q) input (T + s) := by
          rw [← balanced_rankedSweepRank q input (T + s)]
          exact heq
        have hmem : outputAfterInput (rankedSweepGenerator q) input (T + s) ∈
            GenLimit.Generic.sample input (T + s + 1) :=
          GenLimit.Generic.mem_sample_iff.mpr ⟨u, by omega, heq'⟩
        exact hout.2.1 hmem
      · rw [balanced_rankedSweepRank q input (T + s)]
        exact hout.1
    have hcD : c ≤ GenLimit.PatientScope.prefixCount A n := by
      rw [← hranksCard]
      exact Finset.card_le_card hranksSub
    have hn : n ≤ 4 * c + 4 * (T + 3) := by
      dsimp [c, r]
      omega
    calc
      GenLimit.PatientScope.prefixCount KR n ≤ n := by
        simpa [GenLimit.PatientScope.prefixCount,
          GenLimit.PatientScope.prefixFinset] using
          (Finset.card_filter_le (Finset.range n) (fun x => x ∈ KR))
      _ ≤ 4 * c + 4 * (T + 3) := hn
      _ ≤ 4 * GenLimit.PatientScope.prefixCount A n + 4 * (T + 3) := by omega
  exact lowerDensity_quarter_of_counting A KR hKRinf hAK _ hcount

def separationEncodedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  (↑(GenLimit.NoiseLossFeedback.omissionMarkerFinset q) : Set ℤ) ∪
    GenLimit.UnionClosedness.positiveIntegers ∪
      GenLimit.UnionClosedness.negativeCode '' S
theorem separationEncodedLanguage_mem (q : ℕ) (S : Set ℕ) :
    separationEncodedLanguage q S ∈
      GenLimit.NoiseLossFeedback.finiteOmissionClass q := by
  left
  constructor
  · intro z hz
    exact Or.inl (Or.inl hz)
  · refine ⟨0, ?_⟩
    intro z hz
    obtain ⟨k, rfl⟩ := hz
    exact Or.inl (Or.inr
      (by simpa using GenLimit.UnionClosedness.positiveCode_mem k))

theorem negativeCode_mem_separationEncodedLanguage_iff
    (q : ℕ) (S : Set ℕ) (n : ℕ) :
    GenLimit.UnionClosedness.negativeCode n ∈
        separationEncodedLanguage q S ↔ n ∈ S := by
  constructor
  · intro hn
    rcases hn with (hn | hn) | hn
    · exact False.elim
        (GenLimit.NoiseLossFeedback.negativeCode_not_marker q n hn)
    · have hneg := GenLimit.UnionClosedness.negativeCode_mem n
      change GenLimit.UnionClosedness.negativeCode n < 0 at hneg
      change 0 < GenLimit.UnionClosedness.negativeCode n at hn
      omega
    · obtain ⟨m, hm, hmn⟩ := hn
      have hmnNat := GenLimit.UnionClosedness.negativeCode_injective hmn
      simpa [hmnNat] using hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

theorem separationEncodedLanguage_injective (q : ℕ) :
    Function.Injective (separationEncodedLanguage q) := by
  intro S T hST
  ext n
  have hprobe := Set.ext_iff.mp hST
    (GenLimit.UnionClosedness.negativeCode n)
  simpa [negativeCode_mem_separationEncodedLanguage_iff] using hprobe

theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ →
      GenLimit.NoiseLossFeedback.finiteOmissionClass q :=
    fun S => ⟨separationEncodedLanguage q S,
      separationEncodedLanguage_mem q S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply separationEncodedLanguage_injective q
    exact congrArg Subtype.val hST
  letI : Countable
      (GenLimit.NoiseLossFeedback.finiteOmissionClass q) :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

theorem finiteNoise_adjacent_failure (q : ℕ) (gen : Generator ℤ) :
    ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
      ∃ input : Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  by_contra h
  push_neg at h
  apply GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  simpa [SampleFreshGeneratesAfterInput, outputAfterInput,
    GenLimit.NoiseLossFeedback.CorrectAt,
    GenLimit.NoiseLossFeedback.outputAt,
    GenLimit.NoiseLossFeedback.observedThrough] using h K hK input hinput


theorem stage3_uncountable_separation : SeparationClause := by
  intro q
  refine ⟨GenLimit.NoiseLossFeedback.finiteOmissionClass q,
    finiteOmissionClass_uncountable q,
    GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q,
    ?_, ?_⟩
  · refine ⟨rankedSweepGenerator q, ?_⟩
    intro K hK input hinput
    exact ⟨rankedSweep_positive_clause q K hK input hinput,
      rankedSweep_density_clause q K hK input hinput⟩
  · exact finiteNoise_adjacent_failure q

end Stage3Case019

theorem stage3_result : Stage3Case019.MainClaim := by
  exact ⟨Stage3Case019.stage3_countable_half_density,
    Stage3Case019.stage3_uncountable_separation⟩
