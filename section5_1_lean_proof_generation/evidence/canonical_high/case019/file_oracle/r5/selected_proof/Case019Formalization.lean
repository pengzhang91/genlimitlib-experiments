import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open scoped Topology
open GenLimit
open GenLimit.Generic
open GenLimit.InfiniteContamination

namespace Stage3Case019Proof

noncomputable def oracleOfFamily
    (family : Stage3Case019.LanguageFamily ℕ)
    (hinf : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

theorem sample_congr_of_prefix
    {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

theorem consistent_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n i : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    Consistent C a n i ↔ Consistent C b n i := by
  simp only [Consistent]
  rw [sample_congr_of_prefix h]

theorem recursiveCritical_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n i : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    RecursiveCritical C a n i ↔ RecursiveCritical C b n i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [RecursiveCritical] using consistent_congr_of_prefix (i := 0) h
      | succ i =>
          simp only [RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_congr_of_prefix h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_congr_of_prefix h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (by omega)).mp hjcrit)

theorem consistentIndices_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n scope : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    PatientMachine.consistentIndices C a n scope =
      PatientMachine.consistentIndices C b n scope := by
  ext i
  simp only [PatientMachine.mem_consistentIndices]
  rw [consistent_congr_of_prefix h]

theorem criticalIndices_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n scope : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    PatientMachine.criticalIndices C a n scope =
      PatientMachine.criticalIndices C b n scope := by
  ext i
  simp only [PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_congr_of_prefix h]

theorem survivingCriticalIndices_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n scope : ℕ}
    (h : ∀ k, k < n + 1 → a k = b k) :
    PatientMachine.survivingCriticalIndices C a n scope =
      PatientMachine.survivingCriticalIndices C b n scope := by
  have hp : ∀ k, k < n → a k = b k :=
    fun k hk => h k (Nat.lt.step hk)
  ext i
  simp only [PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr_of_prefix hp,
    recursiveCritical_congr_of_prefix h]

theorem highestCritical_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n scope fallback : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    PatientMachine.highestCritical C a n scope fallback =
      PatientMachine.highestCritical C b n scope fallback := by
  unfold PatientMachine.highestCritical
  rw [criticalIndices_congr_of_prefix h]

theorem highestSurvivor_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n scope fallback : ℕ}
    (h : ∀ k, k < n + 1 → a k = b k) :
    PatientMachine.highestSurvivor C a n scope fallback =
      PatientMachine.highestSurvivor C b n scope fallback := by
  unfold PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr_of_prefix h]

theorem lowestConsistentInScope_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n scope fallback : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    PatientMachine.lowestConsistentInScope C a n scope fallback =
      PatientMachine.lowestConsistentInScope C b n scope fallback := by
  unfold PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr_of_prefix h]

theorem lowestConsistent_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n fallback : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    PatientMachine.lowestConsistent C a n fallback =
      PatientMachine.lowestConsistent C b n fallback := by
  unfold PatientMachine.lowestConsistent
  have hc : Consistent C a n = Consistent C b n := by
    funext i
    exact propext (consistent_congr_of_prefix h)
  rw [hc]

theorem stableDecision_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n : ℕ}
    (old : PatientMachine.State)
    (h : ∀ k, k < n + 1 → a k = b k) :
    PatientMachine.stableDecision C a n old =
      PatientMachine.stableDecision C b n old := by
  unfold PatientMachine.stableDecision
  split <;> rename_i hw
  · dsimp only
    rw [highestCritical_congr_of_prefix h]
  · rfl

theorem backtrackDecision_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n : ℕ}
    (old : PatientMachine.State)
    (h : ∀ k, k < n + 1 → a k = b k) :
    PatientMachine.backtrackDecision C a n old =
      PatientMachine.backtrackDecision C b n old := by
  unfold PatientMachine.backtrackDecision
  dsimp only
  have hci := consistentIndices_congr_of_prefix
    (C := C) (scope := old.scope) h
  rw [hci]
  by_cases hcon :
      (PatientMachine.consistentIndices C b (n + 1) old.scope).Nonempty
  · have hsi := survivingCriticalIndices_congr_of_prefix
      (C := C) (scope := old.scope) h
    rw [hsi]
    by_cases hsur :
        (PatientMachine.survivingCriticalIndices C b n old.scope).Nonempty
    · simp only [if_pos hsur]
      rw [highestSurvivor_congr_of_prefix h]
      simp only [dif_pos hcon]
    · simp only [if_neg hsur]
      rw [lowestConsistentInScope_congr_of_prefix h]
      simp only [dif_pos hcon]
  · rw [lowestConsistent_congr_of_prefix h]
    have hc : Consistent C a (n + 1) = Consistent C b (n + 1) := by
      funext i
      exact propext (consistent_congr_of_prefix h)
    rw [hc]
    simp only [dif_neg hcon]

theorem decide_congr_of_prefix
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {n : ℕ}
    (old : PatientMachine.State)
    (h : ∀ k, k < n + 1 → a k = b k) :
    PatientMachine.decide C a n old = PatientMachine.decide C b n old := by
  unfold PatientMachine.decide
  rw [propext (consistent_congr_of_prefix (i := old.focus) h)]
  split
  · exact stableDecision_congr_of_prefix old h
  · exact backtrackDecision_congr_of_prefix old h

theorem patient_run_congr
    (O : OracleFamily) {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    PatientMachine.run O a n = PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      have hp : ∀ k, k < n → a k = b k :=
        fun k hk => h k (Nat.lt.step hk)
      rw [ih hp]
      have hs : GenLimit.sample a (n + 1) = GenLimit.sample b (n + 1) :=
        sample_congr_of_prefix h
      have hd := decide_congr_of_prefix (C := O.language)
        (PatientMachine.run O b n) h
      have hx :
          PatientMachine.leastAvailable O.language O.infinite' a (n + 1)
              (PatientMachine.run O b n).used
              (PatientMachine.decide O.language b n (PatientMachine.run O b n)).focus =
            PatientMachine.leastAvailable O.language O.infinite' b (n + 1)
              (PatientMachine.run O b n).used
              (PatientMachine.decide O.language b n (PatientMachine.run O b n)).focus := by
        unfold PatientMachine.leastAvailable
        congr 1
        funext x
        simp only [PatientMachine.Available]
        rw [hs]
      simp only [PatientMachine.processRound]
      rw [hd, hx]

noncomputable def historyExtension {α : Type*} [Inhabited α]
    {n : ℕ} (xs : Fin n → α) : ℕ → α :=
  fun k => if hk : k < n then xs ⟨k, hk⟩ else default

noncomputable def patientGenerator (O : OracleFamily) : Generator ℕ :=
  fun n xs =>
    if hn : n = 0 then 0
    else PatientMachine.output O (historyExtension xs) (n - 1)

theorem patientGenerator_output
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) stream t =
      PatientMachine.output O stream t := by
  unfold Stage3Case019.outputAfterInput Generic.output patientGenerator
  simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel]
  unfold PatientMachine.output
  congr 2
  apply patient_run_congr
  intro k hk
  simp [historyExtension, hk]

theorem finite_eventually_absent {S : Set ℕ} (hS : S.Finite) :
    ∃ T, ∀ t, T ≤ t → t ∉ S := by
  classical
  let T := hS.toFinset.sup id + 1
  refine ⟨T, ?_⟩
  intro t ht hmem
  have hle : t ≤ hS.toFinset.sup id := by
    apply Finset.le_sup (f := id)
    simpa using hmem
  dsimp [T] at ht
  omega

theorem prefixCount_le_add_finite_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    PatientScope.prefixCount A n ≤
      PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let a := PatientScope.prefixFinset A n
  let b := PatientScope.prefixFinset B n
  let d := PatientScope.prefixFinset (A \ B) n
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    have hx' := PatientScope.mem_prefixFinset.mp hx
    apply Finset.mem_union.mpr
    by_cases hxB : x ∈ B
    · exact Or.inl (PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Or.inr (PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hd : d.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact (Set.Finite.mem_toFinset hfinite).mpr
      (PatientScope.mem_prefixFinset.mp hx).2
  change a.card ≤ b.card + hfinite.toFinset.card
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le b d).trans (Nat.add_le_add_left hd _))

theorem relativeLowerDensity_transfer_finite_loss
    {D E K L : Set ℕ}
    (hKinf : K.Infinite) (hKL : K ⊆ L)
    (hDL : D ⊆ L) (hEK : E ⊆ K)
    (hloss : (D \ E).Finite) :
    PatientScope.relativeLowerDensity D L ≤
      PatientScope.relativeLowerDensity E K := by
  let source : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount D n : ℝ) /
      (PatientScope.prefixCount L n : ℝ)
  let output : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount E n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hloss.toFinset.card : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  have hKtop := PatientScope.tendsto_prefixCount_atTop hKinf
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hKtop)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n := by
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < PatientScope.prefixCount K n :=
      hKtop.eventually (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hden : PatientScope.prefixCount K n ≤
        PatientScope.prefixCount L n :=
      PatientScope.prefixCount_mono hKL n
    have hnum := prefixCount_le_add_finite_diff hloss n
    have hkR : (0 : ℝ) < PatientScope.prefixCount K n := by exact_mod_cast hn
    have hlR : (0 : ℝ) < PatientScope.prefixCount L n := by
      exact lt_of_lt_of_le hkR (by exact_mod_cast hden)
    dsimp [source, output, error]
    calc
      (PatientScope.prefixCount D n : ℝ) /
          (PatientScope.prefixCount L n : ℝ) ≤
        (PatientScope.prefixCount D n : ℝ) /
          (PatientScope.prefixCount K n : ℝ) := by
            apply div_le_div_of_nonneg_left (by positivity) hkR
            exact_mod_cast hden
      _ ≤ ((PatientScope.prefixCount E n : ℝ) + hloss.toFinset.card) /
          (PatientScope.prefixCount K n : ℝ) := by
            apply div_le_div_of_nonneg_right _ hkR.le
            exact_mod_cast hnum
      _ = (PatientScope.prefixCount E n : ℝ) /
            (PatientScope.prefixCount K n : ℝ) +
          (hloss.toFinset.card : ℝ) /
            (PatientScope.prefixCount K n : ℝ) := by rw [add_div]
  have hsourceLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop source :=
    isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩
  have houtputLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop output :=
    isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩
  have houtputRatio : ∀ n, output n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount K n = 0
    · simp [output, hn]
    · rw [show output n = (PatientScope.prefixCount E n : ℝ) /
          PatientScope.prefixCount K n by rfl]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast PatientScope.prefixCount_mono hEK n
  have houtputUpper : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop output :=
    isCoboundedUnder_ge_of_le atTop houtputRatio
  have hle : liminf source atTop ≤ liminf output atTop := by
    apply (le_liminf_iff houtputUpper houtputLower).2
    intro y hy
    obtain ⟨r, hyr, hr⟩ := exists_between hy
    have hrEventually : ∀ᶠ n in atTop, r < source n :=
      eventually_lt_of_lt_liminf hr hsourceLower
    have heventually : ∀ᶠ n in atTop, error n < r - y := by
      have : 0 < r - y := by linarith
      exact herror.eventually (Iio_mem_nhds this)
    filter_upwards [hrEventually, heventually, hprefix] with n hsr herr hp
    linarith
  simpa [PatientScope.relativeLowerDensity, source, output] using hle


theorem relativeLowerDensity_cofinite_ambient
    {D K : Set ℕ} (hKfinite : Kᶜ.Finite) (hDK : D ⊆ K) :
    PatientScope.relativeLowerDensity D K ≤
      PatientScope.relativeLowerDensity D Set.univ := by
  let source : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount D n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  let output : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount D n : ℝ) /
      (PatientScope.prefixCount Set.univ n : ℝ)
  let missing : Set ℕ := Set.univ \ K
  have hmissing : missing.Finite := by
    have heq : missing = Kᶜ := by
      ext n
      simp [missing]
    rw [heq]
    exact hKfinite
  let error : ℕ → ℝ := fun n =>
    (hmissing.toFinset.card : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  have hKinf : K.Infinite := Set.infinite_of_finite_compl hKfinite
  have hKtop := PatientScope.tendsto_prefixCount_atTop hKinf
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hKtop)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n := by
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < PatientScope.prefixCount K n :=
      hKtop.eventually (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hKU : PatientScope.prefixCount K n ≤
        PatientScope.prefixCount Set.univ n :=
      PatientScope.prefixCount_mono (Set.subset_univ K) n
    have hUbound : PatientScope.prefixCount Set.univ n ≤
        PatientScope.prefixCount K n + hmissing.toFinset.card :=
      prefixCount_le_add_finite_diff hmissing n
    have hDU : PatientScope.prefixCount D n ≤
        PatientScope.prefixCount K n :=
      PatientScope.prefixCount_mono hDK n
    have hkR : (0 : ℝ) < PatientScope.prefixCount K n := by exact_mod_cast hn
    have huR : (0 : ℝ) < PatientScope.prefixCount Set.univ n := by
      exact lt_of_lt_of_le hkR (by exact_mod_cast hKU)
    have hKUR : (PatientScope.prefixCount K n : ℝ) ≤
        PatientScope.prefixCount Set.univ n := by exact_mod_cast hKU
    have hUboundR : (PatientScope.prefixCount Set.univ n : ℝ) ≤
        PatientScope.prefixCount K n + hmissing.toFinset.card := by
      exact_mod_cast hUbound
    have hDUR : (PatientScope.prefixCount D n : ℝ) ≤
        PatientScope.prefixCount K n := by exact_mod_cast hDU
    dsimp [source, output, error]
    rw [div_le_iff₀ hkR]
    field_simp [huR.ne']
    nlinarith
  have hsourceLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop source :=
    isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩
  have houtputLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop output :=
    isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩
  have houtputRatio : ∀ n, output n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount Set.univ n = 0
    · simp [output, hn]
    · rw [show output n = (PatientScope.prefixCount D n : ℝ) /
          PatientScope.prefixCount Set.univ n by rfl]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast PatientScope.prefixCount_mono
        (Set.subset_univ D) n
  have houtputUpper : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop output :=
    isCoboundedUnder_ge_of_le atTop houtputRatio
  have hle : liminf source atTop ≤ liminf output atTop := by
    apply (le_liminf_iff houtputUpper houtputLower).2
    intro y hy
    obtain ⟨r, hyr, hr⟩ := exists_between hy
    have hrEventually : ∀ᶠ n in atTop, r < source n :=
      eventually_lt_of_lt_liminf hr hsourceLower
    have heventually : ∀ᶠ n in atTop, error n < r - y := by
      have : 0 < r - y := by linarith
      exact herror.eventually (Iio_mem_nhds this)
    filter_upwards [hrEventually, heventually, hprefix] with n hsr herr hp
    linarith
  simpa [PatientScope.relativeLowerDensity, source, output] using hle

theorem contaminated_is_finiteContamination
    {stream : Stream ℕ} {K : Set ℕ} {q : ℕ}
    (h : InjectiveValueContaminatedPresentationAtMost stream K q) :
    InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration stream K := by
  refine ⟨h.1, ?_, ?_⟩
  · apply (finiteNoise_iff_valuesOutside_finite_of_injective h.1).mpr
    exact (GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
      (Set.range stream) K q).mp h.2.2 |>.1
  · change (K \ Set.range stream).Finite
    have hempty : K \ Set.range stream = ∅ := Set.diff_eq_empty.mpr h.2.1
    rw [hempty]
    exact Set.finite_empty


theorem countable_half_density : Stage3Case019.CountableClause := by
  intro q family hinf
  let O := oracleOfFamily family hinf
  let E := finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hinput
  have hcontam := contaminated_is_finiteContamination hinput
  obtain ⟨j, hjBase, hjPresents⟩ :=
    exists_finiteExpansion_index_for_stream O hcontam
  have hpatient :=
    PatientMachine.patientScope_generation_and_lowerDensity E input hjPresents
  have hRangeDiff : (Set.range input \ family i).Finite :=
    (GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
      (Set.range input) (family i) q).mp hinput.2.2 |>.1
  let rawOutput : ℕ → ℕ := PatientMachine.output E input
  have houtputEq :
      Stage3Case019.outputAfterInput (patientGenerator E) input = rawOutput := by
    funext t
    exact patientGenerator_output E input t
  have hbadTimes :
      (rawOutput ⁻¹' (Set.range input \ family i)).Finite := by
    apply hRangeDiff.preimage
    exact Set.injOn_of_injective (PatientMachine.output_injective E input)
  obtain ⟨Tbad, hTbad⟩ := finite_eventually_absent hbadTimes
  obtain ⟨Tpatient, hTpatient⟩ := hpatient.1
  have hnovel : NovelGeneratesInLimit input
      (Stage3Case019.outputAfterInput (patientGenerator E) input) (family i) := by
    rw [houtputEq]
    refine ⟨max Tbad Tpatient, ?_⟩
    intro t ht
    have htBad : Tbad ≤ t := le_trans (le_max_left _ _) ht
    have htPatient : Tpatient ≤ t := le_trans (le_max_right _ _) ht
    obtain ⟨hmemExpanded, hinputFresh, houtputFresh⟩ := hTpatient t htPatient
    have hmemRange : rawOutput t ∈ Set.range input := by
      rw [hjPresents]
      exact hmemExpanded
    have hmemTarget : rawOutput t ∈ family i := by
      by_contra hnot
      exact hTbad t htBad ⟨hmemRange, hnot⟩
    refine ⟨hmemTarget, ?_, houtputFresh⟩
    rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hs, heq⟩
    exact hinputFresh s (by omega) heq
  have htargetSubset : family i ⊆ E.language j := by
    intro x hx
    rw [← hjPresents]
    exact hinput.2.1 hx
  let D : Set ℕ :=
    GeneratorFirst input rawOutput ∩ E.language j
  let Dtarget : Set ℕ :=
    GeneratorFirst input rawOutput ∩ family i
  have hDsubset : D ⊆ E.language j := fun x hx => hx.2
  have hDtargetSubset : Dtarget ⊆ family i := fun x hx => hx.2
  have hLoss : (D \ Dtarget).Finite := by
    apply hRangeDiff.subset
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hjPresents]
      exact hx.1.2
    · intro hxi
      exact hx.2 ⟨hx.1.1, hxi⟩
  have hdensityTransfer :
      PatientScope.relativeLowerDensity D (E.language j) ≤
        PatientScope.relativeLowerDensity Dtarget (family i) :=
    relativeLowerDensity_transfer_finite_loss
      (hinf i) htargetSubset hDsubset hDtargetSubset hLoss
  refine ⟨hnovel, ?_⟩
  have hhalf : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity D (E.language j) := by
    simpa [PatientMachine.patientLowerDensity, D] using hpatient.2
  have htargetDensity : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity Dtarget (family i) :=
    hhalf.trans hdensityTransfer
  rw [houtputEq]
  simpa [Dtarget, rawOutput] using htargetDensity


noncomputable def separationEncoding (q : ℕ) (S : Set ℕ) : Set ℤ :=
  GenLimit.UnionClosedness.negativeIntegers ∪
    (fun n => GenLimit.UnionClosedness.positiveCode (q + 1 + n)) '' S

theorem separationEncoding_mem_second (q : ℕ) (S : Set ℕ) :
    separationEncoding q S ∈
      NoiseLossFeedback.finiteOmissionSecondClass q := by
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hmarker
    rcases hz with hzneg | ⟨n, hnS, rfl⟩
    · exact (Int.not_lt_of_ge
        (NoiseLossFeedback.omissionMarker_nonnegative hmarker)) hzneg
    · obtain ⟨k, hk, heq⟩ :=
        NoiseLossFeedback.mem_omissionMarkerFinset_iff.mp hmarker
      have hnat : q + 1 + n + 1 = k := by
        exact Int.ofNat_inj.mp (heq.symm)
      omega

theorem separationEncoding_injective (q : ℕ) :
    Function.Injective (separationEncoding q) := by
  intro S T hST
  ext n
  let z := GenLimit.UnionClosedness.positiveCode (q + 1 + n)
  have hzpos : 0 < z :=
    GenLimit.UnionClosedness.positiveCode_mem (q + 1 + n)
  have hzS : z ∈ separationEncoding q S ↔ n ∈ S := by
    constructor
    · intro hz
      rcases hz with hzneg | ⟨m, hm, heq⟩
      · exact False.elim ((Int.not_lt_of_ge (Int.le_of_lt hzpos)) hzneg)
      · have := GenLimit.UnionClosedness.positiveCode_injective heq
        have : m = n := by omega
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  have hzT : z ∈ separationEncoding q T ↔ n ∈ T := by
    constructor
    · intro hz
      rcases hz with hzneg | ⟨m, hm, heq⟩
      · exact False.elim ((Int.not_lt_of_ge (Int.le_of_lt hzpos)) hzneg)
      · have := GenLimit.UnionClosedness.positiveCode_injective heq
        have : m = n := by omega
        simpa [this] using hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  rw [← hzS, hST, hzT]

theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(NoiseLossFeedback.finiteOmissionClass q).Countable := by
  intro hcount
  have hpre := hcount.preimage (separationEncoding_injective q)
  have hpreEq :
      separationEncoding q ⁻¹' NoiseLossFeedback.finiteOmissionClass q =
        (Set.univ : Set (Set ℕ)) := by
    apply Set.eq_univ_of_forall
    intro S
    exact Or.inr (separationEncoding_mem_second q S)
  rw [hpreEq, Set.countable_univ_iff] at hpre
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpre

theorem separation_negative (q : ℕ) :
    ∀ gen : Generator ℤ,
      ∃ K ∈ NoiseLossFeedback.finiteOmissionClass q, ∃ input : Stream ℤ,
        InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬Stage3Case019.SampleFreshGeneratesAfterInput
            input (Stage3Case019.outputAfterInput gen input) K := by
  intro gen
  by_contra hcounter
  have hgood : NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel gen
      (NoiseLossFeedback.finiteOmissionClass q) (q + 1) := by
    intro K hK input hinput
    have hfresh : Stage3Case019.SampleFreshGeneratesAfterInput
        input (Stage3Case019.outputAfterInput gen input) K := by
      by_contra hfail
      exact hcounter ⟨K, hK, input, hinput, hfail⟩
    simpa [Stage3Case019.SampleFreshGeneratesAfterInput,
      Stage3Case019.outputAfterInput, NoiseLossFeedback.CorrectAt,
      NoiseLossFeedback.outputAt, NoiseLossFeedback.observedThrough] using hfresh
  exact NoiseLossFeedback.finiteNoiseLevel_lower q ⟨gen, hgood⟩


noncomputable def universalOracle : OracleFamily where
  language := fun _ => Set.univ
  infinite' := fun _ => Set.infinite_univ
  query := fun _ _ => true
  query_spec := by simp

noncomputable def sideOracle : OracleFamily :=
  finiteExpansionOracleFamily universalOracle

def negativeProjection : ℤ → ℕ
  | Int.ofNat _ => 0
  | Int.negSucc n => n + 1

def positiveProjection : ℤ → ℕ
  | Int.ofNat n => n
  | Int.negSucc _ => 0

def negativeEncode : ℕ → ℤ
  | 0 => 0
  | n + 1 => GenLimit.UnionClosedness.negativeCode n

def positiveEncode : ℕ → ℤ := Int.ofNat

def negativeRank : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * n + 1

def positiveRank : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * n + 2

@[simp] theorem negativeProjection_encode (n : ℕ) :
    negativeProjection (negativeEncode n) = n := by
  cases n <;> simp [negativeProjection, negativeEncode,
    GenLimit.UnionClosedness.negativeCode]

@[simp] theorem positiveProjection_encode (n : ℕ) :
    positiveProjection (positiveEncode n) = n := by
  simp [positiveProjection, positiveEncode]

theorem negativeEncode_injective : Function.Injective negativeEncode := by
  intro m n h
  have := congrArg negativeProjection h
  simpa using this

theorem positiveEncode_injective : Function.Injective positiveEncode := by
  intro m n h
  exact Int.ofNat_inj.mp h

@[simp] theorem balanced_negativeRank (n : ℕ) :
    Stage3Case019.balanced (negativeRank n) = negativeEncode n := by
  cases n with
  | zero => rfl
  | succ n =>
      simp [negativeRank, Stage3Case019.balanced, negativeEncode,
        GenLimit.UnionClosedness.negativeCode]
      omega

@[simp] theorem balanced_positiveRank (n : ℕ) :
    Stage3Case019.balanced (positiveRank n) = positiveEncode n := by
  cases n with
  | zero => rfl
  | succ n =>
      simp [positiveRank, Stage3Case019.balanced, positiveEncode]
      omega

theorem negativeRank_injective : Function.Injective negativeRank := by
  intro m n h
  apply negativeEncode_injective
  simpa only [balanced_negativeRank] using
    congrArg Stage3Case019.balanced h

theorem positiveRank_injective : Function.Injective positiveRank := by
  intro m n h
  apply positiveEncode_injective
  simpa only [balanced_positiveRank] using
    congrArg Stage3Case019.balanced h

noncomputable def separationGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    if NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sequenceSample xs then
      positiveEncode
        (patientGenerator sideOracle n (fun k => positiveProjection (xs k)))
    else
      negativeEncode
        (patientGenerator sideOracle n (fun k => negativeProjection (xs k)))

def positiveSide (K : Set ℤ) : Set ℕ := positiveEncode ⁻¹' K

def negativeSide (K : Set ℤ) : Set ℕ := negativeEncode ⁻¹' K

theorem positiveSide_compl_finite {q : ℕ} {K : Set ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionFirstClass q) :
    (positiveSide K)ᶜ.Finite := by
  obtain ⟨_hmarkers, j, htail⟩ := hK
  apply (Set.finite_lt_nat (j + 1)).subset
  intro n hn
  have hnnot : positiveEncode n ∉ K := hn
  by_contra hnlt
  have hnge : j + 1 ≤ n := Nat.le_of_not_gt hnlt
  apply hnnot
  apply htail
  refine ⟨n - (j + 1), ?_⟩
  simp [positiveEncode, GenLimit.UnionClosedness.positiveCode]
  omega

theorem negativeSide_compl_finite {q : ℕ} {K : Set ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionSecondClass q) :
    (negativeSide K)ᶜ.Finite := by
  apply (Set.finite_lt_nat 1).subset
  intro n hn
  have hnnot : negativeEncode n ∉ K := hn
  by_contra hnlt
  change ¬n < 1 at hnlt
  have hnpos : 0 < n := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  apply hnnot
  exact hK.1 (GenLimit.UnionClosedness.negativeCode_mem k)

theorem positiveProjectedRange_compl_finite
    {q : ℕ} {K : Set ℤ} {input : Stream ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionFirstClass q)
    (hcover : K ⊆ Set.range input) :
    (Set.range (positiveProjection ∘ input))ᶜ.Finite := by
  obtain ⟨_hmarkers, j, htail⟩ := hK
  apply (Set.finite_lt_nat (j + 1)).subset
  intro n hn
  have hnnot : n ∉ Set.range (positiveProjection ∘ input) := hn
  by_contra hnlt
  have hnge : j + 1 ≤ n := Nat.le_of_not_gt hnlt
  have hnK : positiveEncode n ∈ K := by
    apply htail
    refine ⟨n - (j + 1), ?_⟩
    simp [positiveEncode, GenLimit.UnionClosedness.positiveCode]
    omega
  obtain ⟨t, ht⟩ := hcover hnK
  apply hnnot
  refine ⟨t, ?_⟩
  rw [Function.comp_apply, ht]
  exact positiveProjection_encode n

theorem negativeProjectedRange_compl_finite
    {q : ℕ} {K : Set ℤ} {input : Stream ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionSecondClass q)
    (hcover : K ⊆ Set.range input) :
    (Set.range (negativeProjection ∘ input))ᶜ.Finite := by
  apply (Set.finite_lt_nat 1).subset
  intro n hn
  have hnnot : n ∉ Set.range (negativeProjection ∘ input) := hn
  by_contra hnlt
  change ¬n < 1 at hnlt
  have hnpos : 0 < n := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  have hnK : negativeEncode (k + 1) ∈ K :=
    hK.1 (GenLimit.UnionClosedness.negativeCode_mem k)
  obtain ⟨t, ht⟩ := hcover hnK
  apply hnnot
  refine ⟨t, ?_⟩
  rw [Function.comp_apply, ht]
  exact negativeProjection_encode (k + 1)

@[simp] theorem prefixCount_univ (n : ℕ) :
    PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [PatientScope.prefixCount, PatientScope.prefixFinset]

theorem prefixCount_image_rank_lower
    (rank : ℕ → ℕ) (hrank : Function.Injective rank)
    (hbound : ∀ n, rank n ≤ 2 * n)
    (D : Set ℕ) (m : ℕ) :
    PatientScope.prefixCount D (m / 2) ≤
      PatientScope.prefixCount (rank '' D) m := by
  classical
  let source := PatientScope.prefixFinset D (m / 2)
  let target := PatientScope.prefixFinset (rank '' D) m
  have hsub : source.image rank ⊆ target := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hn' := PatientScope.mem_prefixFinset.mp hn
    apply PatientScope.mem_prefixFinset.mpr
    refine ⟨?_, ⟨n, hn'.2, rfl⟩⟩
    have htwice : 2 * n < m := by
      have hdiv : n < m / 2 := hn'.1
      omega
    exact lt_of_le_of_lt (hbound n) htwice
  change source.card ≤ target.card
  rw [← Finset.card_image_of_injective source hrank]
  exact Finset.card_le_card hsub

theorem relativeLowerDensity_rank_image_quarter
    (rank : ℕ → ℕ) (hrank : Function.Injective rank)
    (hbound : ∀ n, rank n ≤ 2 * n)
    (D : Set ℕ)
    (hhalf : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity D Set.univ) :
    (1 / 4 : ℝ) ≤
      PatientScope.relativeLowerDensity (rank '' D) Set.univ := by
  let source : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount D n : ℝ) / n
  let target : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (rank '' D) n : ℝ) / n
  rw [PatientScope.relativeLowerDensity]
  simp only [prefixCount_univ, Nat.cast_id]
  change (1 / 4 : ℝ) ≤ liminf target atTop
  have hsource : (1 / 2 : ℝ) ≤ liminf source atTop := by
    simpa [PatientScope.relativeLowerDensity, source] using hhalf
  have hsourceLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop source :=
    isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩
  have htargetLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop target :=
    isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩
  have htargetUpper : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [target, hn]
    · rw [show target n =
        (PatientScope.prefixCount (rank '' D) n : ℝ) / n by rfl]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      have hcount := PatientScope.prefixCount_mono
        (show rank '' D ⊆ (Set.univ : Set ℕ) by simp) n
      have hcount' : PatientScope.prefixCount (rank '' D) n ≤ n := by
        simpa only [prefixCount_univ] using hcount
      exact_mod_cast hcount'
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htargetUpper)
    htargetLower).2
  intro y hy
  by_cases hy0 : y < 0
  · exact Eventually.of_forall fun n =>
      lt_of_lt_of_le hy0 (div_nonneg (by positivity) (by positivity))
  have hy_nonneg : 0 ≤ y := le_of_not_gt hy0
  have htwo : 2 * y < (1 / 2 : ℝ) := by linarith
  obtain ⟨r, hyr, hrhalf⟩ := exists_between htwo
  have hrsource : r < liminf source atTop := lt_of_lt_of_le hrhalf hsource
  have heventSource : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrsource hsourceLower
  have hdivTop : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (2 * b)] with n hn
    omega
  have heventHalf : ∀ᶠ m : ℕ in atTop, r < source (m / 2) :=
    hdivTop.eventually heventSource
  have hgap : 0 < r - 2 * y := by linarith
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (y / (r - 2 * y))
  filter_upwards [heventHalf, eventually_ge_atTop (2 * max M 1)] with m hm hmLarge
  let N := m / 2
  have hNge : max M 1 ≤ N := by
    dsimp [N]
    omega
  have hNposNat : 0 < N := lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_max_right _ _) |>.trans_le hNge
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast (le_trans (Nat.le_max_left _ _) hNge)
  have hratio : y / (r - 2 * y) < (N : ℝ) := lt_of_lt_of_le hM hMN
  have hybound : y < (r - 2 * y) * N := by
    have hratio' := (div_lt_iff₀ hgap).mp hratio
    nlinarith
  have hmBoundNat : m ≤ 2 * N + 1 := by
    dsimp [N]
    omega
  have hmBound : (m : ℝ) ≤ 2 * N + 1 := by
    exact_mod_cast hmBoundNat
  have hcount := prefixCount_image_rank_lower rank hrank hbound D m
  have hmposNat : 0 < m := lt_of_lt_of_le (by omega : 0 < 2 * max M 1) hmLarge
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hmposNat
  have hsourceAt : r <
      (PatientScope.prefixCount D N : ℝ) / N := by
    simpa [source, N] using hm
  have hcountR :
      (PatientScope.prefixCount D N : ℝ) ≤
        PatientScope.prefixCount (rank '' D) m := by
    exact_mod_cast hcount
  change y < target m
  rw [show target m =
      (PatientScope.prefixCount (rank '' D) m : ℝ) / m by rfl]
  rw [lt_div_iff₀ hmpos]
  have hsourceMul : r * N < PatientScope.prefixCount D N := by
    rwa [lt_div_iff₀ hNpos] at hsourceAt
  calc
    y * m ≤ y * (2 * N + 1) := mul_le_mul_of_nonneg_left hmBound hy_nonneg
    _ < r * N := by nlinarith
    _ < PatientScope.prefixCount D N := hsourceMul
    _ ≤ PatientScope.prefixCount (rank '' D) m := hcountR

theorem exists_sideOracle_index_of_compl_finite
    (R : Set ℕ) (hR : Rᶜ.Finite) :
    ∃ j, sideOracle.language j = R := by
  classical
  let remove : Finset ℕ := hR.toFinset
  let data : FiniteExpansionCode :=
    (0, Finset.equivBitIndices.symm ∅,
      Finset.equivBitIndices.symm remove)
  let j := encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  ext n
  simp [sideOracle, finiteExpansionOracleFamily_language,
    finiteExpansionLanguage, j, data, universalOracle,
    finiteExpansion, remove]

theorem separationGenerator_output_positive
    (q : ℕ) (input : Stream ℤ) (t : ℕ)
    (hdetect : NoiseLossFeedback.omissionMarkerFinset q ⊆
      NoiseLossFeedback.observedThrough input t) :
    Stage3Case019.outputAfterInput (separationGenerator q) input t =
      positiveEncode
        (PatientMachine.output sideOracle (positiveProjection ∘ input) t) := by
  have hsample :
      GenLimit.Generic.sequenceSample (fun k : Fin (t + 1) => input k) =
        NoiseLossFeedback.observedThrough input t :=
    GenLimit.Generic.sequenceSample_prefix input (t + 1)
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output separationGenerator
  rw [if_pos (by simpa [hsample] using hdetect)]
  congr 1
  change Stage3Case019.outputAfterInput (patientGenerator sideOracle)
      (positiveProjection ∘ input) t = _
  exact patientGenerator_output sideOracle _ t

theorem separationGenerator_output_negative
    (q : ℕ) (input : Stream ℤ) (t : ℕ)
    (hdetect : ¬NoiseLossFeedback.omissionMarkerFinset q ⊆
      NoiseLossFeedback.observedThrough input t) :
    Stage3Case019.outputAfterInput (separationGenerator q) input t =
      negativeEncode
        (PatientMachine.output sideOracle (negativeProjection ∘ input) t) := by
  have hsample :
      GenLimit.Generic.sequenceSample (fun k : Fin (t + 1) => input k) =
        NoiseLossFeedback.observedThrough input t :=
    GenLimit.Generic.sequenceSample_prefix input (t + 1)
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output separationGenerator
  rw [if_neg (by simpa [hsample] using hdetect)]
  congr 1
  change Stage3Case019.outputAfterInput (patientGenerator sideOracle)
      (negativeProjection ∘ input) t = _
  exact patientGenerator_output sideOracle _ t

theorem separation_branch_guarantee
    (q : ℕ) (K : Set ℤ) (input : Stream ℤ)
    (encode : ℕ → ℤ) (projection : ℤ → ℕ) (rank : ℕ → ℕ) (Tbranch : ℕ)
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q)
    (hprojEncode : ∀ n, projection (encode n) = n)
    (hencodeInj : Function.Injective encode)
    (hrankInj : Function.Injective rank)
    (hrankBound : ∀ n, rank n ≤ 2 * n)
    (hbalanced : ∀ n, Stage3Case019.balanced (rank n) = encode n)
    (hsideFinite : (encode ⁻¹' K)ᶜ.Finite)
    (hrangeFinite : (Set.range (projection ∘ input))ᶜ.Finite)
    (hbranch : ∀ t, Tbranch ≤ t →
      Stage3Case019.outputAfterInput (separationGenerator q) input t =
        encode (PatientMachine.output sideOracle (projection ∘ input) t)) :
    Stage3Case019.NovelGeneratesAfterInput input
        (Stage3Case019.outputAfterInput (separationGenerator q) input) K ∧
      (1 / 4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
        (Stage3Case019.GeneratorFirstOn input
          (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K) K := by
  classical
  let projected : Stream ℕ := projection ∘ input
  let raw : Stream ℕ := PatientMachine.output sideOracle projected
  let sideTarget : Set ℕ := encode ⁻¹' K
  let sideRange : Set ℕ := Set.range projected
  obtain ⟨j, hj⟩ := exists_sideOracle_index_of_compl_finite sideRange hrangeFinite
  have hpresents : GenLimit.Presents projected (sideOracle.language j) := by
    simpa [GenLimit.Presents, sideRange, hj]
  have hpatient := PatientMachine.patientScope_generation_and_lowerDensity
    sideOracle projected hpresents
  have hsideTargetInf : sideTarget.Infinite := Set.infinite_of_finite_compl hsideFinite
  have hsideSubset : sideTarget ⊆ sideRange := by
    intro n hn
    have hencK : encode n ∈ K := hn
    obtain ⟨t, ht⟩ := hinput.2.1 hencK
    refine ⟨t, ?_⟩
    dsimp [projected]
    rw [ht]
    exact hprojEncode n
  let D : Set ℕ := GeneratorFirst projected raw ∩ sideRange
  let Dgood : Set ℕ := D ∩ sideTarget
  let earlyTimes : Set ℕ := (Finset.range Tbranch : Set ℕ)
  let earlyRaw : Set ℕ := raw '' earlyTimes
  let actual : Stream ℤ :=
    Stage3Case019.outputAfterInput (separationGenerator q) input
  let earlyActual : Set ℤ := actual '' earlyTimes
  let earlyEncoded : Set ℕ := encode ⁻¹' earlyActual
  let blocked : Set ℕ := earlyRaw ∪ earlyEncoded
  let Dlate : Set ℕ := Dgood \ blocked
  have hearlyTimes : earlyTimes.Finite := by
    exact (Finset.range Tbranch).finite_toSet
  have hearlyRaw : earlyRaw.Finite := hearlyTimes.image raw
  have hearlyActual : earlyActual.Finite := hearlyTimes.image actual
  have hearlyEncoded : earlyEncoded.Finite :=
    hearlyActual.preimage hencodeInj.injOn
  have hblocked : blocked.Finite := hearlyRaw.union hearlyEncoded
  have hrawInj : Function.Injective raw := by
    exact PatientMachine.output_injective sideOracle projected
  have hbadTimes : (raw ⁻¹' (sideTargetᶜ ∪ blocked)).Finite :=
    (hsideFinite.union hblocked).preimage hrawInj.injOn
  obtain ⟨Tgood, hTgood⟩ := finite_eventually_absent hbadTimes
  obtain ⟨Tpatient, hTpatient⟩ := hpatient.1
  have hnovel : Stage3Case019.NovelGeneratesAfterInput input actual K := by
    refine ⟨max Tbranch (max Tgood Tpatient), ?_⟩
    intro t ht
    have htBranch : Tbranch ≤ t := le_trans (Nat.le_max_left _ _) ht
    have htGood : Tgood ≤ t :=
      le_trans (le_max_left _ _) (le_trans (Nat.le_max_right _ _) ht)
    have htPatient : Tpatient ≤ t :=
      le_trans (le_max_right _ _) (le_trans (Nat.le_max_right _ _) ht)
    have hnotBad := hTgood t htGood
    have hrawSide : raw t ∈ sideTarget := by
      by_contra hnot
      exact hnotBad (Or.inl hnot)
    have hrawBlocked : raw t ∉ blocked := by
      intro hb
      exact hnotBad (Or.inr hb)
    have hout := hbranch t htBranch
    have hpat := hTpatient t htPatient
    refine ⟨?_, ?_, ?_⟩
    · rw [show actual t = encode (raw t) by simpa [actual, raw, projected] using hout]
      exact hrawSide
    · rw [GenLimit.Generic.mem_sample_iff]
      rintro ⟨s, hs, heq⟩
      have houtActual : actual t = encode (raw t) := by
        simpa [actual, raw, projected] using hout
      have hpEq : projected s = raw t := by
        change projection (input s) = raw t
        rw [heq, houtActual, hprojEncode]
      exact hpat.2.1 s (by omega) hpEq
    · intro s hs
      by_cases hsBranch : Tbranch ≤ s
      · have houtS := hbranch s hsBranch
        rw [show actual s = encode (raw s) by
          simpa [actual, raw, projected] using houtS]
        rw [show actual t = encode (raw t) by
          simpa [actual, raw, projected] using hout]
        intro heq
        exact (Nat.ne_of_lt hs) (hrawInj (hencodeInj heq))
      · intro heq
        have hsEarly : s ∈ earlyTimes := by
          simp [earlyTimes]
          omega
        have hactualEarly : actual s ∈ earlyActual := ⟨s, hsEarly, rfl⟩
        have houtActual : actual t = encode (raw t) := by
          simpa [actual, raw, projected] using hout
        have hencodedEarly : raw t ∈ earlyEncoded := by
          change encode (raw t) ∈ earlyActual
          rw [← houtActual, ← heq]
          exact hactualEarly
        exact hrawBlocked (Or.inr hencodedEarly)
  have hDsubset : D ⊆ sideRange := fun n hn => hn.2
  have hDgoodSubset : Dgood ⊆ sideTarget := fun n hn => hn.2
  have hDloss : (D \ Dgood).Finite := by
    apply hsideFinite.subset
    intro n hn
    exact fun hnSide => hn.2 ⟨hn.1, hnSide⟩
  have hdensityGood : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity Dgood sideTarget := by
    have hhalf : (1 / 2 : ℝ) ≤
        PatientScope.relativeLowerDensity D sideRange := by
      simpa [PatientMachine.patientLowerDensity, D, sideRange, raw, projected, hj]
        using hpatient.2
    exact hhalf.trans (relativeLowerDensity_transfer_finite_loss
      hsideTargetInf hsideSubset hDsubset hDgoodSubset hDloss)
  have hDlateSubset : Dlate ⊆ sideTarget := fun n hn => hn.1.2
  have hlateLoss : (Dgood \ Dlate).Finite := by
    apply hblocked.subset
    intro n hn
    by_contra hnBlock
    exact hn.2 ⟨hn.1, hnBlock⟩
  have hdensityLateSide : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity Dlate sideTarget := by
    exact hdensityGood.trans (relativeLowerDensity_transfer_finite_loss
      hsideTargetInf (by simp) hDgoodSubset hDlateSubset hlateLoss)
  have hdensityLate : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity Dlate Set.univ :=
    hdensityLateSide.trans
      (relativeLowerDensity_cofinite_ambient hsideFinite hDlateSubset)
  have hquarter : (1 / 4 : ℝ) ≤
      PatientScope.relativeLowerDensity (rank '' Dlate) Set.univ :=
    relativeLowerDensity_rank_image_quarter rank hrankInj hrankBound Dlate
      hdensityLate
  let announced : Set ℕ := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn input actual ∩ K)
  let targetRanks : Set ℕ := Stage3Case019.balancedRanks K
  have htargetRanksInf : targetRanks.Infinite := by
    apply (hsideTargetInf.image hrankInj.injOn).mono
    intro m hm
    obtain ⟨n, hn, rfl⟩ := hm
    change Stage3Case019.balanced (rank n) ∈ K
    rw [hbalanced]
    exact hn
  have hrankAnnounced : rank '' Dlate ⊆ announced := by
    intro m hm
    obtain ⟨n, hnLate, rfl⟩ := hm
    have hnGood : n ∈ Dgood := hnLate.1
    have hnD : n ∈ D := hnGood.1
    have hnSide : n ∈ sideTarget := hnGood.2
    obtain ⟨t, hrawt, hfirst⟩ := hnD.1
    have htBranch : Tbranch ≤ t := by
      by_contra hnot
      have htEarly : t ∈ earlyTimes := by
        simp [earlyTimes]
        omega
      exact hnLate.2 (Or.inl ⟨t, htEarly, hrawt⟩)
    have hout := hbranch t htBranch
    change Stage3Case019.balanced (rank n) ∈
      Stage3Case019.GeneratorFirstOn input actual ∩ K
    rw [hbalanced]
    constructor
    · refine ⟨t, ?_, ?_⟩
      · have houtActual : actual t = encode (raw t) := by
          simpa [actual, raw, projected] using hout
        exact houtActual.trans (congrArg encode hrawt)
      · intro s hst heq
        have hpEq : projected s = n := by
          dsimp [projected]
          rw [heq]
          exact hprojEncode n
        exact hfirst s hst hpEq
    · exact hnSide
  have hannouncedTarget : announced ⊆ targetRanks := by
    intro n hn
    exact hn.2
  have htransfer := relativeLowerDensity_transfer_finite_loss
    htargetRanksInf (show targetRanks ⊆ (Set.univ : Set ℕ) by simp)
    (show rank '' Dlate ⊆ (Set.univ : Set ℕ) by simp)
    hannouncedTarget (show (rank '' Dlate \ announced).Finite by
      rw [Set.diff_eq_empty.mpr hrankAnnounced]
      exact Set.finite_empty)
  refine ⟨hnovel, ?_⟩
  have hfinal : (1 / 4 : ℝ) ≤
      PatientScope.relativeLowerDensity announced targetRanks :=
    hquarter.trans htransfer
  simpa [Stage3Case019.balancedRelativeLowerDensity,
    announced, targetRanks, actual] using hfinal


theorem separation_first_guarantee
    (q : ℕ) (K : Set ℤ)
    (hK : K ∈ NoiseLossFeedback.finiteOmissionFirstClass q)
    (input : Stream ℤ)
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
        (Stage3Case019.outputAfterInput (separationGenerator q) input) K ∧
      (1 / 4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
        (Stage3Case019.GeneratorFirstOn input
          (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K) K := by
  obtain ⟨Tbranch, hbranch⟩ :=
    NoiseLossFeedback.allMarkers_eventually_observed hinput hK.1
  refine separation_branch_guarantee q K input positiveEncode positiveProjection
    positiveRank Tbranch hinput positiveProjection_encode positiveEncode_injective
    positiveRank_injective ?_ balanced_positiveRank ?_ ?_ ?_
  · intro n
    cases n <;> simp [positiveRank] <;> omega
  · simpa [positiveSide] using positiveSide_compl_finite hK
  · exact positiveProjectedRange_compl_finite hK hinput.2.1
  · intro t ht
    exact separationGenerator_output_positive q input t (hbranch t ht)

theorem separation_second_guarantee
    (q : ℕ) (K : Set ℤ)
    (hK : K ∈ NoiseLossFeedback.finiteOmissionSecondClass q)
    (input : Stream ℤ)
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
        (Stage3Case019.outputAfterInput (separationGenerator q) input) K ∧
      (1 / 4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
        (Stage3Case019.GeneratorFirstOn input
          (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K) K := by
  refine separation_branch_guarantee q K input negativeEncode negativeProjection
    negativeRank 0 hinput negativeProjection_encode negativeEncode_injective
    negativeRank_injective ?_ balanced_negativeRank ?_ ?_ ?_
  · intro n
    cases n <;> simp [negativeRank] <;> omega
  · simpa [negativeSide] using negativeSide_compl_finite hK
  · exact negativeProjectedRange_compl_finite hK hinput.2.1
  · intro t _ht
    exact separationGenerator_output_negative q input t
      (NoiseLossFeedback.not_allMarkers_observed_second hK hinput t)

theorem uncountable_separation : Stage3Case019.SeparationClause := by
  intro q
  refine ⟨NoiseLossFeedback.finiteOmissionClass q,
    finiteOmissionClass_not_countable q, ?_, ?_, separation_negative q⟩
  · intro K hK
    exact NoiseLossFeedback.finiteOmissionClass_uus q K hK
  · refine ⟨separationGenerator q, ?_⟩
    intro K hK input hinput
    rcases hK with hfirst | hsecond
    · exact separation_first_guarantee q K hfirst input hinput
    · exact separation_second_guarantee q K hsecond input hinput

end Stage3Case019Proof

open Stage3Case019

theorem stage3_result : Stage3Case019.MainClaim := by
  exact ⟨Stage3Case019Proof.countable_half_density,
    Stage3Case019Proof.uncountable_separation⟩
