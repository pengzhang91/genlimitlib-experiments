import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Case025

open Stage3Case025

def prefixStream {t : ℕ} (xs : Fin t → ℕ) : Stream :=
  fun n => if h : n < t then xs ⟨n, h⟩ else 0

@[simp] theorem prefixStream_apply {t : ℕ} (xs : Fin t → ℕ) (i : Fin t) :
    prefixStream xs i = xs i := by simp [prefixStream, i.isLt]

theorem sample_eq_of_prefix_eq
    {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  classical
  unfold GenLimit.sample
  apply Finset.image_congr
  intro n hn
  exact h n (Finset.mem_range.mp hn)

theorem consistent_iff_of_prefix_eq
    {C : GenLimit.LanguageFamily} {stream₁ stream₂ : Stream} {t i : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.Consistent C stream₁ t i ↔
      GenLimit.Consistent C stream₂ t i := by
  simp only [GenLimit.Consistent, sample_eq_of_prefix_eq h]

theorem recursiveCritical_iff_of_prefix_eq
    {C : GenLimit.LanguageFamily} {stream₁ stream₂ : Stream} {t i : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.RecursiveCritical C stream₁ t i ↔
      GenLimit.RecursiveCritical C stream₂ t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [GenLimit.RecursiveCritical] using
            consistent_iff_of_prefix_eq (C := C) (i := 0) h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_iff_of_prefix_eq (C := C) (i := i + 1) h]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjcrit)

theorem consistentIndices_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) (scope : ℕ) :
    GenLimit.PatientMachine.consistentIndices C stream₁ t scope =
      GenLimit.PatientMachine.consistentIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_iff_of_prefix_eq (C := C) (i := i) h]

theorem criticalIndices_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) (scope : ℕ) :
    GenLimit.PatientMachine.criticalIndices C stream₁ t scope =
      GenLimit.PatientMachine.criticalIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_iff_of_prefix_eq (C := C) (i := i) h]

theorem survivingCriticalIndices_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) (scope : ℕ) :
    GenLimit.PatientMachine.survivingCriticalIndices C stream₁ t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_iff_of_prefix_eq (C := C) (i := i)
      (fun n hn => h n (Nat.lt.step hn)),
    recursiveCritical_iff_of_prefix_eq (C := C) (i := i) h]

theorem highestCritical_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) (scope fallback : ℕ) :
    GenLimit.PatientMachine.highestCritical C stream₁ t scope fallback =
      GenLimit.PatientMachine.highestCritical C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq_of_prefix_eq C h scope]

theorem highestSurvivor_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) (scope fallback : ℕ) :
    GenLimit.PatientMachine.highestSurvivor C stream₁ t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_prefix_eq C t h scope]

theorem lowestConsistentInScope_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) (scope fallback : ℕ) :
    GenLimit.PatientMachine.lowestConsistentInScope C stream₁ t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_prefix_eq C h scope]

theorem lowestConsistent_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) (fallback : ℕ) :
    GenLimit.PatientMachine.lowestConsistent C stream₁ t fallback =
      GenLimit.PatientMachine.lowestConsistent C stream₂ t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases hex₁ : ∃ i, GenLimit.Consistent C stream₁ t i
  · have hex₂ : ∃ i, GenLimit.Consistent C stream₂ t i := by
      obtain ⟨i, hi⟩ := hex₁
      exact ⟨i, (consistent_iff_of_prefix_eq (C := C) (i := i) h).1 hi⟩
    simp only [dif_pos hex₁, dif_pos hex₂]
    apply Nat.find_congr (Nat.find_spec hex₁)
    intro n _
    exact consistent_iff_of_prefix_eq (C := C) (i := n) h
  · have hex₂ : ¬ ∃ i, GenLimit.Consistent C stream₂ t i := by
      rintro ⟨i, hi⟩
      exact hex₁ ⟨i, (consistent_iff_of_prefix_eq (C := C) (i := i) h).2 hi⟩
    simp [hex₁, hex₂]

theorem stableDecision_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.stableDecision C stream₁ t old =
      GenLimit.PatientMachine.stableDecision C stream₂ t old := by
  classical
  by_cases hwait : 2 ^ old.tau ≤ old.age
  · simp [GenLimit.PatientMachine.stableDecision, hwait,
      highestCritical_eq_of_prefix_eq C h]
  · simp [GenLimit.PatientMachine.stableDecision, hwait]

theorem backtrackDecision_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.backtrackDecision C stream₁ t old =
      GenLimit.PatientMachine.backtrackDecision C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.backtrackDecision
  rw [consistentIndices_eq_of_prefix_eq C h,
    survivingCriticalIndices_eq_of_prefix_eq C t h,
    highestSurvivor_eq_of_prefix_eq C t h,
    lowestConsistentInScope_eq_of_prefix_eq C h,
    lowestConsistent_eq_of_prefix_eq C h]
  simp only [consistent_iff_of_prefix_eq (C := C) h]

theorem decide_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.decide C stream₁ t old =
      GenLimit.PatientMachine.decide C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [consistent_iff_of_prefix_eq (C := C) h,
    stableDecision_eq_of_prefix_eq C t old h,
    backtrackDecision_eq_of_prefix_eq C t old h]

theorem leastAvailable_eq_of_prefix_eq
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) (used : Finset ℕ) (focus : ℕ) :
    GenLimit.PatientMachine.leastAvailable C hInfinite stream₁ t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite stream₂ t used focus := by
  classical
  have hs := sample_eq_of_prefix_eq h
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr (Nat.find_spec
    (GenLimit.PatientMachine.available_exists C hInfinite stream₁ t used focus))
  intro n _
  simp only [GenLimit.PatientMachine.Available, hs]

theorem processRound_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.processRound O stream₁ t old =
      GenLimit.PatientMachine.processRound O stream₂ t old := by
  classical
  have hd := decide_eq_of_prefix_eq O.language t old h
  simp only [GenLimit.PatientMachine.processRound, hd]
  rw [leastAvailable_eq_of_prefix_eq O.language O.infinite' h]

theorem run_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.run O stream₁ t =
      GenLimit.PatientMachine.run O stream₂ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ,
        ih (fun n hn => h n (Nat.lt.step hn))]
      exact processRound_eq_of_prefix_eq O t _ h

theorem patient_output_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_prefix_eq O (t + 1) h]

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily := by
  classical
  exact {
    language := family
    infinite' := hInfinite
    query := fun i x => if x ∈ family i then true else false
    query_spec := fun i x => by simp }

noncomputable def onlinePatient (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t input _ => GenLimit.PatientMachine.output O (prefixStream input) t

theorem onlinePatient_follows (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlinePatient O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  apply patient_output_eq_of_prefix_eq
  intro n hn
  simp [prefixStream, hn]

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨onlinePatient O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  have hP' : GenLimit.Presents input (O.language i) := by simpa [O] using hP
  have hmain := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    O input (z := i) hP'
  refine ⟨output, onlinePatient_follows O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hmain.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨by simpa [output, O] using hmem, ?_, ?_⟩
    · intro hsample
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hfresh s (Nat.lt_succ_iff.mp hs) heq
    · intro s hs
      simpa [output] using hnovel s hs
  · simpa [output, O, GenLimit.PatientMachine.patientLowerDensity] using hmain.2


theorem relative_ratio_nonneg (A K : Language) (n : ℕ) :
    (0 : ℝ) ≤
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

theorem relative_ratio_le_one {A K : Language} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n

theorem prefixCount_le_add_of_finite_diff
    {A B : Language} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let AF := GenLimit.PatientScope.prefixFinset A n
  let BF := GenLimit.PatientScope.prefixFinset B n
  let DF := hfinite.toFinset
  have hsub : AF ⊆ BF ∪ DF := by
    intro x hx
    have hxA : x ∈ A := (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hx).1, hxB⟩)
    · exact Finset.mem_union_right _
        (Set.Finite.mem_toFinset hfinite |>.mpr ⟨hxA, hxB⟩)
  calc
    GenLimit.PatientScope.prefixCount A n = AF.card := rfl
    _ ≤ (BF ∪ DF).card := Finset.card_le_card hsub
    _ ≤ BF.card + DF.card := Finset.card_union_le BF DF
    _ = GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := rfl

theorem relativeLowerDensity_le_of_finite_reference_expansion
    {A K E : Language} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcount : ∀ n,
      GenLimit.PatientScope.prefixCount (A ∩ E) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card := by
    intro n
    classical
    let AF := GenLimit.PatientScope.prefixFinset (A ∩ E) n
    let KF := GenLimit.PatientScope.prefixFinset (A ∩ K) n
    have hsub : AF ⊆ KF ∪ hfinite.toFinset := by
      intro x hx
      have hparts := GenLimit.PatientScope.mem_prefixFinset.mp hx
      by_cases hxK : x ∈ K
      · exact Finset.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr
            ⟨hparts.1, hparts.2.1, hxK⟩)
      · exact Finset.mem_union_right _
          ((Set.Finite.mem_toFinset hfinite).mpr ⟨hparts.2.2, hxK⟩)
    calc
      GenLimit.PatientScope.prefixCount (A ∩ E) n = AF.card := rfl
      _ ≤ (KF ∪ hfinite.toFinset).card := Finset.card_le_card hsub
      _ ≤ KF.card + hfinite.toFinset.card :=
        Finset.card_union_le KF hfinite.toFinset
      _ = GenLimit.PatientScope.prefixCount (A ∩ K) n +
          hfinite.toFinset.card := rfl
  have herror : Tendsto error atTop (nhds 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.comp
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hden := GenLimit.PatientScope.prefixCount_mono hKE n
    have hnum := hcount n
    dsimp [source, target, error]
    have hdenR :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount E n := by exact_mod_cast hden
    have hnumR :
        (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hnum
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          (GenLimit.PatientScope.prefixCount E n : ℝ)
          ≤ (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_left (by positivity) hnR hdenR
      _ ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) +
              hfinite.toFinset.card) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_right hnumR hnR.le
      _ = (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) +
            (hfinite.toFinset.card : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by rw [add_div]
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => relative_ratio_le_one Set.inter_subset_right n))
    (isBoundedUnder_of
      ⟨0, fun n => relative_ratio_nonneg (A ∩ K) K n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, fun n => relative_ratio_nonneg (A ∩ E) E n⟩)
  have herrEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrEventually, hprefix] with n hrs herr hpref
  linarith

theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro _positive
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  let OE := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨onlinePatient OE, ?_⟩
  intro i input hcontam
  let K := family i
  let noise := GenLimit.InfiniteContamination.displayedNoise input K
  have hnoiseFinite : noise.Finite :=
    GenLimit.InfiniteContamination.displayedNoise_finite hcontam.2
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm hnoiseFinite.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  have hlang : OE.language j = Set.range input := by
    change GenLimit.InfiniteContamination.finiteExpansionLanguage O j = _
    rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
    simp only [j, data,
      GenLimit.InfiniteContamination.finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    rw [Set.Finite.coe_toFinset hnoiseFinite]
    ext x
    simp [GenLimit.InfiniteContamination.finiteExpansion]
    change (x ∈ K ∨ x ∈ noise) ↔ x ∈ Set.range input
    constructor
    · rintro (hx | hx)
      · exact hcontam.1 hx
      · exact hx.1
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  have hP : GenLimit.Presents input (OE.language j) := hlang.symm
  let output := GenLimit.PatientMachine.output OE input
  have hmain := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    OE input (z := j) hP
  refine ⟨output, onlinePatient_follows OE input, ?_, ?_⟩
  · obtain ⟨Tvalid, hvalid⟩ := hmain.1
    have hextra : (OE.language j \ K).Finite := by
      rw [hlang]
      exact hnoiseFinite
    have hPgeneric : GenLimit.Generic.Presents input (OE.language j) := hP
    obtain ⟨Tseen, hseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample hPgeneric hextra.toFinset
        (by intro x hx; exact (Set.Finite.mem_toFinset hextra).mp hx |>.1)
    refine ⟨max Tvalid Tseen, ?_⟩
    intro t ht
    have hv := hvalid t ((Nat.le_max_left _ _).trans ht)
    refine ⟨?_, ?_, hv.2.2⟩
    · by_contra hout
      have hbad : output t ∈ hextra.toFinset :=
        (Set.Finite.mem_toFinset hextra).mpr ⟨hv.1, hout⟩
      have hbadT : output t ∈ GenLimit.Generic.sample input Tseen := hseen hbad
      have hbadNow : output t ∈ GenLimit.Generic.sample input (t + 1) :=
        GenLimit.Generic.sample_mono
          ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)) hbadT
      obtain ⟨s, hs, heq⟩ := GenLimit.Generic.mem_sample_iff.mp hbadNow
      exact hv.2.1 s (Nat.lt_succ_iff.mp hs) heq
    · intro hsample
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hv.2.1 s (Nat.lt_succ_iff.mp hs) heq
  · have hfinite : (OE.language j \ K).Finite := by
      rw [hlang]
      exact hnoiseFinite
    have htransfer := relativeLowerDensity_le_of_finite_reference_expansion
      (A := GenLimit.GeneratorFirst input output) (K := K) (E := OE.language j)
      (hInfinite i) (by rw [hlang]; exact hcontam.1) hfinite
    exact hmain.2.trans htransfer

end Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Case025.stage3_finite_noise_transfer Case025.stage3_positive_engine
