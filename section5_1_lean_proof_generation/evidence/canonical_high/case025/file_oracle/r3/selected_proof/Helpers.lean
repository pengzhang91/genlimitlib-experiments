import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter

namespace Stage3Case025

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

def prefixExtension (t : ℕ) (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

@[simp] theorem prefixExtension_eq
    (t : ℕ) (xs : Fin (t + 1) → ℕ) {n : ℕ} (hn : n < t + 1) :
    prefixExtension t xs n = xs ⟨n, hn⟩ := by
  simp [prefixExtension, hn]

theorem sample_eq_of_eq_lt
    {a b : Stream} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem consistent_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_eq_of_eq_lt h]

theorem recursiveCritical_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using
          consistent_eq_of_eq_lt (C := C) (i := 0) h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_eq_of_eq_lt h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hprev j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_eq_of_eq_lt h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hprev j hj ((ih j (by omega)).mp hjcrit)


theorem consistentIndices_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_eq_of_eq_lt h]

theorem criticalIndices_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_eq_of_eq_lt h]

theorem survivingCriticalIndices_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_eq_of_eq_lt (fun n hn => h n (by omega))]
  rw [recursiveCritical_eq_of_eq_lt h]

theorem highestCritical_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq_of_eq_lt h]

theorem highestSurvivor_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_eq_lt h]

theorem lowestConsistentInScope_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_eq_lt h]

theorem lowestConsistent_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_eq_of_eq_lt h).mp hi⟩
    have hsa := GenLimit.PatientMachine.lowestConsistent_spec
      (fallback := fallback) ha
    have hsb := GenLimit.PatientMachine.lowestConsistent_spec
      (fallback := fallback) hb
    apply le_antisymm
    · exact Nat.le_of_not_gt fun hlt =>
        hsa.2 _ hlt ((consistent_eq_of_eq_lt h).mpr hsb.1)
    · exact Nat.le_of_not_gt fun hlt =>
        hsb.2 _ hlt ((consistent_eq_of_eq_lt h).mp hsa.1)
  · have hb : ¬∃ i, GenLimit.Consistent C b t i := by
      intro hex
      obtain ⟨i, hi⟩ := hex
      exact ha ⟨i, (consistent_eq_of_eq_lt h).mpr hi⟩
    simp [GenLimit.PatientMachine.lowestConsistent, ha, hb]

theorem stableDecision_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  split <;> simp only
  rw [highestCritical_eq_of_eq_lt h]

theorem backtrackDecision_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.backtrackDecision
  rw [consistentIndices_eq_of_eq_lt h]
  rw [survivingCriticalIndices_eq_of_eq_lt h]
  rw [highestSurvivor_eq_of_eq_lt h]
  rw [lowestConsistentInScope_eq_of_eq_lt h]
  rw [lowestConsistent_eq_of_eq_lt h]
  have hex : (∃ j, GenLimit.Consistent C a (t + 1) j) ↔
      ∃ j, GenLimit.Consistent C b (t + 1) j := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (consistent_eq_of_eq_lt h).mp hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (consistent_eq_of_eq_lt h).mpr hj⟩
  simp only [hex]

theorem decide_eq_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [consistent_eq_of_eq_lt h]
  split
  · exact stableDecision_eq_of_eq_lt old h
  · exact backtrackDecision_eq_of_eq_lt old h


theorem available_iff_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    {used : Finset ℕ} {focus x : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.Available C a t used focus x ↔
      GenLimit.PatientMachine.Available C b t used focus x := by
  simp only [GenLimit.PatientMachine.Available, sample_eq_of_eq_lt h]

theorem leastAvailable_eq_of_eq_lt
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {a b : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.leastAvailable C hInfinite a t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite b t used focus := by
  classical
  apply le_antisymm
  · apply GenLimit.PatientMachine.leastAvailable_minimal
    exact (available_iff_of_eq_lt h).mpr
      (GenLimit.PatientMachine.leastAvailable_spec C hInfinite b t used focus)
  · apply GenLimit.PatientMachine.leastAvailable_minimal
    exact (available_iff_of_eq_lt h).mp
      (GenLimit.PatientMachine.leastAvailable_spec C hInfinite a t used focus)

theorem processRound_eq_of_eq_lt
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hd := decide_eq_of_eq_lt (C := O.language) old h
  have hx := leastAvailable_eq_of_eq_lt O.language O.infinite' old.used
    (GenLimit.PatientMachine.decide O.language b t old).focus h
  simp only [GenLimit.PatientMachine.processRound]
  rw [hd, hx]

theorem run_eq_of_eq_lt
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.run O a t =
      GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun n hn => h n (by omega))]
      exact processRound_eq_of_eq_lt O _ h

theorem patientOutput_eq_of_eq_le
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n ≤ t → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_eq_lt O (fun n hn => h n (by omega))]

noncomputable def patientOnlineGenerator (O : GenLimit.OracleFamily) :
    OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixExtension t xs) t

theorem patientOnlineGenerator_follows
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply patientOutput_eq_of_eq_le
  intro n hn
  simp [prefixExtension, Nat.lt_succ_iff.mpr hn]


theorem patient_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  have hRun := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    O input (z := i) hP
  refine ⟨output, patientOnlineGenerator_follows O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hRun.1
    refine ⟨T, ?_⟩
    intro t ht
    have hvalid := hT t ht
    refine ⟨hvalid.1, ?_, hvalid.2.2⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact hvalid.2.1 s (Nat.lt_succ_iff.mp hs) heq
  · simpa [output, GenLimit.PatientMachine.patientLowerDensity] using hRun.2


theorem prefixCount_le_add_finite
    {A B F : Set ℕ} (hsub : A ⊆ B ∪ F) (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hF.toFinset.card := by
  classical
  change (GenLimit.PatientScope.prefixFinset A n).card ≤
    (GenLimit.PatientScope.prefixFinset B n).card + hF.toFinset.card
  apply (Finset.card_le_card ?_).trans
    (Finset.card_union_le
      (GenLimit.PatientScope.prefixFinset B n) hF.toFinset)
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx
  rw [Finset.mem_union]
  rcases hsub hx.2 with hxB | hxF
  · exact Or.inl (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx.1, hxB⟩)
  · exact Or.inr (Set.Finite.mem_toFinset hF |>.2 hxF)

theorem relativeLowerDensity_transfer_finite
    {Q K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite)
    (hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R) :
    (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hKcount := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hden : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKcount
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hden
  have hKpos : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hKcount.eventually (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hKpos] with n hn
    have hKRcount := GenLimit.PatientScope.prefixCount_mono hKR n
    have hsourceCount :
        GenLimit.PatientScope.prefixCount (Q ∩ R) n ≤
          GenLimit.PatientScope.prefixCount (Q ∩ K) n +
            hfinite.toFinset.card := by
      apply prefixCount_le_add_finite (F := R \ K) _ hfinite n
      intro x hx
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨hx.1, hxK⟩
      · exact Or.inr ⟨hx.2, hxK⟩
    have hKposR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hRposR : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n := by
      exact_mod_cast lt_of_lt_of_le hn hKRcount
    have hcross :
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) *
            GenLimit.PatientScope.prefixCount K n ≤
          ((GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) +
            hfinite.toFinset.card) *
            GenLimit.PatientScope.prefixCount R n := by
      have hsourceCountR :
          (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) ≤
            GenLimit.PatientScope.prefixCount (Q ∩ K) n +
              hfinite.toFinset.card := by
        exact_mod_cast hsourceCount
      have hKRcountR :
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
            GenLimit.PatientScope.prefixCount R n := by
        exact_mod_cast hKRcount
      calc
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) *
            GenLimit.PatientScope.prefixCount K n ≤
          ((GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) +
            hfinite.toFinset.card) *
            GenLimit.PatientScope.prefixCount K n := by
              exact mul_le_mul_of_nonneg_right hsourceCountR (by positivity)
        _ ≤ ((GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) +
            hfinite.toFinset.card) *
            GenLimit.PatientScope.prefixCount R n := by
              exact mul_le_mul_of_nonneg_left hKRcountR (by positivity)
    have hratio := (div_le_div_iff₀ hRposR hKposR).2 hcross
    simpa only [source, target, error, add_div] using hratio
  have htarget_le_one : ∀ n, target n ≤ (1 : ℝ) := by
    intro n
    dsimp only [target]
    have hmono := GenLimit.PatientScope.prefixCount_mono
      (show Q ∩ K ⊆ K from Set.inter_subset_right) n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · have hnum : GenLimit.PatientScope.prefixCount (Q ∩ K) n = 0 :=
        Nat.eq_zero_of_le_zero (hn ▸ hmono)
      simp [hn, hnum]
    · have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast hmono
  have htarget_nonneg : ∀ n, (0 : ℝ) ≤ target n := by
    intro n
    dsimp only [target]
    positivity
  have hsource_nonneg : ∀ n, (0 : ℝ) ≤ source n := by
    intro n
    dsimp only [source]
    positivity
  unfold GenLimit.PatientScope.relativeLowerDensity at hhalf ⊢
  change (1 / 2 : ℝ) ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  have hySource : y < liminf source atTop := by
    exact lt_of_lt_of_le hy hhalf
  obtain ⟨r, hyr, hrSource⟩ := exists_between hySource
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrSource
      (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr he hp
  linarith


noncomputable def finiteAdditionFamily
    (family : ℕ → Language) (code : ℕ) : Language :=
  let data := Nat.unpair code
  family data.1 ∪ (Finset.equivBitIndices data.2 : Set ℕ)

def encodeFiniteAddition (i code : ℕ) : ℕ := Nat.pair i code

@[simp] theorem finiteAdditionFamily_encode
    (family : ℕ → Language) (i code : ℕ) :
    finiteAdditionFamily family (encodeFiniteAddition i code) =
      family i ∪ (Finset.equivBitIndices code : Set ℕ) := by
  simp [finiteAdditionFamily, encodeFiniteAddition, Nat.unpair_pair]

theorem finiteAdditionFamily_infinite
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) (code : ℕ) :
    (finiteAdditionFamily family code).Infinite := by
  let data := Nat.unpair code
  exact (hInfinite data.1).mono Set.subset_union_left

theorem finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hPositive family hInfinite
  let expanded : ℕ → Language := finiteAdditionFamily family
  have hExpandedInfinite : ∀ j, (expanded j).Infinite :=
    finiteAdditionFamily_infinite family hInfinite
  obtain ⟨gen, hgen⟩ := hPositive expanded hExpandedInfinite
  refine ⟨gen, ?_⟩
  intro i input hPresentation
  have hbad : (Set.range input \ family i).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hPresentation.2.image input
  let badCode := Finset.equivBitIndices.symm hbad.toFinset
  let j := encodeFiniteAddition i badCode
  have hbadDecoded :
      (Finset.equivBitIndices badCode : Set ℕ) =
        Set.range input \ family i := by
    change (↑(Finset.equivBitIndices (Finset.equivBitIndices.symm hbad.toFinset)) : Set ℕ) = _
    rw [Equiv.apply_symm_apply]
    exact Set.Finite.coe_toFinset hbad
  have hExpandedEq : expanded j = Set.range input := by
    rw [show expanded j = family i ∪
      (Finset.equivBitIndices badCode : Set ℕ) by
        simp [expanded, j, badCode]]
    rw [hbadDecoded]
    ext x
    constructor
    · rintro (hx | hx)
      · exact hPresentation.1 hx
      · exact hx.1
    · intro hx
      by_cases hxK : x ∈ family i
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  have hPresents : GenLimit.Presents input (expanded j) := by
    change Set.range input = expanded j
    exact hExpandedEq.symm
  obtain ⟨output, hFollows, hNovel, hDensity⟩ := hgen j input hPresents
  refine ⟨output, hFollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hNovel
    obtain ⟨B, hB⟩ := hPresentation.2.bddAbove
    refine ⟨max T (B + 1), ?_⟩
    intro t ht
    have hvalid := hT t ((Nat.le_max_left _ _).trans ht)
    refine ⟨?_, hvalid.2.1, hvalid.2.2⟩
    by_contra hout
    have houtRange : output t ∈ Set.range input := by
      rw [← hExpandedEq]
      exact hvalid.1
    obtain ⟨s, hs⟩ := houtRange
    have hsBad : s ∈ GenLimit.Generic.ViolationIndices input
        (fun x => x ∈ family i) := by
      change input s ∉ family i
      simpa [hs] using hout
    have hsB : s ≤ B := hB hsBad
    have hst : s < t + 1 := by
      have hBt : B + 1 ≤ t := (Nat.le_max_right _ _).trans ht
      omega
    have hmem : input s ∈ GenLimit.sample input (t + 1) :=
      GenLimit.value_mem_sample hst
    rw [hs] at hmem
    exact hvalid.2.1 hmem
  · have hhalfRange : (1 / 2 : ℝ) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ Set.range input)
          (Set.range input) := by
      simpa [hExpandedEq] using hDensity
    exact relativeLowerDensity_transfer_finite
      (hInfinite i) hPresentation.1 hbad hhalfRange

end Stage3Case025
