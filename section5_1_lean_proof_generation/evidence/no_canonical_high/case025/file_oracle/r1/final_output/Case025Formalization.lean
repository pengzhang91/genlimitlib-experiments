import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Stage3Case025

namespace Case025

open GenLimit

noncomputable def prefixStream (t : ℕ) (xs : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

@[simp] theorem prefixStream_eq (t : ℕ) (xs : Fin (t + 1) → ℕ)
    {n : ℕ} (hn : n < t + 1) :
    prefixStream t xs n = xs ⟨n, hn⟩ := by
  simp [prefixStream, hn]

theorem sample_eq_of_prefix_eq {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    sample a t = sample b t := by
  classical
  ext x
  simp only [mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem recursiveCritical_congr_of_sample_eq
    (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ}
    (hs : sample a t = sample b t) (i : ℕ) :
    RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [RecursiveCritical, Consistent, hs]
      | succ n =>
          rw [RecursiveCritical, RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨?_, ?_⟩
            · simpa [Consistent, hs] using hcon
            · intro j hj hjcrit
              exact hcrit j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨?_, ?_⟩
            · simpa [Consistent, hs] using hcon
            · intro j hj hjcrit
              exact hcrit j hj ((ih j (by omega)).mp hjcrit)


theorem highestCritical_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} (t scope fallback : ℕ)
    (hcrit : ∀ i, RecursiveCritical C a t i ↔ RecursiveCritical C b t i) :
    PatientMachine.highestCritical C a t scope fallback =
      PatientMachine.highestCritical C b t scope fallback := by
  classical
  have hset : PatientMachine.criticalIndices C a t scope =
      PatientMachine.criticalIndices C b t scope := by
    ext i
    simp [PatientMachine.mem_criticalIndices, hcrit]
  simp only [PatientMachine.highestCritical]
  rw [hset]

theorem highestSurvivor_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} (t scope fallback : ℕ)
    (hcrit0 : ∀ i, RecursiveCritical C a t i ↔ RecursiveCritical C b t i)
    (hcrit1 : ∀ i, RecursiveCritical C a (t + 1) i ↔
      RecursiveCritical C b (t + 1) i) :
    PatientMachine.highestSurvivor C a t scope fallback =
      PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  have hset : PatientMachine.survivingCriticalIndices C a t scope =
      PatientMachine.survivingCriticalIndices C b t scope := by
    ext i
    simp [PatientMachine.mem_survivingCriticalIndices, hcrit0, hcrit1]
  simp only [PatientMachine.highestSurvivor]
  rw [hset]

theorem lowestConsistentInScope_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} (t scope fallback : ℕ)
    (hcon : ∀ i, Consistent C a t i ↔ Consistent C b t i) :
    PatientMachine.lowestConsistentInScope C a t scope fallback =
      PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  have hset : PatientMachine.consistentIndices C a t scope =
      PatientMachine.consistentIndices C b t scope := by
    ext i
    simp [PatientMachine.mem_consistentIndices, hcon]
  simp only [PatientMachine.lowestConsistentInScope]
  rw [hset]

theorem lowestConsistent_congr
    (C : LanguageFamily) {a b : ℕ → ℕ} (t fallback : ℕ)
    (hcon : ∀ i, Consistent C a t i ↔ Consistent C b t i) :
    PatientMachine.lowestConsistent C a t fallback =
      PatientMachine.lowestConsistent C b t fallback := by
  classical
  by_cases ha : ∃ i, Consistent C a t i
  · have hb : ∃ i, Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (hcon i).mp hi⟩
    have hsa := PatientMachine.lowestConsistent_spec (fallback := fallback) ha
    have hsb := PatientMachine.lowestConsistent_spec (fallback := fallback) hb
    apply Nat.le_antisymm
    · exact Nat.le_of_not_gt (fun hlt => hsa.2 _ hlt ((hcon _).mpr hsb.1))
    · exact Nat.le_of_not_gt (fun hlt => hsb.2 _ hlt ((hcon _).mp hsa.1))
  · have hb : ¬ ∃ i, Consistent C b t i := by
      intro hex
      obtain ⟨i, hi⟩ := hex
      exact ha ⟨i, (hcon i).mpr hi⟩
    simp [PatientMachine.lowestConsistent, ha, hb]

theorem stableDecision_congr
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (hcrit1 : ∀ i, RecursiveCritical O.language a (t + 1) i ↔
      RecursiveCritical O.language b (t + 1) i)
    (old : PatientMachine.State) :
    PatientMachine.stableDecision O.language a t old =
      PatientMachine.stableDecision O.language b t old := by
  classical
  simp only [PatientMachine.stableDecision]
  rw [highestCritical_congr O.language (t + 1) (old.scope + 1) old.focus hcrit1]

theorem backtrackDecision_congr
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (hcon1 : ∀ i, Consistent O.language a (t + 1) i ↔
      Consistent O.language b (t + 1) i)
    (hcrit0 : ∀ i, RecursiveCritical O.language a t i ↔
      RecursiveCritical O.language b t i)
    (hcrit1 : ∀ i, RecursiveCritical O.language a (t + 1) i ↔
      RecursiveCritical O.language b (t + 1) i)
    (old : PatientMachine.State) :
    PatientMachine.backtrackDecision O.language a t old =
      PatientMachine.backtrackDecision O.language b t old := by
  classical
  have hconsistent : PatientMachine.consistentIndices O.language a (t + 1) old.scope =
      PatientMachine.consistentIndices O.language b (t + 1) old.scope := by
    ext i
    simp [PatientMachine.mem_consistentIndices, hcon1]
  have hsurvivors : PatientMachine.survivingCriticalIndices O.language a t old.scope =
      PatientMachine.survivingCriticalIndices O.language b t old.scope := by
    ext i
    simp [PatientMachine.mem_survivingCriticalIndices, hcrit0, hcrit1]
  have hhighest := highestSurvivor_congr O.language t old.scope old.focus hcrit0 hcrit1
  have hlowestScope :=
    lowestConsistentInScope_congr O.language (t + 1) old.scope old.focus hcon1
  have hlowest := lowestConsistent_congr O.language (t + 1) old.focus hcon1
  simp only [PatientMachine.backtrackDecision]
  rw [hconsistent, hsurvivors, hhighest, hlowestScope, hlowest]
  have hpred : (fun i => Consistent O.language a (t + 1) i) =
      (fun i => Consistent O.language b (t + 1) i) := by
    funext i
    exact propext (hcon1 i)
  rw [hpred]

theorem decide_congr_of_prefix_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n < t + 1 → a n = b n)
    (old : PatientMachine.State) :
    PatientMachine.decide O.language a t old =
      PatientMachine.decide O.language b t old := by
  classical
  have hs0 : sample a t = sample b t :=
    sample_eq_of_prefix_eq (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t)))
  have hs1 : sample a (t + 1) = sample b (t + 1) :=
    sample_eq_of_prefix_eq h
  have hcon1 (i : ℕ) : Consistent O.language a (t + 1) i ↔
      Consistent O.language b (t + 1) i := by
    simp [Consistent, hs1]
  have hcrit0 (i : ℕ) : RecursiveCritical O.language a t i ↔
      RecursiveCritical O.language b t i :=
    recursiveCritical_congr_of_sample_eq O.language hs0 i
  have hcrit1 (i : ℕ) : RecursiveCritical O.language a (t + 1) i ↔
      RecursiveCritical O.language b (t + 1) i :=
    recursiveCritical_congr_of_sample_eq O.language hs1 i
  simp only [PatientMachine.decide]
  rw [propext (hcon1 old.focus)]
  rw [stableDecision_congr O t hcrit1 old]
  rw [backtrackDecision_congr O t hcon1 hcrit0 hcrit1 old]
theorem leastAvailable_congr_of_sample_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (hs : sample a t = sample b t) (used : Finset ℕ) (focus : ℕ) :
    PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  apply le_antisymm
  · apply PatientMachine.leastAvailable_minimal
    have hspec :=
      PatientMachine.leastAvailable_spec O.language O.infinite' b t used focus
    simpa [PatientMachine.Available, hs] using hspec
  · apply PatientMachine.leastAvailable_minimal
    have hspec :=
      PatientMachine.leastAvailable_spec O.language O.infinite' a t used focus
    simpa [PatientMachine.Available, hs] using hspec

theorem processRound_congr_of_prefix_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n < t + 1 → a n = b n)
    (old : PatientMachine.State) :
    PatientMachine.processRound O a t old =
      PatientMachine.processRound O b t old := by
  classical
  have hd := decide_congr_of_prefix_eq O t h old
  have hs := sample_eq_of_prefix_eq h
  simp only [PatientMachine.processRound]
  rw [hd]
  rw [leastAvailable_congr_of_sample_eq O (t + 1) hs old.used
    (PatientMachine.decide O.language b t old).focus]

theorem run_congr_of_prefix_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    PatientMachine.run O a t = PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      rw [ih (fun n hn => h n (lt_trans hn (Nat.lt_succ_self t)))]
      exact processRound_congr_of_prefix_eq O t h (PatientMachine.run O b t)

theorem output_congr_of_prefix_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n < t + 1 → a n = b n) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  unfold PatientMachine.output
  rw [run_congr_of_prefix_eq O (t + 1) h]

noncomputable def patientOnline (O : OracleFamily) : OnlineGenerator :=
  fun t xs _ => PatientMachine.output O (prefixStream t xs) t

theorem patientOnline_follows (O : OracleFamily) (input : Stream) :
    Follows (patientOnline O) input (PatientMachine.output O input) := by
  intro t
  apply output_congr_of_prefix_eq O t
  intro n hn
  simp [prefixStream, hn]

theorem patient_novel (O : OracleFamily) (input : Stream) {z : ℕ}
    (hP : Presents input (O.language z)) :
    NovelGeneratesInLimit input (PatientMachine.output O input) (O.language z) := by
  obtain ⟨hgen, _⟩ := PatientMachine.patientScope_generation_and_lowerDensity O input hP
  obtain ⟨T, hT⟩ := hgen
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  refine ⟨hmem, ?_, hnovel⟩
  intro hs
  rw [mem_sample_iff] at hs
  obtain ⟨s, hslt, heq⟩ := hs
  exact hfresh s (by omega) heq

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hinfinite
  let O : OracleFamily :=
    { language := family
      infinite' := hinfinite
      query := fun i x => by
        classical
        exact if x ∈ family i then true else false
      query_spec := by
        classical
        intro i x
        simp }
  refine ⟨patientOnline O, ?_⟩
  intro i input hP
  refine ⟨PatientMachine.output O input, patientOnline_follows O input,
    patient_novel O input hP, ?_⟩
  simpa [PatientMachine.patientLowerDensity, O] using
    PatientMachine.patientScope_lowerDensity_half O input hP


open Filter
open scoped Topology
open GenLimit.PatientScope
open GenLimit.InfiniteContamination

theorem ambientPrefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := prefixFinset A n
  let bPrefix := prefixFinset B n
  let diffPrefix := prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    simp only [aPrefix, bPrefix, diffPrefix, mem_prefixFinset,
      Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hcard : aPrefix.card ≤ bPrefix.card + diffPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2 (mem_prefixFinset.mp hx).2
  simpa [prefixCount, aPrefix, bPrefix, diffPrefix] using
    hcard.trans (Nat.add_le_add_left hdiff _)

theorem ambientRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    (0 : ℝ) ≤ (prefixCount A n : ℝ) / (prefixCount K n : ℝ) := by
  positivity

theorem ambientRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
  by_cases hn : prefixCount K n = 0
  · simp [hn]
  · have hnpos : (0 : ℝ) < prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_le_one hnpos]
    exact_mod_cast prefixCount_mono hAK n

theorem relativeLowerDensity_mono_finite_extension
    {A K E : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    relativeLowerDensity (A ∩ E) E ≤ relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) / (prefixCount K n : ℝ)
  have hcountK := tendsto_prefixCount_atTop hK
  have hcountKR : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcountKR
  have hKpos : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
    hcountK.eventually (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hKpos] with n hn
    have hnK : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hnKE : prefixCount K n ≤ prefixCount E n := prefixCount_mono hKE n
    have hnE : (0 : ℝ) < prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn hnKE
    have hdiff : ((A ∩ E) \ (A ∩ K)).Finite := by
      apply hfinite.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hnumNat := ambientPrefixCount_le_add_ncard_diff hdiff n
    have hcard : hdiff.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      exact Set.Finite.mem_toFinset hfinite |>.2
        (by
          have hxm := Set.Finite.mem_toFinset hdiff |>.1 hx
          exact ⟨hxm.1.2, fun hxK => hxm.2 ⟨hxm.1.1, hxK⟩⟩)
    have hnum : (prefixCount (A ∩ E) n : ℝ) ≤
        prefixCount (A ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hnumNat.trans (Nat.add_le_add_left hcard _)
    calc
      source n ≤
          ((prefixCount (A ∩ K) n : ℝ) + hfinite.toFinset.card) /
            (prefixCount E n : ℝ) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt hnE)
      _ ≤ ((prefixCount (A ∩ K) n : ℝ) + hfinite.toFinset.card) /
            (prefixCount K n : ℝ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hnK
        · exact_mod_cast hnKE
      _ = target n + error n := by rw [add_div]
  unfold relativeLowerDensity
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => ambientRatio_le_one (Set.inter_subset_right) n))
    (isBoundedUnder_of
      ⟨0, fun n => ambientRatio_nonneg (A ∩ K) K n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrsource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrsource
      (isBoundedUnder_of
        ⟨0, fun n => ambientRatio_nonneg (A ∩ E) E n⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr herr hp
  linarith

theorem novelGeneratesInLimit_of_finite_extraneous
    {input output : Stream} {K E : GenLimit.Language}
    (hP : Presents input E) (hfinite : (E \ K).Finite)
    (hnovel : NovelGeneratesInLimit input output E) :
    NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hnovel
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hP hfinite.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hfinite).mp hx).1)
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have htGenerate : Tgenerate ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨hmemE, hfresh, hnovelOut⟩ := hTgenerate t htGenerate
  refine ⟨?_, hfresh, hnovelOut⟩
  by_contra hnotK
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hmemE, hnotK⟩
  have hseenAt : output t ∈ GenLimit.sample input Tseen := by
    simpa [GenLimit.Generic.sample, GenLimit.sample] using hTseen hbad
  exact hfresh (GenLimit.sample_mono (htSeen.trans (Nat.le_succ t)) hseenAt)

theorem stage3_finite_noise_transfer
    : FiniteNoiseTransferPrinciple := by
  intro hpositive
  intro family hinfinite
  let O : OracleFamily :=
    { language := family
      infinite' := hinfinite
      query := fun i x => by
        classical
        exact if x ∈ family i then true else false
      query_spec := by
        classical
        intro i x
        simp }
  let expandedO := finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hpositive expandedO.language expandedO.infinite'
  refine ⟨gen, ?_⟩
  intro i input hcontam
  let noiseFinite := displayedNoise_finite hcontam.2
  let data : FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm noiseFinite.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := encodeFiniteExpansionCode data
  have hnoiseSet :
      (↑noiseFinite.toFinset : Set ℕ) = displayedNoise input (family i) :=
    Set.Finite.coe_toFinset noiseFinite
  have homissions : displayedOmissions input (family i) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.2 (hcontam.1 hx.1)
  have hP : Presents input (expandedO.language j) := by
    change Set.range input = finiteExpansionLanguage O j
    rw [finiteExpansionLanguage]
    simp only [j, data, finiteExpansionCode_encode, Equiv.apply_symm_apply]
    rw [hnoiseSet]
    simp only [Finset.coe_empty]
    rw [← homissions]
    exact (finiteExpansion_displayedNoise_displayedOmissions
      input (family i)).symm
  obtain ⟨output, hfollows, hnovel, hdenseExpanded⟩ := hgen j input hP
  refine ⟨output, hfollows, ?_, ?_⟩
  · have hfinite : (expandedO.language j \ family i).Finite := by
      rw [← hP]
      exact displayedNoise_finite hcontam.2
    exact novelGeneratesInLimit_of_finite_extraneous hP hfinite hnovel
  · have hKE : family i ⊆ expandedO.language j := by
      intro x hx
      rw [← hP]
      exact hcontam.1 hx
    have hfinite : (expandedO.language j \ family i).Finite := by
      rw [← hP]
      exact displayedNoise_finite hcontam.2
    exact hdenseExpanded.trans
      (relativeLowerDensity_mono_finite_extension (hinfinite i) hKE hfinite)


end Case025

open Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
