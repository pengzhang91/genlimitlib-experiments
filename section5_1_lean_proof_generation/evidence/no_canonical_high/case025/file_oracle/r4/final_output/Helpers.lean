import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable def oracleFamily
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

theorem sample_eq_of_eq_on_prefix
    {input₁ input₂ : Stream} {t : ℕ}
    (hinput : ∀ n, n < t → input₁ n = input₂ n) :
    GenLimit.sample input₁ t = GenLimit.sample input₂ t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (hinput n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, hinput n hn⟩

theorem consistent_congr
    {family : GenLimit.LanguageFamily} {input₁ input₂ : Stream} {t i : ℕ}
    (hinput : ∀ n, n < t → input₁ n = input₂ n) :
    GenLimit.Consistent family input₁ t i ↔
      GenLimit.Consistent family input₂ t i := by
  unfold GenLimit.Consistent
  rw [sample_eq_of_eq_on_prefix hinput]

theorem recursiveCritical_congr
    {family : GenLimit.LanguageFamily} {input₁ input₂ : Stream} {t i : ℕ}
    (hinput : ∀ n, n < t → input₁ n = input₂ n) :
    GenLimit.RecursiveCritical family input₁ t i ↔
      GenLimit.RecursiveCritical family input₂ t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using
            consistent_congr (family := family) (i := 0) hinput
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_congr hinput).mp hcon, ?_⟩
            intro j hj hcrit
            exact hprev j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hcrit)
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_congr hinput).mpr hcon, ?_⟩
            intro j hj hcrit
            exact hprev j hj ((ih j (Nat.lt_succ_of_le hj)).mp hcrit)

theorem decide_congr
    (family : GenLimit.LanguageFamily) (input₁ input₂ : Stream)
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (hinput : ∀ n, n < t + 1 → input₁ n = input₂ n) :
    GenLimit.PatientMachine.decide family input₁ t old =
      GenLimit.PatientMachine.decide family input₂ t old := by
  classical
  have h_t : ∀ n, n < t → input₁ n = input₂ n :=
    fun n hn => hinput n (hn.trans (Nat.lt_succ_self t))
  have hCons : GenLimit.Consistent family input₁ (t + 1) =
      GenLimit.Consistent family input₂ (t + 1) := by
    funext i
    exact propext (consistent_congr hinput)
  have hCritT : GenLimit.RecursiveCritical family input₁ t =
      GenLimit.RecursiveCritical family input₂ t := by
    funext i
    exact propext (recursiveCritical_congr h_t)
  have hCritSucc : GenLimit.RecursiveCritical family input₁ (t + 1) =
      GenLimit.RecursiveCritical family input₂ (t + 1) := by
    funext i
    exact propext (recursiveCritical_congr hinput)
  unfold GenLimit.PatientMachine.decide
  unfold GenLimit.PatientMachine.stableDecision
  unfold GenLimit.PatientMachine.backtrackDecision
  unfold GenLimit.PatientMachine.highestCritical
  unfold GenLimit.PatientMachine.highestSurvivor
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  unfold GenLimit.PatientMachine.lowestConsistent
  unfold GenLimit.PatientMachine.consistentIndices
  unfold GenLimit.PatientMachine.survivingCriticalIndices
  unfold GenLimit.PatientMachine.criticalIndices
  rw [hCons, hCritT, hCritSucc]

theorem processRound_congr
    (O : GenLimit.OracleFamily) (input₁ input₂ : Stream)
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (hinput : ∀ n, n < t + 1 → input₁ n = input₂ n) :
    GenLimit.PatientMachine.processRound O input₁ t old =
      GenLimit.PatientMachine.processRound O input₂ t old := by
  classical
  have hsample : GenLimit.sample input₁ (t + 1) =
      GenLimit.sample input₂ (t + 1) :=
    sample_eq_of_eq_on_prefix hinput
  have hdecide := decide_congr O.language input₁ input₂ t old hinput
  let d := GenLimit.PatientMachine.decide O.language input₂ t old
  have hAvailable :
      GenLimit.PatientMachine.Available O.language input₁ (t + 1) old.used d.focus =
        GenLimit.PatientMachine.Available O.language input₂ (t + 1) old.used d.focus := by
    funext x
    apply propext
    simp only [GenLimit.PatientMachine.Available, hsample]
  have hx :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' input₁ (t + 1) old.used d.focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' input₂ (t + 1) old.used d.focus := by
    unfold GenLimit.PatientMachine.leastAvailable
    apply Nat.find_congr'
    intro n
    simpa only [hAvailable]
  unfold GenLimit.PatientMachine.processRound
  simp only [hdecide]
  simpa [d] using congrArg (fun x : ℕ =>
    GenLimit.PatientMachine.State.mk d.scope d.tau
      (if d.focus = old.focus then old.age + 1 else 1) d.focus
      (insert x old.used) (some x) d.move) hx

theorem run_congr
    (O : GenLimit.OracleFamily) (input₁ input₂ : Stream) (t : ℕ)
    (hinput : ∀ n, n < t → input₁ n = input₂ n) :
    GenLimit.PatientMachine.run O input₁ t =
      GenLimit.PatientMachine.run O input₂ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun n hn => hinput n (hn.trans (Nat.lt_succ_self t)))]
      exact processRound_congr O input₁ input₂ t _ hinput

theorem output_congr
    (O : GenLimit.OracleFamily) (input₁ input₂ : Stream) (t : ℕ)
    (hinput : ∀ n, n < t + 1 → input₁ n = input₂ n) :
    GenLimit.PatientMachine.output O input₁ t =
      GenLimit.PatientMachine.output O input₂ t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr O input₁ input₂ (t + 1) hinput]

def prefixExtension {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

noncomputable def patientOnlineGenerator (O : GenLimit.OracleFamily) :
    OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixExtension xs) t

theorem follows_patientOnlineGenerator
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_congr
  intro n hn
  simp [prefixExtension, hn]

theorem patient_novel
    (O : GenLimit.OracleFamily) (input : Stream) {i : ℕ}
    (hPresents : GenLimit.Presents input (O.language i)) :
    GenLimit.NovelGeneratesInLimit input
      (GenLimit.PatientMachine.output O input) (O.language i) := by
  obtain ⟨T, hT⟩ :=
    (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input (z := i) hPresents).1
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  refine ⟨hmem, ?_, hnovel⟩
  intro hsample
  rw [GenLimit.mem_sample_iff] at hsample
  obtain ⟨s, hs, heq⟩ := hsample
  exact hfresh s (Nat.lt_succ_iff.mp hs) heq

theorem positivePresentationHalfDensity : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleFamily family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hPresents
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, follows_patientOnlineGenerator O input, ?_, ?_⟩
  · simpa [output, O, oracleFamily] using patient_novel O input hPresents
  · simpa [output, GenLimit.PatientMachine.patientLowerDensity, O,
      oracleFamily] using
      (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input (z := i) hPresents).2

end Stage3Case025

namespace Stage3Case025

open GenLimit.InfiniteContamination

 theorem prefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
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
  have hcard : aPrefix.card ≤ bPrefix.card + diffPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [diffPrefix, Finset.mem_filter] at hx
    exact Set.Finite.mem_toFinset hfinite |>.2 hx.2
  exact hcard.trans (Nat.add_le_add_left hdiff _)

theorem relativeLowerDensity_finite_extension
    {A L E : Set ℕ} (hL : L.Infinite) (hsub : L ⊆ E)
    (hfinite : (E \ L).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ L) L := by
  let ratioE : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  let ratioL : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ L) n : ℝ) /
      (GenLimit.PatientScope.prefixCount L n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount L n : ℝ)
  have hdenNat := GenLimit.PatientScope.tendsto_prefixCount_atTop hL
  have hdenReal : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount L n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdenNat
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hdenReal
  have hratioE_nonneg : ∀ n, 0 ≤ ratioE n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hratioL_nonneg : ∀ n, 0 ≤ ratioL n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hratioL_le_one : ∀ n, ratioL n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount L n = 0
    · simp [ratioL, hn]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount L n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [ratioL]
      rw [div_le_one hpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (Set.inter_subset_right) n
  have hdiffInter : ((A ∩ E) \ (A ∩ L)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxL => hx.2 ⟨hx.1.1, hxL⟩⟩
  have hcompare : ∀ᶠ n : ℕ in atTop,
      ratioE n ≤ ratioL n + error n := by
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount L n :=
      hdenNat.eventually (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hl : (0 : ℝ) < GenLimit.PatientScope.prefixCount L n := by
      exact_mod_cast hn
    have hleNat := GenLimit.PatientScope.prefixCount_mono hsub n
    have he : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn hleNat
    have hcardDiff : hdiffInter.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := (Set.Finite.mem_toFinset hdiffInter).mp hx
      exact (Set.Finite.mem_toFinset hfinite).mpr
        ⟨hx'.1.2, fun hxL => hx'.2 ⟨hx'.1.1, hxL⟩⟩
    have hnumNat := (prefixCount_le_add_ncard_diff hdiffInter n).trans
      (Nat.add_le_add_left hcardDiff _)
    have hnum :
        (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (A ∩ L) n +
            hfinite.toFinset.card := by
      exact_mod_cast hnumNat
    calc
      ratioE n ≤
          (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
            (GenLimit.PatientScope.prefixCount L n : ℝ) := by
        unfold ratioE
        gcongr
      _ ≤
          ((GenLimit.PatientScope.prefixCount (A ∩ L) n : ℝ) +
            hfinite.toFinset.card) /
            (GenLimit.PatientScope.prefixCount L n : ℝ) := by
        exact div_le_div_of_nonneg_right hnum hl.le
      _ = ratioL n + error n := by
        rw [add_div]
  change liminf ratioE atTop ≤ liminf ratioL atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop hratioL_le_one)
    (isBoundedUnder_of ⟨0, hratioL_nonneg⟩)).2
  intro c hc
  let d : ℝ := (c + liminf ratioE atTop) / 2
  have hcd : c < d := by dsimp [d]; linarith
  have hdlim : d < liminf ratioE atTop := by dsimp [d]; linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, d < ratioE n :=
    eventually_lt_of_lt_liminf hdlim
      (isBoundedUnder_of ⟨0, hratioE_nonneg⟩)
  have hsmall : ∀ᶠ n : ℕ in atTop, error n < d - c := by
    have hdc : 0 < d - c := sub_pos.mpr hcd
    exact herror.eventually (Iio_mem_nhds hdc)
  filter_upwards [hlarge, hsmall, hcompare] with n hnLarge hnSmall hnCompare
  linarith

end Stage3Case025

namespace Stage3Case025

open GenLimit.InfiniteContamination

 theorem exists_finiteExpansion_index_for_occurrence_presentation
    (O : GenLimit.OracleFamily) (i : ℕ) (input : Stream)
    (hcomplete : CompleteFiniteOccurrencePresentation input (O.language i)) :
    ∃ j,
      GenLimit.Presents input ((finiteExpansionOracleFamily O).language j) ∧
      O.language i ⊆ (finiteExpansionOracleFamily O).language j ∧
      (((finiteExpansionOracleFamily O).language j \ O.language i).Finite) := by
  let noiseFinite := displayedNoise_finite hcomplete.2
  let data : FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm noiseFinite.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := encodeFiniteExpansionCode data
  have hadd :
      (↑noiseFinite.toFinset : Set ℕ) =
        displayedNoise input (O.language i) :=
    Set.Finite.coe_toFinset noiseFinite
  have homissions : displayedOmissions input (O.language i) = ∅ := by
    exact Set.diff_eq_empty.mpr hcomplete.1
  have hrange :
      finiteExpansion (O.language i)
          (displayedNoise input (O.language i)) ∅ =
        Set.range input := by
    rw [← homissions]
    exact finiteExpansion_displayedNoise_displayedOmissions input (O.language i)
  have hpresents :
      GenLimit.Presents input ((finiteExpansionOracleFamily O).language j) := by
    change Set.range input = finiteExpansionLanguage O j
    rw [finiteExpansionLanguage]
    simp only [j, data, finiteExpansionCode_encode, Equiv.apply_symm_apply]
    rw [hadd]
    simpa using hrange.symm
  refine ⟨j, hpresents, ?_, ?_⟩
  · rw [← hpresents]
    exact hcomplete.1
  · rw [← hpresents]
    exact noiseFinite

theorem novelGeneratesInLimit_of_finite_expansion
    {input output : Stream} {L E : Language}
    (hpresents : GenLimit.Presents input E)
    (hfinite : (E \ L).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output E) :
    GenLimit.NovelGeneratesInLimit input output L := by
  classical
  obtain ⟨Tnovel, hTnovel⟩ := hnovel
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hpresents hfinite.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hfinite).mp hx).1)
  refine ⟨max Tnovel Tseen, ?_⟩
  intro t ht
  have htNovel : Tnovel ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨hmemE, hfresh, hrepeat⟩ := hTnovel t htNovel
  refine ⟨?_, hfresh, hrepeat⟩
  by_contra hmemL
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hmemE, hmemL⟩
  have hseenAtT : output t ∈ GenLimit.sample input (t + 1) := by
    have hseenGeneric := GenLimit.Generic.sample_mono
      (htSeen.trans (Nat.le_succ t)) (hTseen hbad)
    simpa [GenLimit.Generic.sample, GenLimit.sample] using hseenGeneric
  exact hfresh hseenAtT

theorem finiteNoiseTransferPrinciple : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let O := oracleFamily family hInfinite
  let expandedO := finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hpositive expandedO.language expandedO.infinite'
  refine ⟨gen, ?_⟩
  intro i input hcomplete
  have hcompleteO :
      CompleteFiniteOccurrencePresentation input (O.language i) := by
    simpa [O, oracleFamily] using hcomplete
  obtain ⟨j, hpresents, hsub, hfinite⟩ :=
    exists_finiteExpansion_index_for_occurrence_presentation O i input hcompleteO
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply novelGeneratesInLimit_of_finite_expansion hpresents hfinite hnovel
  · have hbaseInfinite : (O.language i).Infinite := O.infinite' i
    have htransfer := relativeLowerDensity_finite_extension
      (A := GenLimit.GeneratorFirst input output)
      hbaseInfinite hsub hfinite
    exact hdensity.trans htransfer

end Stage3Case025
