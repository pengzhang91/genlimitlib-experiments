import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Stage3Case025Proof

open Stage3Case025

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

@[simp] theorem sample_eq_of_eq_below
    {u v : ℕ → ℕ} {t : ℕ} (h : ∀ s, s < t → u s = v s) :
    GenLimit.sample u t = GenLimit.sample v t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, (h s hs).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, h s hs⟩

theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {u v : ℕ → ℕ} {t i : ℕ}
    (h : ∀ s, s < t → u s = v s) :
    GenLimit.RecursiveCritical C u t i ↔
      GenLimit.RecursiveCritical C v t i := by
  have hsamp : GenLimit.sample u t = GenLimit.sample v t :=
    sample_eq_of_eq_below h
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [GenLimit.RecursiveCritical, GenLimit.Consistent, hsamp]
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨?_, ?_⟩
            · simpa [GenLimit.Consistent, hsamp] using hcon
            · intro j hj hjcrit
              exact hsub j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hcon, hsub⟩
            refine ⟨?_, ?_⟩
            · simpa [GenLimit.Consistent, hsamp] using hcon
            · intro j hj hjcrit
              exact hsub j hj ((ih j (by omega)).mp hjcrit)

set_option maxHeartbeats 1000000 in
theorem processRound_congr
    (O : GenLimit.OracleFamily) {u v : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ s, s ≤ t → u s = v s) :
    GenLimit.PatientMachine.processRound O u t old =
      GenLimit.PatientMachine.processRound O v t old := by
  have hsamp : ∀ k, k ≤ t + 1 →
      GenLimit.sample u k = GenLimit.sample v k := by
    intro k hk
    apply sample_eq_of_eq_below
    intro s hs
    exact h s (by omega)
  have hcons : ∀ k, k ≤ t + 1 → ∀ i,
      GenLimit.Consistent O.language u k i ↔
        GenLimit.Consistent O.language v k i := by
    intro k hk i
    simp [GenLimit.Consistent, hsamp k hk]
  have hcrit : ∀ k, k ≤ t + 1 → ∀ i,
      GenLimit.RecursiveCritical O.language u k i ↔
        GenLimit.RecursiveCritical O.language v k i := by
    intro k hk i
    apply recursiveCritical_congr
    intro s hs
    exact h s (by omega)
  have hconsistentIndices : ∀ k, k ≤ t + 1 → ∀ scope,
      GenLimit.PatientMachine.consistentIndices O.language u k scope =
        GenLimit.PatientMachine.consistentIndices O.language v k scope := by
    intro k hk scope
    ext i
    simp [GenLimit.PatientMachine.consistentIndices, hcons k hk i]
  have hcriticalIndices : ∀ k, k ≤ t + 1 → ∀ scope,
      GenLimit.PatientMachine.criticalIndices O.language u k scope =
        GenLimit.PatientMachine.criticalIndices O.language v k scope := by
    intro k hk scope
    ext i
    simp [GenLimit.PatientMachine.criticalIndices, hcrit k hk i]
  have hsurviving : ∀ scope,
      GenLimit.PatientMachine.survivingCriticalIndices O.language u t scope =
        GenLimit.PatientMachine.survivingCriticalIndices O.language v t scope := by
    intro scope
    ext i
    simp [GenLimit.PatientMachine.survivingCriticalIndices,
      hcrit t (by omega) i, hcrit (t + 1) (by omega) i]
  classical
  have hleast : ∀ used focus,
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' u
          (t + 1) used focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' v
          (t + 1) used focus := by
    intro used focus
    unfold GenLimit.PatientMachine.leastAvailable
    apply Nat.find_congr
      (GenLimit.PatientMachine.leastAvailable_spec
        O.language O.infinite' u (t + 1) used focus)
    intro x hx
    simp only [GenLimit.PatientMachine.Available, hsamp (t + 1) (by omega)]
  have hhighestCritical : ∀ scope fallback,
      GenLimit.PatientMachine.highestCritical O.language u (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical O.language v (t + 1) scope fallback := by
    intro scope fallback
    simp [GenLimit.PatientMachine.highestCritical,
      hcriticalIndices (t + 1) (by omega) scope]
  have hhighestSurvivor : ∀ scope fallback,
      GenLimit.PatientMachine.highestSurvivor O.language u t scope fallback =
        GenLimit.PatientMachine.highestSurvivor O.language v t scope fallback := by
    intro scope fallback
    simp [GenLimit.PatientMachine.highestSurvivor, hsurviving scope]
  have hlowestScope : ∀ scope fallback,
      GenLimit.PatientMachine.lowestConsistentInScope O.language u (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope O.language v (t + 1) scope fallback := by
    intro scope fallback
    simp [GenLimit.PatientMachine.lowestConsistentInScope,
      hconsistentIndices (t + 1) (by omega) scope]
  have hlowest : ∀ fallback,
      GenLimit.PatientMachine.lowestConsistent O.language u (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent O.language v (t + 1) fallback := by
    intro fallback
    simp only [GenLimit.PatientMachine.lowestConsistent,
      hcons (t + 1) (by omega)]
    split
    case isTrue hex =>
      have hu : ∃ n, GenLimit.Consistent O.language u (t + 1) n := by
        obtain ⟨n, hn⟩ := hex
        exact ⟨n, (hcons (t + 1) (by omega) n).mpr hn⟩
      apply Nat.find_congr (Nat.find_spec hu)
      intro n hn
      exact hcons (t + 1) (by omega) n
    case isFalse => rfl
  have hdecision :
      GenLimit.PatientMachine.decide O.language u t old =
        GenLimit.PatientMachine.decide O.language v t old := by
    simp only [GenLimit.PatientMachine.decide,
      GenLimit.PatientMachine.stableDecision,
      GenLimit.PatientMachine.backtrackDecision,
      hcons (t + 1) (by omega),
      hconsistentIndices (t + 1) (by omega), hsurviving old.scope,
      hhighestCritical, hhighestSurvivor, hlowestScope, hlowest]
  unfold GenLimit.PatientMachine.processRound
  rw [hdecision]
  simp only [hleast]

noncomputable def extendPrefix {t : ℕ} (input : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun s => if hs : s < t + 1 then input ⟨s, hs⟩ else 0

@[simp] theorem extendPrefix_apply {t : ℕ} (input : Fin (t + 1) → ℕ)
    (s : ℕ) (hs : s < t + 1) :
    extendPrefix input s = input ⟨s, hs⟩ := by
  simp [extendPrefix, hs]

theorem run_congr
    (O : GenLimit.OracleFamily) {u v : ℕ → ℕ} {t : ℕ}
    (h : ∀ s, s < t → u s = v s) :
    GenLimit.PatientMachine.run O u t =
      GenLimit.PatientMachine.run O v t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      have hold : GenLimit.PatientMachine.run O u t =
          GenLimit.PatientMachine.run O v t :=
        ih (fun s hs => h s (Nat.lt.step hs))
      rw [hold]
      exact processRound_congr O t _ fun s hs =>
        h s (Nat.lt_succ_iff.mpr hs)

theorem patient_output_congr
    (O : GenLimit.OracleFamily) {u v : ℕ → ℕ} {t : ℕ}
    (h : ∀ s, s ≤ t → u s = v s) :
    GenLimit.PatientMachine.output O u t =
      GenLimit.PatientMachine.output O v t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr O (fun s hs => h s (Nat.lt_succ_iff.mp hs))]

noncomputable def onlinePatient (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t input _ => GenLimit.PatientMachine.output O (extendPrefix input) t

theorem follows_onlinePatient (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlinePatient O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  unfold onlinePatient
  apply patient_output_congr
  intro s hs
  simp [extendPrefix, Nat.lt_succ_iff.mpr hs]

theorem positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨onlinePatient O, ?_⟩
  intro i input hP
  refine ⟨GenLimit.PatientMachine.output O input,
    follows_onlinePatient O input, ?_, ?_⟩
  · obtain ⟨hgen, _⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input hP
    obtain ⟨T, hT⟩ := hgen
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hinj⟩ := hT t ht
    refine ⟨hmem, ?_, hinj⟩
    intro hout
    rw [GenLimit.mem_sample_iff] at hout
    obtain ⟨s, hs, heq⟩ := hout
    exact hfresh s (Nat.lt_succ_iff.mp hs) heq
  · exact GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP


theorem exists_expansion_index_for_complete
    (O : GenLimit.OracleFamily) {i : ℕ} {input : Stream}
    (hP : CompleteFiniteOccurrencePresentation input (O.language i)) :
    ∃ j, GenLimit.Presents input
      ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) := by
  classical
  let noise :=
    GenLimit.InfiniteContamination.displayedNoise input (O.language i)
  have hnoise : noise.Finite :=
    GenLimit.InfiniteContamination.displayedNoise_finite hP.2
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm hnoise.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  change Set.range input =
    GenLimit.InfiniteContamination.finiteExpansionLanguage O j
  have hnoiseCoe :
      (↑hnoise.toFinset : Set ℕ) = noise :=
    Set.Finite.coe_toFinset hnoise
  rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
  simp only [j, data,
    GenLimit.InfiniteContamination.finiteExpansionCode_encode,
    Equiv.apply_symm_apply]
  rw [hnoiseCoe]
  ext x
  simp only [GenLimit.InfiniteContamination.finiteExpansion, noise,
    GenLimit.InfiniteContamination.displayedNoise, Set.mem_diff,
    Set.mem_union, Set.mem_range, Finset.coe_empty, Set.mem_empty_iff_false,
    not_false_eq_true, and_true]
  constructor
  · intro hx
    by_cases hxK : x ∈ O.language i
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · rintro (hxK | ⟨hx, _⟩)
    · exact hP.1 hxK
    · exact hx

theorem novel_transfer_of_finite_expansion
    {input output : Stream} {K R : Language}
    (hRrange : R = Set.range input)
    (hfinite : (R \ K).Finite)
    (hgen : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hgen
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      (GenLimit.InfiniteContamination.stream_presents_range input)
      hfinite.toFinset (by
        intro x hx
        rw [← hRrange]
        exact ((Set.Finite.mem_toFinset hfinite).mp hx).1)
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have hgenerate := hTgenerate t ((Nat.le_max_left _ _).trans ht)
  have hseenGeneric :
      hfinite.toFinset ⊆ GenLimit.Generic.sample input t := by
    intro x hx
    exact GenLimit.Generic.sample_mono
      ((Nat.le_max_right _ _).trans ht) (hTseen hx)
  have hseen : hfinite.toFinset ⊆ GenLimit.sample input t := by
    simpa [GenLimit.Generic.sample, GenLimit.sample] using hseenGeneric
  refine ⟨?_, hgenerate.2.1, hgenerate.2.2⟩
  by_contra hxK
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hgenerate.1, hxK⟩
  exact hgenerate.2.1
    (GenLimit.sample_mono (Nat.le_succ t) (hseen hbad))

theorem prefixCount_le_ncard_of_finite
    {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  exact (Set.Finite.mem_toFinset hF).mpr
    (GenLimit.PatientScope.mem_prefixFinset.mp hx).2

theorem prefixCount_le_add_ncard_diff
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
    simpa [diffPrefix, GenLimit.PatientScope.prefixCount] using
      prefixCount_le_ncard_of_finite hfinite n
  simpa [aPrefix, bPrefix, diffPrefix,
    GenLimit.PatientScope.prefixCount] using
      hcard.trans (Nat.add_le_add_left hdiff _)

theorem relativeLowerDensity_mono_of_finite_expansion
    {Q K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let count := GenLimit.PatientScope.prefixCount
  let c : ℝ := hfinite.toFinset.card
  let ratioR : ℕ → ℝ := fun n => (count (Q ∩ R) n : ℝ) / count R n
  let ratioK : ℕ → ℝ := fun n => (count (Q ∩ K) n : ℝ) / count K n
  let err : ℕ → ℝ := fun n => c / count K n
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcastK : Tendsto (fun n => (count K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herr : Tendsto err atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcastK
  have hnegerr : Tendsto (fun n => -err n) atTop (𝓝 0) := by
    simpa using herr.neg
  have hcompare : ∀ᶠ n : ℕ in atTop, ratioR n - err n ≤ ratioK n := by
    have hposK : ∀ᶠ n : ℕ in atTop, 0 < count K n :=
      (hcountK.eventually_gt_atTop 0)
    filter_upwards [hposK] with n hnK
    have hnR : 0 < count R n :=
      lt_of_lt_of_le hnK (GenLimit.PatientScope.prefixCount_mono hKR n)
    have hdiffSets : ((Q ∩ R) \ (Q ∩ K)).Finite := by
      apply hfinite.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hnumNat' := prefixCount_le_add_ncard_diff hdiffSets n
    have hcard : hdiffSets.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := (Set.Finite.mem_toFinset hdiffSets).mp hx
      exact (Set.Finite.mem_toFinset hfinite).mpr
        ⟨hx'.1.2, fun hxK => hx'.2 ⟨hx'.1.1, hxK⟩⟩
    have hnumNat :
        count (Q ∩ R) n ≤ count (Q ∩ K) n + hfinite.toFinset.card :=
      hnumNat'.trans (Nat.add_le_add_left hcard _)
    have hnum : (count (Q ∩ R) n : ℝ) ≤ count (Q ∩ K) n + c := by
      change (count (Q ∩ R) n : ℝ) ≤
        (count (Q ∩ K) n : ℝ) + (hfinite.toFinset.card : ℝ)
      exact_mod_cast hnumNat
    have hden : (count K n : ℝ) ≤ count R n := by
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hKR n
    have hmain :
        (count (Q ∩ R) n : ℝ) / count R n ≤
          ((count (Q ∩ K) n : ℝ) + c) / count K n := by
      rw [div_le_div_iff₀ (by exact_mod_cast hnR) (by exact_mod_cast hnK)]
      nlinarith [show (0 : ℝ) ≤ count (Q ∩ K) n by positivity,
        show (0 : ℝ) ≤ c by positivity]
    simpa [ratioR, ratioK, err, sub_le_iff_le_add, add_div] using hmain
  have ratio_nonneg : ∀ S T n,
      (0 : ℝ) ≤ (count (S ∩ T) n : ℝ) / count T n := by
    intro S T n
    positivity
  have ratio_le_one : ∀ S T n,
      (count (S ∩ T) n : ℝ) / count T n ≤ 1 := by
    intro S T n
    by_cases hn : count T n = 0
    · have hnum : count (S ∩ T) n = 0 :=
        Nat.eq_zero_of_le_zero
          ((GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n).trans_eq hn)
      simp [hn, hnum]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  have hRatioRLower :
      IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop ratioR :=
    isBoundedUnder_of ⟨0, fun n => ratio_nonneg Q R n⟩
  have hRatioRUpper :
      IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≤ x₂) atTop ratioR :=
    isBoundedUnder_of ⟨1, fun n => ratio_le_one Q R n⟩
  have hNegLower :
      IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop
        (fun n => -err n) := hnegerr.isBoundedUnder_ge
  have hNegCobounded :
      IsCoboundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop
        (fun n => -err n) := hnegerr.isCoboundedUnder_ge
  have hlimCompare :
      liminf (fun n => ratioR n + (-err n)) atTop ≤
        liminf ratioK atTop :=
    liminf_le_liminf
      (hcompare.mono fun n hn => by simpa [sub_eq_add_neg] using hn)
      (isBoundedUnder_ge_add hRatioRLower hNegLower)
      (isCoboundedUnder_ge_of_le atTop (fun n => ratio_le_one Q K n))
  have hlimAdd :
      liminf ratioR atTop + liminf (fun n => -err n) atTop ≤
        liminf (fun n => ratioR n + (-err n)) atTop := by
    exact le_liminf_add hRatioRLower hRatioRUpper hNegLower hNegCobounded
  have hzero : liminf (fun n => -err n) atTop = 0 := hnegerr.liminf_eq
  rw [hzero, add_zero] at hlimAdd
  simpa [GenLimit.PatientScope.relativeLowerDensity,
    ratioR, ratioK, count] using hlimAdd.trans hlimCompare

end Stage3Case025Proof

open Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  intro family hInfinite
  let O := Stage3Case025Proof.oracleOfFamily family hInfinite
  let expanded := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ :=
    Stage3Case025Proof.positive_engine expanded.language expanded.infinite'
  refine ⟨gen, ?_⟩
  intro i input hP
  have hP' :
      CompleteFiniteOccurrencePresentation input (O.language i) := by
    simpa [O, Stage3Case025Proof.oracleOfFamily] using hP
  obtain ⟨j, hj⟩ :=
    Stage3Case025Proof.exists_expansion_index_for_complete O hP'
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hj
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply Stage3Case025Proof.novel_transfer_of_finite_expansion
      (K := family i) (R := Set.range input)
    · rfl
    · exact GenLimit.InfiniteContamination.displayedNoise_finite hP.2
    · rw [← hj] at hnovel
      exact hnovel
  · have hfinite : (Set.range input \ family i).Finite :=
      GenLimit.InfiniteContamination.displayedNoise_finite hP.2
    have htransfer :=
      Stage3Case025Proof.relativeLowerDensity_mono_of_finite_expansion
        (Q := GenLimit.GeneratorFirst input output)
        (K := family i) (R := Set.range input)
        (hInfinite i) hP.1 hfinite
    have hdensity' :
        (1 / 2 : ℝ) ≤
          GenLimit.PatientScope.relativeLowerDensity
            (GenLimit.GeneratorFirst input output ∩ Set.range input)
            (Set.range input) := by
      rw [← hj] at hdensity
      exact hdensity
    exact hdensity'.trans htransfer
