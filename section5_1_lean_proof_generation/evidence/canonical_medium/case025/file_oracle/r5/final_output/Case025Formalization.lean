import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Set Filter

namespace Stage3Case025Proof

noncomputable def oracleOfFamily
    (family : ℕ → Stage3Case025.Language) (hinfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily := by
  classical
  exact {
    language := family
    infinite' := hinfinite
    query := fun i x => if x ∈ family i then true else false
    query_spec := by intro i x; simp }

def extendHistory (t : ℕ) (history : Fin (t + 1) → ℕ) : Stage3Case025.Stream :=
  fun n => if h : n < t + 1 then history ⟨n, h⟩ else 0

theorem extendHistory_eq (t : ℕ) (history : Fin (t + 1) → ℕ)
    {n : ℕ} (hn : n < t + 1) :
    extendHistory t history n = history ⟨n, hn⟩ := by
  simp [extendHistory, hn]

theorem sample_eq_of_eq_before {a b : Stage3Case025.Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

theorem consistent_iff_of_sample_eq
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream} {t i : ℕ}
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, hs]

theorem recursiveCritical_iff_of_sample_eq
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream} {t : ℕ}
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [GenLimit.RecursiveCritical] using
            consistent_iff_of_sample_eq C hs (i := 0)
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_iff_of_sample_eq C hs).mp hcon, ?_⟩
            intro j hj hjb
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjb)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_iff_of_sample_eq C hs).mpr hcon, ?_⟩
            intro j hj hja
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mp hja)

theorem consistentIndices_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream} {t scope : ℕ}
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  exact and_congr_right fun _ => consistent_iff_of_sample_eq C hs

theorem criticalIndices_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream} {t scope : ℕ}
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  exact and_congr_right fun _ => recursiveCritical_iff_of_sample_eq C hs i

theorem survivingCriticalIndices_eq_of_samples
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream} {t scope : ℕ}
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact recursiveCritical_iff_of_sample_eq C hs0 i
  · exact recursiveCritical_iff_of_sample_eq C hs1 i

theorem highestCritical_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream}
    {t scope fallback : ℕ} (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq_of_sample_eq C hs]

theorem lowestConsistentInScope_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream}
    {t scope fallback : ℕ} (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_sample_eq C hs]

theorem highestSurvivor_eq_of_samples
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream}
    {t scope fallback : ℕ}
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_samples C hs0 hs1]

theorem lowestConsistent_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream}
    {t fallback : ℕ} (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  let pa : ℕ → Prop := GenLimit.Consistent C a t
  let pb : ℕ → Prop := GenLimit.Consistent C b t
  have hp : ∀ i, pa i ↔ pb i := fun i => consistent_iff_of_sample_eq C hs
  by_cases ha : ∃ i, pa i
  · have hb : ∃ i, pb i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (hp i).mp hi⟩
    have hla : GenLimit.PatientMachine.lowestConsistent C a t fallback = Nat.find ha := by
      simp [GenLimit.PatientMachine.lowestConsistent, pa, ha]
    have hlb : GenLimit.PatientMachine.lowestConsistent C b t fallback = Nat.find hb := by
      simp [GenLimit.PatientMachine.lowestConsistent, pb, hb]
    rw [hla, hlb]
    apply Nat.le_antisymm
    · exact Nat.find_min' ha ((hp (Nat.find hb)).mpr (Nat.find_spec hb))
    · exact Nat.find_min' hb ((hp (Nat.find ha)).mp (Nat.find_spec ha))
  · have hb : ¬ ∃ i, pb i := by
      rintro ⟨i, hi⟩
      exact ha ⟨i, (hp i).mpr hi⟩
    simp [GenLimit.PatientMachine.lowestConsistent, pa, pb, ha, hb]

theorem stableDecision_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream}
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (hs : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  simp only [GenLimit.PatientMachine.stableDecision]
  split
  · rw [highestCritical_eq_of_sample_eq C hs]
  · rfl

theorem backtrackDecision_eq_of_samples
    (C : GenLimit.LanguageFamily) {a b : Stage3Case025.Stream}
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  have hci := consistentIndices_eq_of_sample_eq C
    (scope := old.scope) hs1
  have hsurv := survivingCriticalIndices_eq_of_samples C
    (scope := old.scope) hs0 hs1
  have hhigh := highestSurvivor_eq_of_samples C
    (scope := old.scope) (fallback := old.focus) hs0 hs1
  have hlow := lowestConsistentInScope_eq_of_sample_eq C
    (scope := old.scope) (fallback := old.focus) hs1
  have hglobal := lowestConsistent_eq_of_sample_eq C
    (fallback := old.focus) hs1
  have hex : (∃ j, GenLimit.Consistent C a (t + 1) j) ↔
      ∃ j, GenLimit.Consistent C b (t + 1) j := by
    constructor <;> rintro ⟨j, hj⟩
    · exact ⟨j, (consistent_iff_of_sample_eq C hs1).mp hj⟩
    · exact ⟨j, (consistent_iff_of_sample_eq C hs1).mpr hj⟩
  by_cases ha : ∃ j, GenLimit.Consistent C a (t + 1) j
  · have hb := hex.mp ha
    simp only [GenLimit.PatientMachine.backtrackDecision]
    rw [hci, hsurv, hhigh, hlow, hglobal]
    simp [ha, hb]
  · have hb : ¬ ∃ j, GenLimit.Consistent C b (t + 1) j :=
      fun h => ha (hex.mpr h)
    simp only [GenLimit.PatientMachine.backtrackDecision]
    rw [hci, hsurv, hhigh, hlow, hglobal]
    simp [ha, hb]

theorem decide_eq_of_samples
    (O : GenLimit.OracleFamily) {a b : Stage3Case025.Stream}
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.decide O.language a t old =
      GenLimit.PatientMachine.decide O.language b t old := by
  unfold GenLimit.PatientMachine.decide
  have hc : GenLimit.Consistent O.language a (t + 1) old.focus ↔
      GenLimit.Consistent O.language b (t + 1) old.focus :=
    consistent_iff_of_sample_eq O.language hs1
  by_cases ha : GenLimit.Consistent O.language a (t + 1) old.focus
  · have hb := hc.mp ha
    simp [ha, hb, stableDecision_eq_of_sample_eq O.language t old hs1]
  · have hb : ¬ GenLimit.Consistent O.language b (t + 1) old.focus :=
      fun h => ha (hc.mpr h)
    simp [ha, hb, backtrackDecision_eq_of_samples O.language t old hs0 hs1]

theorem leastAvailable_eq_of_sample_eq
    (O : GenLimit.OracleFamily) {a b : Stage3Case025.Stream}
    (t : ℕ) (used : Finset ℕ) (focus : ℕ)
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  apply Nat.le_antisymm
  · apply GenLimit.PatientMachine.leastAvailable_minimal
    have hb := GenLimit.PatientMachine.leastAvailable_spec
      O.language O.infinite' b t used focus
    exact ⟨hb.1, by simpa only [hs] using hb.2.1, hb.2.2⟩
  · apply GenLimit.PatientMachine.leastAvailable_minimal
    have ha := GenLimit.PatientMachine.leastAvailable_spec
      O.language O.infinite' a t used focus
    exact ⟨ha.1, by simpa only [hs] using ha.2.1, ha.2.2⟩

theorem processRound_eq_of_samples
    (O : GenLimit.OracleFamily) {a b : Stage3Case025.Stream}
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  have hd := decide_eq_of_samples O t old hs0 hs1
  simp only [GenLimit.PatientMachine.processRound]
  rw [hd, leastAvailable_eq_of_sample_eq O (t + 1) old.used
    (GenLimit.PatientMachine.decide O.language b t old).focus hs1]

theorem run_eq_of_eq_before
    (O : GenLimit.OracleFamily) {a b : Stage3Case025.Stream} :
    ∀ t, (∀ n, n < t → a n = b n) →
      GenLimit.PatientMachine.run O a t =
        GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      have hprev : ∀ n, n < t → a n = b n :=
        fun n hn => h n (Nat.lt.step hn)
      have hr := ih hprev
      have hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
        sample_eq_of_eq_before h
      have hs0 : GenLimit.sample a t = GenLimit.sample b t :=
        sample_eq_of_eq_before hprev
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, hr]
      exact processRound_eq_of_samples O t
        (GenLimit.PatientMachine.run O b t) hs0 hs1

theorem output_eq_of_eq_before
    (O : GenLimit.OracleFamily) {a b : Stage3Case025.Stream} (t : ℕ)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  simp only [GenLimit.PatientMachine.output]
  rw [run_eq_of_eq_before O (t + 1) h]

noncomputable def onlinePatient (O : GenLimit.OracleFamily) :
    Stage3Case025.OnlineGenerator :=
  fun t input _ =>
    GenLimit.PatientMachine.output O (extendHistory t input) t

theorem follows_onlinePatient (O : GenLimit.OracleFamily)
    (input : Stage3Case025.Stream) :
    Stage3Case025.Follows (onlinePatient O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_eq_of_eq_before O t
  intro n hn
  exact (extendHistory_eq t (fun i => input i) hn).symm

theorem positiveEngine : Stage3Case025.PositivePresentationHalfDensity := by
  intro family hinfinite
  let O := oracleOfFamily family hinfinite
  refine ⟨onlinePatient O, ?_⟩
  intro i input hpresents
  refine ⟨GenLimit.PatientMachine.output O input,
    follows_onlinePatient O input, ?_⟩
  have hmain :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input (z := i) hpresents
  constructor
  · obtain ⟨T, hT⟩ := hmain.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨hmem, ?_, hnovel⟩
    rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hst, heq⟩
    exact hfresh s (Nat.le_of_lt_succ hst) heq
  · simpa [GenLimit.PatientMachine.patientLowerDensity] using hmain.2


noncomputable def finiteAdditionFamily
    (family : ℕ → Stage3Case025.Language) (n : ℕ) : Stage3Case025.Language :=
  let code := Nat.unpair n
  family code.1 ∪ (Finset.equivBitIndices code.2 : Set ℕ)

theorem finiteAdditionFamily_infinite
    (family : ℕ → Stage3Case025.Language)
    (hinfinite : ∀ i, (family i).Infinite) (n : ℕ) :
    (finiteAdditionFamily family n).Infinite := by
  exact (hinfinite (Nat.unpair n).1).mono Set.subset_union_left

theorem range_diff_finite_of_finitelyManyViolations
    {input : Stage3Case025.Stream} {K : Stage3Case025.Language}
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  apply (hbad.image input).subset
  rintro x ⟨⟨t, rfl⟩, htK⟩
  exact ⟨t, htK, rfl⟩

theorem prefixCount_le_add_ncard_of_diff_subset
    {A B F : Set ℕ} (hfinite : F.Finite) (hsubDiff : A \ B ⊆ F) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  let aPrefix := (Finset.range n).filter fun x => x ∈ A
  let bPrefix := (Finset.range n).filter fun x => x ∈ B
  let dPrefix := (Finset.range n).filter fun x => x ∈ A \ B
  have hsub : aPrefix ⊆ bPrefix ∪ dPrefix := by
    intro x hx
    simp only [aPrefix, bPrefix, dPrefix, Finset.mem_filter,
      Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hcard : aPrefix.card ≤ bPrefix.card + dPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : dPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [dPrefix, Finset.mem_filter] at hx
    exact Set.Finite.mem_toFinset hfinite |>.2 (hsubDiff hx.2)
  simpa [aPrefix, bPrefix, dPrefix] using
    hcard.trans (Nat.add_le_add_left hdiff _)

theorem half_relativeLowerDensity_of_finite_extension
    {A K R : Set ℕ} (hKR : K ⊆ R) (hfinite : (R \ K).Finite)
    (hK : K.Infinite)
    (hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ R) R) :
    (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let expandedRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let targetRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have htarget_nonneg : ∀ n, 0 ≤ targetRatio n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htarget_le_one : ∀ n, targetRatio n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [targetRatio, hn]
    · simp only [targetRatio]
      rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (Set.inter_subset_right) n
  have htarget_below : IsBoundedUnder (fun x y : ℝ => x ≥ y)
      atTop targetRatio :=
    isBoundedUnder_of ⟨0, htarget_nonneg⟩
  have htarget_above : IsCoboundedUnder (fun x y : ℝ => x ≥ y)
      atTop targetRatio :=
    isCoboundedUnder_ge_of_le atTop htarget_le_one
  have hexpanded_below : IsBoundedUnder (fun x y : ℝ => x ≥ y)
      atTop expandedRatio := by
    apply isBoundedUnder_of
    refine ⟨0, ?_⟩
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcountReal : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcountReal
  have hcompare : ∀ᶠ n in atTop,
      expandedRatio n ≤ targetRatio n + error n := by
    have hpositive : ∀ᶠ n in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hKRcount := GenLimit.PatientScope.prefixCount_mono hKR n
    have hnumNat := prefixCount_le_add_ncard_of_diff_subset
      (A := A ∩ R) (B := A ∩ K) hfinite (by
        rintro x ⟨⟨hxA, hxR⟩, hxnot⟩
        exact ⟨hxR, fun hxK => hxnot ⟨hxA, hxK⟩⟩) n
    have hKRreal :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount R n := by exact_mod_cast hKRcount
    have hnumReal :
        (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (A ∩ K) n +
            hfinite.toFinset.card := by exact_mod_cast hnumNat
    have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hrpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n :=
      hkpos.trans_le hKRreal
    dsimp [expandedRatio, targetRatio, error]
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
          GenLimit.PatientScope.prefixCount R n
          ≤ (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
              GenLimit.PatientScope.prefixCount K n := by
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hkpos hKRreal
      _ ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) +
              (hfinite.toFinset.card : ℝ)) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            apply div_le_div_of_nonneg_right hnumReal hkpos.le
      _ = (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
              GenLimit.PatientScope.prefixCount K n +
            (hfinite.toFinset.card : ℝ) /
              GenLimit.PatientScope.prefixCount K n := by
            exact add_div _ _ _
  change (1 / 2 : ℝ) ≤ liminf targetRatio atTop
  rw [le_liminf_iff htarget_above htarget_below]
  intro y hy
  let midpoint : ℝ := (y + (1 / 2 : ℝ)) / 2
  have hymid : y < midpoint := by dsimp [midpoint]; linarith
  have hmidhalf : midpoint < (1 / 2 : ℝ) := by dsimp [midpoint]; linarith
  have hmidlim : midpoint < liminf expandedRatio atTop := by
    exact hmidhalf.trans_le hhalf
  have hlarge := eventually_lt_of_lt_liminf hmidlim hexpanded_below
  have hsmall : ∀ᶠ n in atTop, error n < midpoint - y := by
    have hpos : 0 < midpoint - y := sub_pos.mpr hymid
    exact (tendsto_order.1 herror).2 _ hpos
  filter_upwards [hlarge, hsmall, hcompare] with n hnlarge hnsmall hncompare
  linarith


theorem exists_finiteAddition_index
    (family : ℕ → Stage3Case025.Language) (i : ℕ)
    (input : Stage3Case025.Stream)
    (hcomplete : Stage3Case025.CompleteFiniteOccurrencePresentation
      input (family i)) :
    ∃ j, GenLimit.Presents input (finiteAdditionFamily family j) := by
  have hdiff : (Set.range input \ family i).Finite :=
    range_diff_finite_of_finitelyManyViolations hcomplete.2
  let exceptional : Finset ℕ := hdiff.toFinset
  let j := Nat.pair i (Finset.equivBitIndices.symm exceptional)
  refine ⟨j, ?_⟩
  change Set.range input = finiteAdditionFamily family j
  have hexceptional : (exceptional : Set ℕ) = Set.range input \ family i := by
    exact Set.Finite.coe_toFinset hdiff
  rw [finiteAdditionFamily]
  simp only [j, Nat.unpair_pair, Equiv.apply_symm_apply]
  rw [hexceptional]
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ family i
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · rintro (hxK | hxBad)
    · exact hcomplete.1 hxK
    · exact hxBad.1

theorem novelGeneratesInLimit_of_finite_extension
    {input output : Stage3Case025.Stream} {K R : Set ℕ}
    (hKR : K ⊆ R) (hfinite : (R \ K).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  obtain ⟨T, hT⟩ := hnovel
  let stableTimes : Set ℕ := {t | T ≤ t}
  let badTimes : Set ℕ := stableTimes ∩ output ⁻¹' (R \ K)
  have hinj : Set.InjOn output stableTimes := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hablt | hbalt
    · exact (hT b hb).2.2 a hablt hab
    · exact (hT a ha).2.2 b hbalt hab.symm
  have hbadImage : (output '' badTimes).Finite := by
    apply hfinite.subset
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  have hbadFinite : badTimes.Finite := by
    apply hbadImage.of_finite_image
    exact hinj.mono (Set.inter_subset_left)
  have heventually : ∀ᶠ t in atTop, t ∉ badTimes :=
    atTop_le_cofinite hbadFinite.eventually_cofinite_notMem
  obtain ⟨T', hT'⟩ := eventually_atTop.1 heventually
  refine ⟨max T T', ?_⟩
  intro t ht
  have htT : T ≤ t := (le_max_left T T').trans ht
  have htT' : T' ≤ t := (le_max_right T T').trans ht
  obtain ⟨htR, hfresh, hunique⟩ := hT t htT
  refine ⟨?_, hfresh, hunique⟩
  by_contra htK
  exact hT' t htT' ⟨htT, htR, htK⟩

theorem finiteNoiseTransfer : Stage3Case025.FiniteNoiseTransferPrinciple := by
  intro positive
  intro family hinfinite
  let expandedFamily : ℕ → Stage3Case025.Language := finiteAdditionFamily family
  have hexpandedInfinite : ∀ j, (expandedFamily j).Infinite :=
    finiteAdditionFamily_infinite family hinfinite
  obtain ⟨gen, hgen⟩ := positive expandedFamily hexpandedInfinite
  refine ⟨gen, ?_⟩
  intro i input hcomplete
  obtain ⟨j, hpresents⟩ :=
    exists_finiteAddition_index family i input hcomplete
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  have hrange : Set.range input = expandedFamily j := hpresents
  rw [← hrange] at hnovel hdensity
  have hKR : family i ⊆ Set.range input := hcomplete.1
  have hfinite : (Set.range input \ family i).Finite :=
    range_diff_finite_of_finitelyManyViolations hcomplete.2
  refine ⟨output, hfollows,
    novelGeneratesInLimit_of_finite_extension hKR hfinite ?_, ?_⟩
  · exact hnovel
  · apply half_relativeLowerDensity_of_finite_extension
      (A := GenLimit.GeneratorFirst input output)
      hKR hfinite (hinfinite i)
    exact hdensity

end Stage3Case025Proof

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025Proof.finiteNoiseTransfer
    Stage3Case025Proof.positiveEngine
