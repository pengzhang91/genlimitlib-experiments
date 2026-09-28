import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.Pairing

open Filter
open scoped Topology

namespace Stage3Case025

private def codedFinset (n : ℕ) : Finset ℕ :=
  n.bitIndices.toFinset

private noncomputable def finiteExtensionOracle
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language n := family n.unpair.1 ∪ (codedFinset n.unpair.2 : Set ℕ)
  infinite' n := (hInfinite n.unpair.1).mono Set.subset_union_left
  query n x := by
    classical
    exact decide (x ∈ family n.unpair.1 ∪ (codedFinset n.unpair.2 : Set ℕ))
  query_spec n x := by
    classical
    simp

private theorem sample_eq_of_eq_below
    {a b : Stream} {t : ℕ} (h : ∀ s, s < t → a s = b s) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, (h s hs).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, h s hs⟩

private theorem consistent_iff_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_eq_of_eq_below h]

private theorem recursiveCritical_iff_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [GenLimit.RecursiveCritical] using
            consistent_iff_of_eq_below (C := C) (i := 0) h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_iff_of_eq_below (C := C) (i := i + 1) h]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, fun j hj hjcrit => hcrit j hj ?_⟩
            exact (ih j (Nat.lt_succ_of_le hj)).mpr hjcrit
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, fun j hj hjcrit => hcrit j hj ?_⟩
            exact (ih j (Nat.lt_succ_of_le hj)).mp hjcrit

private theorem stableDecision_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  have hcrit :
      GenLimit.PatientMachine.criticalIndices C a (t + 1) (old.scope + 1) =
        GenLimit.PatientMachine.criticalIndices C b (t + 1) (old.scope + 1) := by
    unfold GenLimit.PatientMachine.criticalIndices
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact and_congr Iff.rfl (recursiveCritical_iff_of_eq_below (C := C) (i := i) h)
  have hhighest :
      GenLimit.PatientMachine.highestCritical C a (t + 1) (old.scope + 1) old.focus =
        GenLimit.PatientMachine.highestCritical C b (t + 1) (old.scope + 1) old.focus := by
    simp only [GenLimit.PatientMachine.highestCritical]
    rw [hcrit]
  unfold GenLimit.PatientMachine.stableDecision
  split
  · simp only [hhighest]
  · rfl

private theorem backtrackDecision_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  have ht : ∀ s, s < t → a s = b s :=
    fun s hs => h s (Nat.lt.step hs)
  have hconsistent :
      GenLimit.PatientMachine.consistentIndices C a (t + 1) old.scope =
        GenLimit.PatientMachine.consistentIndices C b (t + 1) old.scope := by
    unfold GenLimit.PatientMachine.consistentIndices
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact and_congr Iff.rfl (consistent_iff_of_eq_below (C := C) (i := i) h)
  have hsurvivors :
      GenLimit.PatientMachine.survivingCriticalIndices C a t old.scope =
        GenLimit.PatientMachine.survivingCriticalIndices C b t old.scope := by
    unfold GenLimit.PatientMachine.survivingCriticalIndices
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact and_congr Iff.rfl <| and_congr
      (recursiveCritical_iff_of_eq_below (C := C) (i := i) ht)
      (recursiveCritical_iff_of_eq_below (C := C) (i := i) h)
  have hexists :
      (∃ i, GenLimit.Consistent C a (t + 1) i) ↔
        ∃ i, GenLimit.Consistent C b (t + 1) i := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (consistent_iff_of_eq_below (C := C) (i := i) h).mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (consistent_iff_of_eq_below (C := C) (i := i) h).mpr hi⟩
  have hhighest :
      GenLimit.PatientMachine.highestSurvivor C a t old.scope old.focus =
        GenLimit.PatientMachine.highestSurvivor C b t old.scope old.focus := by
    simp only [GenLimit.PatientMachine.highestSurvivor]
    rw [hsurvivors]
  have hlowestScope :
      GenLimit.PatientMachine.lowestConsistentInScope C a (t + 1) old.scope old.focus =
        GenLimit.PatientMachine.lowestConsistentInScope C b (t + 1) old.scope old.focus := by
    simp only [GenLimit.PatientMachine.lowestConsistentInScope]
    rw [hconsistent]
  have hlowest :
      GenLimit.PatientMachine.lowestConsistent C a (t + 1) old.focus =
        GenLimit.PatientMachine.lowestConsistent C b (t + 1) old.focus := by
    unfold GenLimit.PatientMachine.lowestConsistent
    by_cases ha : ∃ i, GenLimit.Consistent C a (t + 1) i
    · have hb := hexists.mp ha
      rw [dif_pos ha, dif_pos hb]
      apply le_antisymm
      · apply Nat.find_min' ha
        exact (consistent_iff_of_eq_below (C := C) (i := Nat.find hb) h).mpr
          (Nat.find_spec hb)
      · apply Nat.find_min' hb
        exact (consistent_iff_of_eq_below (C := C) (i := Nat.find ha) h).mp
          (Nat.find_spec ha)
    · have hb : ¬ ∃ i, GenLimit.Consistent C b (t + 1) i := by
        exact fun hb => ha (hexists.mpr hb)
      rw [dif_neg ha, dif_neg hb]
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [hconsistent, hsurvivors, hhighest, hlowestScope, hlowest,
    propext hexists]

private theorem decision_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  have hfocus := consistent_iff_of_eq_below
    (C := C) (i := old.focus) h
  unfold GenLimit.PatientMachine.decide
  rw [propext hfocus]
  split
  · exact stableDecision_eq_of_eq_below h old
  · exact backtrackDecision_eq_of_eq_below h old

private theorem processRound_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hdecision := decision_eq_of_eq_below
    (C := O.language) h old
  have hsample := sample_eq_of_eq_below h
  have hleast :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a (t + 1)
          old.used (GenLimit.PatientMachine.decide O.language b t old).focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b (t + 1)
          old.used (GenLimit.PatientMachine.decide O.language b t old).focus := by
    unfold GenLimit.PatientMachine.leastAvailable
    congr 1
    funext x
    apply propext
    constructor <;> rintro ⟨x, hx⟩ <;> refine ⟨x, ?_⟩
    · simpa only [GenLimit.PatientMachine.Available, hsample] using hx
    · simpa only [GenLimit.PatientMachine.Available, hsample] using hx
  simp only [GenLimit.PatientMachine.processRound, hdecision, hleast]
private theorem run_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.PatientMachine.run O a t =
      GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun s hs => h s (Nat.lt.step hs))]
      exact processRound_eq_of_eq_below O h _

private theorem output_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_eq_below O h]

private def prefixExtension {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun s => if hs : s < t + 1 then xs ⟨s, hs⟩ else 0

private noncomputable def patientOnlineGenerator
    (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixExtension xs) t

private theorem patientOnlineGenerator_follows
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_eq_of_eq_below O
  intro s hs
  simp [prefixExtension, hs]

private theorem prefixCount_inter_le
    (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∩ B) n ≤
      GenLimit.PatientScope.prefixCount B n :=
  GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n

private theorem ratio_nonneg (A B : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (A ∩ B) n : ℝ) /
      GenLimit.PatientScope.prefixCount B n := by positivity

private theorem ratio_le_one (A B : Set ℕ) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount (A ∩ B) n : ℝ) /
        GenLimit.PatientScope.prefixCount B n ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount B n = 0
  · simp [hzero]
  · rw [div_le_one]
    · exact_mod_cast prefixCount_inter_le A B n
    · exact_mod_cast Nat.pos_of_ne_zero hzero

private theorem relativeLowerDensity_transfer
    {D K E : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (D ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
  let c : ℕ := hfinite.toFinset.card
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) /
      GenLimit.PatientScope.prefixCount E n
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  let error : ℕ → ℝ := fun n =>
    (c : ℝ) / GenLimit.PatientScope.prefixCount K n
  have hcount : ∀ n,
      GenLimit.PatientScope.prefixCount (D ∩ E) n ≤
        GenLimit.PatientScope.prefixCount (D ∩ K) n + c := by
    intro n
    classical
    unfold GenLimit.PatientScope.prefixCount
    let left := (Finset.range n).filter fun x => x ∈ D ∩ E
    let right := (Finset.range n).filter fun x => x ∈ D ∩ K
    let exceptional := (Finset.range n).filter fun x => x ∈ E \ K
    have hsub : left ⊆ right ∪ exceptional := by
      intro x hx
      simp only [left, right, exceptional, Finset.mem_filter,
        Finset.mem_union, Set.mem_inter_iff, Set.mem_diff] at hx ⊢
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨hx.1, hx.2.1, hxK⟩
      · exact Or.inr ⟨hx.1, hx.2.2, hxK⟩
    have hexceptional : exceptional.card ≤ c := by
      apply Finset.card_le_card
      intro x hx
      have hx' := hx
      simp only [exceptional, Finset.mem_filter] at hx'
      exact Set.Finite.mem_toFinset hfinite |>.2 hx'.2
    simpa [left, right, c, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset] using (Finset.card_le_card hsub).trans (
      (Finset.card_union_le right exceptional).trans <|
        Nat.add_le_add_left hexceptional _)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    have hpositive : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hpositive] with n hn
    have hKn : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hEn : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn
        (GenLimit.PatientScope.prefixCount_mono hKE n)
    have hnum :
        (GenLimit.PatientScope.prefixCount (D ∩ E) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n + c := by
      exact_mod_cast hcount n
    calc
      source n ≤
          ((GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) + c) /
            GenLimit.PatientScope.prefixCount E n :=
        (div_le_div_iff_of_pos_right hEn).2 hnum
      _ ≤ ((GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) + c) /
            GenLimit.PatientScope.prefixCount K n := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact_mod_cast hn
        · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hKE n
      _ = target n + error n := by rw [add_div]
  have herror : Tendsto error atTop (nhds 0) := by
    have hdenom : Tendsto
        (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
    exact tendsto_const_nhds.div_atTop hdenom
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (fun n => ratio_le_one D K n))
    (isBoundedUnder_of ⟨0, fun n => ratio_nonneg D K n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, fun n => ratio_nonneg D E n⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpos : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpos)
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hrs herr hp
  linarith

theorem stage3_result : MainClaim := by
  intro family hInfinite
  let O := finiteExtensionOracle family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hPresentation
  let bad : Set ℕ := {x | x ∈ Set.range input ∧ x ∉ family i}
  have hbadFinite : bad.Finite := by
    have hindices := hPresentation.2
    rw [GenLimit.Generic.FinitelyManyViolations] at hindices
    change (Set.range input \ family i).Finite
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hindices.image input
  let badFinset : Finset ℕ := hbadFinite.toFinset
  let code : ℕ := ∑ x ∈ badFinset, 2 ^ x
  have hcode : codedFinset code = badFinset := by
    simpa [codedFinset, code] using
      Finset.toFinset_bitIndices_twoPowSum badFinset
  have hrange : Set.range input = family i ∪ (badFinset : Set ℕ) := by
    ext x
    constructor
    · intro hx
      by_cases hxi : x ∈ family i
      · exact Or.inl hxi
      · exact Or.inr (Set.Finite.mem_toFinset hbadFinite |>.2 ⟨hx, hxi⟩)
    · rintro (hxi | hxbad)
      · exact hPresentation.1 hxi
      · exact (Set.Finite.mem_toFinset hbadFinite |>.1 hxbad).1
  have hP : GenLimit.Presents input (O.language (Nat.pair i code)) := by
    simpa [O, finiteExtensionOracle, hcode] using hrange
  let output := GenLimit.PatientMachine.output O input
  have hmain := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
  refine ⟨output, patientOnlineGenerator_follows O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hmain.1
    obtain ⟨S, hS⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample hP badFinset (by
        intro x hx
        simp [O, finiteExtensionOracle, hcode, hx])
    refine ⟨max T S, ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htS : S ≤ t := le_trans (le_max_right _ _) ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t htT
    have hnotBad : output t ∉ (badFinset : Set ℕ) := by
      intro hbad
      have hseen := hS hbad
      rw [GenLimit.Generic.mem_sample_iff] at hseen
      obtain ⟨s, hs, heq⟩ := hseen
      exact hfresh s (by omega) heq
    have hmem' : output t ∈ family i ∪ (badFinset : Set ℕ) := by
      simpa [O, finiteExtensionOracle, hcode] using hmem
    have htarget : output t ∈ family i := hmem'.resolve_right hnotBad
    have hfreshSample : output t ∉ GenLimit.sample input (t + 1) := by
      intro hsample
      rw [GenLimit.mem_sample_iff] at hsample
      obtain ⟨s, hs, heq⟩ := hsample
      exact hfresh s (by omega) heq
    exact ⟨htarget, hfreshSample, hnovel⟩
  · have hKE : family i ⊆ O.language (Nat.pair i code) := by
      intro x hx
      simp [O, finiteExtensionOracle, hx]
    have hdiffFinite : (O.language (Nat.pair i code) \ family i).Finite := by
      apply hbadFinite.subset
      intro x hx
      have hxRange : x ∈ Set.range input := by rw [hP]; exact hx.1
      exact ⟨hxRange, hx.2⟩
    exact hmain.2.trans <|
      relativeLowerDensity_transfer (D := GenLimit.GeneratorFirst input output)
        (hInfinite i) hKE hdiffFinite

end Stage3Case025

open Stage3Case025

/-- Primary endpoint: the unchanged semantic half-density theorem. -/
theorem stage3_result : Stage3Case025.MainClaim :=
  Stage3Case025.stage3_result
