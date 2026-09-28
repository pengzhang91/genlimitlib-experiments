import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Logic.Equiv.Finset

open Set Filter
open scoped Topology

namespace Stage3Case025

namespace Causality

open GenLimit GenLimit.PatientMachine

lemma sample_congr {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    sample a t = sample b t := by
  ext x
  simp only [mem_sample_iff]
  constructor
  · rintro ⟨s, hs, ha⟩
    exact ⟨s, hs, (h s hs).symm.trans ha⟩
  · rintro ⟨s, hs, hb⟩
    exact ⟨s, hs, (h s hs).trans hb⟩

lemma consistent_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    Consistent C a t i ↔ Consistent C b t i := by
  simp only [Consistent, sample_congr h]

lemma recursiveCritical_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa only [RecursiveCritical] using consistent_congr C h
    | succ i =>
      simp only [RecursiveCritical, consistent_congr C h]
      constructor
      · rintro ⟨hi, hall⟩
        refine ⟨hi, ?_⟩
        intro j hj hjb
        exact hall j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjb)
      · rintro ⟨hi, hall⟩
        refine ⟨hi, ?_⟩
        intro j hj hja
        exact hall j hj ((ih j (Nat.lt_succ_of_le hj)).1 hja)

lemma criticalIndices_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    criticalIndices C a t scope = criticalIndices C b t scope := by
  ext i
  simp only [mem_criticalIndices, recursiveCritical_congr C h]

lemma consistentIndices_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    consistentIndices C a t scope = consistentIndices C b t scope := by
  ext i
  simp only [mem_consistentIndices, consistent_congr C h]

lemma survivingCriticalIndices_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s) :
    survivingCriticalIndices C a t scope = survivingCriticalIndices C b t scope := by
  ext i
  simp only [mem_survivingCriticalIndices]
  rw [recursiveCritical_congr C (fun s hs => h s (lt_trans hs (Nat.lt_succ_self t)))]
  rw [recursiveCritical_congr C h]

lemma highestCritical_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    highestCritical C a t scope fallback = highestCritical C b t scope fallback := by
  classical
  unfold highestCritical
  rw [criticalIndices_congr C h]

lemma highestSurvivor_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s) :
    highestSurvivor C a t scope fallback = highestSurvivor C b t scope fallback := by
  classical
  unfold highestSurvivor
  rw [survivingCriticalIndices_congr C h]

lemma lowestConsistentInScope_congr (C : LanguageFamily)
    {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    lowestConsistentInScope C a t scope fallback =
      lowestConsistentInScope C b t scope fallback := by
  classical
  unfold lowestConsistentInScope
  rw [consistentIndices_congr C h]

lemma lowestConsistent_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    lowestConsistent C a t fallback = lowestConsistent C b t fallback := by
  classical
  have hc : ∀ i, Consistent C a t i ↔ Consistent C b t i :=
    fun i => consistent_congr C h
  unfold lowestConsistent
  by_cases ha : ∃ i, Consistent C a t i
  · have hb : ∃ i, Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (hc i).1 hi⟩
    rw [dif_pos ha, dif_pos hb]
    apply Nat.find_congr (Nat.find_spec ha)
    intro i hi
    exact hc i
  · have hb : ¬ ∃ i, Consistent C b t i := by
      intro hb
      obtain ⟨i, hi⟩ := hb
      exact ha ⟨i, (hc i).2 hi⟩
    rw [dif_neg ha, dif_neg hb]

lemma decide_congr (C : LanguageFamily) {a b : ℕ → ℕ} {t : ℕ} (old : State)
    (h : ∀ s, s < t + 1 → a s = b s) :
    decide C a t old = decide C b t old := by
  classical
  have h0 : ∀ s, s < t → a s = b s :=
    fun s hs => h s (lt_trans hs (Nat.lt_succ_self t))
  unfold PatientMachine.decide stableDecision backtrackDecision
  simp only [consistent_congr C h,
    consistentIndices_congr C h,
    survivingCriticalIndices_congr C h,
    highestCritical_congr C h,
    highestSurvivor_congr C h,
    lowestConsistentInScope_congr C h,
    lowestConsistent_congr C h]

lemma leastAvailable_congr (C : LanguageFamily) (hInf : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ s, s < t → a s = b s) :
    leastAvailable C hInf a t used focus = leastAvailable C hInf b t used focus := by
  classical
  unfold leastAvailable
  apply Nat.find_congr (Nat.find_spec (available_exists C hInf a t used focus))
  intro x hx
  simp only [Available, sample_congr h]

lemma processRound_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ} (old : State)
    (h : ∀ s, s < t + 1 → a s = b s) :
    processRound O a t old = processRound O b t old := by
  classical
  have hd := decide_congr O.language old h
  have hx := leastAvailable_congr O.language O.infinite' old.used
    (PatientMachine.decide O.language b t old).focus h
  simp only [processRound, hd, hx]

lemma run_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    run O a t = run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ]
      rw [ih (fun s hs => h s (lt_trans hs (Nat.lt_succ_self t)))]
      exact processRound_congr O (run O b t) h

lemma output_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s) :
    output O a t = output O b t := by
  unfold output
  rw [run_congr O h]

end Causality

end Stage3Case025


namespace Stage3Case025

open Set Filter
open scoped Topology

lemma relativeLowerDensity_mono_finite_extension
    {A K E : Set ℕ} (hKE : K ⊆ E) (hfinite : (E \ K).Finite)
    (hK : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let c : ℕ := (E \ K).ncard
  let u : ℕ → ℝ := fun n => (c : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)
  let v : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hNK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hNKreal : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNK
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa [u] using (tendsto_const_nhds.div_atTop hNKreal)
  have hv_nonneg : ∀ n, 0 ≤ v n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hv_le_one : ∀ n, v n ≤ 1 := by
    intro n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [v, hz]
    · change (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (show A ∩ K ⊆ K from Set.inter_subset_right) n
  have hu_nonneg : ∀ n, 0 ≤ u n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hu_le : ∀ n, u n ≤ (c : ℝ) := by
    intro n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [u, hz]
    · have hden : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      change (c : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ c
      rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)]
      nlinarith [show (0 : ℝ) ≤ c by positivity]
  have hcompare : ∀ᶠ n : ℕ in atTop,
      (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          (GenLimit.PatientScope.prefixCount E n : ℝ) ≤ u n + v n := by
    filter_upwards [hNK.eventually (eventually_gt_atTop 0)] with n hn
    have hKpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hEpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn
        (GenLimit.PatientScope.prefixCount_mono hKE n)
    have hnum : GenLimit.PatientScope.prefixCount (A ∩ E) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + c := by
      classical
      let source := GenLimit.PatientScope.prefixFinset (A ∩ E) n
      let target := GenLimit.PatientScope.prefixFinset (A ∩ K) n
      let extra := source \ target
      change source.card ≤ target.card + c
      have hsplit : source.card ≤ target.card + extra.card := by
        have hsub : source ⊆ target ∪ extra := by
          intro x hx
          by_cases hxK : x ∈ K
          · apply Finset.mem_union_left
            apply GenLimit.PatientScope.mem_prefixFinset.mpr
            have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
            exact ⟨hx'.1, hx'.2.1, hxK⟩
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, by
              intro hxtarget
              exact hxK (GenLimit.PatientScope.mem_prefixFinset.mp hxtarget).2.2⟩)
        exact (Finset.card_le_card hsub).trans (Finset.card_union_le target extra)
      have hextra : extra.card ≤ c := by
        have hsubset : (extra : Set ℕ) ⊆ E \ K := by
          intro x hx
          have hx' := Finset.mem_sdiff.mp hx
          have hxsource := GenLimit.PatientScope.mem_prefixFinset.mp hx'.1
          refine ⟨hxsource.2.2, ?_⟩
          intro hxK
          exact hx'.2 (GenLimit.PatientScope.mem_prefixFinset.mpr
            ⟨hxsource.1, hxsource.2.1, hxK⟩)
        simpa [c] using Set.ncard_le_ncard hsubset hfinite
      exact hsplit.trans (Nat.add_le_add_left hextra _)
    have hden := GenLimit.PatientScope.prefixCount_mono hKE n
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          (GenLimit.PatientScope.prefixCount E n : ℝ)
          ≤ (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
              gcongr
      _ ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n + c : ℕ) : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
              gcongr
      _ = u n + v n := by
              simp [u, v, add_div, add_comm]
  have hleft_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
        (GenLimit.PatientScope.prefixCount E n : ℝ)) :=
    isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩
  have hright_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop (u + v) :=
    isBoundedUnder_of ⟨(c : ℝ) + 1, fun n => by
      change u n + v n ≤ _
      exact add_le_add (hu_le n) (hv_le_one n)⟩
  have hliminf_compare :
      liminf (fun n => (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
        (GenLimit.PatientScope.prefixCount E n : ℝ)) atTop ≤ liminf (u + v) atTop :=
    liminf_le_liminf hcompare hleft_below hright_above.isCoboundedUnder_ge
  have hliminf_add : liminf (u + v) atTop ≤ liminf v atTop := by
    calc
      liminf (u + v) atTop ≤ limsup u atTop + liminf v atTop :=
        liminf_add_le
          (isBoundedUnder_of ⟨0, hu_nonneg⟩)
          (isBoundedUnder_of ⟨(c : ℝ), hu_le⟩)
          (isBoundedUnder_of ⟨0, hv_nonneg⟩)
          (isCoboundedUnder_ge_of_le atTop hv_le_one)
      _ = liminf v atTop := by rw [hu.limsup_eq]; simp
  exact hliminf_compare.trans hliminf_add

end Stage3Case025
