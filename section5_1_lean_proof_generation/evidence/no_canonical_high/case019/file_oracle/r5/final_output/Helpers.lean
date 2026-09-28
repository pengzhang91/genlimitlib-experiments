import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Filter
open scoped Topology

namespace Stage3Case019
namespace PatientCausal

open GenLimit
open PatientMachine

theorem sample_congr {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) : sample a t = sample b t := by
  ext x
  simp only [mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem consistent_congr {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    Consistent C a t i ↔ Consistent C b t i := by
  rw [Consistent, Consistent, sample_congr h]

theorem recursiveCritical_congr {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    RecursiveCritical C a t i ↔ RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [RecursiveCritical] using consistent_congr (C := C) (i := 0) h
      | succ i =>
          simp only [RecursiveCritical]
          constructor
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_congr h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hprev j hj ((ih j (by omega)).mpr hjcrit)
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_congr h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hprev j hj ((ih j (by omega)).mp hjcrit)

theorem consistentIndices_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t → a n = b n) :
    consistentIndices C a t scope = consistentIndices C b t scope := by
  unfold consistentIndices
  congr 1
  funext i
  exact propext (consistent_congr h)

theorem criticalIndices_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t → a n = b n) :
    criticalIndices C a t scope = criticalIndices C b t scope := by
  unfold criticalIndices
  congr 1
  funext i
  exact propext (recursiveCritical_congr h)

theorem survivingCriticalIndices_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t + 1 → a n = b n) :
    survivingCriticalIndices C a t scope = survivingCriticalIndices C b t scope := by
  unfold survivingCriticalIndices
  congr 1
  funext i
  apply propext
  constructor <;> rintro ⟨h₁, h₂⟩
  · exact ⟨(recursiveCritical_congr (fun n hn => h n (Nat.lt.step hn))).mp h₁,
      (recursiveCritical_congr h).mp h₂⟩
  · exact ⟨(recursiveCritical_congr (fun n hn => h n (Nat.lt.step hn))).mpr h₁,
      (recursiveCritical_congr h).mpr h₂⟩

theorem highestCritical_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ n, n < t → a n = b n) :
    highestCritical C a t scope fallback = highestCritical C b t scope fallback := by
  simp only [highestCritical]
  rw [criticalIndices_congr C h]

theorem highestSurvivor_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ n, n < t + 1 → a n = b n) :
    highestSurvivor C a t scope fallback = highestSurvivor C b t scope fallback := by
  simp only [highestSurvivor]
  rw [survivingCriticalIndices_congr C h]

theorem lowestConsistentInScope_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ n, n < t → a n = b n) :
    lowestConsistentInScope C a t scope fallback = lowestConsistentInScope C b t scope fallback := by
  simp only [lowestConsistentInScope]
  rw [consistentIndices_congr C h]

theorem lowestConsistent_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t fallback : ℕ} (h : ∀ n, n < t → a n = b n) :
    lowestConsistent C a t fallback = lowestConsistent C b t fallback := by
  classical
  simp only [lowestConsistent]
  by_cases ha : ∃ i, Consistent C a t i
  · have hb : ∃ i, Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_congr h).mp hi⟩
    rw [dif_pos ha, dif_pos hb]
    apply Nat.find_congr (Classical.choose_spec ha)
    intro n _hn
    exact consistent_congr h
  · have hb : ¬∃ i, Consistent C b t i := by
      rintro ⟨i, hi⟩
      exact ha ⟨i, (consistent_congr h).mpr hi⟩
    rw [dif_neg ha, dif_neg hb]

theorem stableDecision_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t : ℕ} (h : ∀ n, n < t + 1 → a n = b n) (old : State) :
    stableDecision C a t old = stableDecision C b t old := by
  simp only [stableDecision]
  split
  · rw [highestCritical_congr C h]
  · rfl

theorem backtrackDecision_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t : ℕ} (h : ∀ n, n < t + 1 → a n = b n) (old : State) :
    backtrackDecision C a t old = backtrackDecision C b t old := by
  simp only [backtrackDecision]
  rw [consistentIndices_congr C h]
  split
  · rw [survivingCriticalIndices_congr C h]
    split
    · rw [highestSurvivor_congr C h]
    · rw [lowestConsistentInScope_congr C h]
  · rw [lowestConsistent_congr C h]
    have hp : (∃ j, Consistent C a (t + 1) j) ↔
        ∃ j, Consistent C b (t + 1) j := by
      constructor <;> rintro ⟨j, hj⟩
      · exact ⟨j, (consistent_congr h).mp hj⟩
      · exact ⟨j, (consistent_congr h).mpr hj⟩
    rw [propext hp]

theorem decide_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t : ℕ} (h : ∀ n, n < t + 1 → a n = b n) (old : State) :
    PatientMachine.decide C a t old = PatientMachine.decide C b t old := by
  simp only [PatientMachine.decide]
  rw [propext (consistent_congr h (C := C) (i := old.focus))]
  split
  · exact stableDecision_congr C h old
  · exact backtrackDecision_congr C h old

theorem leastAvailable_congr (C : GenLimit.LanguageFamily)
    (hInfinite : ∀ i, (C i).Infinite) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) (used : Finset ℕ) (focus : ℕ) :
    leastAvailable C hInfinite a t used focus =
      leastAvailable C hInfinite b t used focus := by
  classical
  have hs := sample_congr h
  simp only [leastAvailable]
  let x := Classical.choose (available_exists C hInfinite a t used focus)
  apply Nat.find_congr (x := x) (Classical.choose_spec (available_exists C hInfinite a t used focus))
  intro n _hn
  simp [Available, hs]

theorem processRound_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) (old : State) :
    processRound O a t old = processRound O b t old := by
  simp only [processRound]
  rw [decide_congr O.language h old]
  rw [leastAvailable_congr O.language O.infinite' h]

theorem run_congr (O : OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ n, n < t → a n = b n) → run O a t = run O b t := by
  intro t h
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, run_succ, ih (fun n hn => h n (Nat.lt.step hn))]
      exact processRound_congr O h _

theorem output_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    output O a t = output O b t := by
  simp only [output]
  rw [run_congr O (t + 1) h]

def prefixExtension {n : ℕ} (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if h : k < n then xs ⟨k, h⟩ else 0

noncomputable def generator (O : OracleFamily) : Generic.Generator ℕ :=
  fun n xs => if h : n = 0 then 0 else output O (prefixExtension xs) (n - 1)

theorem output_generator (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (generator O) stream t = output O stream t := by
  unfold Stage3Case019.outputAfterInput Generic.output generator
  rw [dif_neg (Nat.succ_ne_zero t), Nat.succ_sub_one]
  apply output_congr
  intro n hn
  simp [prefixExtension, hn]

end PatientCausal

namespace FiniteDensityTransfer

open GenLimit
open PatientScope

theorem prefixCount_inter_le_add_finite
    {A K E : Set ℕ} (hKE : K ⊆ E) (hfinite : (E \ K).Finite) (n : ℕ) :
    prefixCount (A ∩ E) n ≤
      prefixCount (A ∩ K) n + hfinite.toFinset.card := by
  classical
  unfold prefixCount
  calc
    (prefixFinset (A ∩ E) n).card ≤
        (prefixFinset (A ∩ K) n ∪ hfinite.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := mem_prefixFinset.mp hx
      by_cases hxK : x ∈ K
      · apply Finset.mem_union_left
        exact mem_prefixFinset.mpr ⟨hx'.1, hx'.2.1, hxK⟩
      · apply Finset.mem_union_right
        exact Set.Finite.mem_toFinset hfinite |>.mpr ⟨hx'.2.2, hxK⟩
    _ ≤ (prefixFinset (A ∩ K) n).card + hfinite.toFinset.card :=
      Finset.card_union_le _ _

theorem relativeLowerDensity_inter_mono_finite_expansion
    {A K E : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    relativeLowerDensity (A ∩ E) E ≤
      relativeLowerDensity (A ∩ K) K := by
  let c : ℝ := hfinite.toFinset.card
  let expandedRatio : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ)
  let targetRatio : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n => c / (prefixCount K n : ℝ)
  have hcountK := tendsto_prefixCount_atTop hK
  have hcountKR : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hcountK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcountKR
  have hKpos : ∀ᶠ n in atTop, 0 < prefixCount K n :=
    hcountK.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n in atTop,
      expandedRatio n - error n ≤ targetRatio n := by
    filter_upwards [hKpos] with n hn
    have hnKR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hdenNat : prefixCount K n ≤ prefixCount E n :=
      prefixCount_mono hKE n
    have hdenR : (prefixCount K n : ℝ) ≤ prefixCount E n := by
      exact_mod_cast hdenNat
    have hnumNat := prefixCount_inter_le_add_finite
      (A := A) hKE hfinite n
    have hnumR : (prefixCount (A ∩ E) n : ℝ) ≤
        prefixCount (A ∩ K) n + c := by
      dsimp [c]
      exact_mod_cast hnumNat
    have hEpos : (0 : ℝ) < prefixCount E n := lt_of_lt_of_le hnKR hdenR
    dsimp [expandedRatio, targetRatio, error, c]
    have hfirst :
        (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ) ≤
          (prefixCount (A ∩ E) n : ℝ) / (prefixCount K n : ℝ) := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnKR hdenR
    calc
      (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ) -
          (hfinite.toFinset.card : ℝ) / (prefixCount K n : ℝ)
          ≤ (prefixCount (A ∩ E) n : ℝ) / (prefixCount K n : ℝ) -
              (hfinite.toFinset.card : ℝ) / (prefixCount K n : ℝ) :=
            sub_le_sub_right hfirst _
      _ ≤ (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ) := by
        rw [← sub_div]
        apply (div_le_div_iff_of_pos_right hnKR).2
        dsimp [c] at hnumR
        linarith
  have hexpandedBounds : ∀ n, 0 ≤ expandedRatio n ∧ expandedRatio n ≤ 1 := by
    intro n
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · by_cases hzero : prefixCount E n = 0
      · simp [expandedRatio, hzero]
      · change (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ) ≤ 1
        rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        exact_mod_cast prefixCount_mono (Set.inter_subset_right) n
  have htargetBounds : ∀ n, 0 ≤ targetRatio n ∧ targetRatio n ≤ 1 := by
    intro n
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · by_cases hzero : prefixCount K n = 0
      · simp [targetRatio, hzero]
      · change (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ) ≤ 1
        rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        exact_mod_cast prefixCount_mono (Set.inter_subset_right) n
  have herrorNonneg : ∀ n, 0 ≤ error n := fun n =>
    div_nonneg (by positivity) (Nat.cast_nonneg _)
  have hsumLower :
      liminf expandedRatio atTop + liminf (-error) atTop ≤
        liminf (expandedRatio + (-error)) atTop := by
    apply le_liminf_add
    · exact isBoundedUnder_of_eventually_ge (f := atTop) (u := expandedRatio)
        (Filter.Eventually.of_forall fun n => (hexpandedBounds n).1)
    · exact isBoundedUnder_of_eventually_le (f := atTop) (u := expandedRatio)
        (Filter.Eventually.of_forall fun n => (hexpandedBounds n).2)
    · exact isBoundedUnder_of_eventually_ge (f := atTop) (u := -error)
        (hKpos.mono fun n hn => by
          have hnR : (1 : ℝ) ≤ prefixCount K n := by exact_mod_cast hn
          have hc : 0 ≤ c := by positivity
          change -c ≤ -error n
          dsimp [error]
          rw [neg_le_neg_iff]
          exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hnR)).2
            (by nlinarith))
    · exact Filter.isCoboundedUnder_ge_of_le atTop
        (fun n => show -error n ≤ (0 : ℝ) from neg_nonpos.mpr (herrorNonneg n))
  have hsumCompare :
      liminf (expandedRatio + (-error)) atTop ≤ liminf targetRatio atTop := by
    apply liminf_le_liminf
    · filter_upwards [hcompare] with n hn
      simpa [Pi.add_apply] using hn
    · exact isBoundedUnder_of_eventually_ge (f := atTop)
        (hKpos.mono fun n hn => by
          have hnR : (1 : ℝ) ≤ prefixCount K n := by exact_mod_cast hn
          have hc : 0 ≤ c := by positivity
          simp only [Pi.add_apply, Pi.neg_apply]
          have herrle : error n ≤ c := by
            dsimp [error]
            rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hnR)]
            nlinarith
          show -c ≤ expandedRatio n + -error n
          linarith [(hexpandedBounds n).1])
    · exact Filter.isCoboundedUnder_ge_of_le atTop
        (fun n => (htargetBounds n).2)
  have hnegError : liminf (-error) atTop = 0 := by
    simpa using herror.neg.liminf_eq
  change liminf expandedRatio atTop ≤ liminf targetRatio atTop
  rw [← add_zero (liminf expandedRatio atTop), ← hnegError]
  exact hsumLower.trans hsumCompare

end FiniteDensityTransfer
end Stage3Case019
