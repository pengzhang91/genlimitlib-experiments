import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open Stage3Case019
open scoped Topology

namespace Case019

private theorem sample_congr
    {a b : Stream ℕ} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem consistent_congr
    (C : GenLimit.LanguageFamily) {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) (i : ℕ) :
    GenLimit.Consistent C a n i ↔ GenLimit.Consistent C b n i := by
  unfold GenLimit.Consistent
  rw [sample_congr h]

private theorem critical_congr
    (C : GenLimit.LanguageFamily) {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) (i : ℕ) :
    GenLimit.RecursiveCritical C a n i ↔ GenLimit.RecursiveCritical C b n i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using consistent_congr C h 0
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hc, hs⟩
            refine ⟨(consistent_congr C h _).1 hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjc)
          · rintro ⟨hc, hs⟩
            refine ⟨(consistent_congr C h _).2 hc, ?_⟩
            intro j hj hjc
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjc)

private theorem decide_congr
    (C : GenLimit.LanguageFamily) {a b : Stream ℕ} {t : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  have hc : ∀ i, GenLimit.Consistent C a (t + 1) i ↔
      GenLimit.Consistent C b (t + 1) i := consistent_congr C h
  have hr : ∀ i, GenLimit.RecursiveCritical C a (t + 1) i ↔
      GenLimit.RecursiveCritical C b (t + 1) i := critical_congr C h
  have hold : ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i :=
    critical_congr C (fun k hk => h k (Nat.lt.step hk))
  have hci : GenLimit.PatientMachine.consistentIndices C a (t + 1) old.scope =
      GenLimit.PatientMachine.consistentIndices C b (t + 1) old.scope := by
    ext i
    simp [hc i]
  have hcri : GenLimit.PatientMachine.criticalIndices C a (t + 1) (old.scope + 1) =
      GenLimit.PatientMachine.criticalIndices C b (t + 1) (old.scope + 1) := by
    ext i
    simp [hr i]
  have hsurv : GenLimit.PatientMachine.survivingCriticalIndices C a t old.scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t old.scope := by
    ext i
    simp [hold i, hr i]
  have hlcis : GenLimit.PatientMachine.lowestConsistentInScope C a (t + 1) old.scope old.focus =
      GenLimit.PatientMachine.lowestConsistentInScope C b (t + 1) old.scope old.focus := by
    unfold GenLimit.PatientMachine.lowestConsistentInScope
    simp only [hci]
  have he : (∃ i, GenLimit.Consistent C a (t + 1) i) ↔
      ∃ i, GenLimit.Consistent C b (t + 1) i := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hc i).1 hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hc i).2 hi⟩
  have hlc : GenLimit.PatientMachine.lowestConsistent C a (t + 1) old.focus =
      GenLimit.PatientMachine.lowestConsistent C b (t + 1) old.focus := by
    unfold GenLimit.PatientMachine.lowestConsistent
    by_cases ha : ∃ i, GenLimit.Consistent C a (t + 1) i
    · have hb : ∃ i, GenLimit.Consistent C b (t + 1) i := he.1 ha
      simp only [dif_pos ha, dif_pos hb]
      exact Nat.find_congr' (fun {i} => hc i)
    · have hb : ¬ ∃ i, GenLimit.Consistent C b (t + 1) i := fun hb => ha (he.2 hb)
      simp [ha, hb]
  unfold GenLimit.PatientMachine.decide
  rw [propext (hc old.focus)]
  unfold GenLimit.PatientMachine.stableDecision
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [hci, hcri, hsurv, hlcis, hlc, propext he]
  congr 1
  · unfold GenLimit.PatientMachine.highestCritical
    simp only [hcri]
  · unfold GenLimit.PatientMachine.highestSurvivor
    simp only [hsurv]

private theorem leastAvailable_congr
    (C : GenLimit.LanguageFamily) (hI : ∀ i, (C i).Infinite)
    {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k)
    (used : Finset ℕ) (focus : ℕ) :
    GenLimit.PatientMachine.leastAvailable C hI a n used focus =
      GenLimit.PatientMachine.leastAvailable C hI b n used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr'
  intro x
  unfold GenLimit.PatientMachine.Available
  rw [sample_congr h]

private theorem run_congr
    (O : GenLimit.OracleFamily) {a b : Stream ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.PatientMachine.run O a n = GenLimit.PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      have ih' := ih (fun k hk => h k (Nat.lt.step hk))
      rw [ih']
      have hd := decide_congr O.language h (GenLimit.PatientMachine.run O b n)
      unfold GenLimit.PatientMachine.processRound
      simp only [hd]
      rw [leastAvailable_congr O.language O.infinite' h]

noncomputable def patientPrefixGenerator (O : GenLimit.OracleFamily) : Generator ℕ :=
  fun n xs =>
    if n = 0 then 0
    else GenLimit.PatientMachine.output O
      (fun k => if hk : k < n then xs ⟨k, hk⟩ else 0) (n - 1)

@[simp] theorem patientPrefixGenerator_outputAfterInput
    (O : GenLimit.OracleFamily) (input : Stream ℕ) (t : ℕ) :
    outputAfterInput (patientPrefixGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  unfold outputAfterInput GenLimit.Generic.output patientPrefixGenerator
  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  unfold GenLimit.PatientMachine.output
  rw [run_congr O]
  intro k hk
  rw [dif_pos hk]

private theorem patient_prefixCount_le_add_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let a := GenLimit.PatientScope.prefixFinset A n
  let b := GenLimit.PatientScope.prefixFinset B n
  let d := GenLimit.PatientScope.prefixFinset (A \ B) n
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _ (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hd : d.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2 (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le b d).trans (Nat.add_le_add_left hd _))

private theorem liminf_le_of_vanishing_error
    (source output error : ℕ → ℝ)
    (hsource0 : ∀ n, 0 ≤ source n) (hsource1 : ∀ n, source n ≤ 1)
    (houtput0 : ∀ n, 0 ≤ output n) (houtput1 : ∀ n, output n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hle : ∀ᶠ n in atTop, source n ≤ output n + error n) :
    liminf source atTop ≤ liminf output atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop houtput1)
    (isBoundedUnder_of ⟨0, houtput0⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hsrc : ∀ᶠ n in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr (isBoundedUnder_of ⟨0, hsource0⟩)
  have herr : ∀ᶠ n in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hsrc, herr, hle] with n hn he hc
  linarith

 theorem relativeLowerDensity_transfer_finite
    {A K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let c := hfinite.toFinset.card
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
      GenLimit.PatientScope.prefixCount R n
  let output : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  let error : ℕ → ℝ := fun n =>
    (c : ℝ) / GenLimit.PatientScope.prefixCount K n
  have hKt := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hKtReal : Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop := by
    simpa only [Function.comp_apply] using tendsto_natCast_atTop_atTop.comp hKt
  have herr : Tendsto error atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hKtReal
  have ratio_nonneg : ∀ (S T : Set ℕ) n,
      0 ≤ (GenLimit.PatientScope.prefixCount S n : ℝ) /
        GenLimit.PatientScope.prefixCount T n := by
    intro S T n
    positivity
  have ratio_le_one : ∀ {S T : Set ℕ}, S ⊆ T → ∀ n,
      (GenLimit.PatientScope.prefixCount S n : ℝ) /
        GenLimit.PatientScope.prefixCount T n ≤ 1 := by
    intro S T hST n
    by_cases hz : GenLimit.PatientScope.prefixCount T n = 0
    · simp [hz]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hST n
  have hle : ∀ᶠ n in atTop, source n ≤ output n + error n := by
    filter_upwards [hKt.eventually (eventually_gt_atTop 0)] with n hn
    have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hn
    have hden : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hdiff : ((A ∩ R) \ (A ∩ K)).Finite := by
      apply hfinite.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hraw := patient_prefixCount_le_add_finite hdiff n
    have hcard : hdiff.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      apply Set.Finite.mem_toFinset hfinite |>.2
      have hx' := (Set.Finite.mem_toFinset hdiff).mp hx
      exact ⟨hx'.1.2, fun hxK => hx'.2 ⟨hx'.1.1, hxK⟩⟩
    have hnum : GenLimit.PatientScope.prefixCount (A ∩ R) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + c := by
      exact hraw.trans (Nat.add_le_add_left (by simpa [c] using hcard) _)
    calc
      source n ≤ (GenLimit.PatientScope.prefixCount (A ∩ R) n : ℝ) /
          GenLimit.PatientScope.prefixCount K n := by
        apply div_le_div_of_nonneg_left (by positivity) hkpos
        exact_mod_cast hden
      _ ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n + c : ℕ) /
          GenLimit.PatientScope.prefixCount K n := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hnum
        · positivity
      _ = output n + error n := by
        simp [output, error, Nat.cast_add, add_div]
  unfold GenLimit.PatientScope.relativeLowerDensity
  exact liminf_le_of_vanishing_error source output error
    (ratio_nonneg _ _) (ratio_le_one inter_subset_right)
    (ratio_nonneg _ _) (ratio_le_one inter_subset_right) herr hle

end Case019
