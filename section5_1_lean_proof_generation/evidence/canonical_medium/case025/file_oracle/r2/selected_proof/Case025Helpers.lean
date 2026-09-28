import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

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

def extendCurrent {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

theorem sample_eq_of_eq_before
    {a b : Stream} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem consistent_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  unfold GenLimit.Consistent
  rw [sample_eq_of_eq_before h]

theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using consistent_congr C h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          rw [consistent_congr C h]
          constructor <;> rintro ⟨hc, hs⟩ <;> refine ⟨hc, ?_⟩
          · intro j hj hjcrit
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjcrit)
          · intro j hj hjcrit
            exact hs j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjcrit)

theorem consistentIndices_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_congr C h]

theorem criticalIndices_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_congr C h]

theorem survivingCriticalIndices_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_congr C h]
  rw [recursiveCritical_congr C (fun n hn => h n (Nat.lt.step hn))]

theorem highestCritical_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr C h]

theorem highestSurvivor_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr C h]

theorem lowestConsistentInScope_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr C h]

theorem lowestConsistent_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  have hp : (∃ i, GenLimit.Consistent C a t i) ↔
      ∃ i, GenLimit.Consistent C b t i := by
    simp_rw [consistent_congr C h]
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb := hp.mp ha
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr' (fun {i} => consistent_congr C h)
  · have hb : ¬∃ i, GenLimit.Consistent C b t i := fun hb => ha (hp.mpr hb)
    rw [dif_neg ha, dif_neg hb]

theorem stableDecision_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  split
  · simp only
    rw [highestCritical_congr C h]
  · rfl

theorem backtrackDecision_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  have hexists : (∃ j, GenLimit.Consistent C a (t + 1) j) =
      (∃ j, GenLimit.Consistent C b (t + 1) j) := by
    apply propext
    simp_rw [consistent_congr C h]
  unfold GenLimit.PatientMachine.backtrackDecision
  rw [consistentIndices_congr C h]
  rw [survivingCriticalIndices_congr C h]
  rw [highestSurvivor_congr C h]
  rw [lowestConsistentInScope_congr C h]
  rw [hexists]
  rw [lowestConsistent_congr C h]

theorem decide_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [consistent_congr C h]
  split
  · exact stableDecision_congr C t old h
  · exact backtrackDecision_congr C t old h

theorem leastAvailable_congr
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {a b : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.leastAvailable C hInfinite a t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  apply propext
  unfold GenLimit.PatientMachine.Available
  rw [sample_eq_of_eq_before h]

theorem processRound_congr
    (O : GenLimit.OracleFamily) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hd := decide_congr O.language t old h
  unfold GenLimit.PatientMachine.processRound
  rw [hd]
  simp only
  rw [leastAvailable_congr O.language O.infinite' old.used _ h]

theorem run_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.run O a t =
      GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun n hn => h n (Nat.lt.step hn))]
      exact processRound_congr O t _ h

theorem output_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr O h]

noncomputable def patientOnlineGenerator (O : GenLimit.OracleFamily) :
    OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (extendCurrent xs) t

theorem follows_patientOnlineGenerator (O : GenLimit.OracleFamily)
    (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_congr O
  intro n hn
  simp [extendCurrent, hn]

theorem positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hP
  refine ⟨GenLimit.PatientMachine.output O input,
    follows_patientOnlineGenerator O input, ?_, ?_⟩
  · obtain ⟨⟨T, hT⟩, -⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hinj⟩ := hT t ht
    refine ⟨hmem, ?_, hinj⟩
    intro hs
    rw [GenLimit.mem_sample_iff] at hs
    obtain ⟨s, hst, hs⟩ := hs
    exact hfresh s (Nat.lt_succ_iff.mp hst) hs
  · exact GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP

noncomputable def finiteAdditionLanguage
    (family : ℕ → Language) (n : ℕ) : Language :=
  family (Nat.unpair n).1 ∪
    (Finset.equivBitIndices (Nat.unpair n).2 : Set ℕ)

theorem finiteAdditionLanguage_infinite
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) (n : ℕ) :
    (finiteAdditionLanguage family n).Infinite := by
  exact (hInfinite (Nat.unpair n).1).mono Set.subset_union_left

def encodeFiniteAddition (i code : ℕ) : ℕ := Nat.pair i code

@[simp] theorem finiteAdditionLanguage_encode
    (family : ℕ → Language) (i code : ℕ) :
    finiteAdditionLanguage family (encodeFiniteAddition i code) =
      family i ∪ (Finset.equivBitIndices code : Set ℕ) := by
  simp [finiteAdditionLanguage, encodeFiniteAddition, Nat.unpair_pair]

theorem prefixCount_le_finite_card {E : Set ℕ} (hE : E.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount E n ≤ hE.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  exact (Set.Finite.mem_toFinset hE).mpr (GenLimit.PatientScope.mem_prefixFinset.mp hx).2

theorem prefixCount_inter_enlargement_le
    (Q K R : Set ℕ) (hE : (R \ K).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Q ∩ R) n ≤
      GenLimit.PatientScope.prefixCount (Q ∩ K) n + hE.toFinset.card := by
  classical
  let A := GenLimit.PatientScope.prefixFinset (Q ∩ R) n
  let B := GenLimit.PatientScope.prefixFinset (Q ∩ K) n
  let E := GenLimit.PatientScope.prefixFinset (R \ K) n
  have hsubset : A ⊆ B ∪ E := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxK : x ∈ K
    · exact Finset.mem_union_left E <|
        GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2.1, hxK⟩
    · exact Finset.mem_union_right B <|
        GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2.2, hxK⟩
  change A.card ≤ B.card + hE.toFinset.card
  calc
    A.card ≤ (B ∪ E).card := Finset.card_le_card hsubset
    _ ≤ B.card + E.card := Finset.card_union_le B E
    _ ≤ B.card + hE.toFinset.card :=
      Nat.add_le_add_left (prefixCount_le_finite_card hE n) B.card

theorem relativeLowerDensity_enlargement_le
    (Q K R : Set ℕ) (hK : K.Infinite) (hKR : K ⊆ R)
    (hE : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hE.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (𝓝 0) := by
    have hcast : Tendsto
        (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
        atTop atTop := tendsto_natCast_atTop_atTop.comp hcountK
    exact tendsto_const_nhds.div_atTop hcast
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hcountK.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hpositive] with n hn
    have hnK : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hn
    have hdenNat := GenLimit.PatientScope.prefixCount_mono hKR n
    have hden : (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        GenLimit.PatientScope.prefixCount R n := by exact_mod_cast hdenNat
    have hnumNat := prefixCount_inter_enlargement_le Q K R hE n
    have hnum : (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) ≤
        GenLimit.PatientScope.prefixCount (Q ∩ K) n + hE.toFinset.card := by
      exact_mod_cast hnumNat
    calc
      source n ≤
          (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) hnK hden
      _ ≤ ((GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) +
            hE.toFinset.card) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        exact div_le_div_of_nonneg_right hnum (by positivity)
      _ = target n + error n := by rw [add_div]
  have hsourceLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop source := by
    apply isBoundedUnder_of
    refine ⟨0, fun n => ?_⟩
    change (0 : ℝ) ≤
      (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
        (GenLimit.PatientScope.prefixCount R n : ℝ)
    exact div_nonneg (by positivity) (by positivity)
  have htargetLower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop target := by
    apply isBoundedUnder_of
    refine ⟨0, fun n => ?_⟩
    change (0 : ℝ) ≤
      (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)
    exact div_nonneg (by positivity) (by positivity)
  have htargetUpper : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop target := by
    apply isCoboundedUnder_ge_of_le atTop
    intro n
    change (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff htargetUpper htargetLower).2
  intro y hy
  obtain ⟨d, hyd, hd⟩ := exists_between hy
  have hdEventually : ∀ᶠ n : ℕ in atTop, d < source n :=
    eventually_lt_of_lt_liminf hd hsourceLower
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < d - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyd))
  filter_upwards [hdEventually, herrorEventually, hcompare] with n hdN heN hcN
  linarith

end Stage3Case025
