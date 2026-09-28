import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.SweepGenerators

open Set Filter
open scoped Topology

namespace Case019

noncomputable def oracleOfFamily
    (family : GenLimit.Generic.LanguageFamily ℕ)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem sample_eq_of_eqOn_lt
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ k, k < t → a k = b k) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

private theorem consistent_iff_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  unfold GenLimit.Consistent
  rw [sample_eq_of_eqOn_lt h]

private theorem recursiveCritical_iff_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using
          consistent_iff_of_eqOn_lt (C := C) (i := 0) h
      | succ n =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical,
            consistent_iff_of_eqOn_lt h]
          constructor
          · rintro ⟨hc, hsub⟩
            exact ⟨hc, fun j hj hjc => hsub j hj ((ih j (by omega)).mpr hjc)⟩
          · rintro ⟨hc, hsub⟩
            exact ⟨hc, fun j hj hjc => hsub j hj ((ih j (by omega)).mp hjc)⟩

private theorem consistentIndices_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp [GenLimit.PatientMachine.mem_consistentIndices,
    consistent_iff_of_eqOn_lt h]

private theorem criticalIndices_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp [GenLimit.PatientMachine.mem_criticalIndices,
    recursiveCritical_iff_of_eqOn_lt h]

private theorem survivingCriticalIndices_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  have hprev : ∀ k, k < t → a k = b k := fun k hk => h k (by omega)
  ext i
  simp [GenLimit.PatientMachine.mem_survivingCriticalIndices,
    recursiveCritical_iff_of_eqOn_lt h,
    recursiveCritical_iff_of_eqOn_lt hprev]

private theorem highestCritical_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq_of_eqOn_lt h]

private theorem highestSurvivor_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_eqOn_lt h]

private theorem lowestConsistentInScope_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_eqOn_lt h]

private theorem lowestConsistent_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      simpa only [consistent_iff_of_eqOn_lt h] using ha
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr (Nat.find_spec ha)
      (fun n _ => consistent_iff_of_eqOn_lt h)
  · have hb : ¬∃ i, GenLimit.Consistent C b t i := by
      simpa only [← consistent_iff_of_eqOn_lt h] using ha
    rw [dif_neg ha, dif_neg hb]

private theorem backtrackDecision_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  have hconsistent := consistentIndices_eq_of_eqOn_lt
    (C := C) (scope := old.scope) h
  have hsurvivors := survivingCriticalIndices_eq_of_eqOn_lt
    (C := C) (scope := old.scope) h
  have hhighest := highestSurvivor_eq_of_eqOn_lt
    (C := C) (scope := old.scope) (fallback := old.focus) h
  have hscope := lowestConsistentInScope_eq_of_eqOn_lt
    (C := C) (scope := old.scope) (fallback := old.focus) h
  have hglobal := lowestConsistent_eq_of_eqOn_lt
    (C := C) (fallback := old.focus) h
  simp only [GenLimit.PatientMachine.backtrackDecision]
  rw [hconsistent, hsurvivors, hhighest, hscope, hglobal]
  by_cases hb : ∃ j, GenLimit.Consistent C b (t + 1) j
  · have ha : ∃ j, GenLimit.Consistent C a (t + 1) j := by
      simpa only [consistent_iff_of_eqOn_lt h] using hb
    simp [ha, hb]
  · have ha : ¬∃ j, GenLimit.Consistent C a (t + 1) j := by
      simpa only [consistent_iff_of_eqOn_lt h] using hb
    simp [ha, hb]

private theorem stableDecision_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  have hf := highestCritical_eq_of_eqOn_lt
    (C := C) (scope := old.scope + 1) (fallback := old.focus) h
  simp only [GenLimit.PatientMachine.stableDecision]
  split <;> simp [hf]

private theorem decide_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  have hc := consistent_iff_of_eqOn_lt
    (C := C) (i := old.focus) h
  simp only [GenLimit.PatientMachine.decide]
  by_cases ha : GenLimit.Consistent C a (t + 1) old.focus
  · have hb := hc.mp ha
    simp [ha, hb, stableDecision_eq_of_eqOn_lt old h]
  · have hb : ¬GenLimit.Consistent C b (t + 1) old.focus :=
      fun hh => ha (hc.mpr hh)
    simp [ha, hb, backtrackDecision_eq_of_eqOn_lt old h]

private theorem leastAvailable_eq_of_eqOn_lt
    {C : GenLimit.LanguageFamily} (hinf : ∀ i, (C i).Infinite)
    {a b : ℕ → ℕ} {t used focus}
    (h : ∀ k, k < t → a k = b k) :
    GenLimit.PatientMachine.leastAvailable C hinf a t used focus =
      GenLimit.PatientMachine.leastAvailable C hinf b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr (Nat.find_spec
    (GenLimit.PatientMachine.available_exists C hinf a t used focus))
  intro x hx
  unfold GenLimit.PatientMachine.Available
  rw [sample_eq_of_eqOn_lt h]

private theorem processRound_eq_of_eqOn_lt
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  have hd := decide_eq_of_eqOn_lt (C := O.language) old h
  simp only [GenLimit.PatientMachine.processRound]
  rw [hd]
  have hl := leastAvailable_eq_of_eqOn_lt O.infinite'
    (used := old.used)
    (focus := (GenLimit.PatientMachine.decide O.language b t old).focus) h
  rw [hl]

private theorem run_eq_of_eqOn_lt
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ k, k < t → a k = b k) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ,
        ih (fun k hk => h k (by omega))]
      exact processRound_eq_of_eqOn_lt O _ h

private def prefixCompletion {t : ℕ} (xs : Fin t → ℕ) : ℕ → ℕ :=
  fun n => if hn : n < t then xs ⟨n, hn⟩ else 0

private theorem prefixCompletion_eq {t : ℕ} (xs : Fin t → ℕ)
    {k : ℕ} (hk : k < t) : prefixCompletion xs k = xs ⟨k, hk⟩ := by
  simp [prefixCompletion, hk]

noncomputable def patientGenerator (O : GenLimit.OracleFamily) :
    GenLimit.Generic.Generator ℕ :=
  fun t xs => match t with
    | 0 => 0
    | s + 1 => GenLimit.PatientMachine.output O (prefixCompletion xs) s

private theorem patientGenerator_output
    (O : GenLimit.OracleFamily) (input : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) input t =
      GenLimit.PatientMachine.output O input t := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output patientGenerator
  simp only
  have hrun :
      GenLimit.PatientMachine.run O
          (prefixCompletion (fun i : Fin (t + 1) => input i)) (t + 1) =
        GenLimit.PatientMachine.run O input (t + 1) := by
    apply run_eq_of_eqOn_lt O (t + 1)
    intro k hk
    exact prefixCompletion_eq _ hk
  unfold GenLimit.PatientMachine.output
  rw [hrun]

private theorem contamination_of_level
    {input : ℕ → ℕ} {L : Set ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input L q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration input L := by
  refine ⟨h.1, ?_, ?_⟩
  · exact (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective h.1).2
      ((GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
        (Set.range input) L q).1 h.2.2).1
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty


private theorem separation_negative (q : ℕ) (gen : GenLimit.Generic.Generator ℤ) :
    ∃ K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q,
      ∃ input : GenLimit.Generic.Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (q + 1) ∧
          ¬Stage3Case019.SampleFreshGeneratesAfterInput
            input (Stage3Case019.outputAfterInput gen input) K := by
  have hn := GenLimit.NoiseLossFeedback.finiteNoiseLevel_lower q
  unfold GenLimit.NoiseLossFeedback.GeneratableInLimitWithNoiseLevel at hn
  unfold GenLimit.NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel at hn
  push_neg at hn
  obtain ⟨K, hK, input, hinput, hfail⟩ := hn gen
  refine ⟨K, hK, input, hinput, ?_⟩
  intro hgood
  obtain ⟨T, hT⟩ := hgood
  obtain ⟨t, ht, hbad⟩ := hfail T
  exact hbad (by
    simpa [Stage3Case019.outputAfterInput,
      GenLimit.NoiseLossFeedback.CorrectAt,
      GenLimit.NoiseLossFeedback.outputAt,
      GenLimit.NoiseLossFeedback.observedThrough] using hT t ht)

private theorem prefixCount_le_add_finite_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let a := (Finset.range n).filter fun x => x ∈ A
  let b := (Finset.range n).filter fun x => x ∈ B
  let d := (Finset.range n).filter fun x => x ∈ A \ B
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    simp only [a, b, d, Finset.mem_filter, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hd : d.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [d, Finset.mem_filter] at hx
    exact Set.Finite.mem_toFinset hfinite |>.2 hx.2
  calc
    a.card ≤ (b ∪ d).card := Finset.card_le_card hsub
    _ ≤ b.card + d.card := Finset.card_union_le _ _
    _ ≤ b.card + hfinite.toFinset.card := Nat.add_le_add_left hd _

private theorem relativeLowerDensity_le_of_finite_diff
    {A B K : Set ℕ} (hK : K.Infinite) (hfinite : (A \ B).Finite)
    (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  let ratio (S : Set ℕ) (n : ℕ) : ℝ :=
    (GenLimit.PatientScope.prefixCount S n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error (n : ℕ) : ℝ :=
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hcountK)
  have hprefix : ∀ n, ratio A n ≤ ratio B n + error n := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratio, error, hn]
    · have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [show ratio A n =
          (GenLimit.PatientScope.prefixCount A n : ℝ) /
            GenLimit.PatientScope.prefixCount K n by rfl,
        show ratio B n + error n =
          ((GenLimit.PatientScope.prefixCount B n : ℝ) +
            hfinite.toFinset.card) /
              GenLimit.PatientScope.prefixCount K n by
                simp [ratio, error, add_div]]
      apply div_le_div_of_nonneg_right _ hnR.le
      exact_mod_cast prefixCount_le_add_finite_diff hfinite n
  have hBupper : ∀ n, ratio B n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratio, hn]
    · have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  change liminf (ratio A) atTop ≤ liminf (ratio B) atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop hBupper)
    (isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < ratio A n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩)
  have heEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, heEventually] with n hrn hen
  have hp := hprefix n
  linarith

private theorem relativeLowerDensity_eq_of_finite_symmetricDifference
    {A B K : Set ℕ} (hK : K.Infinite)
    (hAB : (A \ B).Finite) (hBA : (B \ A).Finite)
    (hAK : A ⊆ K) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K =
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply le_antisymm
  · exact relativeLowerDensity_le_of_finite_diff hK hAB hBK
  · exact relativeLowerDensity_le_of_finite_diff hK hBA hAK

private theorem relativeLowerDensity_antitone_reference
    {A K L : Set ℕ} (hA : A ⊆ L) (hLK : L ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity A L := by
  let ratio (S : Set ℕ) (n : ℕ) : ℝ :=
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount S n : ℝ)
  have hpoint : ∀ n, ratio K n ≤ ratio L n := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount L n = 0
    · have hAn : GenLimit.PatientScope.prefixCount A n = 0 := by
        exact Nat.eq_zero_of_le_zero <|
          (GenLimit.PatientScope.prefixCount_mono hA n).trans_eq hn
      simp [ratio, hAn]
    · have hLpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount L n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hKpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n :=
        lt_of_lt_of_le hLpos (by
          exact_mod_cast GenLimit.PatientScope.prefixCount_mono hLK n)
      exact div_le_div_of_nonneg_left (by positivity) hLpos
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hLK n)
  change liminf (ratio K) atTop ≤ liminf (ratio L) atTop
  exact liminf_le_liminf (Eventually.of_forall hpoint)
    (hu := isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩)
    (hv := isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop (fun n => by
      by_cases hn : GenLimit.PatientScope.prefixCount L n = 0
      · have hAn : GenLimit.PatientScope.prefixCount A n = 0 := by
          exact Nat.eq_zero_of_le_zero <|
            (GenLimit.PatientScope.prefixCount_mono hA n).trans_eq hn
        simp [ratio, hAn]
      · have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount L n := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        rw [div_le_one hnR]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hA n))


private theorem relativeLowerDensity_reference_le_of_finite_diff
    {A L K : Set ℕ} (hL : L.Infinite) (hAL : A ⊆ L) (hLK : L ⊆ K)
    (hfinite : (K \ L).Finite) :
    GenLimit.PatientScope.relativeLowerDensity A L ≤
      GenLimit.PatientScope.relativeLowerDensity A K := by
  let ratio (S : Set ℕ) (n : ℕ) : ℝ :=
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount S n : ℝ)
  let error (n : ℕ) : ℝ :=
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount L n : ℝ)
  have hcountL := GenLimit.PatientScope.tendsto_prefixCount_atTop hL
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hcountL)
  have hprefix : ∀ n, ratio L n ≤ ratio K n + error n := by
    intro n
    by_cases hln : GenLimit.PatientScope.prefixCount L n = 0
    · have han : GenLimit.PatientScope.prefixCount A n = 0 :=
        Nat.eq_zero_of_le_zero <|
          (GenLimit.PatientScope.prefixCount_mono hAL n).trans_eq hln
      simp [ratio, error, hln, han]
    · have hlR : (0 : ℝ) < GenLimit.PatientScope.prefixCount L n := by
        exact_mod_cast Nat.pos_of_ne_zero hln
      have hkn : GenLimit.PatientScope.prefixCount K n ≠ 0 := by
        exact Nat.ne_of_gt <| lt_of_lt_of_le (Nat.pos_of_ne_zero hln)
          (GenLimit.PatientScope.prefixCount_mono hLK n)
      have hkR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hkn
      have hAcount := GenLimit.PatientScope.prefixCount_mono hAL n
      have hKcount := prefixCount_le_add_finite_diff hfinite n
      dsimp only [ratio, error]
      have hAcast : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
          GenLimit.PatientScope.prefixCount L n := by exact_mod_cast hAcount
      have hKcast : (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount L n + hfinite.toFinset.card := by
        exact_mod_cast hKcount
      have hLcast : (GenLimit.PatientScope.prefixCount L n : ℝ) ≤
          GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hLK n
      field_simp [hlR.ne', hkR.ne']
      nlinarith
  have hKupper : ∀ n, ratio K n ≤ 1 := by
    intro n
    by_cases hkn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratio, hkn]
    · have hkR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hkn
      rw [div_le_one hkR]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono (hAL.trans hLK) n
  change liminf (ratio L) atTop ≤ liminf (ratio K) atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop hKupper)
    (isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < ratio L n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩)
  have heEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, heEventually] with n hrn hen
  have hp := hprefix n
  linarith

private theorem countable_half_density : Stage3Case019.CountableClause := by
  intro q family hinf
  let O := oracleOfFamily family hinf
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hinput
  have hcontam := contamination_of_level hinput
  obtain ⟨j, hjBase, hjPresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream
      O hcontam
  have hpatient :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      E input hjPresents
  have hout : Stage3Case019.outputAfterInput (patientGenerator E) input =
      GenLimit.PatientMachine.output E input := by
    funext t
    exact patientGenerator_output E input t
  have hLE : family i ⊆ E.language j := by
    rw [← hjPresents]
    exact hinput.2.1
  have hnoise : (E.language j \ family i).Finite := by
    rw [← hjPresents]
    exact ((GenLimit.Generic.setDifferenceAtMost_iff_finite_ncard_le
      (Set.range input) (family i) q).1 hinput.2.2).1
  constructor
  · obtain ⟨Tgen, hTgen⟩ := hpatient.1
    obtain ⟨Tseen, hTseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample
        hjPresents hnoise.toFinset (by
          intro x hx
          exact ((Set.Finite.mem_toFinset hnoise).mp hx).1)
    refine ⟨max Tgen Tseen, ?_⟩
    intro t ht
    have hgen := hTgen t ((Nat.le_max_left _ _).trans ht)
    have hseen : hnoise.toFinset ⊆ GenLimit.Generic.sample input (t + 1) := by
      intro x hx
      exact GenLimit.Generic.sample_mono
        ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)) (hTseen hx)
    rw [hout]
    refine ⟨?_, ?_, hgen.2.2⟩
    · by_contra hx
      have hbad : GenLimit.PatientMachine.output E input t ∈ hnoise.toFinset :=
        (Set.Finite.mem_toFinset hnoise).mpr ⟨hgen.1, hx⟩
      have hsamp := hseen hbad
      rw [GenLimit.Generic.mem_sample_iff] at hsamp
      obtain ⟨s, hs, hval⟩ := hsamp
      exact hgen.2.1 s (by omega) hval
    · rw [GenLimit.mem_sample_iff]
      rintro ⟨s, hs, hval⟩
      exact hgen.2.1 s (by omega) hval
  · rw [hout]
    let first := GenLimit.GeneratorFirst input
      (GenLimit.PatientMachine.output E input)
    let A := first ∩ E.language j
    let B := first ∩ family i
    have hAB : (A \ B).Finite := by
      apply hnoise.subset
      intro x hx
      exact ⟨hx.1.2, fun hxL => hx.2 ⟨hx.1.1, hxL⟩⟩
    have hBE : B ⊆ E.language j := by
      intro x hx
      exact hLE hx.2
    have hdensityTransfer :
        GenLimit.PatientScope.relativeLowerDensity A (E.language j) ≤
          GenLimit.PatientScope.relativeLowerDensity B (E.language j) :=
      relativeLowerDensity_le_of_finite_diff (E.infinite' j) hAB hBE
    have hreferenceTransfer :
        GenLimit.PatientScope.relativeLowerDensity B (E.language j) ≤
          GenLimit.PatientScope.relativeLowerDensity B (family i) :=
      relativeLowerDensity_antitone_reference (fun _ hx => hx.2) hLE
    exact hpatient.2.trans (hdensityTransfer.trans hreferenceTransfer)

private def positiveIndex (z : ℤ) : ℕ := z.toNat - 1
private def negativeIndex (z : ℤ) : ℕ := z.natAbs - 1

@[simp] private theorem positiveIndex_code (n : ℕ) :
    positiveIndex (GenLimit.UnionClosedness.positiveCode n) = n := by
  simp [positiveIndex, GenLimit.UnionClosedness.positiveCode]

@[simp] private theorem negativeIndex_code (n : ℕ) :
    negativeIndex (GenLimit.UnionClosedness.negativeCode n) = n := by
  simp [negativeIndex, GenLimit.UnionClosedness.negativeCode]

private noncomputable def univOracle : GenLimit.OracleFamily :=
  oracleOfFamily (fun _ => Set.univ) (fun _ => Set.infinite_univ)

private noncomputable def expandedUnivOracle : GenLimit.OracleFamily :=
  GenLimit.InfiniteContamination.finiteExpansionOracleFamily univOracle

private theorem exists_expandedUniv_index
    (stream : ℕ → ℕ) (hcofinite : (Set.univ \ Set.range stream).Finite) :
    ∃ j, GenLimit.Generic.Presents stream (expandedUnivOracle.language j) := by
  let remove := hcofinite.toFinset
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (0, Finset.equivBitIndices.symm ∅,
      Finset.equivBitIndices.symm remove)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  change Set.range stream =
    GenLimit.InfiniteContamination.finiteExpansionLanguage univOracle j
  rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
  simp only [j, data, GenLimit.InfiniteContamination.finiteExpansionCode_encode,
    Equiv.apply_symm_apply]
  simp only [GenLimit.InfiniteContamination.finiteExpansion, univOracle,
    oracleOfFamily]
  ext n
  simp [remove, Set.Finite.mem_toFinset]

private noncomputable def sidePatientGenerator
    (code : ℕ → ℤ) (decode : ℤ → ℕ) : GenLimit.Generic.Generator ℤ :=
  fun t xs => code (patientGenerator expandedUnivOracle t (fun k => decode (xs k)))

private theorem sidePatientGenerator_output
    (code : ℕ → ℤ) (decode : ℤ → ℕ) (input : ℕ → ℤ) (t : ℕ) :
    Stage3Case019.outputAfterInput (sidePatientGenerator code decode) input t =
      code (GenLimit.PatientMachine.output expandedUnivOracle
        (fun s => decode (input s)) t) := by
  change code (Stage3Case019.outputAfterInput
    (patientGenerator expandedUnivOracle) (fun s => decode (input s)) t) = _
  rw [patientGenerator_output]

private noncomputable def separationGenerator (q : ℕ) :
    GenLimit.Generic.Generator ℤ :=
  fun t xs =>
    if GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
        GenLimit.Generic.sequenceSample xs then
      sidePatientGenerator GenLimit.UnionClosedness.positiveCode positiveIndex t xs
    else
      sidePatientGenerator GenLimit.UnionClosedness.negativeCode negativeIndex t xs

private theorem positive_decode_cofinite
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionFirstClass q)
    {input : ℕ → ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    (Set.univ \ Set.range (fun s => positiveIndex (input s))).Finite := by
  obtain ⟨_hmarkers, j, htail⟩ := hK
  apply (Set.finite_Iio j).subset
  intro n hn
  by_contra hnj
  have hjn : j ≤ n := Nat.le_of_not_gt hnj
  have hcode : GenLimit.UnionClosedness.positiveCode n ∈ K := by
    apply htail
    exact ⟨n - j, by
      apply Int.ofNat_inj.mpr
      omega⟩
  obtain ⟨s, hs⟩ := hinput.2.1 hcode
  exact hn.2 ⟨s, by
    change positiveIndex (input s) = n
    rw [hs]
    exact positiveIndex_code n⟩

private theorem negative_decode_surjective
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionSecondClass q)
    {input : ℕ → ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    Set.range (fun s => negativeIndex (input s)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  have hcode : GenLimit.UnionClosedness.negativeCode n ∈ K :=
    hK.1 (GenLimit.UnionClosedness.negativeCode_mem n)
  obtain ⟨s, hs⟩ := hinput.2.1 hcode
  exact ⟨s, by
    change negativeIndex (input s) = n
    rw [hs]
    exact negativeIndex_code n⟩

private theorem side_patient_novel
    (code : ℕ → ℤ) (decode : ℤ → ℕ)
    (hdecode : ∀ n, decode (code n) = n)
    (hinj : Function.Injective code)
    (input : ℕ → ℤ) (base : Set ℕ)
    (hbase : base ⊆ Set.range (fun s => decode (input s)))
    (hbaseCofinite : (Set.univ \ base).Finite)
    (hbad : (Set.range (fun s => decode (input s)) \ base).Finite) :
    ∃ T, ∀ t, T ≤ t →
      Stage3Case019.outputAfterInput
          (sidePatientGenerator code decode) input t ∈ code '' base ∧
        Stage3Case019.outputAfterInput
            (sidePatientGenerator code decode) input t ∉
          GenLimit.Generic.sample input (t + 1) ∧
        ∀ s, s < t →
          Stage3Case019.outputAfterInput
              (sidePatientGenerator code decode) input s ≠
            Stage3Case019.outputAfterInput
              (sidePatientGenerator code decode) input t := by
  let decoded : ℕ → ℕ := fun s => decode (input s)
  have hcofinite : (Set.univ \ Set.range decoded).Finite := by
    apply hbaseCofinite.subset
    intro n hn
    exact ⟨hn.1, fun hbaseMem => hn.2 (hbase hbaseMem)⟩
  obtain ⟨j, hj⟩ := exists_expandedUniv_index decoded hcofinite
  have hp := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    expandedUnivOracle decoded hj
  have hrange : expandedUnivOracle.language j = Set.range decoded := hj.symm
  have hextra : (expandedUnivOracle.language j \ base).Finite := by
    rw [hrange]
    exact hbad
  obtain ⟨Tgen, hTgen⟩ := hp.1
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hj hextra.toFinset (by
      intro n hn
      exact ((Set.Finite.mem_toFinset hextra).mp hn).1)
  refine ⟨max Tgen Tseen, ?_⟩
  intro t ht
  have hg := hTgen t ((Nat.le_max_left _ _).trans ht)
  have hseen : hextra.toFinset ⊆ GenLimit.Generic.sample decoded (t + 1) := by
    intro n hn
    exact GenLimit.Generic.sample_mono
      ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)) (hTseen hn)
  rw [sidePatientGenerator_output]
  have houtBase : GenLimit.PatientMachine.output expandedUnivOracle decoded t ∈ base := by
    by_contra hn
    have hmem : GenLimit.PatientMachine.output expandedUnivOracle decoded t ∈
        hextra.toFinset := (Set.Finite.mem_toFinset hextra).mpr ⟨hg.1, hn⟩
    have hsamp := hseen hmem
    rw [GenLimit.Generic.mem_sample_iff] at hsamp
    obtain ⟨s, hs, heq⟩ := hsamp
    exact hg.2.1 s (by omega) heq
  refine ⟨⟨_, houtBase, rfl⟩, ?_, ?_⟩
  · rw [GenLimit.Generic.mem_sample_iff]
    rintro ⟨s, hs, heq⟩
    have hdec := congrArg decode heq
    rw [hdecode] at hdec
    exact hg.2.1 s (by omega) hdec
  · intro s hst heq
    rw [sidePatientGenerator_output] at heq
    exact hg.2.2 s hst (hinj heq)



private theorem prefixCount_le_of_stride
    {A B : Set ℕ} {offset n m : ℕ} (hoffset : offset ≤ 2)
    (hstride : ∀ k, k ∈ A → 2 * k + offset ∈ B)
    (hbound : 2 * n + 2 ≤ m) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B m := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  let source := (Finset.range n).filter fun k => k ∈ A
  let target := (Finset.range m).filter fun k => k ∈ B
  let f : ℕ → ℕ := fun k => 2 * k + offset
  have hinj : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    omega
  have hsub : source.image f ⊆ target := by
    intro x hx
    simp only [source, target, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range] at hx ⊢
    obtain ⟨k, ⟨hkn, hkA⟩, rfl⟩ := hx
    refine ⟨?_, hstride k hkA⟩
    dsimp [f]
    omega
  calc
    source.card = (source.image f).card :=
      (Finset.card_image_of_injective source hinj).symm
    _ ≤ target.card := Finset.card_le_card hsub

private theorem quarter_density_of_stride
    {A B K : Set ℕ} {offset : ℕ} (hoffset : offset ≤ 2)
    (hstride : ∀ k, k ∈ A → 2 * k + offset ∈ B)
    (hBK : B ⊆ K)
    (hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A Set.univ) :
    (1 / 4 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity B K := by
  let ratio (S : Set ℕ) (n : ℕ) : ℝ :=
    (GenLimit.PatientScope.prefixCount S n : ℝ) / n
  have hcountUniv : ∀ n,
      GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
    intro n
    simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  have hhalf' : (1 / 2 : ℝ) ≤ liminf (ratio A) atTop := by
    simpa only [GenLimit.PatientScope.relativeLowerDensity, ratio, hcountUniv]
      using hhalf
  have hBupper : ∀ n, ratio B n ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [ratio, hn]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast (GenLimit.PatientScope.prefixCount_mono
        (fun _ _ => trivial : B ⊆ Set.univ) n).trans_eq (hcountUniv n)
  have hBnonneg : ∀ n, 0 ≤ ratio B n := fun n =>
    div_nonneg (by positivity) (by positivity)
  have hquarterUniv : (1 / 4 : ℝ) ≤ liminf (ratio B) atTop := by
    apply (le_liminf_iff
      (isCoboundedUnder_ge_of_le atTop hBupper)
      (isBoundedUnder_of ⟨0, hBnonneg⟩)).2
    intro y hy
    by_cases hy0 : y < 0
    · exact Eventually.of_forall fun n => lt_of_lt_of_le hy0 (hBnonneg n)
    have hy_nonneg : 0 ≤ y := le_of_not_gt hy0
    have htwo : 2 * y < (1 / 2 : ℝ) := by nlinarith
    obtain ⟨r, hyr, hrhalf⟩ := exists_between htwo
    have hrDensity : r < liminf (ratio A) atTop := hrhalf.trans_le hhalf'
    have hrEventually : ∀ᶠ n : ℕ in atTop, r < ratio A n :=
      eventually_lt_of_lt_liminf hrDensity
        (isBoundedUnder_of ⟨0, fun n => div_nonneg (by positivity) (by positivity)⟩)
    let halfIndex : ℕ → ℕ := fun m => m / 2 - 1
    have hhalfIndex : Tendsto halfIndex atTop atTop := by
      apply tendsto_atTop.2
      intro N
      filter_upwards [eventually_ge_atTop (2 * (N + 1))] with m hm
      dsimp [halfIndex]
      omega
    have hrComposed : ∀ᶠ m : ℕ in atTop, r < ratio A (halfIndex m) :=
      hhalfIndex.eventually hrEventually
    have hgap : 0 < r - 2 * y := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * y / (r - 2 * y))
    filter_upwards [hrComposed, eventually_ge_atTop (max 2 (2 * (N + 2)))] with m hrm hm
    let n := halfIndex m
    have hnN : N < n := by
      dsimp [n, halfIndex]
      omega
    have hnpos : 0 < n := by omega
    have hmpos : 0 < m := lt_of_lt_of_le (by omega) hm
    have hbound : 2 * n + 2 ≤ m := by
      dsimp [n, halfIndex]
      omega
    have hmupper : m ≤ 2 * n + 3 := by
      dsimp [n, halfIndex]
      omega
    have hcounts := prefixCount_le_of_stride hoffset hstride hbound
    have hratioA : r <
        (GenLimit.PatientScope.prefixCount A n : ℝ) / n := by
      simpa [ratio, n] using hrm
    have hNreal : 4 * y / (r - 2 * y) < (n : ℝ) := by
      exact lt_trans hN (by exact_mod_cast hnN)
    have hgrowth : 4 * y < (r - 2 * y) * n := by
      simpa [mul_comm] using (div_lt_iff₀ hgap).mp hNreal
    have hcountR : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
        GenLimit.PatientScope.prefixCount B m := by exact_mod_cast hcounts
    have hmR : (m : ℝ) ≤ 2 * n + 3 := by exact_mod_cast hmupper
    dsimp only [ratio]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hmRpos : (0 : ℝ) < m := by exact_mod_cast hmpos
    rw [lt_div_iff₀ hmRpos]
    rw [lt_div_iff₀ hnR] at hratioA
    nlinarith
  have habsolute : (1 / 4 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity B Set.univ := by
    simpa only [GenLimit.PatientScope.relativeLowerDensity, ratio, hcountUniv]
      using hquarterUniv
  exact habsolute.trans <| relativeLowerDensity_antitone_reference hBK
    (fun _ _ => trivial)

private theorem side_patient_half_density
    (decode : ℤ → ℕ) (input : ℕ → ℤ) (base : Set ℕ)
    (hbase : base ⊆ Set.range (fun s => decode (input s)))
    (hbaseCofinite : (Set.univ \ base).Finite)
    (hbad : (Set.range (fun s => decode (input s)) \ base).Finite) :
    (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity
      (GenLimit.GeneratorFirst (fun s => decode (input s))
          (GenLimit.PatientMachine.output expandedUnivOracle
            (fun s => decode (input s))) ∩ base)
      Set.univ := by
  let decoded : ℕ → ℕ := fun s => decode (input s)
  have hcofinite : (Set.univ \ Set.range decoded).Finite := by
    apply hbaseCofinite.subset
    intro n hn
    exact ⟨hn.1, fun hbaseMem => hn.2 (hbase hbaseMem)⟩
  obtain ⟨j, hj⟩ := exists_expandedUniv_index decoded hcofinite
  have hp := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    expandedUnivOracle decoded hj
  have hrange : expandedUnivOracle.language j = Set.range decoded := hj.symm
  let A := GenLimit.GeneratorFirst decoded
    (GenLimit.PatientMachine.output expandedUnivOracle decoded) ∩
      expandedUnivOracle.language j
  let B := GenLimit.GeneratorFirst decoded
    (GenLimit.PatientMachine.output expandedUnivOracle decoded) ∩ base
  have hAB : (A \ B).Finite := by
    apply hbad.subset
    intro n hn
    exact ⟨by simpa [A, hrange] using hn.1.2, by
      intro hnb
      exact hn.2 ⟨hn.1.1, hnb⟩⟩
  have hBE : B ⊆ expandedUnivOracle.language j := by
    intro n hn
    rw [hrange]
    exact hbase hn.2
  have hhalfE : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity B
        (expandedUnivOracle.language j) := by
    exact hp.2.trans <| relativeLowerDensity_le_of_finite_diff
      (expandedUnivOracle.infinite' j) hAB hBE
  have hEuniv : expandedUnivOracle.language j ⊆ Set.univ := fun _ _ => trivial
  have hunivE : (Set.univ \ expandedUnivOracle.language j).Finite := by
    rw [hrange]
    exact hcofinite
  have htransfer := relativeLowerDensity_reference_le_of_finite_diff
    (expandedUnivOracle.infinite' j) hBE hEuniv hunivE
  exact hhalfE.trans (by simpa [B, decoded] using htransfer)

private theorem separationGenerator_output_positive
    (q : ℕ) (input : ℕ → ℤ) (t : ℕ)
    (hmarkers : GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.NoiseLossFeedback.observedThrough input t) :
    Stage3Case019.outputAfterInput (separationGenerator q) input t =
      Stage3Case019.outputAfterInput
        (sidePatientGenerator GenLimit.UnionClosedness.positiveCode positiveIndex)
        input t := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output separationGenerator
  rw [GenLimit.Generic.sequenceSample_prefix]
  simp [hmarkers]

private theorem separationGenerator_output_negative
    (q : ℕ) (input : ℕ → ℤ) (t : ℕ)
    (hmarkers : ¬GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
      GenLimit.NoiseLossFeedback.observedThrough input t) :
    Stage3Case019.outputAfterInput (separationGenerator q) input t =
      Stage3Case019.outputAfterInput
        (sidePatientGenerator GenLimit.UnionClosedness.negativeCode negativeIndex)
        input t := by
  unfold Stage3Case019.outputAfterInput GenLimit.Generic.output separationGenerator
  rw [GenLimit.Generic.sequenceSample_prefix]
  simp [hmarkers]

private theorem separation_first_novel
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionFirstClass q)
    {input : ℕ → ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (separationGenerator q) input) K := by
  obtain ⟨hmarkers, j, htail⟩ := hK
  let decoded : ℕ → ℕ := fun s => positiveIndex (input s)
  have hbase : Set.Ici j ⊆ Set.range decoded := by
    intro n hn
    have hcode : GenLimit.UnionClosedness.positiveCode n ∈ K := by
      apply htail
      have hjn : j ≤ n := hn
      exact ⟨n - j, by apply Int.ofNat_inj.mpr; omega⟩
    obtain ⟨s, hs⟩ := hinput.2.1 hcode
    refine ⟨s, ?_⟩
    change positiveIndex (input s) = n
    rw [hs]
    exact positiveIndex_code n
  have hbad : (Set.range decoded \ Set.Ici j).Finite := by
    apply (Set.finite_Iio j).subset
    intro n hn
    exact Nat.lt_of_not_ge hn.2
  have hcofinite : (Set.univ \ Set.Ici j).Finite := by
    apply (Set.finite_Iio j).subset
    intro n hn
    exact Nat.lt_of_not_ge hn.2
  obtain ⟨Tp, hTp⟩ := side_patient_novel
    GenLimit.UnionClosedness.positiveCode positiveIndex positiveIndex_code
    GenLimit.UnionClosedness.positiveCode_injective input (Set.Ici j)
    hbase hcofinite hbad
  obtain ⟨Td, hTd⟩ :=
    GenLimit.NoiseLossFeedback.allMarkers_eventually_observed hinput hmarkers
  refine ⟨max Tp Td, ?_⟩
  intro t ht
  have hp := hTp t ((Nat.le_max_left _ _).trans ht)
  have hd := hTd t ((Nat.le_max_right _ _).trans ht)
  have hout := separationGenerator_output_positive q input t hd
  rw [hout]
  refine ⟨?_, hp.2.1, ?_⟩
  · obtain ⟨n, hn, heq⟩ := hp.1
    rw [← heq]
    have hjn : j ≤ n := hn
    exact htail ⟨n - j, by apply Int.ofNat_inj.mpr; omega⟩
  · intro s hst heq
    by_cases hsmarkers :
        GenLimit.NoiseLossFeedback.omissionMarkerFinset q ⊆
          GenLimit.NoiseLossFeedback.observedThrough input s
    · rw [separationGenerator_output_positive q input s hsmarkers] at heq
      exact hp.2.2 s hst heq
    · rw [separationGenerator_output_negative q input s hsmarkers,
          sidePatientGenerator_output] at heq
      rw [sidePatientGenerator_output] at heq
      have hneg := GenLimit.UnionClosedness.negativeCode_mem
        (GenLimit.PatientMachine.output expandedUnivOracle
          (fun k => negativeIndex (input k)) s)
      have hpos := GenLimit.UnionClosedness.positiveCode_mem
        (GenLimit.PatientMachine.output expandedUnivOracle
          (fun k => positiveIndex (input k)) t)
      rw [heq] at hneg
      exact (Int.not_lt_of_ge (le_of_lt hpos)) hneg

private theorem separation_second_novel
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionSecondClass q)
    {input : ℕ → ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (separationGenerator q) input) K := by
  let decoded : ℕ → ℕ := fun s => negativeIndex (input s)
  have hrange : Set.range decoded = Set.univ :=
    negative_decode_surjective hK hinput
  have hbase : Set.univ ⊆ Set.range decoded := by rw [hrange]
  have hcofinite : (Set.univ \ (Set.univ : Set ℕ)).Finite := by simp
  have hbad : (Set.range decoded \ (Set.univ : Set ℕ)).Finite := by simp
  obtain ⟨Tp, hTp⟩ := side_patient_novel
    GenLimit.UnionClosedness.negativeCode negativeIndex negativeIndex_code
    GenLimit.UnionClosedness.negativeCode_injective input Set.univ
    hbase hcofinite hbad
  refine ⟨Tp, ?_⟩
  intro t ht
  have hp := hTp t ht
  have hno := GenLimit.NoiseLossFeedback.not_allMarkers_observed_second
    hK hinput t
  have hout := separationGenerator_output_negative q input t hno
  rw [hout]
  refine ⟨?_, hp.2.1, ?_⟩
  · obtain ⟨n, _hn, heq⟩ := hp.1
    rw [← heq]
    exact hK.1 (GenLimit.UnionClosedness.negativeCode_mem n)
  · intro s hst heq
    have hnoS := GenLimit.NoiseLossFeedback.not_allMarkers_observed_second
      hK hinput s
    rw [separationGenerator_output_negative q input s hnoS] at heq
    exact hp.2.2 s hst heq


@[simp] private theorem balanced_negativeCode (n : ℕ) :
    Stage3Case019.balanced (2 * n + 1) =
      GenLimit.UnionClosedness.negativeCode n := by
  simp [Stage3Case019.balanced, GenLimit.UnionClosedness.negativeCode]
  omega

@[simp] private theorem balanced_positiveCode (n : ℕ) :
    Stage3Case019.balanced (2 * n + 2) =
      GenLimit.UnionClosedness.positiveCode n := by
  simp [Stage3Case019.balanced, GenLimit.UnionClosedness.positiveCode]
  omega

private theorem separation_first_density
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionFirstClass q)
    {input : ℕ → ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    (1 / 4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K) K := by
  classical
  obtain ⟨hmarkers, j, htail⟩ := hK
  let decoded : ℕ → ℕ := fun s => positiveIndex (input s)
  let pout : ℕ → ℕ := GenLimit.PatientMachine.output expandedUnivOracle decoded
  let A : Set ℕ := GenLimit.GeneratorFirst decoded pout ∩ Set.Ici j
  have hbase : Set.Ici j ⊆ Set.range decoded := by
    intro n hn
    have hcode : GenLimit.UnionClosedness.positiveCode n ∈ K := by
      apply htail
      have hjn : j ≤ n := hn
      exact ⟨n - j, by apply Int.ofNat_inj.mpr; omega⟩
    obtain ⟨s, hs⟩ := hinput.2.1 hcode
    refine ⟨s, ?_⟩
    change positiveIndex (input s) = n
    rw [hs]
    exact positiveIndex_code n
  have hbad : (Set.range decoded \ Set.Ici j).Finite := by
    apply (Set.finite_Iio j).subset
    intro n hn
    exact Nat.lt_of_not_ge hn.2
  have hcofinite : (Set.univ \ Set.Ici j).Finite := by
    apply (Set.finite_Iio j).subset
    intro n hn
    exact Nat.lt_of_not_ge hn.2
  have hhalfA : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A Set.univ := by
    simpa [A, decoded, pout] using side_patient_half_density
      positiveIndex input (Set.Ici j) hbase hcofinite hbad
  obtain ⟨Td, hTd⟩ :=
    GenLimit.NoiseLossFeedback.allMarkers_eventually_observed hinput hmarkers
  let early : Finset ℕ := (Finset.range Td).image pout
  let A' : Set ℕ := A \ (early : Set ℕ)
  have hAA' : (A \ A').Finite := by
    apply early.finite_toSet.subset
    intro n hn
    by_contra hnearly
    exact hn.2 ⟨hn.1, hnearly⟩
  have hhalfA' : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A' Set.univ := by
    exact hhalfA.trans <| relativeLowerDensity_le_of_finite_diff
      Set.infinite_univ hAA' (fun _ _ => trivial)
  let D : Set ℕ := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn input
      (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K)
  let KR : Set ℕ := Stage3Case019.balancedRanks K
  have hDK : D ⊆ KR := by
    intro r hr
    exact hr.2
  have hstride : ∀ n, n ∈ A' → 2 * n + 2 ∈ D := by
    intro n hn
    have hnA : n ∈ A := hn.1
    obtain ⟨t, htout, htfresh⟩ := hnA.1
    have htTd : Td ≤ t := by
      by_contra hnot
      have htlt : t < Td := Nat.lt_of_not_ge hnot
      exact hn.2 (by
        simp only [early, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
        exact ⟨t, htlt, htout⟩)
    have hdetect := hTd t htTd
    have hsep := separationGenerator_output_positive q input t hdetect
    have hside := sidePatientGenerator_output
      GenLimit.UnionClosedness.positiveCode positiveIndex input t
    have hout : Stage3Case019.outputAfterInput (separationGenerator q) input t =
        GenLimit.UnionClosedness.positiveCode n := by
      rw [hsep, hside]
      exact congrArg GenLimit.UnionClosedness.positiveCode htout
    have hfirst : GenLimit.UnionClosedness.positiveCode n ∈
        Stage3Case019.GeneratorFirstOn input
          (Stage3Case019.outputAfterInput (separationGenerator q) input) := by
      refine ⟨t, hout, ?_⟩
      intro s hst heq
      have hdec := congrArg positiveIndex heq
      rw [positiveIndex_code] at hdec
      exact htfresh s hst hdec
    have hnK : GenLimit.UnionClosedness.positiveCode n ∈ K := by
      apply htail
      have hjn : j ≤ n := hnA.2
      exact ⟨n - j, by apply Int.ofNat_inj.mpr; omega⟩
    change Stage3Case019.balanced (2 * n + 2) ∈
      Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K
    rw [balanced_positiveCode]
    exact ⟨hfirst, hnK⟩
  have hquarter := quarter_density_of_stride (A := A') (B := D) (K := KR)
    (offset := 2) (by omega) hstride hDK hhalfA'
  simpa [Stage3Case019.balancedRelativeLowerDensity, D, KR] using hquarter

private theorem separation_second_density
    {q : ℕ} {K : Set ℤ}
    (hK : K ∈ GenLimit.NoiseLossFeedback.finiteOmissionSecondClass q)
    {input : ℕ → ℤ}
    (hinput : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    (1 / 4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K) K := by
  let decoded : ℕ → ℕ := fun s => negativeIndex (input s)
  let pout : ℕ → ℕ := GenLimit.PatientMachine.output expandedUnivOracle decoded
  let A : Set ℕ := GenLimit.GeneratorFirst decoded pout ∩ Set.univ
  have hrange : Set.range decoded = Set.univ :=
    negative_decode_surjective hK hinput
  have hbase : Set.univ ⊆ Set.range decoded := by rw [hrange]
  have hcofinite : (Set.univ \ (Set.univ : Set ℕ)).Finite := by simp
  have hbad : (Set.range decoded \ (Set.univ : Set ℕ)).Finite := by simp
  have hhalfA : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity A Set.univ := by
    simpa [A, decoded, pout] using side_patient_half_density
      negativeIndex input Set.univ hbase hcofinite hbad
  let D : Set ℕ := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn input
      (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K)
  let KR : Set ℕ := Stage3Case019.balancedRanks K
  have hDK : D ⊆ KR := by
    intro r hr
    exact hr.2
  have hstride : ∀ n, n ∈ A → 2 * n + 1 ∈ D := by
    intro n hn
    obtain ⟨t, htout, htfresh⟩ := hn.1
    have hno := GenLimit.NoiseLossFeedback.not_allMarkers_observed_second
      hK hinput t
    have hsep := separationGenerator_output_negative q input t hno
    have hside := sidePatientGenerator_output
      GenLimit.UnionClosedness.negativeCode negativeIndex input t
    have hout : Stage3Case019.outputAfterInput (separationGenerator q) input t =
        GenLimit.UnionClosedness.negativeCode n := by
      rw [hsep, hside]
      exact congrArg GenLimit.UnionClosedness.negativeCode htout
    have hfirst : GenLimit.UnionClosedness.negativeCode n ∈
        Stage3Case019.GeneratorFirstOn input
          (Stage3Case019.outputAfterInput (separationGenerator q) input) := by
      refine ⟨t, hout, ?_⟩
      intro s hst heq
      have hdec := congrArg negativeIndex heq
      rw [negativeIndex_code] at hdec
      exact htfresh s hst hdec
    have hnK : GenLimit.UnionClosedness.negativeCode n ∈ K :=
      hK.1 (GenLimit.UnionClosedness.negativeCode_mem n)
    change Stage3Case019.balanced (2 * n + 1) ∈
      Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (separationGenerator q) input) ∩ K
    rw [balanced_negativeCode]
    exact ⟨hfirst, hnK⟩
  have hquarter := quarter_density_of_stride (A := A) (B := D) (K := KR)
    (offset := 1) (by omega) hstride hDK hhalfA
  simpa [Stage3Case019.balancedRelativeLowerDensity, D, KR] using hquarter

private def encodedSecond (q : ℕ) (A : Set ℕ) : Set ℤ :=
  GenLimit.UnionClosedness.negativeIntegers ∪
    GenLimit.UnionClosedness.positiveCode ''
      ((fun n : ℕ => n + q + 1) '' A)

private theorem encodedSecond_mem_class (q : ℕ) (A : Set ℕ) :
    encodedSecond q A ∈
      GenLimit.NoiseLossFeedback.finiteOmissionClass q := by
  right
  constructor
  · intro z hz
    exact Or.inl hz
  · rw [Set.disjoint_left]
    intro z hzEncoded hzMarker
    rcases hzEncoded with hzNegative | ⟨m, ⟨n, hn, rfl⟩, rfl⟩
    · have hzNonnegative :=
        GenLimit.NoiseLossFeedback.omissionMarker_nonnegative hzMarker
      exact (Int.not_lt_of_ge hzNonnegative) hzNegative
    · obtain ⟨k, hk, heq⟩ :=
        GenLimit.NoiseLossFeedback.mem_omissionMarkerFinset_iff.mp hzMarker
      unfold GenLimit.UnionClosedness.positiveCode at heq
      have hnat : k = n + q + 1 + 1 := Int.ofNat_inj.mp heq
      omega

private theorem positiveCode_shift_mem_encodedSecond_iff
    (q : ℕ) (A : Set ℕ) (n : ℕ) :
    GenLimit.UnionClosedness.positiveCode (n + q + 1) ∈ encodedSecond q A ↔
      n ∈ A := by
  constructor
  · intro hmem
    rcases hmem with hnegative | ⟨m, ⟨a, ha, hm⟩, hcode⟩
    · have hpositive := GenLimit.UnionClosedness.positiveCode_mem (n + q + 1)
      exact False.elim ((Int.not_lt_of_ge (le_of_lt hpositive)) hnegative)
    · have hm' := GenLimit.UnionClosedness.positiveCode_injective hcode
      have hshift : a + q + 1 = n + q + 1 := hm.trans hm'
      have han : a = n := by omega
      simpa [han] using ha
  · intro hn
    exact Or.inr ⟨n + q + 1, ⟨n, hn, rfl⟩, rfl⟩

private theorem encodedSecond_injective (q : ℕ) :
    Function.Injective (encodedSecond q) := by
  intro A B hAB
  ext n
  rw [← positiveCode_shift_mem_encodedSecond_iff q A n,
    ← positiveCode_shift_mem_encodedSecond_iff q B n, hAB]

private theorem finiteOmissionClass_not_countable (q : ℕ) :
    ¬(GenLimit.NoiseLossFeedback.finiteOmissionClass q).Countable := by
  intro hcountable
  let encode : Set ℕ →
      {K : Set ℤ // K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q} :=
    fun A => ⟨encodedSecond q A, encodedSecond_mem_class q A⟩
  have hinjective : Function.Injective encode := by
    intro A B hAB
    apply encodedSecond_injective q
    exact congrArg Subtype.val hAB
  letI : Countable
      {K : Set ℤ // K ∈ GenLimit.NoiseLossFeedback.finiteOmissionClass q} :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hinjective.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

private theorem uncountable_separation : Stage3Case019.SeparationClause := by
  intro q
  refine ⟨GenLimit.NoiseLossFeedback.finiteOmissionClass q,
    finiteOmissionClass_not_countable q,
    GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q, ?_, ?_⟩
  · refine ⟨separationGenerator q, ?_⟩
    intro K hK input hinput
    rcases hK with hfirst | hsecond
    · exact ⟨separation_first_novel hfirst hinput,
        separation_first_density hfirst hinput⟩
    · exact ⟨separation_second_novel hsecond hinput,
        separation_second_density hsecond hinput⟩
  · intro gen
    exact separation_negative q gen

end Case019

open Stage3Case019

theorem stage3_result : Stage3Case019.MainClaim := by
  exact ⟨Case019.countable_half_density, Case019.uncountable_separation⟩
