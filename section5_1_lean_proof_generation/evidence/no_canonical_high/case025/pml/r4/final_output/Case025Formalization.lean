import Stage3Model
import GenLimit.Paper39_DenseGeneration
import Mathlib.Combinatorics.Colex

open Filter
open scoped Topology

namespace Stage3Case025

private def finiteCode (n : ℕ) : Finset ℕ :=
  Finset.equivBitIndices n

private def augmentedFamily (family : ℕ → Language) : ℕ → Language :=
  fun k => family k.unpair.1 ∪ (finiteCode k.unpair.2 : Set ℕ)

private noncomputable def augmentedOracle
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := augmentedFamily family
  infinite' := by
    intro k
    exact (hInfinite k.unpair.1).mono Set.subset_union_left
  query := by
    classical
    exact fun i u => if u ∈ augmentedFamily family i then true else false
  query_spec := by
    classical
    intro i u
    simp

private def prefixCompletion {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else xs ⟨t, Nat.lt_succ_self t⟩

private theorem prefixCompletion_eq {t : ℕ} (xs : Fin (t + 1) → ℕ)
    {n : ℕ} (hn : n < t + 1) :
    prefixCompletion xs n = xs ⟨n, hn⟩ := by
  simp [prefixCompletion, hn]

private theorem sample_congr_of_lt
    {a b : Stream} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

private theorem consistent_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) (i : ℕ) :
    GenLimit.Consistent C a t i = GenLimit.Consistent C b t i := by
  unfold GenLimit.Consistent
  rw [h]

private theorem recursiveCritical_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) (i : ℕ) :
    GenLimit.RecursiveCritical C a t i =
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [GenLimit.RecursiveCritical] using
            consistent_congr_of_sample C h 0
      | succ n =>
          simp only [GenLimit.RecursiveCritical]
          apply propext
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨?_, ?_⟩
            · simpa only [consistent_congr_of_sample C h (n + 1)] using hcon
            · intro j hj hjcrit
              apply hsub j hj
              rw [ih j (by omega)]
              exact hjcrit
          · rintro ⟨hcon, hsub⟩
            refine ⟨?_, ?_⟩
            · simpa only [consistent_congr_of_sample C h (n + 1)] using hcon
            · intro j hj hjcrit
              apply hsub j hj
              rw [← ih j (by omega)]
              exact hjcrit

private theorem consistentIndices_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t scope : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.consistentIndices
  apply Finset.filter_congr
  intro i hi
  exact Iff.of_eq (consistent_congr_of_sample C h i)

private theorem criticalIndices_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t scope : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.criticalIndices
  apply Finset.filter_congr
  intro i hi
  exact Iff.of_eq (recursiveCritical_congr_of_sample C h i)

private theorem survivingIndices_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t scope : ℕ}
    (hold : GenLimit.sample a t = GenLimit.sample b t)
    (hnew : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.survivingCriticalIndices
  apply Finset.filter_congr
  intro i hi
  rw [recursiveCritical_congr_of_sample C hold i,
    recursiveCritical_congr_of_sample C hnew i]

private theorem highestCritical_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t scope fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr_of_sample C h]

private theorem highestSurvivor_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t scope fallback : ℕ}
    (hold : GenLimit.sample a t = GenLimit.sample b t)
    (hnew : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingIndices_congr_of_sample C hold hnew]

private theorem lowestInScope_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t scope fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr_of_sample C h]

private theorem lowestConsistent_congr_of_sample
    (C : ℕ → Language) {a b : Stream} {t fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  have hex :
      (∃ i, GenLimit.Consistent C a t i) ↔
        ∃ i, GenLimit.Consistent C b t i := by
    constructor <;> rintro ⟨i, hi⟩
    · exact ⟨i, by simpa only [consistent_congr_of_sample C h i] using hi⟩
    · exact ⟨i, by simpa only [consistent_congr_of_sample C h i] using hi⟩
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb := hex.mp ha
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr' (fun {i} => Iff.of_eq (consistent_congr_of_sample C h i))
  · have hb : ¬ ∃ i, GenLimit.Consistent C b t i :=
      fun hb => ha (hex.mpr hb)
    rw [dif_neg ha, dif_neg hb]

private theorem stableDecision_congr_of_sample
    (C : ℕ → Language) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (hnow : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  split
  · simp only [highestCritical_congr_of_sample C hnow]
  · rfl

private theorem backtrackDecision_congr_of_sample
    (C : ℕ → Language) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (hold : GenLimit.sample a t = GenLimit.sample b t)
    (hnow : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [consistentIndices_congr_of_sample C hnow,
    survivingIndices_congr_of_sample C hold hnow,
    highestSurvivor_congr_of_sample C hold hnow,
    lowestInScope_congr_of_sample C hnow,
    lowestConsistent_congr_of_sample C hnow,
    consistent_congr_of_sample C hnow]

private theorem decide_congr_of_prefix
    (C : ℕ → Language) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  have hold : GenLimit.sample a t = GenLimit.sample b t :=
    sample_congr_of_lt (fun n hn => h n (Nat.lt_succ_of_lt hn))
  have hnow : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
    sample_congr_of_lt h
  classical
  unfold GenLimit.PatientMachine.decide
  rw [consistent_congr_of_sample C hnow old.focus]
  split
  · exact stableDecision_congr_of_sample C t old hnow
  · exact backtrackDecision_congr_of_sample C t old hold hnow

private theorem leastAvailable_congr_of_prefix
    (C : ℕ → Language) (hInfinite : ∀ i, (C i).Infinite)
    {a b : Stream} (t : ℕ) (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.leastAvailable C hInfinite a t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite b t used focus := by
  have hs := sample_congr_of_lt h
  classical
  unfold GenLimit.PatientMachine.leastAvailable
    GenLimit.PatientMachine.available_exists
    GenLimit.PatientMachine.Available
  rw [hs]

private theorem patient_run_congr
    (O : GenLimit.OracleFamily) {a b : Stream} :
    ∀ t, (∀ n, n < t → a n = b n) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero =>
      intro h
      rfl
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      have hrun := ih (fun n hn => h n (Nat.lt_succ_of_lt hn))
      rw [hrun]
      have hd := decide_congr_of_prefix O.language t
        (GenLimit.PatientMachine.run O b t) h
      unfold GenLimit.PatientMachine.processRound
      rw [hd]
      have hl := leastAvailable_congr_of_prefix O.language O.infinite'
        (t + 1) (GenLimit.PatientMachine.run O b t).used
        (GenLimit.PatientMachine.decide O.language b t
          (GenLimit.PatientMachine.run O b t)).focus h
      simp only [hl]

private theorem patient_output_prefix
    (O : GenLimit.OracleFamily) (input : Stream) (t : ℕ) :
    GenLimit.PatientMachine.output O
        (prefixCompletion (t := t) (fun i : Fin (t + 1) => input i)) t =
      GenLimit.PatientMachine.output O input t := by
  unfold GenLimit.PatientMachine.output
  rw [patient_run_congr O (t + 1)]
  intro n hn
  exact prefixCompletion_eq (fun i : Fin (t + 1) => input i) hn

private noncomputable def onlinePatientGenerator
    (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t input _ => GenLimit.PatientMachine.output O (prefixCompletion input) t

private theorem follows_onlinePatientGenerator
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlinePatientGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  exact (patient_output_prefix O input t).symm

private theorem patient_output_injective
    (O : GenLimit.OracleFamily) (input : Stream) :
    Function.Injective (GenLimit.PatientMachine.output O input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact GenLimit.PatientMachine.output_ne_of_lt O input hlt hst
  · exact GenLimit.PatientMachine.output_ne_of_lt O input hgt hst.symm

private noncomputable def relativeRatio (A K : Language) (n : ℕ) : ℝ :=
  (GenLimit.PatientScope.prefixCount A n : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)

private theorem relativeRatio_nonneg (A K : Language) (n : ℕ) :
    0 ≤ relativeRatio A K n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem relativeRatio_le_one
    {A K : Language} (hAK : A ⊆ K) (n : ℕ) :
    relativeRatio A K n ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [relativeRatio, hzero]
  · rw [relativeRatio, div_le_one]
    · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n
    · exact_mod_cast Nat.pos_of_ne_zero hzero

private theorem liminf_le_of_le_add_vanishing
    (source target error : ℕ → ℝ)
    (hsource0 : ∀ n, 0 ≤ source n) (_hsource1 : ∀ n, source n ≤ 1)
    (htarget0 : ∀ n, 0 ≤ target n) (htarget1 : ∀ n, target n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n) :
    liminf source atTop ≤ liminf target atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget1)
    (isBoundedUnder_of ⟨0, htarget0⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrsource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrsource
      (isBoundedUnder_of ⟨0, hsource0⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hcompare] with n hr he hc
  linarith

private theorem prefixCount_union_finset_le
    (A : Language) (F : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ (F : Set ℕ)) n ≤
      GenLimit.PatientScope.prefixCount A n + F.card := by
  classical
  calc
    GenLimit.PatientScope.prefixCount (A ∪ (F : Set ℕ)) n =
        (GenLimit.PatientScope.prefixFinset (A ∪ (F : Set ℕ)) n).card := rfl
    _ ≤ (GenLimit.PatientScope.prefixFinset A n ∪ F).card := by
      apply Finset.card_le_card
      intro x hx
      rw [GenLimit.PatientScope.mem_prefixFinset] at hx
      simp only [Finset.mem_union, GenLimit.PatientScope.mem_prefixFinset,
        Finset.mem_coe, Set.mem_union] at hx ⊢
      exact hx.2.elim (fun hA => Or.inl ⟨hx.1, hA⟩) Or.inr
    _ ≤ (GenLimit.PatientScope.prefixFinset A n).card + F.card :=
      Finset.card_union_le _ _
    _ = GenLimit.PatientScope.prefixCount A n + F.card := rfl

private theorem relativeLowerDensity_finite_union_le
    (D K : Language) (F : Finset ℕ) (hK : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity
        (D ∩ (K ∪ (F : Set ℕ))) (K ∪ (F : Set ℕ)) ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
  let source := relativeRatio (D ∩ (K ∪ (F : Set ℕ)))
    (K ∪ (F : Set ℕ))
  let target := relativeRatio (D ∩ K) K
  let error : ℕ → ℝ := fun n =>
    (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcount := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcountR : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcountR
  have hcompare : ∀ᶠ n : ℕ in atTop,
      source n ≤ target n + error n := by
    filter_upwards [hcount.eventually (eventually_gt_atTop 0)] with n hn
    have hKpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hUnionPos : (0 : ℝ) <
        GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n := by
      exact lt_of_lt_of_le hKpos (by
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono
          (Set.subset_union_left) n)
    have hnumNat :
        GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n + F.card := by
      calc
        GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n ≤
            GenLimit.PatientScope.prefixCount ((D ∩ K) ∪ (F : Set ℕ)) n := by
          apply GenLimit.PatientScope.prefixCount_mono
          intro x hx
          rcases hx.2 with hxK | hxF
          · exact Or.inl ⟨hx.1, hxK⟩
          · exact Or.inr hxF
        _ ≤ GenLimit.PatientScope.prefixCount (D ∩ K) n + F.card :=
          prefixCount_union_finset_le (D ∩ K) F n
    have hnum :
        (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n + F.card := by
      exact_mod_cast hnumNat
    have hden :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n := by
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (Set.subset_union_left) n
    dsimp only [source, target, error, relativeRatio]
    calc
      (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
          GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n ≤
        (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
          GenLimit.PatientScope.prefixCount K n := by
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hKpos hden
      _ ≤ ((GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) + F.card) /
          GenLimit.PatientScope.prefixCount K n :=
            div_le_div_of_nonneg_right hnum hKpos.le
      _ = (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n +
          (F.card : ℝ) / GenLimit.PatientScope.prefixCount K n := by
            rw [add_div]
  change liminf source atTop ≤ liminf target atTop
  exact liminf_le_of_le_add_vanishing source target error
    (fun n => relativeRatio_nonneg _ _ n)
    (fun n => relativeRatio_le_one Set.inter_subset_right n)
    (fun n => relativeRatio_nonneg _ _ n)
    (fun n => relativeRatio_le_one Set.inter_subset_right n)
    herror hcompare

end Stage3Case025

open Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  intro family hInfinite
  let O := augmentedOracle family hInfinite
  refine ⟨onlinePatientGenerator O, ?_⟩
  intro i input hP
  classical
  let badIndices := GenLimit.Generic.ViolationIndices input
    (fun x => x ∈ family i)
  have hbadIndices : badIndices.Finite := hP.2
  let bad : Finset ℕ := hbadIndices.toFinset.image input
  have hrange : Set.range input = family i ∪ (bad : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      by_cases hx : input t ∈ family i
      · exact Or.inl hx
      · refine Or.inr ?_
        simp only [bad, Finset.mem_coe, Finset.mem_image]
        exact ⟨t, by simpa [badIndices, GenLimit.Generic.ViolationIndices], rfl⟩
    · rintro (hx | hx)
      · exact hP.1 hx
      · simp only [bad, Finset.mem_coe, Finset.mem_image] at hx
        obtain ⟨t, -, rfl⟩ := hx
        exact ⟨t, rfl⟩
  let code := Finset.equivBitIndices.symm bad
  let z := Nat.pair i code
  have hlanguage : O.language z = family i ∪ (bad : Set ℕ) := by
    simp [O, augmentedOracle, augmentedFamily, finiteCode, z, code]
  have hpresents : GenLimit.Presents input (O.language z) := by
    rw [hlanguage]
    exact hrange
  let output := GenLimit.PatientMachine.output O input
  obtain ⟨⟨T, hT⟩, hdensity⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input hpresents
  refine ⟨output, follows_onlinePatientGenerator O input, ?_, ?_⟩
  have hinjective : Function.Injective output := patient_output_injective O input
  have htimes : (output ⁻¹' (bad : Set ℕ)).Finite :=
    bad.finite_toSet.preimage hinjective.injOn
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range htimes.toFinset
  have havoid : ∀ t, N ≤ t → output t ∉ (bad : Set ℕ) := by
    intro t ht hmem
    have htmem : t ∈ htimes.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hmem
    have : t < N := Finset.mem_range.mp (hN htmem)
    omega
  · refine ⟨max T N, ?_⟩
    intro t ht
    have hmain := hT t (le_trans (le_max_left _ _) ht)
    have hnoBad := havoid t (le_trans (le_max_right _ _) ht)
    refine ⟨?_, ?_, hmain.2.2⟩
    · rw [hlanguage] at hmain
      exact hmain.1.resolve_right hnoBad
    · intro hsample
      rw [GenLimit.mem_sample_iff] at hsample
      obtain ⟨s, hs, heq⟩ := hsample
      exact hmain.2.1 s (Nat.lt_succ_iff.mp hs) heq
  · unfold GenLimit.PatientMachine.patientLowerDensity at hdensity
    rw [hlanguage] at hdensity
    exact hdensity.trans (relativeLowerDensity_finite_union_le
      (GenLimit.GeneratorFirst input output) (family i) bad (hInfinite i))

