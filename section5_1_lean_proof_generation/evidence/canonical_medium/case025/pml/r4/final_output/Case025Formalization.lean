import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Combinatorics.Colex
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Stage3Case025

namespace Case025Formalization

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact decide (x ∈ family i)
  query_spec i x := by
    classical
    simp

noncomputable def prefixExtension {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

private theorem sample_eq_of_eq_of_lt
    {u v : Stream} {t : ℕ} (h : ∀ n, n < t → u n = v n) :
    GenLimit.sample u t = GenLimit.sample v t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

private theorem recursiveCritical_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t i : ℕ}
    (hs : GenLimit.sample u t = GenLimit.sample v t) :
    GenLimit.RecursiveCritical C u t i ↔
      GenLimit.RecursiveCritical C v t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [GenLimit.RecursiveCritical, GenLimit.Consistent, hs]
      | succ n =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨?_, ?_⟩
            · simpa [GenLimit.Consistent, hs] using hcon
            · intro j hj hjcrit
              exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨?_, ?_⟩
            · simpa [GenLimit.Consistent, hs] using hcon
            · intro j hj hjcrit
              exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

private theorem consistentIndices_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t scope : ℕ}
    (hs : GenLimit.sample u t = GenLimit.sample v t) :
    GenLimit.PatientMachine.consistentIndices C u t scope =
      GenLimit.PatientMachine.consistentIndices C v t scope := by
  classical
  unfold GenLimit.PatientMachine.consistentIndices
  congr 1
  funext i
  apply propext
  simp [GenLimit.Consistent, hs]

private theorem criticalIndices_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t scope : ℕ}
    (hs : GenLimit.sample u t = GenLimit.sample v t) :
    GenLimit.PatientMachine.criticalIndices C u t scope =
      GenLimit.PatientMachine.criticalIndices C v t scope := by
  classical
  unfold GenLimit.PatientMachine.criticalIndices
  congr 1
  funext i
  exact propext (recursiveCritical_congr hs)

private theorem survivingCriticalIndices_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t scope : ℕ}
    (hs0 : GenLimit.sample u t = GenLimit.sample v t)
    (hs1 : GenLimit.sample u (t + 1) = GenLimit.sample v (t + 1)) :
    GenLimit.PatientMachine.survivingCriticalIndices C u t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C v t scope := by
  classical
  unfold GenLimit.PatientMachine.survivingCriticalIndices
  congr 1
  funext i
  apply propext
  simp only [recursiveCritical_congr hs0, recursiveCritical_congr hs1]

private theorem highestCritical_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t scope fallback : ℕ}
    (hs : GenLimit.sample u t = GenLimit.sample v t) :
    GenLimit.PatientMachine.highestCritical C u t scope fallback =
      GenLimit.PatientMachine.highestCritical C v t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr hs]

private theorem highestSurvivor_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t scope fallback : ℕ}
    (hs0 : GenLimit.sample u t = GenLimit.sample v t)
    (hs1 : GenLimit.sample u (t + 1) = GenLimit.sample v (t + 1)) :
    GenLimit.PatientMachine.highestSurvivor C u t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C v t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr hs0 hs1]

private theorem lowestConsistentInScope_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t scope fallback : ℕ}
    (hs : GenLimit.sample u t = GenLimit.sample v t) :
    GenLimit.PatientMachine.lowestConsistentInScope C u t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C v t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr hs]

private theorem lowestConsistent_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t fallback : ℕ}
    (hs : GenLimit.sample u t = GenLimit.sample v t) :
    GenLimit.PatientMachine.lowestConsistent C u t fallback =
      GenLimit.PatientMachine.lowestConsistent C v t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  have hp : (fun i => GenLimit.Consistent C u t i) =
      (fun i => GenLimit.Consistent C v t i) := by
    funext i
    apply propext
    simp [GenLimit.Consistent, hs]
  by_cases hu : ∃ i, GenLimit.Consistent C u t i
  · have hv : ∃ i, GenLimit.Consistent C v t i := by
      simpa only [← hp] using hu
    rw [dif_pos hu, dif_pos hv]
    apply Nat.find_congr (Nat.find_spec hu)
    intro n hn
    simp [GenLimit.Consistent, hs]
  · have hv : ¬∃ i, GenLimit.Consistent C v t i := by
      simpa only [← hp] using hu
    rw [dif_neg hu, dif_neg hv]

private theorem stableDecision_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t : ℕ}
    (hs1 : GenLimit.sample u (t + 1) = GenLimit.sample v (t + 1))
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.stableDecision C u t old =
      GenLimit.PatientMachine.stableDecision C v t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  split
  · let a := GenLimit.PatientMachine.highestCritical C u (t + 1)
      (old.scope + 1) old.focus
    let b := GenLimit.PatientMachine.highestCritical C v (t + 1)
      (old.scope + 1) old.focus
    have hab : a = b := highestCritical_congr hs1
    simp only [a, b, hab]
  · rfl

private theorem backtrackDecision_congr
    {C : GenLimit.LanguageFamily} {u v : Stream} {t : ℕ}
    (hs0 : GenLimit.sample u t = GenLimit.sample v t)
    (hs1 : GenLimit.sample u (t + 1) = GenLimit.sample v (t + 1))
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.backtrackDecision C u t old =
      GenLimit.PatientMachine.backtrackDecision C v t old := by
  classical
  have hci := consistentIndices_congr (C := C) (scope := old.scope) hs1
  have hsi := survivingCriticalIndices_congr
    (C := C) (scope := old.scope) hs0 hs1
  have hhs := highestSurvivor_congr
    (C := C) (scope := old.scope) (fallback := old.focus) hs0 hs1
  have hlcis := lowestConsistentInScope_congr
    (C := C) (scope := old.scope) (fallback := old.focus) hs1
  have hlc := lowestConsistent_congr
    (C := C) (fallback := old.focus) hs1
  have hp : (∃ j, GenLimit.Consistent C u (t + 1) j) ↔
      ∃ j, GenLimit.Consistent C v (t + 1) j := by
    simp [GenLimit.Consistent, hs1]
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [hci, hsi, hhs, hlcis, hlc, hp]

private theorem decision_congr
    (O : GenLimit.OracleFamily) {u v : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → u n = v n)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.decide O.language u t old =
      GenLimit.PatientMachine.decide O.language v t old := by
  classical
  have hs1 : GenLimit.sample u (t + 1) = GenLimit.sample v (t + 1) :=
    sample_eq_of_eq_of_lt h
  have hs0 : GenLimit.sample u t = GenLimit.sample v t :=
    sample_eq_of_eq_of_lt (fun n hn => h n (Nat.lt.step hn))
  unfold GenLimit.PatientMachine.decide
  have hc : GenLimit.Consistent O.language u (t + 1) old.focus ↔
      GenLimit.Consistent O.language v (t + 1) old.focus := by
    simp [GenLimit.Consistent, hs1]
  exact if_congr hc (stableDecision_congr hs1 old)
    (backtrackDecision_congr hs0 hs1 old)

private theorem leastAvailable_congr
    (O : GenLimit.OracleFamily) {u v : Stream} {t : ℕ}
    (h : ∀ n, n < t → u n = v n)
    (used : Finset ℕ) (focus : ℕ) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite' u t used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' v t used focus := by
  classical
  have hs : GenLimit.sample u t = GenLimit.sample v t :=
    sample_eq_of_eq_of_lt h
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  apply propext
  simp only [GenLimit.PatientMachine.Available, hs]

private theorem processRound_congr
    (O : GenLimit.OracleFamily) {u v : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → u n = v n)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.processRound O u t old =
      GenLimit.PatientMachine.processRound O v t old := by
  classical
  unfold GenLimit.PatientMachine.processRound
  rw [decision_congr O h old]
  simp only
  rw [leastAvailable_congr O h]

private theorem run_congr
    (O : GenLimit.OracleFamily) {u v : Stream} {t : ℕ}
    (h : ∀ n, n < t → u n = v n) :
    GenLimit.PatientMachine.run O u t =
      GenLimit.PatientMachine.run O v t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      rw [ih (fun n hn => h n (Nat.lt.step hn))]
      exact processRound_congr O (fun n hn => h n hn) _

private theorem output_congr
    (O : GenLimit.OracleFamily) {u v : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → u n = v n) :
    GenLimit.PatientMachine.output O u t =
      GenLimit.PatientMachine.output O v t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr O h]

noncomputable def onlineOfOracle (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixExtension xs) t

private theorem follows_onlineOfOracle
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlineOfOracle O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  symm
  apply output_congr O
  intro n hn
  simp [prefixExtension, hn]

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨onlineOfOracle O, ?_⟩
  intro i input hP
  refine ⟨GenLimit.PatientMachine.output O input,
    follows_onlineOfOracle O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ :=
      (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input hP).1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hinput, houtput⟩ := hT t ht
    refine ⟨hmem, ?_, ?_⟩
    · intro hx
      rw [GenLimit.mem_sample_iff] at hx
      obtain ⟨s, hs, heq⟩ := hx
      exact hinput s (Nat.lt_succ_iff.mp hs) heq
    · intro s hs heq
      exact houtput s hs heq
  · exact (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input hP).2

open Filter
open scoped Topology
open GenLimit.PatientScope

theorem prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    prefixCount (A ∪ B) n ≤ prefixCount A n + prefixCount B n := by
  classical
  unfold prefixCount
  calc
    (prefixFinset (A ∪ B) n).card ≤
        (prefixFinset A n ∪ prefixFinset B n).card := by
      apply Finset.card_le_card
      intro x hx
      rw [mem_prefixFinset] at hx
      simp only [Finset.mem_union, mem_prefixFinset]
      rcases hx.2 with hxA | hxB
      · exact Or.inl ⟨hx.1, hxA⟩
      · exact Or.inr ⟨hx.1, hxB⟩
    _ ≤ (prefixFinset A n).card + (prefixFinset B n).card :=
      Finset.card_union_le _ _

 theorem prefixCount_le_ncard {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    prefixCount F n ≤ F.ncard := by
  classical
  unfold prefixCount
  rw [Set.ncard_eq_toFinset_card F hF]
  apply Finset.card_le_card
  intro x hx
  exact hF.mem_toFinset.mpr (mem_prefixFinset.mp hx).2

theorem finite_extension_half
    (A K R : Set ℕ) (hK : K.Infinite) (hKR : K ⊆ R)
    (hfin : (R \ K).Finite)
    (hhalf : (1 / 2 : ℝ) ≤ relativeLowerDensity (A ∩ R) R) :
    (1 / 2 : ℝ) ≤ relativeLowerDensity (A ∩ K) K := by
  let f : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ R) n : ℝ) / prefixCount R n
  let g : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / prefixCount K n
  let e : ℕ → ℝ := fun n =>
    (R \ K).ncard / (prefixCount K n : ℝ)
  have hcast : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_prefixCount_atTop hK)
  have he : Tendsto e atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcast
  have hcomp : ∀ᶠ n : ℕ in atTop, f n - e n ≤ g n := by
    have hKpos : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
      (tendsto_prefixCount_atTop hK).eventually (eventually_gt_atTop 0)
    filter_upwards [hKpos] with n hn
    have hnum : prefixCount (A ∩ R) n ≤
        prefixCount (A ∩ K) n + (R \ K).ncard := by
      calc
        prefixCount (A ∩ R) n ≤
            prefixCount ((A ∩ K) ∪ (R \ K)) n :=
          prefixCount_mono (by
            intro x hx
            by_cases hxK : x ∈ K
            · exact Or.inl ⟨hx.1, hxK⟩
            · exact Or.inr ⟨hx.2, hxK⟩) n
        _ ≤ prefixCount (A ∩ K) n + prefixCount (R \ K) n :=
          prefixCount_union_le _ _ _
        _ ≤ prefixCount (A ∩ K) n + (R \ K).ncard :=
          Nat.add_le_add_left (prefixCount_le_ncard hfin n) _
    have hden : prefixCount K n ≤ prefixCount R n := prefixCount_mono hKR n
    have hnR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hdenR : (prefixCount K n : ℝ) ≤ prefixCount R n := by exact_mod_cast hden
    have hnumR : (prefixCount (A ∩ R) n : ℝ) ≤
        prefixCount (A ∩ K) n + (R \ K).ncard := by exact_mod_cast hnum
    dsimp [f, g, e]
    have hrnonneg : (0 : ℝ) ≤ prefixCount (A ∩ R) n := by positivity
    have hdiv : (prefixCount (A ∩ R) n : ℝ) / prefixCount R n ≤
        (prefixCount (A ∩ R) n : ℝ) / prefixCount K n := by
      exact div_le_div_of_nonneg_left hrnonneg hnR hdenR
    calc
      (prefixCount (A ∩ R) n : ℝ) / prefixCount R n -
          (R \ K).ncard / prefixCount K n
          ≤ (prefixCount (A ∩ R) n : ℝ) / prefixCount K n -
              (R \ K).ncard / prefixCount K n := sub_le_sub_right hdiv _
      _ = ((prefixCount (A ∩ R) n : ℝ) - (R \ K).ncard) /
            prefixCount K n := by rw [sub_div]
      _ ≤ (prefixCount (A ∩ K) n : ℝ) / prefixCount K n := by
        apply div_le_div_of_nonneg_right _ hnR.le
        linarith
  have hf_lower : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hf_upper : ∀ n, f n ≤ 1 := by
    intro n
    by_cases hn : prefixCount R n = 0
    · simp [f, hn]
    · change (prefixCount (A ∩ R) n : ℝ) / prefixCount R n ≤ 1
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  have hg_lower : ∀ n, 0 ≤ g n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hg_upper : ∀ n, g n ≤ 1 := by
    intro n
    by_cases hn : prefixCount K n = 0
    · simp [g, hn]
    · change (prefixCount (A ∩ K) n : ℝ) / prefixCount K n ≤ 1
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  rw [relativeLowerDensity] at hhalf ⊢
  change (1 / 2 : ℝ) ≤ liminf g atTop
  change (1 / 2 : ℝ) ≤ liminf f atTop at hhalf
  by_contra hnot
  have hlt : liminf g atTop < (1 / 2 : ℝ) := lt_of_not_ge hnot
  let ε : ℝ := ((1 / 2 : ℝ) - liminf g atTop) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hevent : ∀ᶠ n in atTop, e n < ε := (he.eventually (gt_mem_nhds hε))
  have hcompare : ∀ᶠ n in atTop, f n - ε ≤ g n := by
    filter_upwards [hcomp, hevent] with n hfg heps
    linarith
  have hleftBounded : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => f n - ε) :=
    isBoundedUnder_of ⟨-ε, fun n => by linarith [hf_lower n]⟩
  have hlim := liminf_le_liminf hcompare hleftBounded
    (isCoboundedUnder_ge_of_le atTop hg_upper)
  rw [liminf_sub_const atTop f ε
    (isCoboundedUnder_ge_of_le atTop hf_upper)
    (isBoundedUnder_of ⟨0, hf_lower⟩)] at hlim
  dsimp [ε] at hlim
  linarith


noncomputable def finiteAdditionFamily
    (family : ℕ → Language) (code : ℕ) : Language :=
  let data := Nat.unpair code
  family data.1 ∪ (Finset.equivBitIndices data.2 : Set ℕ)

theorem finiteAdditionFamily_infinite
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) (code : ℕ) :
    (finiteAdditionFamily family code).Infinite := by
  exact (hInfinite (Nat.unpair code).1).mono Set.subset_union_left

noncomputable def finiteAdditionCode (i : ℕ) (F : Set ℕ) (hF : F.Finite) : ℕ :=
  Nat.pair i (Finset.equivBitIndices.symm hF.toFinset)

theorem finiteAdditionFamily_code
    (family : ℕ → Language) (i : ℕ) (F : Set ℕ) (hF : F.Finite) :
    finiteAdditionFamily family (finiteAdditionCode i F hF) = family i ∪ F := by
  classical
  simp [finiteAdditionFamily, finiteAdditionCode, Set.Finite.coe_toFinset]

private theorem range_diff_finite
    (input : Stream) (K : Set ℕ)
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  apply hbad.image input |>.subset
  intro x hx
  obtain ⟨t, rfl⟩ := hx.1
  exact ⟨t, by simpa [GenLimit.Generic.ViolationIndices] using hx.2⟩

private theorem finite_set_seen
    (input : Stream) (F : Set ℕ) (hF : F.Finite)
    (hsub : F ⊆ Set.range input) :
    ∃ U, F ⊆ GenLimit.sample input U := by
  classical
  induction F, hF using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x F hxF hfinite ih =>
      obtain ⟨U, hU⟩ := ih (fun y hy => hsub (Set.mem_insert_of_mem x hy))
      obtain ⟨t, ht⟩ := hsub (Set.mem_insert x F)
      refine ⟨max U (t + 1), ?_⟩
      intro y hy
      rcases hy with rfl | hy
      · exact GenLimit.mem_sample_iff.mpr
          ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) (Nat.le_max_right _ _), ht⟩
      · exact GenLimit.sample_mono (Nat.le_max_left _ _) (hU hy)

theorem finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let expanded := finiteAdditionFamily family
  have hexpanded : ∀ j, (expanded j).Infinite :=
    finiteAdditionFamily_infinite family hInfinite
  obtain ⟨gen, hgen⟩ := hpositive expanded hexpanded
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  let F := Set.range input \ family i
  have hF : F.Finite := range_diff_finite input (family i) hpresentation.2
  let j := finiteAdditionCode i F hF
  have hj : expanded j = family i ∪ F := finiteAdditionFamily_code family i F hF
  have hrange : Set.range input = family i ∪ F := by
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hxK : x ∈ family i
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    · intro x hx
      rcases hx with hx | hx
      · exact hpresentation.1 hx
      · exact hx.1
  have hpresents : GenLimit.Presents input (expanded j) := by
    rw [hj, ← hrange]
    rfl
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hnovel
    have hFsub : F ⊆ Set.range input := Set.diff_subset
    obtain ⟨U, hseen⟩ := finite_set_seen input F hF hFsub
    refine ⟨max T U, ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (Nat.le_max_left _ _) ht
    have htU : U ≤ t + 1 :=
      le_trans (Nat.le_max_right _ _) (le_trans ht (Nat.le_succ t))
    obtain ⟨houtR, hfresh, huniq⟩ := hT t htT
    refine ⟨?_, hfresh, huniq⟩
    rw [hj] at houtR
    rcases houtR with houtK | houtF
    · exact houtK
    · exact False.elim (hfresh (GenLimit.sample_mono htU (hseen houtF)))
  · exact finite_extension_half
      (GenLimit.GeneratorFirst input output) (family i) (expanded j)
      (hInfinite i) (by rw [hj]; exact Set.subset_union_left)
      (by
        rw [hj]
        apply hF.subset
        intro x hx
        exact hx.1.resolve_left hx.2)
      hdensity


end Case025Formalization

open Case025Formalization

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Case025Formalization.finite_noise_transfer
    Case025Formalization.stage3_positive_engine
