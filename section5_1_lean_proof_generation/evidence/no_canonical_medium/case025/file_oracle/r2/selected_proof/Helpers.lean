import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Combinatorics.Colex
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Stage3Case025

noncomputable def oracleOfFamily (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily := by
  classical
  exact
    { language := family
      infinite' := hinf
      query := fun i x => decide (x ∈ family i)
      query_spec := by simp }

noncomputable def prefixCompletion (t : ℕ) (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

@[simp] theorem prefixCompletion_apply {t : ℕ} (xs : Fin (t + 1) → ℕ)
    {n : ℕ} (hn : n < t + 1) :
    prefixCompletion t xs n = xs ⟨n, hn⟩ := by
  simp [prefixCompletion, hn]

private theorem sample_eq_of_eq_before
    {a b : Stream} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  classical
  unfold GenLimit.sample
  apply Finset.image_congr
  intro k hk
  exact h k (Finset.mem_range.mp hk)

private theorem consistent_congr
    {family : ℕ → Language} {a b : Stream} {n i : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.Consistent family a n i ↔ GenLimit.Consistent family b n i := by
  simp only [GenLimit.Consistent, sample_eq_of_eq_before h]

private theorem recursiveCritical_congr
    {family : ℕ → Language} {a b : Stream} {n i : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.RecursiveCritical family a n i ↔
      GenLimit.RecursiveCritical family b n i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [GenLimit.RecursiveCritical] using
          (consistent_congr (family := family) (i := 0) h)
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_congr h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hprev j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hprev⟩
            refine ⟨(consistent_congr h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hprev j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

private theorem processRound_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hsamp : ∀ m, m ≤ t + 1 → GenLimit.sample a m = GenLimit.sample b m := by
    intro m hm
    apply sample_eq_of_eq_before
    intro k hk
    exact h k (lt_of_lt_of_le hk hm)
  have hc0 : ∀ i, GenLimit.Consistent O.language a t i ↔
      GenLimit.Consistent O.language b t i := fun i =>
    consistent_congr (fun k hk => h k (Nat.lt.step hk))
  have hc1 : ∀ i, GenLimit.Consistent O.language a (t + 1) i ↔
      GenLimit.Consistent O.language b (t + 1) i := fun i => consistent_congr h
  have hr0 : ∀ i, GenLimit.RecursiveCritical O.language a t i ↔
      GenLimit.RecursiveCritical O.language b t i := fun i =>
    recursiveCritical_congr (fun k hk => h k (Nat.lt.step hk))
  have hr1 : ∀ i, GenLimit.RecursiveCritical O.language a (t + 1) i ↔
      GenLimit.RecursiveCritical O.language b (t + 1) i := fun i =>
    recursiveCritical_congr h
  have hcons (scope : ℕ) :
      GenLimit.PatientMachine.consistentIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.consistentIndices O.language b (t + 1) scope := by
    ext i
    simp [GenLimit.PatientMachine.consistentIndices, hc1]
  have hcrit (scope : ℕ) :
      GenLimit.PatientMachine.criticalIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices O.language b (t + 1) scope := by
    ext i
    simp [GenLimit.PatientMachine.criticalIndices, hr1]
  have hsurv (scope : ℕ) :
      GenLimit.PatientMachine.survivingCriticalIndices O.language a t scope =
        GenLimit.PatientMachine.survivingCriticalIndices O.language b t scope := by
    ext i
    simp [GenLimit.PatientMachine.survivingCriticalIndices, hr0, hr1]
  have hhighest (scope fallback : ℕ) :
      GenLimit.PatientMachine.highestCritical O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical O.language b (t + 1) scope fallback := by
    simp only [GenLimit.PatientMachine.highestCritical, hcrit scope]
  have hhighSurv (scope fallback : ℕ) :
      GenLimit.PatientMachine.highestSurvivor O.language a t scope fallback =
        GenLimit.PatientMachine.highestSurvivor O.language b t scope fallback := by
    simp only [GenLimit.PatientMachine.highestSurvivor, hsurv scope]
  have hlowScope (scope fallback : ℕ) :
      GenLimit.PatientMachine.lowestConsistentInScope O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope O.language b (t + 1) scope fallback := by
    simp only [GenLimit.PatientMachine.lowestConsistentInScope, hcons scope]
  have hlowGlobal (fallback : ℕ) :
      GenLimit.PatientMachine.lowestConsistent O.language a (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent O.language b (t + 1) fallback := by
    unfold GenLimit.PatientMachine.lowestConsistent
    by_cases ha : ∃ i, GenLimit.Consistent O.language a (t + 1) i
    · have hb : ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        obtain ⟨i, hi⟩ := ha
        exact ⟨i, (hc1 i).mp hi⟩
      simp only [dif_pos ha, dif_pos hb]
      exact Nat.find_congr' (fun {i} => hc1 i)
    · have hb : ¬ ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        rintro ⟨i, hi⟩
        exact ha ⟨i, (hc1 i).mpr hi⟩
      simp [ha, hb]
  have hstable :
      GenLimit.PatientMachine.stableDecision O.language a t old =
        GenLimit.PatientMachine.stableDecision O.language b t old := by
    unfold GenLimit.PatientMachine.stableDecision
    by_cases hw : 2 ^ old.tau ≤ old.age <;> simp [hw, hhighest]
  have hback :
      GenLimit.PatientMachine.backtrackDecision O.language a t old =
        GenLimit.PatientMachine.backtrackDecision O.language b t old := by
    unfold GenLimit.PatientMachine.backtrackDecision
    rw [hcons old.scope]
    by_cases hn : (GenLimit.PatientMachine.consistentIndices O.language b
        (t + 1) old.scope).Nonempty
    · simp only [dif_pos hn, hsurv old.scope, hhighSurv, hlowScope]
    · simp only [dif_neg hn, hlowGlobal]
      have hex : (∃ j, GenLimit.Consistent O.language a (t + 1) j) ↔
          ∃ j, GenLimit.Consistent O.language b (t + 1) j :=
        exists_congr hc1
      by_cases hb : ∃ j, GenLimit.Consistent O.language b (t + 1) j
      · have ha := hex.mpr hb
        simp [ha, hb]
      · have ha : ¬ ∃ j, GenLimit.Consistent O.language a (t + 1) j :=
          fun ha => hb (hex.mp ha)
        simp [ha, hb]
  have hdecide :
      GenLimit.PatientMachine.decide O.language a t old =
        GenLimit.PatientMachine.decide O.language b t old := by
    unfold GenLimit.PatientMachine.decide
    by_cases ha : GenLimit.Consistent O.language a (t + 1) old.focus
    · have hb := (hc1 old.focus).mp ha
      simp [ha, hb, hstable]
    · have hb : ¬ GenLimit.Consistent O.language b (t + 1) old.focus :=
        fun hb => ha ((hc1 old.focus).mpr hb)
      simp [ha, hb, hback]
  have hleast (focus : ℕ) :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a (t + 1)
          old.used focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b (t + 1)
          old.used focus := by
    unfold GenLimit.PatientMachine.leastAvailable
    apply Nat.find_congr'
    intro x
    simp only [GenLimit.PatientMachine.Available, hsamp (t + 1) le_rfl]
  simp only [GenLimit.PatientMachine.processRound]
  rw [hdecide, hleast]


private theorem run_congr_prefix
    (O : GenLimit.OracleFamily) {a b : Stream} :
    ∀ n, (∀ k, k < n → a k = b k) →
      GenLimit.PatientMachine.run O a n = GenLimit.PatientMachine.run O b n := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      have hab : ∀ k, k < n → a k = b k := fun k hk => h k (Nat.lt.step hk)
      have hrun := ih hab
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ, hrun]
      exact processRound_congr O _ h

private theorem output_congr_prefix
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr_prefix O (t + 1) h]

noncomputable def patientOnlineGenerator
    (family : ℕ → Language) (hinf : ∀ i, (family i).Infinite) : OnlineGenerator :=
  fun t xs _ =>
    GenLimit.PatientMachine.output (oracleOfFamily family hinf)
      (prefixCompletion t xs) t

private theorem patient_follows
    (family : ℕ → Language) (hinf : ∀ i, (family i).Infinite)
    (input : Stream) :
    Follows (patientOnlineGenerator family hinf) input
      (GenLimit.PatientMachine.output (oracleOfFamily family hinf) input) := by
  intro t
  apply output_congr_prefix
  intro k hk
  simp [prefixCompletion, hk]

theorem positivePresentationHalfDensity : PositivePresentationHalfDensity := by
  intro family hinf
  let O := oracleOfFamily family hinf
  refine ⟨patientOnlineGenerator family hinf, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, patient_follows family hinf input, ?_, ?_⟩
  · obtain ⟨hgen, hdens⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
    obtain ⟨T, hT⟩ := hgen
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨hmem, ?_, hnovel⟩
    rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hs, heq⟩
    exact hfresh s (Nat.lt_succ_iff.mp hs) heq
  · exact GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP

set_option maxHeartbeats 800000 in
private theorem relativeLowerDensity_inter_le_of_subset_finite
    (A K E : Set ℕ) (hKE : K ⊆ E) (hfinite : (E \ K).Finite)
    (hK : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let c : ℕ := hfinite.toFinset.card
  let ratioE : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  let ratioK : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let err : ℕ → ℝ := fun n =>
    (c : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcount : ∀ n,
      GenLimit.PatientScope.prefixCount (A ∩ E) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + c := by
    intro n
    classical
    unfold GenLimit.PatientScope.prefixCount
    have hsub :
        GenLimit.PatientScope.prefixFinset (A ∩ E) n ⊆
          GenLimit.PatientScope.prefixFinset (A ∩ K) n ∪ hfinite.toFinset := by
      intro x hx
      rw [Finset.mem_union]
      by_cases hxK : x ∈ K
      · exact Or.inl (GenLimit.PatientScope.mem_prefixFinset.2
          ⟨(GenLimit.PatientScope.mem_prefixFinset.1 hx).1,
            (GenLimit.PatientScope.mem_prefixFinset.1 hx).2.1, hxK⟩)
      · exact Or.inr ((Set.Finite.mem_toFinset hfinite).2
          ⟨(GenLimit.PatientScope.mem_prefixFinset.1 hx).2.2, hxK⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcompare : ∀ᶠ n : ℕ in atTop, ratioE n ≤ ratioK n + err n := by
    have hpos : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hkR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hden := GenLimit.PatientScope.prefixCount_mono hKE n
    have hnum : (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount (A ∩ K) n + c : ℕ) := by
      exact_mod_cast hcount n
    have heR : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n :=
      lt_of_lt_of_le hkR (by exact_mod_cast hden)
    calc
      ratioE n ≤
          (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        dsimp [ratioE]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hkR
          (by exact_mod_cast hden)
      _ ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n + c : ℕ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt hkR)
      _ = ratioK n + err n := by
        simp only [ratioK, err, Nat.cast_add, add_div]
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
    have htR : Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
        atTop atTop := tendsto_natCast_atTop_atTop.comp ht
    exact tendsto_const_nhds.div_atTop htR
  have hratioE_nonneg : ∀ n, 0 ≤ ratioE n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hratioE_le_one : ∀ n, ratioE n ≤ 1 := by
    intro n
    by_cases hz : GenLimit.PatientScope.prefixCount E n = 0
    · simp [ratioE, hz]
    · have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      change (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          (GenLimit.PatientScope.prefixCount E n : ℝ) ≤ 1
      rw [div_le_one hp]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono inter_subset_right n
  have hratioK_le_one : ∀ n, ratioK n ≤ 1 := by
    intro n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratioK, hz]
    · have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      change (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one hp]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono inter_subset_right n
  change liminf ratioE atTop ≤ liminf ratioK atTop
  apply (liminf_le_iff
    (isCoboundedUnder_ge_of_le atTop hratioE_le_one)
    (isBoundedUnder_of ⟨0, hratioE_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hrK, hry⟩ := exists_between hy
  have hfreq : ∃ᶠ n : ℕ in atTop, ratioK n < r :=
    frequently_lt_of_liminf_lt
      (isCoboundedUnder_ge_of_le atTop hratioK_le_one) hrK
  have herrSmall : ∀ᶠ n : ℕ in atTop, err n < y - r :=
    herr.eventually_lt_const (sub_pos.mpr hry)
  exact (hfreq.and_eventually (herrSmall.and hcompare)).mono (by
    intro n hn
    linarith [hn.2.2])




noncomputable def finiteAdditionFamily
    (family : ℕ → Language) (n : ℕ) : Language :=
  family (Nat.unpair n).1 ∪
    (Finset.equivBitIndices (Nat.unpair n).2 : Set ℕ)

theorem finiteAdditionFamily_infinite
    (family : ℕ → Language) (hinf : ∀ i, (family i).Infinite) (n : ℕ) :
    (finiteAdditionFamily family n).Infinite :=
  (hinf (Nat.unpair n).1).mono Set.subset_union_left

private theorem range_diff_finite_of_finitelyManyViolations
    (input : Stream) (K : Language)
    (h : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
  exact h.image input

private theorem finiteAdditionFamily_presents_range
    (family : ℕ → Language) {i : ℕ} {input : Stream}
    (hcover : family i ⊆ Set.range input)
    (hnoise : (Set.range input \ family i).Finite) :
    ∃ j, GenLimit.Presents input (finiteAdditionFamily family j) := by
  classical
  let noiseCode := Finset.equivBitIndices.symm hnoise.toFinset
  let j := Nat.pair i noiseCode
  refine ⟨j, ?_⟩
  change Set.range input = finiteAdditionFamily family j
  have hfinset :
      (Finset.equivBitIndices noiseCode : Set ℕ) =
        Set.range input \ family i := by
    rw [Equiv.apply_symm_apply]
    exact Set.Finite.coe_toFinset hnoise
  rw [finiteAdditionFamily]
  simp only [j, Nat.unpair_pair]
  rw [hfinset]
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ family i
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · rintro (hx | hx)
    · exact hcover hx
    · exact hx.1

private theorem novelGeneratesInLimit_of_finite_extraneous_seen
    {input output : Stream} {K E : Language}
    (hextraneous : (E \ K).Finite)
    (hseen : E \ K ⊆ Set.range input)
    (hgenerate : GenLimit.NovelGeneratesInLimit input output E) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hgenerate
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      (show GenLimit.Presents input (Set.range input) from rfl)
      hextraneous.toFinset (by
        intro x hx
        exact hseen ((Set.Finite.mem_toFinset hextraneous).1 hx))
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have hcorrect := hTgenerate t ((Nat.le_max_left _ _).trans ht)
  have hseenNow : hextraneous.toFinset ⊆ GenLimit.sample input (t + 1) := by
    intro x hx
    simpa [Nat.succ_eq_add_one, GenLimit.sample, GenLimit.Generic.sample] using
      GenLimit.Generic.sample_mono
        ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t))
        (hTseen hx)
  refine ⟨?_, hcorrect.2.1, hcorrect.2.2⟩
  by_contra hxK
  have hxBad : output t ∈ hextraneous.toFinset :=
    (Set.Finite.mem_toFinset hextraneous).2 ⟨hcorrect.1, hxK⟩
  exact hcorrect.2.1 (hseenNow hxBad)


theorem finiteNoiseTransferPrinciple : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinf
  obtain ⟨gen, hgen⟩ :=
    hpositive (finiteAdditionFamily family)
      (finiteAdditionFamily_infinite family hinf)
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  have hnoise : (Set.range input \ family i).Finite :=
    range_diff_finite_of_finitelyManyViolations input (family i) hpresentation.2
  obtain ⟨j, hjPresents⟩ :=
    finiteAdditionFamily_presents_range family hpresentation.1 hnoise
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hjPresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply novelGeneratesInLimit_of_finite_extraneous_seen
      (K := family i) (E := finiteAdditionFamily family j)
      (hnoise.subset (by
        intro x hx
        exact ⟨by rw [hjPresents]; exact hx.1, hx.2⟩))
      (by
        intro x hx
        rw [hjPresents]
        exact hx.1)
      hnovel
  · exact hdensity.trans
      (relativeLowerDensity_inter_le_of_subset_finite
        (GenLimit.GeneratorFirst input output)
        (family i) (finiteAdditionFamily family j)
        (by
          intro x hx
          rw [← hjPresents]
          exact hpresentation.1 hx)
        (hnoise.subset (by
          intro x hx
          exact ⟨by rw [hjPresents]; exact hx.1, hx.2⟩))
        (hinf i))

end Stage3Case025
