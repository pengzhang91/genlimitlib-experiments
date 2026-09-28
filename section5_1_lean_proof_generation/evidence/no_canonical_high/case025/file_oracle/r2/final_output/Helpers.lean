import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Logic.Equiv.Finset

open Filter Topology

namespace Stage3Case025

noncomputable section

private def decodedFinset (n : ℕ) : Finset ℕ :=
  (Encodable.decode n).getD ∅

private def expandedFamily (family : ℕ → Language) : ℕ → Language :=
  fun n => family n.unpair.1 ∪ (decodedFinset n.unpair.2 : Set ℕ)

private theorem expandedFamily_infinite
    {family : ℕ → Language} (hinf : ∀ i, (family i).Infinite) :
    ∀ n, (expandedFamily family n).Infinite := by
  intro n
  exact (hinf n.unpair.1).mono Set.subset_union_left

private noncomputable def expandedOracle
    (family : ℕ → Language) (hinf : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily := by
  classical
  exact
    { language := expandedFamily family
      infinite' := expandedFamily_infinite hinf
      query := fun i x => decide (x ∈ expandedFamily family i)
      query_spec := by simp }

private def prefixStream {t : ℕ} (xs : Fin t → ℕ) : Stream :=
  fun n => if h : n < t then xs ⟨n, h⟩ else 0

private theorem prefixStream_eq {t : ℕ} (xs : Fin t → ℕ) (i : Fin t) :
    prefixStream xs i = xs i := by
  simp [prefixStream, i.isLt]

private theorem sample_eq_of_eq_before
    {a b : Stream} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, hnx⟩
    exact ⟨n, hn, (h n hn).symm.trans hnx⟩
  · rintro ⟨n, hn, hnx⟩
    exact ⟨n, hn, (h n hn).trans hnx⟩

private theorem consistent_iff_of_sample_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, h]

private theorem recursiveCritical_iff_of_sample_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [GenLimit.RecursiveCritical] using
            (consistent_iff_of_sample_eq (i := 0) h)
      | succ i =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨(consistent_iff_of_sample_eq h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hsub⟩
            refine ⟨(consistent_iff_of_sample_eq h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

private theorem consistentIndices_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_iff_of_sample_eq h]

private theorem criticalIndices_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_iff_of_sample_eq h i]

private theorem survivingCriticalIndices_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (ht : GenLimit.sample a t = GenLimit.sample b t)
    (ht1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_iff_of_sample_eq ht i,
    recursiveCritical_iff_of_sample_eq ht1 i]

private theorem highestCritical_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq h]

private theorem highestSurvivor_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (ht : GenLimit.sample a t = GenLimit.sample b t)
    (ht1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq ht ht1]

private theorem lowestConsistentInScope_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq h]

private theorem lowestConsistent_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t fallback : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_iff_of_sample_eq h).mp hi⟩
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr' (hp := ha) (hq := hb)
      (consistent_iff_of_sample_eq h)
  · have hb : ¬ ∃ i, GenLimit.Consistent C b t i := by
      intro hex
      obtain ⟨i, hi⟩ := hex
      exact ha ⟨i, (consistent_iff_of_sample_eq h).mpr hi⟩
    simp [ha, hb]

private theorem backtrackDecision_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (ht : GenLimit.sample a t = GenLimit.sample b t)
    (ht1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  have hcon := consistentIndices_eq (C := C) (scope := old.scope) ht1
  have hsurv := survivingCriticalIndices_eq (C := C) (scope := old.scope) ht ht1
  have hhigh := highestSurvivor_eq (C := C) (scope := old.scope)
    (fallback := old.focus) ht ht1
  have hscope := lowestConsistentInScope_eq (C := C) (scope := old.scope)
    (fallback := old.focus) ht1
  have hglobal := lowestConsistent_eq (C := C) (fallback := old.focus) ht1
  have hall : (∃ j, GenLimit.Consistent C a (t + 1) j) ↔
      ∃ j, GenLimit.Consistent C b (t + 1) j := by
    constructor <;> rintro ⟨j, hj⟩
    · exact ⟨j, (consistent_iff_of_sample_eq ht1).mp hj⟩
    · exact ⟨j, (consistent_iff_of_sample_eq ht1).mpr hj⟩
  simp only [GenLimit.PatientMachine.backtrackDecision]
  rw [hcon, hsurv, hhigh, hscope, hglobal]
  by_cases ha : ∃ j, GenLimit.Consistent C a (t + 1) j
  · have hb := hall.mp ha
    simp [ha, hb]
  · have hb : ¬ ∃ j, GenLimit.Consistent C b (t + 1) j :=
      fun h => ha (hall.mpr h)
    simp [ha, hb]

private theorem stableDecision_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (ht1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  have hcritical := highestCritical_eq (C := C) (t := t + 1)
    (scope := old.scope + 1) (fallback := old.focus) ht1
  simp only [GenLimit.PatientMachine.stableDecision]
  split <;> simp [hcritical]

private theorem decide_eq
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (ht : GenLimit.sample a t = GenLimit.sample b t)
    (ht1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  have hconsistent := consistent_iff_of_sample_eq (C := C)
    (i := old.focus) ht1
  simp only [GenLimit.PatientMachine.decide]
  by_cases ha : GenLimit.Consistent C a (t + 1) old.focus
  · have hb := hconsistent.mp ha
    simp [ha, hb, stableDecision_eq (C := C) old ht1]
  · have hb : ¬ GenLimit.Consistent C b (t + 1) old.focus :=
      fun h => ha (hconsistent.mpr h)
    simp [ha, hb, backtrackDecision_eq (C := C) old ht ht1]

private theorem leastAvailable_eq
    {C : GenLimit.LanguageFamily} (hinf : ∀ i, (C i).Infinite)
    {a b : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.leastAvailable C hinf a t used focus =
      GenLimit.PatientMachine.leastAvailable C hinf b t used focus := by
  classical
  let ha := GenLimit.PatientMachine.available_exists C hinf a t used focus
  let hb := GenLimit.PatientMachine.available_exists C hinf b t used focus
  simp only [GenLimit.PatientMachine.leastAvailable]
  exact Nat.find_congr' (hp := ha) (hq := hb) (by
    intro n
    simp only [GenLimit.PatientMachine.Available, h])

private theorem processRound_eq
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (ht : GenLimit.sample a t = GenLimit.sample b t)
    (ht1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hd := decide_eq (C := O.language) old ht ht1
  have hx := leastAvailable_eq O.infinite' old.used
    (GenLimit.PatientMachine.decide O.language b t old).focus ht1
  simp only [GenLimit.PatientMachine.processRound]
  rw [hd, hx]

private theorem run_eq_of_eq_before
    (O : GenLimit.OracleFamily) {a b : Stream} :
    ∀ t, (∀ n, n < t → a n = b n) →
      GenLimit.PatientMachine.run O a t =
        GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      have hold := ih (fun n hn => h n (Nat.lt.step hn))
      rw [hold]
      apply processRound_eq
      · apply sample_eq_of_eq_before
        exact fun n hn => h n (Nat.lt.step hn)
      · apply sample_eq_of_eq_before
        simpa only [Nat.succ_eq_add_one] using h

private theorem output_eq_of_eq_before
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_eq_before O (t + 1) h]

private def patientOnlineGenerator (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixStream xs) t

private theorem patientOnlineGenerator_follows
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_eq_of_eq_before
  intro n hn
  symm
  exact prefixStream_eq (fun i : Fin (t + 1) => input i) ⟨n, hn⟩

private theorem exists_expanded_index
    (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    ∃ z, expandedFamily family z = family i ∪ (F : Set ℕ) := by
  refine ⟨Nat.pair i (Encodable.encode F), ?_⟩
  simp [expandedFamily, decodedFinset, Encodable.encodek]

private theorem range_eq_target_union_noise
    {input : Stream} {K : Language} (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ (Set.range input \ K) := by
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · rintro (hx | hx)
    · exact hcover hx
    · exact hx.1

private theorem noise_finite
    {input : Stream} {K : Language}
    (hnoise : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  have himage : Set.range input \ K =
      input '' GenLimit.Generic.ViolationIndices input (fun x => x ∈ K) := by
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, ht⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, rfl⟩, ht⟩
  rw [himage]
  exact hnoise.image input

private theorem finset_eventually_subset_sample
    (input : Stream) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ Set.range input) :
    ∃ T, ∀ t, T ≤ t → S ⊆ GenLimit.sample input t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, fun _ _ => Finset.empty_subset _⟩
  | @insert x S hx ih =>
      obtain ⟨Tx, hTx⟩ :=
        GenLimit.eventually_mem_sample_of_presents
          (show GenLimit.Presents input (Set.range input) from rfl)
          (hS (show x ∈ insert x S by simp))
      obtain ⟨TS, hTS⟩ := ih (by
        intro y hy
        exact hS (by simp [hy]))
      refine ⟨max Tx TS, ?_⟩
      intro t ht y hy
      simp only [Finset.mem_insert] at hy
      cases hy with
      | inl hy =>
          subst y
          exact hTx t ((Nat.le_max_left _ _).trans ht)
      | inr hy =>
          exact hTS t ((Nat.le_max_right _ _).trans ht) hy

private theorem novel_transfer
    {input output : Stream} {K E : Language}
     (hfinite : (E \ K).Finite)
    (hseen : E \ K ⊆ Set.range input)
    (hgen : GenLimit.NovelGeneratesInLimit input output E) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgen, hTgen⟩ := hgen
  obtain ⟨Tseen, hTseen⟩ :=
    finset_eventually_subset_sample input hfinite.toFinset (by
      intro x hx
      exact hseen ((Set.Finite.mem_toFinset hfinite).mp hx))
  refine ⟨max Tgen Tseen, ?_⟩
  intro t ht
  have hgood := hTgen t ((Nat.le_max_left _ _).trans ht)
  have hsample : hfinite.toFinset ⊆ GenLimit.sample input t :=
    hTseen t ((Nat.le_max_right _ _).trans ht)
  refine ⟨?_, hgood.2.1, hgood.2.2⟩
  by_contra hout
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hgood.1, hout⟩
  exact hgood.2.1 (GenLimit.sample_mono (Nat.le_succ t) (hsample hbad))

private theorem prefixCount_finite_bound
    {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  exact Finset.card_le_card (by
    intro x hx
    exact (Set.Finite.mem_toFinset hF).mpr
      (GenLimit.PatientScope.mem_prefixFinset.mp hx).2)

private theorem prefixCount_le_add_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  have hsub : GenLimit.PatientScope.prefixFinset A n ⊆
      GenLimit.PatientScope.prefixFinset B n ∪ hfinite.toFinset := by
    intro x hx
    have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hx).1, hxB⟩)
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset hfinite).mpr ⟨hxA, hxB⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private theorem density_transfer_finite_extension
    {A K E : Language} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite)
    (hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E) :
    (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
      (GenLimit.PatientScope.prefixCount E n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcountKR : Tendsto (fun n =>
      (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcountKR
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    have hpos : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount K n :=
      hcountK.eventually (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hdenK : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdiff : ((A ∩ E) \ (A ∩ K)).Finite := by
      apply hfinite.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hsetsub : ((A ∩ E) \ (A ∩ K)) ⊆ E \ K := by
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hcard : hdiff.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      exact (Set.Finite.mem_toFinset hfinite).mpr
        (hsetsub ((Set.Finite.mem_toFinset hdiff).mp hx))
    have hnum : GenLimit.PatientScope.prefixCount (A ∩ E) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card :=
      (prefixCount_le_add_finite hdiff n).trans (Nat.add_le_add_left hcard _)
    have hden : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount E n :=
      GenLimit.PatientScope.prefixCount_mono hKE n
    have hnumR :
        (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (A ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hnum
    have hdenER : (0 : ℝ) < GenLimit.PatientScope.prefixCount E n := by
      exact lt_of_lt_of_le hdenK (by exact_mod_cast hden)
    dsimp only [source, target, error]
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          GenLimit.PatientScope.prefixCount E n ≤
        (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          GenLimit.PatientScope.prefixCount K n := by
            gcongr
      _ ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℕ) +
            hfinite.toFinset.card : ℕ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            gcongr
      _ = (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n +
          (hfinite.toFinset.card : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by
            push_cast
            rw [add_div]
  have htarget_nonneg : ∀ n, 0 ≤ target n := by
    intro n
    positivity
  have htarget_le_one : ∀ n, target n ≤ 1 := by
    intro n
    dsimp only [target]
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  rw [GenLimit.PatientScope.relativeLowerDensity] at hhalf ⊢
  change (1 / 2 : ℝ) ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  have hysource : y < liminf source atTop := by
    exact lt_of_lt_of_le hy hhalf
  obtain ⟨r, hyr, hrsource⟩ := exists_between hysource
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrsource
      (isBoundedUnder_of ⟨0, fun n => by dsimp [source]; positivity⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr he hp
  linarith

theorem positivePresentationHalfDensity : PositivePresentationHalfDensity := by
  intro family hinf
  let O := expandedOracle family hinf
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hP
  refine ⟨GenLimit.PatientMachine.output O input,
    patientOnlineGenerator_follows O input, ?_⟩
  have hp : GenLimit.Presents input
      (O.language (Nat.pair i (Encodable.encode (∅ : Finset ℕ)))) := by
    simpa [O, expandedOracle, expandedFamily, decodedFinset,
      Encodable.encodek] using hP
  have hmain := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    O input hp
  have hlang : O.language (Nat.pair i (Encodable.encode (∅ : Finset ℕ))) =
      family i := by
    ext x
    simp [O, expandedOracle, expandedFamily, decodedFinset,
      Encodable.encodek]
  obtain ⟨T, hT⟩ := hmain.1
  refine ⟨⟨T, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨hmem, hinput, houtput⟩ := hT t ht
    refine ⟨hlang ▸ hmem, ?_, houtput⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact hinput s (by omega) heq
  · have hdensity := hmain.2
    unfold GenLimit.PatientMachine.patientLowerDensity at hdensity
    rw [hlang] at hdensity
    exact hdensity

theorem finiteNoiseTransfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinf
  let expanded : ℕ → Language := expandedFamily family
  have hexpInf : ∀ z, (expanded z).Infinite := expandedFamily_infinite hinf
  obtain ⟨gen, hgen⟩ := hpositive expanded hexpInf
  refine ⟨gen, ?_⟩
  intro i input hinput
  let noiseSet : Set ℕ := Set.range input \ family i
  have hnoiseFinite : noiseSet.Finite := noise_finite hinput.2
  let noise : Finset ℕ := hnoiseFinite.toFinset
  obtain ⟨z, hz⟩ := exists_expanded_index family i noise
  have hnoiseCoe : (noise : Set ℕ) = noiseSet := by
    exact Set.Finite.coe_toFinset hnoiseFinite
  have hrange : Set.range input = expanded z := by
    change Set.range input = expandedFamily family z
    rw [hz, hnoiseCoe]
    exact range_eq_target_union_noise hinput.1
  obtain ⟨output, hfollows, hnovel, hdensity⟩ :=
    hgen z input (show GenLimit.Presents input (expanded z) from hrange)
  refine ⟨output, hfollows, ?_, ?_⟩
  · apply novel_transfer (K := family i) (E := expanded z)
      (hfinite := ?_) (hseen := ?_) hnovel
    · rw [← hrange]
      exact hnoiseFinite
    · rw [← hrange]
      exact fun _ hx => hx.1
  · apply density_transfer_finite_extension
      (A := GenLimit.GeneratorFirst input output)
      (K := family i) (E := expanded z) (hK := hinf i)
      (hKE := by rw [← hrange]; exact hinput.1)
      (hfinite := by rw [← hrange]; exact hnoiseFinite)
      (hhalf := hdensity)

end

end Stage3Case025
