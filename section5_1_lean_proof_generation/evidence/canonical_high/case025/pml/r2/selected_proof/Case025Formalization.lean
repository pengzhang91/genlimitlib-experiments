import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Stage3Case025Formalization

open Stage3Case025

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

def completePrefix (t : ℕ) (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

theorem sample_eq_of_eq_below
    {a b : Stream} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem consistent_iff_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_eq_of_eq_below h]

theorem recursiveCritical_iff_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
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
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨(consistent_iff_of_eq_below h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_iff.mpr hj)).mpr hjcrit)
          · rintro ⟨hcon, hsub⟩
            refine ⟨(consistent_iff_of_eq_below h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hsub j hj ((ih j (Nat.lt_succ_iff.mpr hj)).mp hjcrit)

theorem consistentIndices_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_iff_of_eq_below h]

theorem criticalIndices_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_iff_of_eq_below h]

theorem survivingCriticalIndices_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  have ht : ∀ n, n < t → a n = b n :=
    fun n hn => h n (hn.trans (Nat.lt_succ_self t))
  rw [recursiveCritical_iff_of_eq_below ht,
    recursiveCritical_iff_of_eq_below h]

theorem highestCritical_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  simp only [GenLimit.PatientMachine.highestCritical]
  rw [criticalIndices_eq_of_eq_below h]

theorem highestSurvivor_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  simp only [GenLimit.PatientMachine.highestSurvivor]
  rw [survivingCriticalIndices_eq_of_eq_below h]

theorem lowestConsistentInScope_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  simp only [GenLimit.PatientMachine.lowestConsistentInScope]
  rw [consistentIndices_eq_of_eq_below h]

theorem lowestConsistent_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_iff_of_eq_below h).mp hi⟩
    obtain ⟨haCon, haMin⟩ :=
      GenLimit.PatientMachine.lowestConsistent_spec
        (C := C) (stream := a) (fallback := fallback) ha
    obtain ⟨hbCon, hbMin⟩ :=
      GenLimit.PatientMachine.lowestConsistent_spec
        (C := C) (stream := b) (fallback := fallback) hb
    apply le_antisymm
    · by_contra hnot
      have hlt := Nat.lt_of_not_ge hnot
      exact haMin _ hlt ((consistent_iff_of_eq_below h).mpr hbCon)
    · by_contra hnot
      have hlt := Nat.lt_of_not_ge hnot
      exact hbMin _ hlt ((consistent_iff_of_eq_below h).mp haCon)
  · have hb : ¬ ∃ i, GenLimit.Consistent C b t i := by
      rintro ⟨i, hi⟩
      exact ha ⟨i, (consistent_iff_of_eq_below h).mpr hi⟩
    simp [GenLimit.PatientMachine.lowestConsistent, ha, hb]

theorem decide_eq_of_eq_below
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  have hcon := consistent_iff_of_eq_below (C := C) (i := old.focus) h
  have hconsistent := consistentIndices_eq_of_eq_below
    (C := C) (scope := old.scope) h
  have hsurviving := survivingCriticalIndices_eq_of_eq_below
    (C := C) (scope := old.scope) h
  have hhighest := highestCritical_eq_of_eq_below
    (C := C) (scope := old.scope + 1) (fallback := old.focus) h
  have hhighSurvivor := highestSurvivor_eq_of_eq_below
    (C := C) (scope := old.scope) (fallback := old.focus) h
  have hlowestScope := lowestConsistentInScope_eq_of_eq_below
    (C := C) (scope := old.scope) (fallback := old.focus) h
  have hlowest := lowestConsistent_eq_of_eq_below
    (C := C) (fallback := old.focus) h
  unfold GenLimit.PatientMachine.decide
  rw [show GenLimit.Consistent C a (t + 1) old.focus =
    GenLimit.Consistent C b (t + 1) old.focus from propext hcon]
  unfold GenLimit.PatientMachine.stableDecision
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only
  rw [hconsistent, hsurviving, hhighest, hhighSurvivor,
    hlowestScope, hlowest]
  have hex : (∃ i, GenLimit.Consistent C a (t + 1) i) ↔
      ∃ i, GenLimit.Consistent C b (t + 1) i := by
    constructor <;> rintro ⟨i, hi⟩
    · exact ⟨i, (consistent_iff_of_eq_below h).mp hi⟩
    · exact ⟨i, (consistent_iff_of_eq_below h).mpr hi⟩
  by_cases hfocus : GenLimit.Consistent C b (t + 1) old.focus
  · simp [hfocus]
  · simp only [hfocus, if_false]
    by_cases hscope :
        (GenLimit.PatientMachine.consistentIndices C b (t + 1) old.scope).Nonempty
    · simp [hscope]
    · simp only [hscope, if_false]
      by_cases hall : ∃ j, GenLimit.Consistent C b (t + 1) j
      · have halla : ∃ j, GenLimit.Consistent C a (t + 1) j := hex.mpr hall
        simp [hall, halla]
      · have halla : ¬ ∃ j, GenLimit.Consistent C a (t + 1) j :=
          fun ha => hall (hex.mp ha)
        simp [hall, halla]

theorem leastAvailable_eq_of_eq_below
    {C : GenLimit.LanguageFamily} (hInfinite : ∀ i, (C i).Infinite)
    {a b : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.leastAvailable C hInfinite a t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite b t used focus := by
  classical
  have hs := sample_eq_of_eq_below h
  have ha := GenLimit.PatientMachine.leastAvailable_spec
    C hInfinite a t used focus
  have hb := GenLimit.PatientMachine.leastAvailable_spec
    C hInfinite b t used focus
  apply le_antisymm
  · apply GenLimit.PatientMachine.leastAvailable_minimal
    simpa [GenLimit.PatientMachine.Available, hs] using hb
  · apply GenLimit.PatientMachine.leastAvailable_minimal
    simpa [GenLimit.PatientMachine.Available, hs] using ha

theorem processRound_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hdecide := decide_eq_of_eq_below (C := O.language) old h
  dsimp only [GenLimit.PatientMachine.processRound]
  rw [hdecide]
  rw [leastAvailable_eq_of_eq_below O.infinite' old.used _ h]

theorem run_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.run O a t =
      GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      have hprev : ∀ n, n < t → a n = b n :=
        fun n hn => h n (hn.trans (Nat.lt_succ_self t))
      rw [ih hprev]
      exact processRound_eq_of_eq_below O _ h

theorem output_eq_of_eq_below
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_eq_below O h]

noncomputable def onlinePatientGenerator (O : GenLimit.OracleFamily) :
    OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (completePrefix t xs) t

theorem follows_onlinePatientGenerator
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlinePatientGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_eq_of_eq_below O
  intro n hn
  simp [onlinePatientGenerator, completePrefix, hn]

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨onlinePatientGenerator O, ?_⟩
  intro i input hPresents
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, follows_onlinePatientGenerator O input, ?_, ?_⟩
  · obtain ⟨⟨T, hgenerate⟩, _⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input (z := i) hPresents
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hinput, houtput⟩ := hgenerate t ht
    refine ⟨hmem, ?_, houtput⟩
    rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hs, heq⟩
    exact hinput s (Nat.lt_succ_iff.mp hs) heq
  · have hdensity :=
      GenLimit.PatientMachine.patientScope_lowerDensity_half
        O input (z := i) hPresents
    simpa [GenLimit.PatientMachine.patientLowerDensity, O, oracleOfFamily,
      output] using hdensity


theorem ambientPrefixCount_le_ncard_of_finite
    {F : Language} (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  exact Set.Finite.mem_toFinset hF |>.2
    (GenLimit.PatientScope.mem_prefixFinset.mp hx).2

theorem ambientPrefixCount_le_add_ncard_diff
    {A B : Language} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := GenLimit.PatientScope.prefixFinset A n
  let bPrefix := GenLimit.PatientScope.prefixFinset B n
  let diffPrefix := GenLimit.PatientScope.prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    simp only [aPrefix, bPrefix, diffPrefix,
      GenLimit.PatientScope.mem_prefixFinset, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hcard : aPrefix.card ≤ bPrefix.card + diffPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    simpa [diffPrefix, GenLimit.PatientScope.prefixCount] using
      ambientPrefixCount_le_ncard_of_finite hfinite n
  simpa [aPrefix, bPrefix, diffPrefix,
    GenLimit.PatientScope.prefixCount] using
      hcard.trans (Nat.add_le_add_left hdiff _)

theorem ambientPrefixCount_le_add_ncard_of_diff_subset
    {A B F : Language} (hF : F.Finite) (hdiff : A \ B ⊆ F) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hF.toFinset.card := by
  classical
  let aPrefix := GenLimit.PatientScope.prefixFinset A n
  let bPrefix := GenLimit.PatientScope.prefixFinset B n
  let fPrefix := GenLimit.PatientScope.prefixFinset F n
  have hsub : aPrefix ⊆ bPrefix ∪ fPrefix := by
    intro x hx
    simp only [aPrefix, bPrefix, fPrefix,
      GenLimit.PatientScope.mem_prefixFinset, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hdiff ⟨hx.2, hxB⟩⟩
  have hcard : aPrefix.card ≤ bPrefix.card + fPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hfCount : fPrefix.card ≤ hF.toFinset.card := by
    simpa [fPrefix, GenLimit.PatientScope.prefixCount] using
      ambientPrefixCount_le_ncard_of_finite hF n
  simpa [aPrefix, bPrefix, fPrefix,
    GenLimit.PatientScope.prefixCount] using
      hcard.trans (Nat.add_le_add_left hfCount _)

theorem relativeLowerDensity_finite_extension
    (Q K R : Language) (hKR : K ⊆ R) (hfinite : (R \ K).Finite)
    (hKInfinite : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let ratioR : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let ratioK : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hKInfinite
  have hdenom : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hdenom
  have hratioR_nonneg : ∀ n, 0 ≤ ratioR n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hratioK_nonneg : ∀ n, 0 ≤ ratioK n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hratioR_le_one : ∀ n, ratioR n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount R n = 0
    · simp [ratioR, hn]
    · dsimp only [ratioR]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (Set.inter_subset_right) n
  have hratioK_le_one : ∀ n, ratioK n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [ratioK, hn]
    · dsimp only [ratioK]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono
        (Set.inter_subset_right) n
  have herror_nonneg : ∀ n, 0 ≤ error n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have herror_le : ∀ n, error n ≤ (hfinite.toFinset.card : ℝ) := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [error, hn]
    · have hdenomOne : (1 : ℝ) ≤
          GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      dsimp only [error]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  have hprefix : ∀ᶠ n : ℕ in atTop,
      ratioR n ≤ error n + ratioK n := by
    filter_upwards [hcountK.eventually (eventually_gt_atTop 0)] with n hn
    have hnK : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdenomMono : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hnumDiff : (Q ∩ R) \ (Q ∩ K) ⊆ R \ K := by
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hnumCount : GenLimit.PatientScope.prefixCount (Q ∩ R) n ≤
        GenLimit.PatientScope.prefixCount (Q ∩ K) n +
          hfinite.toFinset.card :=
      ambientPrefixCount_le_add_ncard_of_diff_subset hfinite hnumDiff n
    dsimp only [ratioR, ratioK, error]
    calc
      (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
          GenLimit.PatientScope.prefixCount R n ≤
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
          GenLimit.PatientScope.prefixCount K n := by
            apply div_le_div_of_nonneg_left
            · positivity
            · exact hnK
            · exact_mod_cast hdenomMono
      _ ≤ ((GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℕ) +
            hfinite.toFinset.card : ℕ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            apply div_le_div_of_nonneg_right
            · exact_mod_cast hnumCount
            · exact hnK.le
      _ = (hfinite.toFinset.card : ℝ) /
            GenLimit.PatientScope.prefixCount K n +
          (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by
              push_cast
              rw [add_div]
              ring
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf ratioR atTop ≤ liminf ratioK atTop
  calc
    liminf ratioR atTop ≤ liminf (error + ratioK) atTop :=
      liminf_le_liminf hprefix
        (isBoundedUnder_of ⟨0, hratioR_nonneg⟩)
        (isCoboundedUnder_ge_of_le atTop (fun n =>
          add_le_add (herror_le n) (hratioK_le_one n)))
    _ ≤ limsup error atTop + liminf ratioK atTop :=
      liminf_add_le
        (isBoundedUnder_of ⟨0, herror_nonneg⟩)
        (isBoundedUnder_of
          ⟨(hfinite.toFinset.card : ℝ), herror_le⟩)
        (isBoundedUnder_of ⟨0, hratioK_nonneg⟩)
        (isCoboundedUnder_ge_of_le atTop hratioK_le_one)
    _ = liminf ratioK atTop := by rw [herror.limsup_eq]; simp

theorem finset_eventually_subset_basicSample
    {input : Stream} {R : Language} (hPresents : GenLimit.Presents input R)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ R) :
    ∃ T, S ⊆ GenLimit.sample input T := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x S hxS ih =>
      have hxR : x ∈ R := hS (by simp)
      have hSR : (S : Set ℕ) ⊆ R := by
        intro y hy
        exact hS (by simp [hy])
      obtain ⟨Tx, hTx⟩ := GenLimit.eventually_mem_sample_of_presents hPresents hxR
      obtain ⟨TS, hTS⟩ := ih hSR
      refine ⟨max Tx TS, ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hTx _ (Nat.le_max_left _ _)
      · exact GenLimit.sample_mono (Nat.le_max_right _ _) (hTS hy)

theorem novelGeneratesInLimit_of_finite_extension
    {input output : Stream} {K R : Language}
    (hPresents : GenLimit.Presents input R)
    (hfinite : (R \ K).Finite)
    (hgenerate : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgenerate, hTgenerate⟩ := hgenerate
  obtain ⟨Tseen, hTseen⟩ :=
    finset_eventually_subset_basicSample
      hPresents hfinite.toFinset (by
        intro x hx
        exact ((Set.Finite.mem_toFinset hfinite).mp hx).1)
  refine ⟨max Tgenerate Tseen, ?_⟩
  intro t ht
  have htGenerate : Tgenerate ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  have hcorrect := hTgenerate t htGenerate
  have hseen : hfinite.toFinset ⊆ GenLimit.sample input t := by
    intro x hx
    exact GenLimit.sample_mono htSeen (hTseen hx)
  refine ⟨?_, hcorrect.2.1, hcorrect.2.2⟩
  by_contra houtside
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hcorrect.1, houtside⟩
  exact hcorrect.2.1
    (GenLimit.sample_mono (Nat.le_succ t) (hseen hbad))


theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let O := oracleOfFamily family hInfinite
  let expandedO :=
    GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ :=
    hpositive expandedO.language expandedO.infinite'
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  have hnoise : (Set.range input \ family i).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hpresentation.2.image input
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm hnoise.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  have hExpanded : expandedO.language j = Set.range input := by
    change GenLimit.InfiniteContamination.finiteExpansionLanguage O j = _
    rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
    simp only [j, data,
      GenLimit.InfiniteContamination.finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    have hnoiseCoe : (↑hnoise.toFinset : Set ℕ) =
        Set.range input \ family i :=
      Set.Finite.coe_toFinset hnoise
    simp only [O, oracleOfFamily, Finset.coe_empty]
    change GenLimit.InfiniteContamination.finiteExpansion
      (family i) (↑hnoise.toFinset : Set ℕ) (∅ : Set ℕ) = _
    rw [hnoiseCoe]
    ext x
    simp only [GenLimit.InfiniteContamination.finiteExpansion,
      Set.mem_diff, Set.mem_union, Set.mem_empty_iff_false, not_false_eq_true]
    constructor
    · rintro ⟨hx | hx, _⟩
      · exact hpresentation.1 hx
      · exact hx.1
    · intro hx
      refine ⟨?_, trivial⟩
      by_cases hxK : x ∈ family i
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  have hPresents : GenLimit.Presents input (expandedO.language j) :=
    hExpanded.symm
  obtain ⟨output, hfollow, hnovelExpanded, hdensityExpanded⟩ :=
    hgen j input hPresents
  refine ⟨output, hfollow, ?_, ?_⟩
  · apply novelGeneratesInLimit_of_finite_extension hPresents
    · rw [hExpanded]
      exact hnoise
    · exact hnovelExpanded
  · apply hdensityExpanded.trans
      (relativeLowerDensity_finite_extension
        (GenLimit.GeneratorFirst input output)
        (family i) (expandedO.language j) ?_ ?_ (hInfinite i))
    · rw [hExpanded]
      exact hpresentation.1
    · rw [hExpanded]
      exact hnoise

end Stage3Case025Formalization


open Stage3Case025

/-- Diagnostic milestone M1: Section 4's positive-presentation engine. -/
theorem stage3_positive_engine : PositivePresentationHalfDensity :=
  Stage3Case025Formalization.stage3_positive_engine

/-- Diagnostic milestone M2: Section 5's finite-noise transfer. -/
theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple :=
  Stage3Case025Formalization.stage3_finite_noise_transfer

/-- Primary endpoint: the unchanged semantic half-density theorem. -/
theorem stage3_result : Stage3Case025.MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
