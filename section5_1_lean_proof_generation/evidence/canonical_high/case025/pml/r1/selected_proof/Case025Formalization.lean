import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Combinatorics.Colex

open Filter
open scoped Topology

namespace Stage3Case025Proof

open Stage3Case025

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily := by
  classical
  exact {
  language := family
  infinite' := hInfinite
  query i x := if x ∈ family i then true else false
  query_spec i x := by simp }

def extendHistory {t : ℕ} (history : Fin t → ℕ) : Stream :=
  fun n => if h : n < t then history ⟨n, h⟩ else 0

theorem extendHistory_eq {t : ℕ} (history : Fin t → ℕ) (n : ℕ)
    (hn : n < t) :
    extendHistory history n = history ⟨n, hn⟩ := by
  simp [extendHistory, hn]

theorem sample_eq_of_eqOn
    {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t → stream₁ n = stream₂ n) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

theorem recursiveCritical_iff_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (hsample : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    ∀ i, GenLimit.RecursiveCritical C stream₁ t i ↔
      GenLimit.RecursiveCritical C stream₂ t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero =>
        simp only [GenLimit.RecursiveCritical, GenLimit.Consistent, hsample]
    | succ i =>
        simp only [GenLimit.RecursiveCritical, GenLimit.Consistent, hsample]
        constructor
        · rintro ⟨hcon, hcrit⟩
          refine ⟨hcon, ?_⟩
          intro j hj hjcrit
          exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
        · rintro ⟨hcon, hcrit⟩
          refine ⟨hcon, ?_⟩
          intro j hj hjcrit
          exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

theorem consistentIndices_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t scope : ℕ}
    (hsample : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.consistentIndices C stream₁ t scope =
      GenLimit.PatientMachine.consistentIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices,
    GenLimit.Consistent, hsample]

theorem criticalIndices_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t scope : ℕ}
    (hsample : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.criticalIndices C stream₁ t scope =
      GenLimit.PatientMachine.criticalIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_iff_of_sample_eq C hsample i]

theorem survivingCriticalIndices_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t scope : ℕ}
    (hsample₀ : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t)
    (hsample₁ : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.survivingCriticalIndices C stream₁ t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C stream₂ t scope := by
  classical
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_iff_of_sample_eq C hsample₀ i,
    recursiveCritical_iff_of_sample_eq C hsample₁ i]

theorem highestCritical_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (scope fallback : ℕ)
    (hsample : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.highestCritical C stream₁ t scope fallback =
      GenLimit.PatientMachine.highestCritical C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_eq_of_sample_eq (scope := scope) C hsample]

theorem highestSurvivor_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (scope fallback : ℕ)
    (hsample₀ : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t)
    (hsample₁ : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.highestSurvivor C stream₁ t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_eq_of_sample_eq
    (scope := scope) C hsample₀ hsample₁]

theorem lowestConsistentInScope_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (scope fallback : ℕ)
    (hsample : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.lowestConsistentInScope C stream₁ t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C stream₂ t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_eq_of_sample_eq (scope := scope) C hsample]

theorem lowestConsistent_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (fallback : ℕ)
    (hsample : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.lowestConsistent C stream₁ t fallback =
      GenLimit.PatientMachine.lowestConsistent C stream₂ t fallback := by
  classical
  have hconsistent : ∀ i,
      GenLimit.Consistent C stream₁ t i ↔ GenLimit.Consistent C stream₂ t i := by
    intro i
    simp only [GenLimit.Consistent, hsample]
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases h₁ : ∃ i, GenLimit.Consistent C stream₁ t i
  · have h₂ : ∃ i, GenLimit.Consistent C stream₂ t i := by
      simpa only [hconsistent] using h₁
    rw [dif_pos h₁, dif_pos h₂]
    apply Nat.le_antisymm
    · exact Nat.find_min' h₁ ((hconsistent _).mpr (Nat.find_spec h₂))
    · exact Nat.find_min' h₂ ((hconsistent _).mp (Nat.find_spec h₁))
  · have h₂ : ¬ ∃ i, GenLimit.Consistent C stream₂ t i := by
      simpa only [hconsistent] using h₁
    rw [dif_neg h₁, dif_neg h₂]

theorem stableDecision_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (hsample : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.stableDecision C stream₁ t old =
      GenLimit.PatientMachine.stableDecision C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  split
  · dsimp only
    rw [highestCritical_eq_of_sample_eq C (old.scope + 1) old.focus hsample]
  · rfl

theorem backtrackDecision_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (hsample₀ : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t)
    (hsample₁ : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.backtrackDecision C stream₁ t old =
      GenLimit.PatientMachine.backtrackDecision C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.backtrackDecision
  dsimp only
  rw [consistentIndices_eq_of_sample_eq (scope := old.scope) C hsample₁]
  split
  · rw [survivingCriticalIndices_eq_of_sample_eq
      (scope := old.scope) C hsample₀ hsample₁]
    split
    · rw [highestSurvivor_eq_of_sample_eq C old.scope old.focus
        hsample₀ hsample₁]
    · rw [lowestConsistentInScope_eq_of_sample_eq C old.scope old.focus hsample₁]
  · rw [lowestConsistent_eq_of_sample_eq C old.focus hsample₁]
    have hexists : (∃ i, GenLimit.Consistent C stream₁ (t + 1) i) ↔
        ∃ i, GenLimit.Consistent C stream₂ (t + 1) i := by
      simp only [GenLimit.Consistent, hsample₁]
    simp only [hexists]

theorem decide_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (hsample₀ : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t)
    (hsample₁ : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.decide C stream₁ t old =
      GenLimit.PatientMachine.decide C stream₂ t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [show GenLimit.Consistent C stream₁ (t + 1) old.focus =
      GenLimit.Consistent C stream₂ (t + 1) old.focus by
    apply propext
    simp only [GenLimit.Consistent, hsample₁]]
  split
  · exact stableDecision_eq_of_sample_eq C t old hsample₁
  · exact backtrackDecision_eq_of_sample_eq C t old hsample₀ hsample₁

theorem leastAvailable_eq_of_sample_eq
    (C : GenLimit.LanguageFamily) (hInfinite : ∀ i, (C i).Infinite)
    {stream₁ stream₂ : Stream} (t : ℕ) (used : Finset ℕ) (focus : ℕ)
    (hsample : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.PatientMachine.leastAvailable C hInfinite stream₁ t used focus =
      GenLimit.PatientMachine.leastAvailable C hInfinite stream₂ t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  apply propext
  simp only [GenLimit.PatientMachine.Available, hsample]

theorem processRound_eq_of_sample_eq
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (hsample₀ : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t)
    (hsample₁ : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.processRound O stream₁ t old =
      GenLimit.PatientMachine.processRound O stream₂ t old := by
  classical
  have hdecide := decide_eq_of_sample_eq O.language t old hsample₀ hsample₁
  unfold GenLimit.PatientMachine.processRound
  rw [hdecide]
  dsimp only
  rw [leastAvailable_eq_of_sample_eq O.language O.infinite'
    (t + 1) old.used _ hsample₁]

theorem run_eq_of_eqOn
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} :
    ∀ t, (∀ n, n < t → stream₁ n = stream₂ n) →
      GenLimit.PatientMachine.run O stream₁ t =
        GenLimit.PatientMachine.run O stream₂ t := by
  intro t
  induction t with
  | zero =>
      intro h
      rfl
  | succ t ih =>
      intro h
      have hprev : ∀ n, n < t → stream₁ n = stream₂ n := by
        intro n hn
        exact h n (Nat.lt.step hn)
      have hrun := ih hprev
      have hsamplePrev :
          GenLimit.sample stream₁ t = GenLimit.sample stream₂ t :=
        sample_eq_of_eqOn hprev
      have hsample :
          GenLimit.sample stream₁ (t + 1) =
            GenLimit.sample stream₂ (t + 1) := by
        apply sample_eq_of_eqOn
        simpa only [Nat.lt_add_one_iff] using h
      simp only [GenLimit.PatientMachine.run_succ]
      rw [hrun]
      exact processRound_eq_of_sample_eq O t _ hsamplePrev hsample

theorem output_eq_of_eqOn
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_eqOn O (t + 1) h]

noncomputable def onlinePatientGenerator
    (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t input _ =>
    GenLimit.PatientMachine.output O (extendHistory input) t

theorem follows_onlinePatientGenerator
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlinePatientGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_eq_of_eqOn
  intro n hn
  exact (extendHistory_eq (fun i : Fin (t + 1) => input i) n hn).symm

theorem prefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  let aPrefix := (Finset.range n).filter fun x => x ∈ A
  let bPrefix := (Finset.range n).filter fun x => x ∈ B
  let dPrefix := (Finset.range n).filter fun x => x ∈ A \ B
  have hsub : aPrefix ⊆ bPrefix ∪ dPrefix := by
    intro x hx
    simp only [aPrefix, bPrefix, dPrefix, Finset.mem_filter,
      Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hcard : aPrefix.card ≤ bPrefix.card + dPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : dPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [dPrefix, Finset.mem_filter] at hx
    simpa using hx.2
  exact hcard.trans (Nat.add_le_add_left hdiff _)

theorem relativeLowerDensity_le_of_finite_super
    (Q K R : Set ℕ) (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let count := GenLimit.PatientScope.prefixCount
  let ratioR : ℕ → ℝ := fun n =>
    (count (Q ∩ R) n : ℝ) / (count R n : ℝ)
  let ratioK : ℕ → ℝ := fun n =>
    (count (Q ∩ K) n : ℝ) / (count K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) / (count K n : ℝ)
  have hnumFinite : ((Q ∩ R) \ (Q ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcountKReal : Tendsto (fun n => (count K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact hcountKReal.const_div_atTop (hfinite.toFinset.card : ℝ)
  have hcompare : ∀ᶠ n : ℕ in atTop, ratioR n ≤ ratioK n + error n := by
    filter_upwards [hcountK.eventually (eventually_gt_atTop 0)] with n hn
    have hden : count K n ≤ count R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hnum : count (Q ∩ R) n ≤
        count (Q ∩ K) n + hnumFinite.toFinset.card :=
      prefixCount_le_add_ncard_diff hnumFinite n
    have hcardle : hnumFinite.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      have hx' : x ∈ (Q ∩ R) \ (Q ∩ K) := by simpa using hx
      have hx'' : x ∈ R \ K := by
        exact ⟨hx'.1.2, fun hxK => hx'.2 ⟨hx'.1.1, hxK⟩⟩
      simpa using hx''
    have hnum' : count (Q ∩ R) n ≤
        count (Q ∩ K) n + hfinite.toFinset.card :=
      hnum.trans (Nat.add_le_add_left hcardle _)
    have hnR : (0 : ℝ) < count K n := by exact_mod_cast hn
    have hdenR : (count K n : ℝ) ≤ count R n := by exact_mod_cast hden
    have hnumR : (count (Q ∩ R) n : ℝ) ≤
        count (Q ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hnum'
    change (count (Q ∩ R) n : ℝ) / count R n ≤
      (count (Q ∩ K) n : ℝ) / count K n +
        (hfinite.toFinset.card : ℝ) / count K n
    calc
      (count (Q ∩ R) n : ℝ) / count R n ≤
          (count (Q ∩ R) n : ℝ) / count K n := by
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnR hdenR
      _ ≤ ((count (Q ∩ K) n : ℝ) + (hfinite.toFinset.card : ℝ)) /
          (count K n : ℝ) := by
        exact div_le_div_of_nonneg_right hnumR hnR.le
      _ = (count (Q ∩ K) n : ℝ) / count K n +
          (hfinite.toFinset.card : ℝ) / count K n := by
        rw [add_div]
  have hratioK_nonneg : ∀ n, 0 ≤ ratioK n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hratioK_le_one : ∀ n, ratioK n ≤ 1 := by
    intro n
    by_cases hn : count K n = 0
    · simp [ratioK, hn]
    · have hnR : (0 : ℝ) < count K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      change (count (Q ∩ K) n : ℝ) / count K n ≤ 1
      rw [div_le_one hnR]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  have hratioR_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop ratioR := by
    change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, ratioR n ≥ b
    refine ⟨0, Eventually.of_forall ?_⟩
    intro n
    change 0 ≤ (count (Q ∩ R) n : ℝ) / (count R n : ℝ)
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hratioK_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop ratioK := by
    change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, ratioK n ≥ b
    exact ⟨0, Eventually.of_forall (fun n => hratioK_nonneg n)⟩
  have hratioK_upper : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop ratioK :=
    isCoboundedUnder_ge_of_le atTop hratioK_le_one
  change liminf ratioR atTop ≤ liminf ratioK atTop
  rw [le_liminf_iff hratioK_upper hratioK_lower]
  intro a ha
  let b : ℝ := (a + liminf ratioR atTop) / 2
  have hab : a < b := by dsimp [b]; linarith
  have hb : b < liminf ratioR atTop := by dsimp [b]; linarith
  have hpositive : 0 < b - a := sub_pos.mpr hab
  have herrSmall : ∀ᶠ n : ℕ in atTop, error n < b - a :=
    (tendsto_order.1 herror).2 _ hpositive
  have hratioLarge := eventually_lt_of_lt_liminf hb hratioR_lower
  filter_upwards [hcompare, herrSmall, hratioLarge] with n hcomp herr hlarge
  linarith

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  refine ⟨onlinePatientGenerator O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  have hmain :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
  refine ⟨output, follows_onlinePatientGenerator O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hmain.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨hmem, ?_, hnovel⟩
    intro hx
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hx
    exact hfresh s (Nat.le_of_lt_succ hs) heq
  · exact hmain.2

noncomputable def finiteAdditionLanguage
    (family : ℕ → Language) (n : ℕ) : Language :=
  family n.unpair.1 ∪ (Finset.equivBitIndices n.unpair.2 : Set ℕ)

theorem finiteAdditionLanguage_infinite
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) (n : ℕ) :
    (finiteAdditionLanguage family n).Infinite :=
  (hInfinite n.unpair.1).mono Set.subset_union_left

theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let expanded : ℕ → Language := finiteAdditionLanguage family
  have hExpandedInfinite : ∀ j, (expanded j).Infinite :=
    finiteAdditionLanguage_infinite family hInfinite
  obtain ⟨gen, hgen⟩ := hpositive expanded hExpandedInfinite
  refine ⟨gen, ?_⟩
  intro i input hPresentation
  have hnoise : (Set.range input \ family i).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hPresentation.2.image input
  let noiseCode := Finset.equivBitIndices.symm hnoise.toFinset
  let j := Nat.pair i noiseCode
  have hExpandedEq : expanded j = Set.range input := by
    change family (Nat.unpair j).1 ∪
      (Finset.equivBitIndices (Nat.unpair j).2 : Set ℕ) = Set.range input
    simp only [j, Nat.unpair_pair, noiseCode, Equiv.apply_symm_apply]
    rw [Set.Finite.coe_toFinset hnoise]
    ext x
    constructor
    · rintro (hx | hx)
      · exact hPresentation.1 hx
      · exact hx.1
    · intro hx
      by_cases hxK : x ∈ family i
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  have hPresents : GenLimit.Presents input (expanded j) := hExpandedEq.symm
  obtain ⟨output, hFollows, hNovelExpanded, hDensityExpanded⟩ :=
    hgen j input hPresents
  refine ⟨output, hFollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hNovelExpanded
    let badTimes : Set ℕ :=
      {t | T ≤ t ∧ output t ∈ Set.range input \ family i}
    have hbadImage : (output '' badTimes).Finite := by
      apply hnoise.subset
      rintro x ⟨t, ht, rfl⟩
      exact ht.2
    have hbadInj : Set.InjOn output badTimes := by
      intro a ha b hb hab
      rcases lt_trichotomy a b with hablt | rfl | hbalt
      · exact False.elim ((hT b hb.1).2.2 a hablt hab)
      · rfl
      · exact False.elim ((hT a ha.1).2.2 b hbalt hab.symm)
    have hbadFinite : badTimes.Finite :=
      Set.Finite.of_finite_image hbadImage hbadInj
    obtain ⟨B, hB⟩ := hbadFinite.bddAbove
    refine ⟨max T (B + 1), ?_⟩
    intro t ht
    have htT : T ≤ t := (le_max_left T (B + 1)).trans ht
    obtain ⟨hmemRange, hfresh, hnovel⟩ := hT t htT
    refine ⟨?_, hfresh, hnovel⟩
    by_contra htK
    have htBad : t ∈ badTimes := ⟨htT, hExpandedEq ▸ hmemRange, htK⟩
    have htB : t ≤ B := hB htBad
    have hBt : B + 1 ≤ t := (le_max_right T (B + 1)).trans ht
    omega
  · have hsubset : family i ⊆ expanded j := by
      rw [hExpandedEq]
      exact hPresentation.1
    have hdiff : (expanded j \ family i).Finite := by
      rw [hExpandedEq]
      exact hnoise
    exact hDensityExpanded.trans
      (relativeLowerDensity_le_of_finite_super
        (GenLimit.GeneratorFirst input output) (family i) (expanded j)
        (hInfinite i) hsubset hdiff)

end Stage3Case025Proof

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025Proof.stage3_finite_noise_transfer
    Stage3Case025Proof.stage3_positive_engine
