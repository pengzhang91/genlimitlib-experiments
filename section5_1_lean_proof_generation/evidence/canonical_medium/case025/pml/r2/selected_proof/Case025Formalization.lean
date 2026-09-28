import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Combinatorics.Colex

open Filter
open scoped Topology

namespace Stage3Case025

open GenLimit

noncomputable def baseOracle
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by classical simp

abbrev AdditionCode := ℕ × ℕ

def additionCode (n : ℕ) : AdditionCode := Nat.unpair n

def encodeAdditionCode (data : AdditionCode) : ℕ := Nat.pair data.1 data.2

@[simp] theorem additionCode_encode (data : AdditionCode) :
    additionCode (encodeAdditionCode data) = data := by
  simp [additionCode, encodeAdditionCode, Nat.unpair_pair]

noncomputable def additionFamily (family : ℕ → Language) (n : ℕ) : Language :=
  family (additionCode n).1 ∪ (Finset.equivBitIndices (additionCode n).2 : Set ℕ)

theorem additionFamily_infinite
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) (n : ℕ) :
    (additionFamily family n).Infinite := by
  exact (hInfinite (additionCode n).1).mono Set.subset_union_left

noncomputable def additionOracle
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily :=
  baseOracle (additionFamily family) (additionFamily_infinite family hInfinite)

private theorem sample_congr_of_eq_lt
    {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) :
    GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨k, hk, rfl⟩
  · exact ⟨k, hk, (h k hk).symm⟩
  · exact ⟨k, hk, h k hk⟩

private theorem consistent_congr_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t i : ℕ}
    (h : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    GenLimit.Consistent C stream₁ t i ↔
      GenLimit.Consistent C stream₂ t i := by
  unfold GenLimit.Consistent
  rw [h]

private theorem recursiveCritical_congr_of_sample_eq
    (C : GenLimit.LanguageFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t) :
    ∀ i, GenLimit.RecursiveCritical C stream₁ t i ↔
      GenLimit.RecursiveCritical C stream₂ t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa only [GenLimit.RecursiveCritical] using
            consistent_congr_of_sample_eq C h (i := 0)
      | succ n =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_congr_of_sample_eq C h).1 hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_congr_of_sample_eq C h).2 hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjcrit)

private theorem processRound_congr_of_samples
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : ℕ → ℕ} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (ht : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t)
    (hsucc : GenLimit.sample stream₁ (t + 1) =
      GenLimit.sample stream₂ (t + 1)) :
    GenLimit.PatientMachine.processRound O stream₁ t old =
      GenLimit.PatientMachine.processRound O stream₂ t old := by
  classical
  have hconS : ∀ i, GenLimit.Consistent O.language stream₁ (t + 1) i ↔
      GenLimit.Consistent O.language stream₂ (t + 1) i :=
    fun i => consistent_congr_of_sample_eq O.language hsucc
  have hcritT : ∀ i, GenLimit.RecursiveCritical O.language stream₁ t i ↔
      GenLimit.RecursiveCritical O.language stream₂ t i :=
    recursiveCritical_congr_of_sample_eq O.language ht
  have hcritS : ∀ i, GenLimit.RecursiveCritical O.language stream₁ (t + 1) i ↔
      GenLimit.RecursiveCritical O.language stream₂ (t + 1) i :=
    recursiveCritical_congr_of_sample_eq O.language hsucc
  have hconsistentIndices : ∀ scope,
      GenLimit.PatientMachine.consistentIndices O.language stream₁ (t + 1) scope =
        GenLimit.PatientMachine.consistentIndices O.language stream₂ (t + 1) scope := by
    intro scope
    ext i
    simp only [GenLimit.PatientMachine.mem_consistentIndices]
    rw [hconS i]
  have hcriticalIndices : ∀ scope,
      GenLimit.PatientMachine.criticalIndices O.language stream₁ (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices O.language stream₂ (t + 1) scope := by
    intro scope
    ext i
    simp only [GenLimit.PatientMachine.mem_criticalIndices]
    rw [hcritS i]
  have hsurvivors : ∀ scope,
      GenLimit.PatientMachine.survivingCriticalIndices O.language stream₁ t scope =
        GenLimit.PatientMachine.survivingCriticalIndices O.language stream₂ t scope := by
    intro scope
    ext i
    simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
    rw [hcritT i, hcritS i]
  have hhighestCritical : ∀ scope fallback,
      GenLimit.PatientMachine.highestCritical O.language stream₁ (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical O.language stream₂ (t + 1) scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.highestCritical]
    rw [hcriticalIndices scope]
  have hhighestSurvivor : ∀ scope fallback,
      GenLimit.PatientMachine.highestSurvivor O.language stream₁ t scope fallback =
        GenLimit.PatientMachine.highestSurvivor O.language stream₂ t scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.highestSurvivor]
    rw [hsurvivors scope]
  have hlowestScope : ∀ scope fallback,
      GenLimit.PatientMachine.lowestConsistentInScope O.language stream₁ (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope O.language stream₂ (t + 1) scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.lowestConsistentInScope]
    rw [hconsistentIndices scope]
  have hlowest : ∀ fallback,
      GenLimit.PatientMachine.lowestConsistent O.language stream₁ (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent O.language stream₂ (t + 1) fallback := by
    intro fallback
    simp only [GenLimit.PatientMachine.lowestConsistent]
    by_cases h₁ : ∃ i, GenLimit.Consistent O.language stream₁ (t + 1) i
    · have h₂ : ∃ i, GenLimit.Consistent O.language stream₂ (t + 1) i := by
        simpa only [hconS] using h₁
      rw [dif_pos h₁, dif_pos h₂]
      apply Nat.le_antisymm
      · exact Nat.find_min' h₁ ((hconS _).2 (Nat.find_spec h₂))
      · exact Nat.find_min' h₂ ((hconS _).1 (Nat.find_spec h₁))
    · have h₂ : ¬ ∃ i, GenLimit.Consistent O.language stream₂ (t + 1) i := by
        simpa only [hconS] using h₁
      rw [dif_neg h₁, dif_neg h₂]
  have hdecide :
      GenLimit.PatientMachine.decide O.language stream₁ t old =
        GenLimit.PatientMachine.decide O.language stream₂ t old := by
    simp only [GenLimit.PatientMachine.decide,
      GenLimit.PatientMachine.stableDecision,
      GenLimit.PatientMachine.backtrackDecision]
    rw [hconS old.focus]
    simp_rw [hhighestCritical, hconsistentIndices, hsurvivors,
      hhighestSurvivor, hlowestScope, hlowest, hconS]
  have hleast : ∀ focus,
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' stream₁
          (t + 1) old.used focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' stream₂
          (t + 1) old.used focus := by
    intro focus
    have havail : ∀ x,
        GenLimit.PatientMachine.Available O.language stream₁
            (t + 1) old.used focus x ↔
          GenLimit.PatientMachine.Available O.language stream₂
            (t + 1) old.used focus x := by
      intro x
      simp only [GenLimit.PatientMachine.Available]
      rw [hsucc]
    simp only [GenLimit.PatientMachine.leastAvailable]
    let h₁ := GenLimit.PatientMachine.available_exists O.language O.infinite'
      stream₁ (t + 1) old.used focus
    let h₂ := GenLimit.PatientMachine.available_exists O.language O.infinite'
      stream₂ (t + 1) old.used focus
    apply Nat.le_antisymm
    · exact Nat.find_min' h₁ ((havail _).2 (Nat.find_spec h₂))
    · exact Nat.find_min' h₂ ((havail _).1 (Nat.find_spec h₁))
  unfold GenLimit.PatientMachine.processRound
  simp only [hdecide, hleast]

private theorem run_congr_of_eq_lt
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → stream₁ k = stream₂ k) :
    GenLimit.PatientMachine.run O stream₁ t =
      GenLimit.PatientMachine.run O stream₂ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ]
      have hold : GenLimit.PatientMachine.run O stream₁ t =
          GenLimit.PatientMachine.run O stream₂ t :=
        ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      rw [hold]
      have hsampT : GenLimit.sample stream₁ t =
          GenLimit.sample stream₂ t :=
        sample_congr_of_eq_lt (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hsamp : GenLimit.sample stream₁ (t + 1) =
          GenLimit.sample stream₂ (t + 1) :=
        sample_congr_of_eq_lt h
      exact processRound_congr_of_samples O t _ hsampT hsamp

private theorem patientOutput_congr_of_eq_le
    (O : GenLimit.OracleFamily) {stream₁ stream₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k ≤ t → stream₁ k = stream₂ k) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  unfold GenLimit.PatientMachine.output
  exact congrArg (fun s : GenLimit.PatientMachine.State => s.lastOutput.getD 0)
    (run_congr_of_eq_lt O (fun k hk => h k (Nat.lt_succ_iff.mp hk)))

noncomputable def prefixStream
    (t : ℕ) (input : Fin (t + 1) → ℕ) : Stream :=
  fun k => if hk : k < t + 1 then input ⟨k, hk⟩ else 0

noncomputable def patientOnlineGenerator (O : GenLimit.OracleFamily) :
    OnlineGenerator :=
  fun t input _ => GenLimit.PatientMachine.output O (prefixStream t input) t

private theorem patientOnline_follows
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  unfold patientOnlineGenerator
  apply patientOutput_congr_of_eq_le
  intro k hk
  simp [prefixStream, Nat.lt_succ_iff.mpr hk]

private theorem patient_novel
    (O : GenLimit.OracleFamily) (input : Stream) {z : ℕ}
    (hP : GenLimit.Presents input (O.language z)) :
    GenLimit.NovelGeneratesInLimit input
      (GenLimit.PatientMachine.output O input) (O.language z) := by
  obtain ⟨hgen, _⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
  obtain ⟨T, hT⟩ := hgen
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hinj⟩ := hT t ht
  refine ⟨hmem, ?_, hinj⟩
  intro hsamp
  rw [GenLimit.mem_sample_iff] at hsamp
  obtain ⟨s, hs, heq⟩ := hsamp
  exact hfresh s (Nat.lt_succ_iff.mp hs) heq

private theorem positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := baseOracle family hInfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, patientOnline_follows O input, ?_, ?_⟩
  · exact patient_novel O input hP
  · exact GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP

private theorem prefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hAB : A ⊆ B) (hfinite : (B \ A).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount B n ≤
      GenLimit.PatientScope.prefixCount A n + (B \ A).ncard := by
  classical
  let a := GenLimit.PatientScope.prefixFinset A n
  let b := GenLimit.PatientScope.prefixFinset B n
  have hab : a ⊆ b := by
    intro x hx
    rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
    exact ⟨hx.1, hAB hx.2⟩
  have hdiff : b \ a ⊆ hfinite.toFinset := by
    intro x hx
    have hxb := GenLimit.PatientScope.mem_prefixFinset.mp
      (Finset.mem_sdiff.mp hx).1
    have hxa : x ∉ A := by
      intro hxA
      exact (Finset.mem_sdiff.mp hx).2
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxb.1, hxA⟩)
    exact Set.Finite.mem_toFinset hfinite |>.2 ⟨hxb.2, hxa⟩
  have hcarddiff : (b \ a).card ≤ (B \ A).ncard := by
    rw [Set.ncard_eq_toFinset_card (B \ A) hfinite]
    exact Finset.card_le_card hdiff
  have hinter : b ∩ a = a := Finset.inter_eq_right.mpr hab
  have hcard : b.card = (b \ a).card + a.card := by
    calc
      b.card = (b \ a).card + (b ∩ a).card :=
        (Finset.card_sdiff_add_card_inter b a).symm
      _ = (b \ a).card + a.card := by rw [hinter]
  change b.card ≤ a.card + (B \ A).ncard
  omega

private theorem finite_perturbation_lowerDensity
    {K R Q : Set ℕ} (hKR : K ⊆ R) (hfinite : (R \ K).Finite)
    (hKInfinite : K.Infinite)
    (hhalf : (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R) :
    (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  unfold GenLimit.PatientScope.relativeLowerDensity at hhalf ⊢
  have ratio_nonneg : ∀ (S : Set ℕ) n,
      (0 : ℝ) ≤ (GenLimit.PatientScope.prefixCount (Q ∩ S) n : ℝ) /
        (GenLimit.PatientScope.prefixCount S n : ℝ) := by
    intro S n
    positivity
  have ratio_le_one : ∀ (S : Set ℕ) n,
      (GenLimit.PatientScope.prefixCount (Q ∩ S) n : ℝ) /
        (GenLimit.PatientScope.prefixCount S n : ℝ) ≤ 1 := by
    intro S n
    by_cases hz : GenLimit.PatientScope.prefixCount S n = 0
    · simp [hz]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono (Set.inter_subset_right) n
  have hcobR := Filter.isCoboundedUnder_ge_of_le atTop (ratio_le_one R)
  have hboundR : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
        (GenLimit.PatientScope.prefixCount R n : ℝ)) :=
    (show BddBelow (Set.range fun n =>
      (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
        (GenLimit.PatientScope.prefixCount R n : ℝ)) from
      ⟨0, by rintro _ ⟨n, rfl⟩; exact ratio_nonneg R n⟩).isBoundedUnder_of_range
  have hcobK := Filter.isCoboundedUnder_ge_of_le atTop (ratio_le_one K)
  have hboundK : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) :=
    (show BddBelow (Set.range fun n =>
      (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) from
      ⟨0, by rintro _ ⟨n, rfl⟩; exact ratio_nonneg K n⟩).isBoundedUnder_of_range
  rw [Filter.le_liminf_iff' hcobR hboundR] at hhalf
  rw [Filter.le_liminf_iff' hcobK hboundK]
  intro y hy
  let z : ℝ := (y + 1 / 2) / 2
  have hyz : y < z := by dsimp [z]; linarith
  have hzh : z < (1 / 2 : ℝ) := by dsimp [z]; linarith
  have hR := hhalf z hzh
  let c : ℝ := ((R \ K).ncard : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hKInfinite
  have hcastK : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herr : Tendsto
      (fun n => c / (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hcastK
  have hsmall : ∀ᶠ n : ℕ in atTop,
      c / (GenLimit.PatientScope.prefixCount K n : ℝ) < z - y := by
    exact herr.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < z - y))
  have hKpos : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hcountK.eventually (eventually_gt_atTop 0)
  filter_upwards [hR, hsmall, hKpos] with n hnR hnsmall hnKpos
  let k := GenLimit.PatientScope.prefixCount K n
  let r := GenLimit.PatientScope.prefixCount R n
  let dK := GenLimit.PatientScope.prefixCount (Q ∩ K) n
  let dR := GenLimit.PatientScope.prefixCount (Q ∩ R) n
  have hkr : k ≤ r := GenLimit.PatientScope.prefixCount_mono hKR n
  have hnumSubset : Q ∩ K ⊆ Q ∩ R := Set.inter_subset_inter_right Q hKR
  have hnumFinite : ((Q ∩ R) \ (Q ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  have hdBound : dR ≤ dK + (R \ K).ncard := by
    exact le_trans
      (prefixCount_le_add_ncard_diff hnumSubset hnumFinite n)
      (Nat.add_le_add_left (Set.ncard_le_ncard
        (by
          intro x hx
          exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩)
        hfinite) dK)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hnKpos
  have hrR : (0 : ℝ) < r := by exact_mod_cast lt_of_lt_of_le hnKpos hkr
  have hdk : (dR : ℝ) - c ≤ dK := by
    have hcast : (dR : ℝ) ≤ (dK : ℝ) + c := by
      dsimp [c]
      exact_mod_cast hdBound
    linarith
  have hratio : (dR : ℝ) / r - c / k ≤ (dK : ℝ) / k := by
    have hdr_nonneg : (0 : ℝ) ≤ dR := by positivity
    have hdivmono : (dR : ℝ) / r ≤ (dR : ℝ) / k := by
      exact div_le_div_of_nonneg_left hdr_nonneg hkR (by exact_mod_cast hkr)
    calc
      (dR : ℝ) / r - c / k ≤ (dR : ℝ) / k - c / k := sub_le_sub_right hdivmono _
      _ = ((dR : ℝ) - c) / k := by ring
      _ ≤ (dK : ℝ) / k := (div_le_div_iff_of_pos_right hkR).2 hdk
  change y ≤ (dK : ℝ) / k
  have hnR' : z ≤ (dR : ℝ) / r := hnR
  have : y < (dR : ℝ) / r - c / k := by
    dsimp [c, k] at hnsmall
    linarith
  exact le_trans this.le hratio

private theorem bad_values_finite
    {input : Stream} {K : Language}
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
  exact hbad.image input

private theorem novel_transfer_finite_additions
    {input output : Stream} {K R : Language}
    (hKR : K ⊆ R) (hfinite : (R \ K).Finite)
    (hnovel : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  obtain ⟨T, hT⟩ := hnovel
  let badTimes : Set ℕ := {t | T ≤ t ∧ output t ∈ R \ K}
  have hinj : Set.InjOn output badTimes := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hablt | rfl | hbalt
    · exact False.elim ((hT b hb.1).2.2 a hablt hab)
    · rfl
    · exact False.elim ((hT a ha.1).2.2 b hbalt hab.symm)
  have himage : output '' badTimes ⊆ R \ K := by
    rintro x ⟨t, ht, rfl⟩
    exact ht.2
  have htimes : badTimes.Finite :=
    Set.Finite.of_finite_image (hfinite.subset himage) hinj
  obtain ⟨U, hU⟩ := htimes.bddAbove
  refine ⟨max T (U + 1), ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  obtain ⟨htR, hfresh, hrepeat⟩ := hT t htT
  refine ⟨?_, hfresh, hrepeat⟩
  by_contra htK
  have htBad : t ∈ badTimes := ⟨htT, htR, htK⟩
  have htU := hU htBad
  have hUt : U + 1 ≤ t := le_trans (le_max_right _ _) ht
  omega

end Stage3Case025

open Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  unfold Stage3Case025.MainClaim Stage3Case025.PresentationDependentHalfDensity
  intro family hInfinite
  have hAdditionInfinite : ∀ n, (additionFamily family n).Infinite :=
    additionFamily_infinite family hInfinite
  obtain ⟨gen, hgen⟩ := positive_engine (additionFamily family) hAdditionInfinite
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  let K : Language := family i
  let R : Language := Set.range input
  have hKR : K ⊆ R := hpresentation.1
  have hfinite : (R \ K).Finite := bad_values_finite hpresentation.2
  let data : AdditionCode :=
    (i, Finset.equivBitIndices.symm hfinite.toFinset)
  let j : ℕ := encodeAdditionCode data
  have hcoded : additionFamily family j = R := by
    have hcoe :
        (↑hfinite.toFinset : Set ℕ) = R \ K := hfinite.coe_toFinset
    rw [additionFamily]
    simp only [j, data, additionCode_encode, Equiv.apply_symm_apply]
    rw [hcoe]
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · rintro (hxK | ⟨hxR, _⟩)
      · exact hKR hxK
      · exact hxR
    · intro hxR
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hxR, hxK⟩
  have hpresents : GenLimit.Presents input (additionFamily family j) := by
    change Set.range input = additionFamily family j
    exact hcoded.symm
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows,
    novel_transfer_finite_additions hKR hfinite ?_, ?_⟩
  · simpa [hcoded] using hnovel
  · apply finite_perturbation_lowerDensity hKR hfinite (hInfinite i)
    simpa [hcoded] using hdensity
