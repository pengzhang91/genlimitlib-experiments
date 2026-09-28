import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Logic.Equiv.Finset

open Set Filter
open scoped Topology

namespace Stage3Case025

private noncomputable def prefixStream {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

private theorem prefixStream_eq {t : ℕ} (xs : Fin (t + 1) → ℕ) (i : Fin (t + 1)) :
    prefixStream xs i = xs i := by
  simp [prefixStream, i.isLt]

private theorem sample_congr_of_eq_lt
    {a b : Stream} {t : ℕ} (h : ∀ s, s < t → a s = b s) :
    GenLimit.sample a t = GenLimit.sample b t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨s, hs, rfl⟩
  · exact ⟨s, hs, (h s hs).symm⟩
  · exact ⟨s, hs, h s hs⟩

private theorem consistent_congr_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_congr_of_eq_lt h]

private theorem recursiveCritical_congr_of_eq_lt
    {C : GenLimit.LanguageFamily} {a b : Stream} {t i : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.RecursiveCritical C a t i ↔ GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simpa [GenLimit.RecursiveCritical] using
            consistent_congr_of_eq_lt (C := C) (i := 0) h
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_congr_of_eq_lt h).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨(consistent_congr_of_eq_lt h).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

private theorem consistentIndices_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.consistentIndices
  apply Finset.filter_congr
  intro i hi
  exact consistent_congr_of_eq_lt h

private theorem criticalIndices_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.criticalIndices
  apply Finset.filter_congr
  intro i hi
  exact recursiveCritical_congr_of_eq_lt h

private theorem survivingCriticalIndices_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.survivingCriticalIndices
  apply Finset.filter_congr
  intro i hi
  have ht : ∀ s, s < t → a s = b s := fun s hs => h s (Nat.lt.step hs)
  constructor <;> rintro ⟨h1, h2⟩
  · exact ⟨(recursiveCritical_congr_of_eq_lt ht).mp h1,
      (recursiveCritical_congr_of_eq_lt h).mp h2⟩
  · exact ⟨(recursiveCritical_congr_of_eq_lt ht).mpr h1,
      (recursiveCritical_congr_of_eq_lt h).mpr h2⟩

private theorem highestCritical_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr h]

private theorem highestSurvivor_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr h]

private theorem lowestConsistentInScope_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t scope fallback : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr h]

private theorem lowestConsistent_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t fallback : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_congr_of_eq_lt h).mp hi⟩
    simp only [dif_pos ha, dif_pos hb]
    apply Nat.find_congr (Nat.find_spec ha)
    intro n hn
    exact consistent_congr_of_eq_lt h
  · have hb : ¬ ∃ i, GenLimit.Consistent C b t i := by
      intro hb
      obtain ⟨i, hi⟩ := hb
      exact ha ⟨i, (consistent_congr_of_eq_lt h).mpr hi⟩
    simp [ha, hb]

private theorem backtrackDecision_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  have hc := consistentIndices_congr (C := C) (scope := old.scope) h
  have hs := survivingCriticalIndices_congr (C := C) (scope := old.scope) h
  have hh := highestSurvivor_congr (C := C) (scope := old.scope)
    (fallback := old.focus) h
  have hli := lowestConsistentInScope_congr (C := C) (scope := old.scope)
    (fallback := old.focus) h
  have hl := lowestConsistent_congr (C := C) (fallback := old.focus) h
  unfold GenLimit.PatientMachine.backtrackDecision
  simp only [hc, hs, hh, hli, hl]
  by_cases hb : ∃ j, GenLimit.Consistent C b (t + 1) j
  · have ha : ∃ j, GenLimit.Consistent C a (t + 1) j := by
      obtain ⟨j, hj⟩ := hb
      exact ⟨j, (consistent_congr_of_eq_lt h).mpr hj⟩
    simp [ha, hb]
  · have ha : ¬ ∃ j, GenLimit.Consistent C a (t + 1) j := by
      intro ha
      obtain ⟨j, hj⟩ := ha
      exact hb ⟨j, (consistent_congr_of_eq_lt h).mp hj⟩
    simp [ha, hb]

private theorem stableDecision_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  unfold GenLimit.PatientMachine.stableDecision
  simp only [highestCritical_congr (C := C) (scope := old.scope + 1)
    (fallback := old.focus) h]

private theorem decide_congr
    {C : GenLimit.LanguageFamily} {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  by_cases ha : GenLimit.Consistent C a (t + 1) old.focus
  · have hb := (consistent_congr_of_eq_lt h).mp ha
    simp [ha, hb, stableDecision_congr old h]
  · have hb : ¬ GenLimit.Consistent C b (t + 1) old.focus := by
      exact fun hb => ha ((consistent_congr_of_eq_lt h).mpr hb)
    simp [ha, hb, backtrackDecision_congr old h]

private theorem leastAvailable_congr
    {C : GenLimit.LanguageFamily} (hinfinite : ∀ i, (C i).Infinite)
    {a b : Stream} {t : ℕ} (used : Finset ℕ) (focus : ℕ)
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.PatientMachine.leastAvailable C hinfinite a t used focus =
      GenLimit.PatientMachine.leastAvailable C hinfinite b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr
    (GenLimit.PatientMachine.leastAvailable_spec C hinfinite a t used focus)
  intro n hn
  unfold GenLimit.PatientMachine.Available
  rw [sample_congr_of_eq_lt h]

private theorem processRound_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  unfold GenLimit.PatientMachine.processRound
  simp only [decide_congr old h]
  simp only [leastAvailable_congr O.infinite' old.used
    (GenLimit.PatientMachine.decide O.language b t old).focus h]

private theorem run_congr_of_eq_lt
    (O : GenLimit.OracleFamily) {a b : Stream} :
    ∀ t, (∀ s, s < t → a s = b s) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro; rfl
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      have hold := ih (fun s hs => h s (Nat.lt.step hs))
      rw [hold]
      exact processRound_congr O (GenLimit.PatientMachine.run O b t) h

private theorem output_congr_of_eq_le
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ s, s ≤ t → a s = b s) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr_of_eq_lt O (t + 1) (fun s hs => h s (Nat.lt_succ_iff.mp hs))]

private noncomputable def onlineOfOracle (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixStream xs) t

private theorem onlineOfOracle_follows (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlineOfOracle O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  symm
  apply output_congr_of_eq_le O
  intro s hs
  exact prefixStream_eq _ ⟨s, Nat.lt_succ_of_le hs⟩

private noncomputable def oracleOfFamily
    (family : ℕ → Language) (hinfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := @decide (x ∈ family i) (Classical.decEq True |> fun _ => Classical.propDecidable _)
  query_spec i x := by classical simp

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hinfinite
  let O := oracleOfFamily family hinfinite
  refine ⟨onlineOfOracle O, ?_⟩
  intro i input hpresents
  refine ⟨GenLimit.PatientMachine.output O input,
    onlineOfOracle_follows O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ :=
      (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
        O input hpresents).1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hout⟩ := hT t ht
    refine ⟨hmem, ?_, hout⟩
    intro hx
    rw [GenLimit.mem_sample_iff] at hx
    obtain ⟨s, hs, heq⟩ := hx
    exact (hfresh s (Nat.le_of_lt_succ hs)) heq
  · exact (GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input hpresents).2

private noncomputable def decodeFinset (n : ℕ) : Finset ℕ :=
  (Encodable.decode n).getD ∅

private noncomputable def expandedFamily (family : ℕ → Language) : ℕ → Language :=
  fun n => family (Nat.unpair n).1 ∪ (decodeFinset (Nat.unpair n).2 : Set ℕ)

private theorem expandedFamily_infinite
    {family : ℕ → Language} (hinfinite : ∀ i, (family i).Infinite) :
    ∀ n, (expandedFamily family n).Infinite := by
  intro n
  exact (hinfinite (Nat.unpair n).1).mono Set.subset_union_left

private theorem decodeFinset_encode (F : Finset ℕ) :
    decodeFinset (Encodable.encode F) = F := by
  simp [decodeFinset, Encodable.encodek]

private theorem prefixCount_le_add_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := GenLimit.PatientScope.prefixFinset A n
  let bPrefix := GenLimit.PatientScope.prefixFinset B n
  let diffPrefix := GenLimit.PatientScope.prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxB⟩)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2
      (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
  calc
    GenLimit.PatientScope.prefixCount A n = aPrefix.card := rfl
    _ ≤ (bPrefix ∪ diffPrefix).card := Finset.card_le_card hsub
    _ ≤ bPrefix.card + diffPrefix.card := Finset.card_union_le _ _
    _ ≤ bPrefix.card + hfinite.toFinset.card := Nat.add_le_add_left hdiff _
    _ = GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := rfl

private theorem liminf_le_of_le_add_vanishing
    (source output error : ℕ → ℝ)
    (hsource_nonneg : ∀ n, 0 ≤ source n)
    (hsource_le_one : ∀ n, source n ≤ 1)
    (houtput_nonneg : ∀ n, 0 ≤ output n)
    (houtput_le_one : ∀ n, output n ≤ 1)
    (herror : Tendsto error atTop (𝓝 0))
    (hcompare : ∀ᶠ n in atTop, source n ≤ output n + error n) :
    liminf source atTop ≤ liminf output atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop houtput_le_one)
    (isBoundedUnder_of ⟨0, houtput_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hsourceEventually : ∀ᶠ n in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herrorEventually : ∀ᶠ n in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hsourceEventually, herrorEventually, hcompare] with n hs he hc
  linarith

private theorem relativeLowerDensity_finite_expansion
    (Q K R : Set ℕ) (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
      GenLimit.PatientScope.prefixCount R n
  let output : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  have hKcount := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hKcount)
  have hsource_nonneg : ∀ n, 0 ≤ source n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have houtput_nonneg : ∀ n, 0 ≤ output n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hsource_le_one : ∀ n, source n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount R n = 0
    · simp [source, hn]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  have houtput_le_one : ∀ n, output n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [output, hn]
    · rw [div_le_one (by positivity)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  have hcompare : ∀ᶠ n in atTop, source n ≤ output n + error n := by
    filter_upwards [hKcount.eventually (eventually_gt_atTop 0)] with n hn
    have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hkrCount : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hrpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n := by
      exact lt_of_lt_of_le hkpos (by exact_mod_cast hkrCount)
    have hdiff : ((Q ∩ R) \ (Q ∩ K)) ⊆ R \ K := by
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hfinite' : ((Q ∩ R) \ (Q ∩ K)).Finite := hfinite.subset hdiff
    have hcount := prefixCount_le_add_finite hfinite' n
    have hcard : hfinite'.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      exact Set.Finite.mem_toFinset hfinite |>.2
        (hdiff (Set.Finite.mem_toFinset hfinite' |>.1 hx))
    have hcount' : GenLimit.PatientScope.prefixCount (Q ∩ R) n ≤
        GenLimit.PatientScope.prefixCount (Q ∩ K) n + hfinite.toFinset.card :=
      hcount.trans (Nat.add_le_add_left hcard _)
    dsimp [source, output, error]
    have hcountR :
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (Q ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hcount'
    have hdenom :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount R n := by
      exact_mod_cast hkrCount
    calc
      (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
          GenLimit.PatientScope.prefixCount R n ≤
        (GenLimit.PatientScope.prefixCount (Q ∩ K) n + hfinite.toFinset.card : ℝ) /
          GenLimit.PatientScope.prefixCount R n :=
        div_le_div_of_nonneg_right hcountR hrpos.le
      _ ≤ (GenLimit.PatientScope.prefixCount (Q ∩ K) n + hfinite.toFinset.card : ℝ) /
          GenLimit.PatientScope.prefixCount K n := by
        exact div_le_div_of_nonneg_left (by positivity) hkpos hdenom
      _ = (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n +
          (hfinite.toFinset.card : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by rw [add_div]
  exact liminf_le_of_le_add_vanishing source output error
    hsource_nonneg hsource_le_one houtput_nonneg houtput_le_one herror hcompare

private theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinfinite
  let expanded := expandedFamily family
  have hexpandedInfinite : ∀ n, (expanded n).Infinite :=
    expandedFamily_infinite hinfinite
  obtain ⟨gen, hgen⟩ := hpositive expanded hexpandedInfinite
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  let K := family i
  let R : Language := Set.range input
  have hKR : K ⊆ R := hpresentation.1
  have hfinite : (R \ K).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hpresentation.2.image input
  let F : Finset ℕ := hfinite.toFinset
  let z := Nat.pair i (Encodable.encode F)
  have hz : expanded z = R := by
    change family (Nat.unpair z).1 ∪
      (decodeFinset (Nat.unpair z).2 : Set ℕ) = R
    rw [Nat.unpair_pair, decodeFinset_encode]
    ext x
    simp only [Finset.coe_sort_coe, Set.mem_union, Set.mem_range]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hKR hx
      · exact (Set.Finite.mem_toFinset hfinite).mp hx |>.1
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ((Set.Finite.mem_toFinset hfinite).mpr ⟨hx, hxK⟩)
  have hpresents : GenLimit.Presents input (expanded z) := by
    change Set.range input = expanded z
    exact hz.symm
  obtain ⟨output, hfollows, hnovelR, hdensityR⟩ := hgen z input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hnovelR
    obtain ⟨Tseen, hTseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample hpresents F (by
        intro x hx
        rw [hz]
        exact (Set.Finite.mem_toFinset hfinite).mp hx |>.1)
    refine ⟨max T Tseen, ?_⟩
    intro t ht
    have htT : T ≤ t := (Nat.le_max_left _ _).trans ht
    have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
    obtain ⟨hmemR, hfresh, hout⟩ := hT t htT
    refine ⟨?_, hfresh, hout⟩
    by_contra hnotK
    have hmemRange : output t ∈ R := by simpa [hz] using hmemR
    have hmemF : output t ∈ F :=
      (Set.Finite.mem_toFinset hfinite).mpr ⟨hmemRange, hnotK⟩
    have hgeneric : output t ∈ GenLimit.Generic.sample input (t + 1) :=
      GenLimit.Generic.sample_mono (htSeen.trans (Nat.le_succ t)) (hTseen hmemF)
    apply hfresh
    rw [GenLimit.mem_sample_iff]
    rw [GenLimit.Generic.mem_sample_iff] at hgeneric
    exact hgeneric
  · have hinfiniteK : K.Infinite := hinfinite i
    apply le_trans hdensityR
    simpa [hz, K, R] using
      relativeLowerDensity_finite_expansion
        (GenLimit.GeneratorFirst input output) K R hinfiniteK hKR hfinite

theorem stage3_result_internal : MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine

end Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025.stage3_result_internal
