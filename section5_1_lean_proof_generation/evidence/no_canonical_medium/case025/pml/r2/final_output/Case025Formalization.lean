import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology
open Stage3Case025

namespace Case025

noncomputable def oracleOfFamily (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query := by classical exact fun i x => decide (x ∈ family i)
  query_spec := by
    intro i x
    classical
    simp

noncomputable def extendPrefix {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

lemma extendPrefix_eq {t : ℕ} (xs : Fin (t + 1) → ℕ) {n : ℕ}
    (hn : n < t + 1) : extendPrefix xs n = xs ⟨n, hn⟩ := by
  simp [extendPrefix, hn]

lemma sample_congr_of_prefix {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  classical
  unfold GenLimit.sample
  apply Finset.image_congr
  intro n hn
  exact h n (Finset.mem_range.mp hn)

lemma consistent_congr (C : GenLimit.LanguageFamily) {a b : Stream} {t i : ℕ}
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, hs]

lemma recursiveCritical_congr (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [GenLimit.RecursiveCritical, consistent_congr C hs]
      | succ i =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical,
            consistent_congr C hs]
          constructor
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hcrit⟩
            refine ⟨hcon, ?_⟩
            intro j hj hjcrit
            exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

lemma consistentIndices_congr (C : GenLimit.LanguageFamily) {a b : Stream}
    {t scope : ℕ} (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.consistentIndices
  apply Finset.filter_congr
  intro i hi
  exact consistent_congr C hs

lemma criticalIndices_congr (C : GenLimit.LanguageFamily) {a b : Stream}
    {t scope : ℕ} (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.criticalIndices
  apply Finset.filter_congr
  intro i hi
  exact recursiveCritical_congr C hs i

lemma survivingCriticalIndices_congr (C : GenLimit.LanguageFamily) {a b : Stream}
    {t scope : ℕ} (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  unfold GenLimit.PatientMachine.survivingCriticalIndices
  apply Finset.filter_congr
  intro i hi
  constructor <;> rintro ⟨h0, h1⟩
  · exact ⟨(recursiveCritical_congr C hs0 i).mp h0,
      (recursiveCritical_congr C hs1 i).mp h1⟩
  · exact ⟨(recursiveCritical_congr C hs0 i).mpr h0,
      (recursiveCritical_congr C hs1 i).mpr h1⟩

lemma highestCritical_congr (C : GenLimit.LanguageFamily) {a b : Stream}
    {t scope fallback : ℕ} (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr C hs]

lemma highestSurvivor_congr (C : GenLimit.LanguageFamily) {a b : Stream}
    {t scope fallback : ℕ} (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr C hs0 hs1]

lemma lowestConsistentInScope_congr (C : GenLimit.LanguageFamily) {a b : Stream}
    {t scope fallback : ℕ} (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr C hs]

lemma lowestConsistent_congr (C : GenLimit.LanguageFamily) {a b : Stream}
    {t fallback : ℕ} (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_congr C hs).mp hi⟩
    rw [dif_pos ha, dif_pos hb]
    apply Nat.find_congr (Nat.find_spec ha)
    intro n hn
    exact consistent_congr C hs
  · have hb : ¬ ∃ i, GenLimit.Consistent C b t i := by
      intro h
      obtain ⟨i, hi⟩ := h
      exact ha ⟨i, (consistent_congr C hs).mpr hi⟩
    rw [dif_neg ha, dif_neg hb]

lemma stableDecision_congr (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  classical
  simpa only [GenLimit.PatientMachine.stableDecision,
    highestCritical_congr C hs1]

lemma backtrackDecision_congr (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  simpa only [GenLimit.PatientMachine.backtrackDecision,
    consistentIndices_congr C hs1,
    survivingCriticalIndices_congr C hs0 hs1,
    highestSurvivor_congr C hs0 hs1,
    lowestConsistentInScope_congr C hs1,
    lowestConsistent_congr C hs1,
    consistent_congr C hs1]

lemma decide_congr (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  unfold GenLimit.PatientMachine.decide
  rw [show GenLimit.Consistent C a (t + 1) old.focus ↔
    GenLimit.Consistent C b (t + 1) old.focus from consistent_congr C hs1]
  split
  · exact stableDecision_congr C old hs1
  · exact backtrackDecision_congr C old hs0 hs1

lemma leastAvailable_congr (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (used : Finset ℕ) (focus : ℕ)
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  apply Nat.find_congr
    (Nat.find_spec (GenLimit.PatientMachine.available_exists O.language O.infinite' a t used focus))
  intro x hx
  simp only [GenLimit.PatientMachine.Available, hs]

lemma processRound_congr (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  simpa only [GenLimit.PatientMachine.processRound,
    decide_congr O.language old hs0 hs1,
    leastAvailable_congr O old.used _ hs1]

lemma patient_run_congr (O : GenLimit.OracleFamily) {a b : Stream} :
    ∀ t, (∀ n, n < t → a n = b n) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      have hp : ∀ n, n < t → a n = b n := fun n hn => h n (Nat.lt.step hn)
      rw [ih hp]
      apply processRound_congr
      · apply sample_congr_of_prefix hp
      · apply sample_congr_of_prefix h

lemma patient_output_congr (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [patient_run_congr O (t + 1) h]

noncomputable def onlinePatient (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (extendPrefix xs) t

lemma onlinePatient_follows (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlinePatient O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  apply patient_output_congr O
  intro n hn
  simp [onlinePatient, extendPrefix, hn]

lemma stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hinf
  let O := oracleOfFamily family hinf
  refine ⟨onlinePatient O, ?_⟩
  intro i input hP
  refine ⟨GenLimit.PatientMachine.output O input, onlinePatient_follows O input, ?_⟩
  obtain ⟨⟨T, hT⟩, hd⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
  refine ⟨⟨T, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨hmem, ?_, hnovel⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact hfresh s (Nat.le_of_lt_succ hs) heq
  · simpa [GenLimit.PatientMachine.patientLowerDensity, O, oracleOfFamily] using hd



open GenLimit.PatientScope

lemma prefixCount_aug_le (A K : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    prefixCount (A ∩ (K ∪ (F : Set ℕ))) n ≤
      prefixCount (A ∩ K) n + F.card := by
  classical
  unfold prefixCount
  let X := prefixFinset (A ∩ (K ∪ (F : Set ℕ))) n
  let Y := prefixFinset (A ∩ K) n
  have hsub : X ⊆ Y ∪ F := by
    intro x hx
    simp only [X, Y, Finset.mem_union, mem_prefixFinset] at hx ⊢
    rcases hx with ⟨hxn, hxA, hxK | hxF⟩
    · exact Or.inl ⟨hxn, hxA, hxK⟩
    · exact Or.inr hxF
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le Y F)

lemma finite_union_density_transfer (A K : Set ℕ) (hK : K.Infinite) (F : Finset ℕ) :
    relativeLowerDensity (A ∩ (K ∪ (F : Set ℕ))) (K ∪ (F : Set ℕ)) ≤
      relativeLowerDensity (A ∩ K) K := by
  let u : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  let v : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
      (prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
  let e : ℕ → ℝ := fun n => (F.card : ℝ) / (prefixCount K n : ℝ)
  have hcount := tendsto_prefixCount_atTop hK
  have hcountR : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using hcountR.const_div_atTop (F.card : ℝ)
  have hKpos : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
    hcount.eventually (eventually_gt_atTop 0)
  have hv_le : ∀ᶠ n : ℕ in atTop, v n ≤ u n + e n := by
    filter_upwards [hKpos] with n hn
    have hnR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hden : (prefixCount K n : ℝ) ≤ prefixCount (K ∪ (F : Set ℕ)) n := by
      exact_mod_cast prefixCount_mono (Set.subset_union_left) n
    have hnum : (prefixCount (A ∩ (K ∪ (F : Set ℕ))) n : ℝ) ≤
        prefixCount (A ∩ K) n + F.card := by
      exact_mod_cast prefixCount_aug_le A K F n
    dsimp [u, v, e]
    calc
      (prefixCount (A ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
          (prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
          ≤ (prefixCount (A ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
              (prefixCount K n : ℝ) := by
                apply div_le_div_of_nonneg_left
                · positivity
                · exact hnR
                · exact hden
      _ ≤ ((prefixCount (A ∩ K) n : ℝ) + F.card) /
              (prefixCount K n : ℝ) :=
            div_le_div_of_nonneg_right hnum hnR.le
      _ = (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ) +
              (F.card : ℝ) / (prefixCount K n : ℝ) := by rw [add_div]
  have hu_nonneg : ∀ n, 0 ≤ u n := by intro n; positivity
  have hu_le_one : ∀ n, u n ≤ 1 := by
    intro n
    dsimp [u]
    by_cases hn : prefixCount K n = 0
    · simp [hn]
    · rw [div_le_one (by positivity)]
      exact_mod_cast prefixCount_mono Set.inter_subset_right n
  have hv_nonneg : ∀ n, 0 ≤ v n := by intro n; positivity
  have hu_above : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hu_le_one)
  have hue_bddAbove : IsCoboundedUnder (· ≥ ·) atTop (fun n => u n + e n) := by
    simpa only [Pi.add_apply] using
      isCoboundedUnder_ge_add hu_above he.isCoboundedUnder_ge
  have hfirst : liminf v atTop ≤ liminf (fun n => u n + e n) atTop :=
    liminf_le_liminf hv_le
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hv_nonneg))
      hue_bddAbove
  have he_below := he.isBoundedUnder_ge
  have he_above := he.isBoundedUnder_le
  have hu_below : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hu_nonneg)
  have hu_cobelow : IsCoboundedUnder (· ≥ ·) atTop u :=
    isCoboundedUnder_ge_of_le atTop hu_le_one
  have hadd : liminf (fun n => e n + u n) atTop ≤ limsup e atTop + liminf u atTop :=
    liminf_add_le he_below he_above hu_below hu_cobelow
  have hsecond : liminf (fun n => u n + e n) atTop ≤ liminf u atTop := by
    rw [liminf_congr (Eventually.of_forall fun n => add_comm (u n) (e n))]
    simpa [he.limsup_eq] using hadd
  change liminf v atTop ≤ liminf u atTop
  exact hfirst.trans hsecond

noncomputable def decodeFinset (n : ℕ) : Finset ℕ :=
  ((Encodable.decode n : Option (List ℕ)).getD []).toFinset

noncomputable def augmentedFamily (family : ℕ → Language) (n : ℕ) : Language :=
  family (Nat.unpair n).1 ∪ (decodeFinset (Nat.unpair n).2 : Set ℕ)

lemma augmentedFamily_infinite (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) (n : ℕ) :
    (augmentedFamily family n).Infinite := by
  exact (hinf (Nat.unpair n).1).mono Set.subset_union_left

lemma decodeFinset_encode (F : Finset ℕ) :
    decodeFinset (Encodable.encode F.toList) = F := by
  simp [decodeFinset]

lemma augmentedFamily_pair (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    augmentedFamily family (Nat.pair i (Encodable.encode F.toList)) =
      family i ∪ (F : Set ℕ) := by
  simp [augmentedFamily, Nat.unpair_pair, decodeFinset_encode]

lemma stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro positive family hinf
  let enlarged : ℕ → Language := augmentedFamily family
  have henlarged : ∀ j, (enlarged j).Infinite := by
    intro j
    exact augmentedFamily_infinite family hinf j
  obtain ⟨gen, hgen⟩ := positive enlarged henlarged
  refine ⟨gen, ?_⟩
  intro i input hP
  let K := family i
  have hvalues : (Set.range input \ K).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hP.2.image input
  let F : Finset ℕ := hvalues.toFinset
  have hF : (F : Set ℕ) = Set.range input \ K := by
    simp [F]
  let j := Nat.pair i (Encodable.encode F.toList)
  have henlarged_j : enlarged j = K ∪ (F : Set ℕ) := by
    simpa [enlarged, j, K] using augmentedFamily_pair family i F
  have hrange : Set.range input = K ∪ (F : Set ℕ) := by
    rw [hF]
    ext x
    constructor
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    · rintro (hxK | ⟨hx, -⟩)
      · exact hP.1 hxK
      · exact hx
  have hpresents : GenLimit.Presents input (enlarged j) := by
    rw [henlarged_j]
    exact hrange
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hnovel
    obtain ⟨B, hB⟩ := hP.2.bddAbove
    refine ⟨max T (B + 1), ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htB : B + 1 ≤ t := le_trans (le_max_right _ _) ht
    obtain ⟨hmem, hfresh, hdistinct⟩ := hT t htT
    refine ⟨?_, hfresh, hdistinct⟩
    rw [henlarged_j] at hmem
    rcases hmem with hmemK | hmemF
    · exact hmemK
    · exfalso
      have houtside : output t ∈ Set.range input \ K := by
        rw [← hF]
        exact hmemF
      obtain ⟨s, hsout⟩ := houtside.1
      have hsviol : s ∈ GenLimit.Generic.ViolationIndices input (fun x => x ∈ K) := by
        change ¬ input s ∈ K
        simpa [hsout] using houtside.2
      have hsB : s ≤ B := hB hsviol
      apply hfresh
      rw [GenLimit.mem_sample_iff]
      exact ⟨s, Nat.lt.step (lt_of_le_of_lt hsB (lt_of_lt_of_le (Nat.lt_succ_self B) htB)), hsout⟩
  · have htransfer := finite_union_density_transfer
      (GenLimit.GeneratorFirst input output) K (hinf i) F
    rw [← henlarged_j] at htransfer
    exact hdensity.trans htransfer

end Case025

open Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
