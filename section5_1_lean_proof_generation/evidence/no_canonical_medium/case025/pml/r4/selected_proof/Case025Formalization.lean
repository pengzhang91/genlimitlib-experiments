import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Logic.Equiv.Finset
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open Stage3Case025

namespace Case025

noncomputable def oracleOfFamily (family : ℕ → Set ℕ)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by classical exact if x ∈ family i then true else false
  query_spec i x := by classical simp

noncomputable def prefixStream {t : ℕ} (xs : Fin t → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t then xs ⟨n, h⟩ else 0

lemma prefixStream_apply {t : ℕ} (xs : Fin t → ℕ) {n : ℕ} (hn : n < t) :
    prefixStream xs n = xs ⟨n, hn⟩ := by
  simp [prefixStream, hn]

lemma sample_eq_of_eq_below {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

lemma consistent_iff_of_eq_below (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t i : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_eq_of_eq_below h]

lemma recursiveCritical_iff_of_eq_below (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t i : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.RecursiveCritical C a t i ↔ GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero =>
        simpa [GenLimit.RecursiveCritical] using
          consistent_iff_of_eq_below C h (i := 0)
    | succ i =>
        simp only [GenLimit.RecursiveCritical]
        rw [consistent_iff_of_eq_below C h]
        constructor
        · rintro ⟨hc, hsub⟩
          exact ⟨hc, fun j hj hcrit =>
            hsub j hj ((ih j (Nat.lt_succ_of_le hj)).2 hcrit)⟩
        · rintro ⟨hc, hsub⟩
          exact ⟨hc, fun j hj hcrit =>
            hsub j hj ((ih j (Nat.lt_succ_of_le hj)).1 hcrit)⟩

lemma consistentIndices_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  classical
  apply Finset.filter_congr
  intro i hi
  exact consistent_iff_of_eq_below C h

lemma criticalIndices_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  classical
  apply Finset.filter_congr
  intro i hi
  exact recursiveCritical_iff_of_eq_below C h

lemma survivingCriticalIndices_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope : ℕ} (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  apply Finset.filter_congr
  intro i hi
  rw [recursiveCritical_iff_of_eq_below C
    (fun n hn => h n (Nat.lt.step hn))]
  rw [recursiveCritical_iff_of_eq_below C h]

lemma highestCritical_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestCritical
  rw [criticalIndices_congr C h]

lemma highestSurvivor_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t scope fallback : ℕ} (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.highestSurvivor
  rw [survivingCriticalIndices_congr C h]

lemma lowestConsistentInScope_congr (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistentInScope
  rw [consistentIndices_congr C h]

lemma lowestConsistent_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    {t fallback : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  unfold GenLimit.PatientMachine.lowestConsistent
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_iff_of_eq_below C h).1 hi⟩
    simp only [ha, hb, dite_true]
    apply Nat.find_congr (Nat.find_spec ha)
    intro n hn
    exact consistent_iff_of_eq_below C h
  · have hb : ¬ ∃ i, GenLimit.Consistent C b t i := by
      rintro ⟨i, hi⟩
      exact ha ⟨i, (consistent_iff_of_eq_below C h).2 hi⟩
    simp only [ha, hb, dite_false]

lemma decide_congr (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ}
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  classical
  simp only [GenLimit.PatientMachine.decide]
  rw [consistent_iff_of_eq_below C h]
  by_cases hc : GenLimit.Consistent C b (t + 1) old.focus
  · simp only [hc, if_true, GenLimit.PatientMachine.stableDecision]
    split
    · rw [highestCritical_congr C h]
    · rfl
  · simp only [hc, if_false, GenLimit.PatientMachine.backtrackDecision]
    rw [consistentIndices_congr C h]
    split
    · rw [survivingCriticalIndices_congr C h]
      split
      · rw [highestSurvivor_congr C h]
      · rw [lowestConsistentInScope_congr C h]
    · rw [lowestConsistent_congr C h]
      have hall : (∃ j, GenLimit.Consistent C a (t + 1) j) ↔
          ∃ j, GenLimit.Consistent C b (t + 1) j := by
        constructor <;> rintro ⟨j, hj⟩
        · exact ⟨j, (consistent_iff_of_eq_below C h).1 hj⟩
        · exact ⟨j, (consistent_iff_of_eq_below C h).2 hj⟩
      simp only [hall]

lemma leastAvailable_congr (C : GenLimit.LanguageFamily)
    (hinf : ∀ i, (C i).Infinite) {a b : ℕ → ℕ} {t : ℕ}
    (used : Finset ℕ) (focus : ℕ) (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.leastAvailable C hinf a t used focus =
      GenLimit.PatientMachine.leastAvailable C hinf b t used focus := by
  classical
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  apply propext
  simp only [GenLimit.PatientMachine.Available, sample_eq_of_eq_below h]

lemma processRound_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ}
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  unfold GenLimit.PatientMachine.processRound
  rw [decide_congr O.language t old h]
  dsimp only
  rw [leastAvailable_congr O.language O.infinite' old.used _ h]

lemma run_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun n hn => h n (Nat.lt.step hn))]
      exact processRound_congr O t _ h

noncomputable def onlineOfOracle (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixStream xs) t

lemma follows_onlineOfOracle (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlineOfOracle O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  unfold onlineOfOracle GenLimit.PatientMachine.output
  rw [run_congr O (t + 1)]
  intro n hn
  exact (prefixStream_apply (fun i : Fin (t + 1) => input i) hn).symm

end Case025

open Stage3Case025

 theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hinf
  let O := Case025.oracleOfFamily family hinf
  refine ⟨Case025.onlineOfOracle O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  have hmain :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input (z := i) hP
  refine ⟨output, Case025.follows_onlineOfOracle O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hmain.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨hmem, ?_, hnovel⟩
    intro hsamp
    rw [GenLimit.mem_sample_iff] at hsamp
    obtain ⟨s, hs, heq⟩ := hsamp
    exact hfresh s (Nat.lt_succ_iff.mp hs) heq
  · simpa [GenLimit.PatientMachine.patientLowerDensity, O] using hmain.2

namespace Case025

noncomputable def finiteCode (n : ℕ) : Finset ℕ :=
  (Encodable.decode n : Option (Finset ℕ)).getD ∅

@[simp] lemma finiteCode_encode (F : Finset ℕ) :
    finiteCode (Encodable.encode F) = F := by
  simp [finiteCode, Encodable.encodek]

noncomputable def finiteExpansion (family : ℕ → Set ℕ) : ℕ → Set ℕ :=
  fun n => family (Nat.unpair n).1 ∪ (finiteCode (Nat.unpair n).2 : Set ℕ)

lemma finiteExpansion_infinite (family : ℕ → Set ℕ)
    (hinf : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExpansion family n).Infinite := by
  intro n
  exact (hinf (Nat.unpair n).1).mono Set.subset_union_left

lemma finiteExpansion_pair (family : ℕ → Set ℕ) (i : ℕ) (F : Finset ℕ) :
    finiteExpansion family (Nat.pair i (Encodable.encode F)) =
      family i ∪ (F : Set ℕ) := by
  simp [finiteExpansion]

lemma range_eq_union_outside {input : Stream} {K : Set ℕ}
    (hcover : K ⊆ Set.range input) :
    Set.range input = K ∪ (Set.range input \ K) := by
  ext x
  constructor
  · intro hx
    by_cases hk : x ∈ K
    · exact Or.inl hk
    · exact Or.inr ⟨hx, hk⟩
  · rintro (hx | ⟨hx, -⟩)
    · exact hcover hx
    · exact hx

lemma eventually_avoids_finite_of_novel
    {output : Stream} {F : Set ℕ} (hF : F.Finite)
    {T : ℕ} (hnovel : ∀ t, T ≤ t → ∀ s, s < t → output s ≠ output t) :
    ∃ T', ∀ t, T' ≤ t → output t ∉ F := by
  let bad : Set ℕ := {t | T ≤ t ∧ output t ∈ F}
  have hinj : Set.InjOn output bad := by
    intro s hs t ht heq
    rcases lt_trichotomy s t with hst | hst | hts
    · exact False.elim ((hnovel t ht.1 s hst) heq)
    · exact hst
    · exact False.elim ((hnovel s hs.1 t hts) heq.symm)
  have himage : (output '' bad).Finite :=
    hF.subset (by rintro x ⟨t, ht, rfl⟩; exact ht.2)
  have hbad : bad.Finite := Set.Finite.of_finite_image himage hinj
  obtain ⟨U, hU⟩ := hbad.bddAbove
  refine ⟨max T (U + 1), ?_⟩
  intro t ht hmem
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have htbad : t ∈ bad := ⟨htT, hmem⟩
  have htle : t ≤ U := hU htbad
  have hUt : U + 1 ≤ t := le_trans (le_max_right _ _) ht
  omega

end Case025

namespace Case025

lemma prefixCount_inter_union_le
    (G K : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (G ∩ (K ∪ (F : Set ℕ))) n ≤
      GenLimit.PatientScope.prefixCount (G ∩ K) n + F.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  calc
    (GenLimit.PatientScope.prefixFinset (G ∩ (K ∪ (F : Set ℕ))) n).card ≤
        (GenLimit.PatientScope.prefixFinset (G ∩ K) n ∪ F).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_union]
      have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
      rcases hx'.2 with ⟨hxG, hxK | hxF⟩
      · exact Or.inl (GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨hx'.1, hxG, hxK⟩)
      · exact Or.inr hxF
    _ ≤ (GenLimit.PatientScope.prefixFinset (G ∩ K) n).card + F.card :=
      Finset.card_union_le _ _

lemma ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

lemma ratio_le_one_of_subset {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hk]
  · have hkR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    rw [div_le_one hkR]
    exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n

lemma finite_error_le (K : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ F.card := by
  by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hk]
  · have hkone : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hnonneg : (0 : ℝ) ≤ F.card := by positivity
    exact (div_le_self hnonneg hkone)

lemma relativeLowerDensity_finite_union_le
    (G K : Set ℕ) (F : Finset ℕ) (hK : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity
        (G ∩ (K ∪ (F : Set ℕ))) (K ∪ (F : Set ℕ)) ≤
      GenLimit.PatientScope.relativeLowerDensity (G ∩ K) K := by
  let expanded : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (G ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
  let original : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (G ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let err : ℕ → ℝ := fun n =>
    (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hkTop := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hkPos : ∀ᶠ n in atTop, 0 < GenLimit.PatientScope.prefixCount K n :=
    hkTop.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n in atTop, expanded n ≤ err n + original n := by
    filter_upwards [hkPos] with n hn
    have hkR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hn
    have hdenNat := GenLimit.PatientScope.prefixCount_mono
      (show K ⊆ K ∪ (F : Set ℕ) from Set.subset_union_left) n
    have hdenR : (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n := by
      exact_mod_cast hdenNat
    have hnumNat := prefixCount_inter_union_le G K F n
    have hnumR : (GenLimit.PatientScope.prefixCount (G ∩ (K ∪ (F : Set ℕ))) n : ℝ) ≤
        GenLimit.PatientScope.prefixCount (G ∩ K) n + F.card := by
      exact_mod_cast hnumNat
    dsimp only [expanded, err, original]
    calc
      (GenLimit.PatientScope.prefixCount (G ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount (G ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_left (by positivity) hkR hdenR
      _ ≤ ((GenLimit.PatientScope.prefixCount (G ∩ K) n : ℝ) + F.card) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_right hnumR hkR.le
      _ = (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ) +
          (GenLimit.PatientScope.prefixCount (G ∩ K) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by ring
  have hexpBelow : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop expanded :=
    isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun n => ratio_nonneg _ _ n)
  have hsumAbove : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop (err + original) :=
    isCoboundedUnder_ge_of_le atTop (x := (F.card : ℝ) + 1) (fun n => by
      dsimp only [err, original, Pi.add_apply]
      exact add_le_add (finite_error_le K F n)
        (ratio_le_one_of_subset Set.inter_subset_right n))
  have hlimCompare : liminf expanded atTop ≤ liminf (err + original) atTop :=
    liminf_le_liminf hcompare hexpBelow hsumAbove
  have hkReal : Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hkTop
  have herr : Tendsto err atTop (nhds 0) := by
    simpa only [err] using hkReal.const_div_atTop (F.card : ℝ)
  have herrBelow : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop err :=
    isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun n => by dsimp only [err]; positivity)
  have herrAbove : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop err :=
    isBoundedUnder_of_eventually_le
      (Eventually.of_forall fun n => by
        dsimp only [err]
        exact finite_error_le K F n)
  have horigBelow : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop original :=
    isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun n => ratio_nonneg _ _ n)
  have horigAbove : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop original :=
    isCoboundedUnder_ge_of_le atTop (x := 1) (fun n =>
      ratio_le_one_of_subset Set.inter_subset_right n)
  have hadd : liminf (err + original) atTop ≤
      limsup err atTop + liminf original atTop :=
    liminf_add_le herrBelow herrAbove horigBelow horigAbove
  have herrLimsup : limsup err atTop = 0 := herr.limsup_eq
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf expanded atTop ≤ liminf original atTop
  calc
    liminf expanded atTop ≤ liminf (err + original) atTop := hlimCompare
    _ ≤ limsup err atTop + liminf original atTop := hadd
    _ = liminf original atTop := by rw [herrLimsup]; simp

end Case025

 theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive
  intro family hinf
  let expanded := Case025.finiteExpansion family
  have hexpanded : ∀ n, (expanded n).Infinite :=
    Case025.finiteExpansion_infinite family hinf
  obtain ⟨gen, hgen⟩ := hpositive expanded hexpanded
  refine ⟨gen, ?_⟩
  intro i input hpres
  have hbad : (Set.range input \ family i).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hpres.2.image input
  let F : Finset ℕ := hbad.toFinset
  let z := Nat.pair i (Encodable.encode F)
  have hP : GenLimit.Presents input (expanded z) := by
    change Set.range input = expanded z
    rw [show expanded z = family i ∪ (F : Set ℕ) by
      simp [expanded, z, Case025.finiteExpansion_pair]]
    rw [Case025.range_eq_union_outside hpres.1]
    exact congrArg (fun S : Set ℕ => family i ∪ S) hbad.coe_toFinset.symm
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen z input hP
  refine ⟨output, hfollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hnovel
    have havoid := Case025.eventually_avoids_finite_of_novel
      (show ((F : Finset ℕ) : Set ℕ).Finite from F.finite_toSet)
      (T := T) (fun t ht => (hT t ht).2.2)
    obtain ⟨T', hT'⟩ := havoid
    refine ⟨max T T', ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htT' : T' ≤ t := le_trans (le_max_right _ _) ht
    obtain ⟨hmem, hfresh, hnew⟩ := hT t htT
    have hmem' : output t ∈ family i ∪ (F : Set ℕ) := by
      simpa [expanded, z, Case025.finiteExpansion_pair] using hmem
    rcases hmem' with htarget | hfinite
    · exact ⟨htarget, hfresh, hnew⟩
    · exact False.elim ((hT' t htT') hfinite)
  · have hfiniteDensity := Case025.relativeLowerDensity_finite_union_le
      (GenLimit.GeneratorFirst input output) (family i) F (hinf i)
    have hexpandedEq : expanded z = family i ∪ (F : Set ℕ) := by
      simp [expanded, z, Case025.finiteExpansion_pair]
    rw [hexpandedEq] at hdensity
    exact hdensity.trans hfiniteDensity

 theorem stage3_result : Stage3Case025.MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
