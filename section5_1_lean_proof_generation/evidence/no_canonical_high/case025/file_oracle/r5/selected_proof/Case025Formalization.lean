import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Logic.Equiv.Finset
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable section

private def decodedFinset (n : ℕ) : Finset ℕ :=
  (Encodable.decode n).getD ∅

private theorem decodedFinset_encode (s : Finset ℕ) :
    decodedFinset (Encodable.encode s) = s := by
  simp [decodedFinset, Encodable.encodek]

private def finiteExtensionFamily (family : ℕ → Language) : ℕ → Language :=
  fun n =>
    family (Nat.unpair n).1 ∪ (decodedFinset (Nat.unpair n).2 : Set ℕ)

private theorem finiteExtensionFamily_infinite
    {family : ℕ → Language} (hInfinite : ∀ i, (family i).Infinite) :
    ∀ n, (finiteExtensionFamily family n).Infinite := by
  intro n
  exact (hInfinite (Nat.unpair n).1).mono Set.subset_union_left

private def finiteExtensionOracle
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily := by
  classical
  exact
    { language := finiteExtensionFamily family
      infinite' := finiteExtensionFamily_infinite hInfinite
      query := fun i x => decide (x ∈ finiteExtensionFamily family i)
      query_spec := by simp }

private def prefixCompletion {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

private theorem prefixCompletion_eq {t : ℕ} (xs : Fin (t + 1) → ℕ)
    {n : ℕ} (hn : n < t + 1) :
    prefixCompletion xs n = xs ⟨n, hn⟩ := by
  simp [prefixCompletion, hn]

private theorem sample_eq_of_eq_below
    {a b : Stream} {n : ℕ} (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {a b : Stream} {n i : ℕ}
    (hsample : GenLimit.sample a n = GenLimit.sample b n) :
    GenLimit.RecursiveCritical C a n i ↔
      GenLimit.RecursiveCritical C b n i := by
  have hconsistent : ∀ j,
      GenLimit.Consistent C a n j ↔ GenLimit.Consistent C b n j := by
    intro j
    simp only [GenLimit.Consistent, hsample]
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa only [GenLimit.RecursiveCritical] using hconsistent 0
      | succ i =>
          simp only [GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hchain⟩
            refine ⟨(hconsistent _).mp hcon, ?_⟩
            intro j hj hjcrit
            exact hchain j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
          · rintro ⟨hcon, hchain⟩
            refine ⟨(hconsistent _).mpr hcon, ?_⟩
            intro j hj hjcrit
            exact hchain j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)

private theorem processRound_congr
    (O : GenLimit.OracleFamily) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hs : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
    sample_eq_of_eq_below h
  have hs0 : GenLimit.sample a t = GenLimit.sample b t :=
    sample_eq_of_eq_below (fun k hk => h k (lt_trans hk (Nat.lt_succ_self t)))
  have hcon1 (i : ℕ) :
      GenLimit.Consistent O.language a (t + 1) i ↔
        GenLimit.Consistent O.language b (t + 1) i := by
    simp only [GenLimit.Consistent, hs]
  have hcrit0 (i : ℕ) :
      GenLimit.RecursiveCritical O.language a t i ↔
        GenLimit.RecursiveCritical O.language b t i :=
    recursiveCritical_congr O.language hs0
  have hcrit1 (i : ℕ) :
      GenLimit.RecursiveCritical O.language a (t + 1) i ↔
        GenLimit.RecursiveCritical O.language b (t + 1) i :=
    recursiveCritical_congr O.language hs
  have hconsistentIndices (scope : ℕ) :
      GenLimit.PatientMachine.consistentIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.consistentIndices O.language b (t + 1) scope := by
    ext i
    simp only [GenLimit.PatientMachine.mem_consistentIndices, hcon1]
  have hcriticalIndices (scope : ℕ) :
      GenLimit.PatientMachine.criticalIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices O.language b (t + 1) scope := by
    ext i
    simp only [GenLimit.PatientMachine.mem_criticalIndices, hcrit1]
  have hsurvivingIndices (scope : ℕ) :
      GenLimit.PatientMachine.survivingCriticalIndices O.language a t scope =
        GenLimit.PatientMachine.survivingCriticalIndices O.language b t scope := by
    ext i
    simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices, hcrit0, hcrit1]
  have hhighestCritical (scope fallback : ℕ) :
      GenLimit.PatientMachine.highestCritical O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical O.language b (t + 1) scope fallback := by
    unfold GenLimit.PatientMachine.highestCritical
    rw [hcriticalIndices]
  have hhighestSurvivor (scope fallback : ℕ) :
      GenLimit.PatientMachine.highestSurvivor O.language a t scope fallback =
        GenLimit.PatientMachine.highestSurvivor O.language b t scope fallback := by
    unfold GenLimit.PatientMachine.highestSurvivor
    rw [hsurvivingIndices]
  have hlowestInScope (scope fallback : ℕ) :
      GenLimit.PatientMachine.lowestConsistentInScope O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope O.language b (t + 1) scope fallback := by
    unfold GenLimit.PatientMachine.lowestConsistentInScope
    rw [hconsistentIndices]
  have hlowest (fallback : ℕ) :
      GenLimit.PatientMachine.lowestConsistent O.language a (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent O.language b (t + 1) fallback := by
    by_cases ha : ∃ i, GenLimit.Consistent O.language a (t + 1) i
    · have hb : ∃ i, GenLimit.Consistent O.language b (t + 1) i :=
        (exists_congr hcon1).mp ha
      simp only [GenLimit.PatientMachine.lowestConsistent, dif_pos ha, dif_pos hb]
      exact Nat.find_congr (Nat.find_spec ha) (fun n _ => hcon1 n)
    · have hb : ¬ ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        simpa only [exists_congr hcon1] using ha
      simp only [GenLimit.PatientMachine.lowestConsistent, dif_neg ha, dif_neg hb]
  have hstable :
      GenLimit.PatientMachine.stableDecision O.language a t old =
        GenLimit.PatientMachine.stableDecision O.language b t old := by
    simp only [GenLimit.PatientMachine.stableDecision, hhighestCritical]
  have hbacktrack :
      GenLimit.PatientMachine.backtrackDecision O.language a t old =
        GenLimit.PatientMachine.backtrackDecision O.language b t old := by
    simp only [GenLimit.PatientMachine.backtrackDecision, hcon1,
      hconsistentIndices, hsurvivingIndices, hhighestSurvivor,
      hlowestInScope, hlowest]
  have hdecide :
      GenLimit.PatientMachine.decide O.language a t old =
        GenLimit.PatientMachine.decide O.language b t old := by
    unfold GenLimit.PatientMachine.decide
    rw [hcon1, hstable, hbacktrack]
  have hleast (used : Finset ℕ) (focus : ℕ) :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a (t + 1) used focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b (t + 1) used focus := by
    unfold GenLimit.PatientMachine.leastAvailable
    congr 1
    funext x
    apply propext
    simp only [GenLimit.PatientMachine.Available, hs]
  unfold GenLimit.PatientMachine.processRound
  simp only [hdecide, hleast]

private theorem run_congr
    (O : GenLimit.OracleFamily) {a b : Stream} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.PatientMachine.run O a n = GenLimit.PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun k hk => h k (lt_trans hk (Nat.lt_succ_self n)))]
      exact processRound_congr O n _ h

private theorem output_prefixCompletion
    (O : GenLimit.OracleFamily) (input : Stream) (t : ℕ) :
    GenLimit.PatientMachine.output O
        (prefixCompletion (fun i : Fin (t + 1) => input i)) t =
      GenLimit.PatientMachine.output O input t := by
  unfold GenLimit.PatientMachine.output
  rw [run_congr O]
  intro k hk
  exact prefixCompletion_eq _ hk

private def onlinePatientGenerator (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (prefixCompletion xs) t

private theorem follows_onlinePatientGenerator
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlinePatientGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  symm
  exact output_prefixCompletion O input t

private theorem exact_finite_extension
    {family : ℕ → Language} {i : ℕ} {input : Stream}
    (hComplete : CompleteFiniteOccurrencePresentation input (family i)) :
    ∃ F : Finset ℕ,
      GenLimit.Presents input (family i ∪ (F : Set ℕ)) := by
  let bad := GenLimit.Generic.ViolationIndices input (fun x => x ∈ family i)
  have hbad : bad.Finite := hComplete.2
  let F : Finset ℕ := hbad.toFinset.image input
  refine ⟨F, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    by_cases hx : input t ∈ family i
    · exact Set.mem_union_left _ hx
    · apply Set.mem_union_right
      change input t ∈ F
      rw [Finset.mem_image]
      refine ⟨t, ?_, rfl⟩
      apply (Set.Finite.mem_toFinset hbad).2
      exact hx
  · intro x hx
    rcases hx with hxK | hxF
    · exact hComplete.1 hxK
    · change x ∈ F at hxF
      rw [Finset.mem_image] at hxF
      obtain ⟨t, -, rfl⟩ := hxF
      exact ⟨t, rfl⟩


private theorem prefixCount_inter_union_le
    (D K : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n ≤
      GenLimit.PatientScope.prefixCount (D ∩ K) n + F.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  have hsub :
      GenLimit.PatientScope.prefixFinset (D ∩ (K ∪ (F : Set ℕ))) n ⊆
        GenLimit.PatientScope.prefixFinset (D ∩ K) n ∪ F := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    rcases hx'.2.2 with hxK | hxF
    · apply Finset.mem_union_left
      exact GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hx'.1, hx'.2.1, hxK⟩
    · exact Finset.mem_union_right _ hxF
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _)

private theorem relativeRatio_nonneg (D K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

private theorem relativeRatio_le_one (D K : Set ℕ) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  have hcount :
      GenLimit.PatientScope.prefixCount (D ∩ K) n ≤
        GenLimit.PatientScope.prefixCount K n :=
    GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · have hnum : GenLimit.PatientScope.prefixCount (D ∩ K) n = 0 :=
      Nat.eq_zero_of_le_zero (hzero ▸ hcount)
    simp [hzero, hnum]
  · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast hcount

private theorem relativeLowerDensity_finite_extension_le
    (D K : Set ℕ) (F : Finset ℕ) (hK : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity
        (D ∩ (K ∪ (F : Set ℕ))) (K ∪ (F : Set ℕ)) ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcount := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hcount)
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hcount.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdenNat :
        GenLimit.PatientScope.prefixCount K n ≤
          GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n :=
      GenLimit.PatientScope.prefixCount_mono Set.subset_union_left n
    have hdenR :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n := by
      exact_mod_cast hdenNat
    have hnumNat := prefixCount_inter_union_le D K F n
    have hnumR :
        (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n + F.card := by
      exact_mod_cast hnumNat
    dsimp [source, target, error]
    calc
      (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
          ≤ (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnR hdenR
      _ ≤ ((GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) + F.card) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_right hnumR hnR.le
      _ = (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) +
            (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            rw [add_div]
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => relativeRatio_le_one D K n))
    (isBoundedUnder_of
      ⟨0, fun n => relativeRatio_nonneg D K n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hsourceEventually : ∀ᶠ n : ℕ in atTop, r < source n := by
    exact eventually_lt_of_lt_liminf hr (by
      simpa only [source] using
        (isBoundedUnder_of
          ⟨0, fun n => relativeRatio_nonneg D (K ∪ (F : Set ℕ)) n⟩))
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hsourceEventually, herrorEventually, hcompare] with
      n hsource hsmall hle
  linarith



private theorem finset_seen_by
    (input : Stream) (F : Finset ℕ)
    (hF : (F : Set ℕ) ⊆ Set.range input) :
    ∃ T, ∀ x ∈ F, ∃ s, s < T ∧ input s = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x F hx ih =>
      have hxrange : x ∈ Set.range input := hF (by simp)
      obtain ⟨sx, hsx⟩ := hxrange
      have hsub : (F : Set ℕ) ⊆ Set.range input := by
        intro y hy
        exact hF (by simp [hy])
      obtain ⟨T, hT⟩ := ih hsub
      refine ⟨max T (sx + 1), ?_⟩
      intro y hy
      simp only [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact ⟨sx, lt_of_lt_of_le (Nat.lt_succ_self sx) (Nat.le_max_right _ _), hsx⟩
      · obtain ⟨s, hs, heq⟩ := hT y hy
        exact ⟨s, lt_of_lt_of_le hs (Nat.le_max_left _ _), heq⟩

private theorem novelty_of_finite_extension
    {input output : Stream} {K : Language} (F : Finset ℕ)
    (hP : GenLimit.Presents input (K ∪ (F : Set ℕ)))
    (hNovel : GenLimit.NovelGeneratesInLimit input output
      (K ∪ (F : Set ℕ))) :
    GenLimit.NovelGeneratesInLimit input output K := by
  have hcoverage : (F : Set ℕ) ⊆ Set.range input := by
    intro x hx
    rw [hP]
    exact Set.mem_union_right K hx
  obtain ⟨S, hS⟩ := finset_seen_by input F hcoverage
  obtain ⟨T, hT⟩ := hNovel
  refine ⟨max T S, ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (Nat.le_max_left _ _) ht
  have htS : S ≤ t := le_trans (Nat.le_max_right _ _) ht
  obtain ⟨hmem, hfresh, hrepeat⟩ := hT t htT
  refine ⟨?_, hfresh, hrepeat⟩
  rcases hmem with hK | hFmem
  · exact hK
  · obtain ⟨s, hsS, hinput⟩ := hS (output t) hFmem
    exact False.elim (hfresh (GenLimit.mem_sample_iff.mpr
      ⟨s, lt_of_lt_of_le hsS (Nat.le_succ_of_le htS), hinput⟩))


private theorem target_index_for_extension
    (family : ℕ → Language) (i : ℕ) (F : Finset ℕ) :
    finiteExtensionFamily family (Nat.pair i (Encodable.encode F)) =
      family i ∪ (F : Set ℕ) := by
  simp [finiteExtensionFamily, Nat.unpair_pair, decodedFinset_encode]

end

end Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  unfold Stage3Case025.MainClaim
  unfold Stage3Case025.PresentationDependentHalfDensity
  intro family hInfinite
  let O := Stage3Case025.finiteExtensionOracle family hInfinite
  refine ⟨Stage3Case025.onlinePatientGenerator O, ?_⟩
  intro i input hComplete
  obtain ⟨F, hP⟩ := Stage3Case025.exact_finite_extension hComplete
  let z := Nat.pair i (Encodable.encode F)
  have hz : O.language z = family i ∪ (F : Set ℕ) := by
    exact Stage3Case025.target_index_for_extension family i F
  have hPz : GenLimit.Presents input (O.language z) := by
    simpa only [hz] using hP
  obtain ⟨hGeneration, hDensity⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hPz
  let output := GenLimit.PatientMachine.output O input
  have hNovelExtension :
      GenLimit.NovelGeneratesInLimit input output (family i ∪ (F : Set ℕ)) := by
    obtain ⟨T, hT⟩ := hGeneration
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hrepeat⟩ := hT t ht
    refine ⟨hz ▸ hmem, ?_, hrepeat⟩
    intro hsample
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
    exact hfresh s (Nat.le_of_lt_succ hs) heq
  refine ⟨output, Stage3Case025.follows_onlinePatientGenerator O input,
    Stage3Case025.novelty_of_finite_extension F hP hNovelExtension, ?_⟩
  have hDensityExtension :
      (1 / 2 : ℝ) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ (family i ∪ (F : Set ℕ)))
          (family i ∪ (F : Set ℕ)) := by
    simpa only [GenLimit.PatientMachine.patientLowerDensity, hz] using hDensity
  exact hDensityExtension.trans
    (Stage3Case025.relativeLowerDensity_finite_extension_le
      (GenLimit.GeneratorFirst input output) (family i) F (hInfinite i))
