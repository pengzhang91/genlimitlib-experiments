import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Stage3Case025
open Set

noncomputable def oracleOf (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem sample_congr {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

private theorem recursiveCritical_congr (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t : ℕ}
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [GenLimit.RecursiveCritical, GenLimit.Consistent, hs]
      | succ i =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hprev⟩
            refine ⟨?_, ?_⟩
            · simpa [GenLimit.Consistent, hs] using hcon
            · intro j hj hjcrit
              apply hprev j hj
              exact (ih j (Nat.lt_succ_of_le hj)).2 hjcrit
          · rintro ⟨hcon, hprev⟩
            refine ⟨?_, ?_⟩
            · simpa [GenLimit.Consistent, hs] using hcon
            · intro j hj hjcrit
              apply hprev j hj
              exact (ih j (Nat.lt_succ_of_le hj)).1 hjcrit

private theorem decide_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ}
    (t : ℕ) (old : GenLimit.PatientMachine.State)
    (hs0 : GenLimit.sample a t = GenLimit.sample b t)
    (hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1)) :
    GenLimit.PatientMachine.decide O.language a t old =
      GenLimit.PatientMachine.decide O.language b t old := by
  classical
  have hc : ∀ i, GenLimit.Consistent O.language a (t + 1) i ↔
      GenLimit.Consistent O.language b (t + 1) i := by
    intro i
    simp [GenLimit.Consistent, hs1]
  have hr : ∀ i, GenLimit.RecursiveCritical O.language a (t + 1) i ↔
      GenLimit.RecursiveCritical O.language b (t + 1) i :=
    recursiveCritical_congr O.language hs1
  have hr0 : ∀ i, GenLimit.RecursiveCritical O.language a t i ↔
      GenLimit.RecursiveCritical O.language b t i :=
    recursiveCritical_congr O.language hs0
  have hconsistent : ∀ scope,
      GenLimit.PatientMachine.consistentIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.consistentIndices O.language b (t + 1) scope := by
    intro scope
    ext i
    simp [hc]
  have hcritical : ∀ scope,
      GenLimit.PatientMachine.criticalIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices O.language b (t + 1) scope := by
    intro scope
    ext i
    simp [hr]
  have hsurviving : ∀ scope,
      GenLimit.PatientMachine.survivingCriticalIndices O.language a t scope =
        GenLimit.PatientMachine.survivingCriticalIndices O.language b t scope := by
    intro scope
    ext i
    simp [hr0, hr]
  have hhighestCritical : ∀ scope fallback,
      GenLimit.PatientMachine.highestCritical O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical O.language b (t + 1) scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.highestCritical
    rw [hcritical]
  have hhighestSurvivor : ∀ scope fallback,
      GenLimit.PatientMachine.highestSurvivor O.language a t scope fallback =
        GenLimit.PatientMachine.highestSurvivor O.language b t scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.highestSurvivor
    rw [hsurviving]
  have hlowestScope : ∀ scope fallback,
      GenLimit.PatientMachine.lowestConsistentInScope O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope O.language b (t + 1) scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.lowestConsistentInScope
    rw [hconsistent]
  have hlowest : ∀ fallback,
      GenLimit.PatientMachine.lowestConsistent O.language a (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent O.language b (t + 1) fallback := by
    intro fallback
    unfold GenLimit.PatientMachine.lowestConsistent
    by_cases ha : ∃ i, GenLimit.Consistent O.language a (t + 1) i
    · have hb : ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        obtain ⟨i, hi⟩ := ha
        exact ⟨i, (hc i).1 hi⟩
      simp only [ha, hb, dif_pos]
      exact Nat.find_congr' (fun {n} => hc n)
    · have hb : ¬ ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        rintro ⟨i, hi⟩
        exact ha ⟨i, (hc i).2 hi⟩
      simp [ha, hb]
  unfold GenLimit.PatientMachine.decide
  rw [propext (hc old.focus)]
  by_cases hfocus : GenLimit.Consistent O.language b (t + 1) old.focus
  · simp only [hfocus, if_true]
    unfold GenLimit.PatientMachine.stableDecision
    by_cases hwait : 2 ^ old.tau ≤ old.age
    · simp only [hwait, if_pos]
      rw [hhighestCritical]
    · simp [hwait]
  · simp only [hfocus, if_false]
    unfold GenLimit.PatientMachine.backtrackDecision
    rw [hconsistent]
    by_cases hcon :
        (GenLimit.PatientMachine.consistentIndices O.language b (t + 1) old.scope).Nonempty
    · simp only [hcon, dif_pos]
      rw [hsurviving, hhighestSurvivor, hlowestScope]
    · simp only [hcon, dif_neg, if_false]
      rw [hlowest]
      have hexists : (∃ i, GenLimit.Consistent O.language a (t + 1) i) ↔
          ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        constructor <;> rintro ⟨i, hi⟩
        · exact ⟨i, (hc i).1 hi⟩
        · exact ⟨i, (hc i).2 hi⟩
      rw [propext hexists]
      split <;> simp_all

private theorem leastAvailable_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ}
    (t : ℕ) (used : Finset ℕ) (focus : ℕ)
    (hs : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  unfold GenLimit.PatientMachine.leastAvailable
  congr 1
  funext x
  apply propext
  simp only [GenLimit.PatientMachine.Available]
  rw [hs]

private theorem run_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ n, n < t → a n = b n) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      have hab : GenLimit.PatientMachine.run O a t =
          GenLimit.PatientMachine.run O b t :=
        ih (fun n hn => h n (Nat.lt.step hn))
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, hab]
      have hs0 : GenLimit.sample a t = GenLimit.sample b t :=
        sample_congr (fun n hn => h n (Nat.lt.step hn))
      have hs1 : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
        sample_congr h
      have hd := decide_congr O t (GenLimit.PatientMachine.run O b t) hs0 hs1
      simp only [GenLimit.PatientMachine.processRound]
      rw [hd]
      have hx := leastAvailable_congr O (t + 1)
        (GenLimit.PatientMachine.run O b t).used
        (GenLimit.PatientMachine.decide O.language b t
          (GenLimit.PatientMachine.run O b t)).focus hs1
      rw [hx]

private theorem output_congr (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (h : ∀ n, n ≤ t → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  have hrun := run_congr O (t + 1) (fun n hn => h n (Nat.lt_succ_iff.mp hn))
  rw [hrun]

noncomputable def extendHistory (t : ℕ) (xs : Fin (t+1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n ≤ t then xs ⟨n, Nat.lt_succ_iff.mpr h⟩ else 0

noncomputable def onlineOf (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (extendHistory t xs) t

private theorem follows_onlineOf (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlineOf O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_congr
  intro n hn
  simp [extendHistory, hn]

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hinf
  let O := oracleOf family hinf
  refine ⟨onlineOf O, ?_⟩
  intro i input hP
  refine ⟨GenLimit.PatientMachine.output O input, follows_onlineOf O input, ?_, ?_⟩
  · obtain ⟨hgen, hdens⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
    obtain ⟨T, hT⟩ := hgen
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨hmem, ?_, hnovel⟩
    intro hx
    rw [GenLimit.mem_sample_iff] at hx
    obtain ⟨s, hs, heq⟩ := hx
    exact hfresh s (Nat.lt_succ_iff.mp hs) heq
  · exact GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP

private theorem finite_range_diff_of_occurrence_noise
    {input : Stream} {K : Language}
    (hnoise : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
  exact hnoise.image input

private theorem exists_expansion_index
    (O : GenLimit.OracleFamily) {i : ℕ} {input : Stream}
    (hcomplete : O.language i ⊆ Set.range input)
    (hnoise : GenLimit.Generic.FinitelyManyViolations input
      (fun x => x ∈ O.language i)) :
    ∃ j, GenLimit.Presents input
      (GenLimit.InfiniteContamination.finiteExpansionLanguage O j) := by
  classical
  let noiseFinite : (Set.range input \ O.language i).Finite :=
    finite_range_diff_of_occurrence_noise hnoise
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm noiseFinite.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  change Set.range input =
    GenLimit.InfiniteContamination.finiteExpansionLanguage O j
  rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
  simp only [j, data,
    GenLimit.InfiniteContamination.finiteExpansionCode_encode,
    Equiv.apply_symm_apply]
  have hnoiseSet : (↑noiseFinite.toFinset : Set ℕ) =
      Set.range input \ O.language i :=
    Set.Finite.coe_toFinset noiseFinite
  rw [hnoiseSet]
  simp only [GenLimit.InfiniteContamination.finiteExpansion,
    Finset.coe_empty, Set.diff_empty]
  ext x
  constructor
  · intro hx
    by_cases hxK : x ∈ O.language i
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · rintro (hxK | ⟨hx, -⟩)
    · exact hcomplete hxK
    · exact hx

private theorem novelGenerates_of_finite_extraneous
    {input output : Stream} {K R : Language}
    (hP : GenLimit.Presents input R)
    (hfinite : (R \ K).Finite)
    (hgen : GenLimit.NovelGeneratesInLimit input output R) :
    GenLimit.NovelGeneratesInLimit input output K := by
  classical
  obtain ⟨Tgen, hTgen⟩ := hgen
  obtain ⟨Tseen, hTseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample
      hP hfinite.toFinset (by
        intro x hx
        exact (Set.Finite.mem_toFinset hfinite).mp hx |>.1)
  refine ⟨max Tgen Tseen, ?_⟩
  intro t ht
  have htGen : Tgen ≤ t := (Nat.le_max_left _ _).trans ht
  have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
  obtain ⟨hmemR, hfresh, hnovel⟩ := hTgen t htGen
  refine ⟨?_, hfresh, hnovel⟩
  by_contra hnotK
  have hbad : output t ∈ hfinite.toFinset :=
    (Set.Finite.mem_toFinset hfinite).mpr ⟨hmemR, hnotK⟩
  have hseenGeneric : output t ∈ GenLimit.Generic.sample input (t + 1) :=
    GenLimit.Generic.sample_mono
      (htSeen.trans (Nat.le_succ t)) (hTseen hbad)
  rw [GenLimit.Generic.mem_sample_iff] at hseenGeneric
  exact hfresh (GenLimit.mem_sample_iff.mpr hseenGeneric)

open Filter
open scoped Topology

private theorem liminf_le_of_eventually_le_add_vanishing
    (source target error : ℕ → ℝ)
    (hsourceNonneg : ∀ n, 0 ≤ source n)
    (htargetNonneg : ∀ n, 0 ≤ target n)
    (htargetLeOne : ∀ n, target n ≤ 1)
    (herror : Tendsto error atTop (nhds 0))
    (hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n) :
    liminf source atTop ≤ liminf target atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htargetLeOne)
    (isBoundedUnder_of ⟨0, htargetNonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrSource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrSource
      (isBoundedUnder_of ⟨0, hsourceNonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hcompare] with
      n hr hsmall hcount
  linarith

private theorem relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

private theorem relativeRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n

private theorem prefixCount_le_add_finite_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  have hsub :
      (Finset.range n).filter (fun x => x ∈ A) ⊆
        (Finset.range n).filter (fun x => x ∈ B) ∪ hfinite.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ((Set.Finite.mem_toFinset hfinite).mpr ⟨hx.2, hxB⟩)
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _)

private theorem relativeLowerDensity_mono_finite_extension
    {Q K R : Set ℕ} (hKR : K ⊆ R) (hfinite : (R \ K).Finite)
    (hKinf : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hnumFinite : ((Q ∩ R) \ (Q ∩ K)).Finite := by
    apply hfinite.subset
    intro x hx
    exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
  let error : ℕ → ℝ := fun n =>
    (hnumFinite.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hdenReal : Tendsto
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hKinf)
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hdenReal
  have hKpos : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    (GenLimit.PatientScope.tendsto_prefixCount_atTop hKinf).eventually
      (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      source n ≤ target n + error n := by
    filter_upwards [hKpos] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hden : (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        GenLimit.PatientScope.prefixCount R n := by
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hKR n
    have hcountNat := prefixCount_le_add_finite_diff hnumFinite n
    have hcount :
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (Q ∩ K) n +
            hnumFinite.toFinset.card := by
      exact_mod_cast hcountNat
    have hratio := div_le_div₀
      (show (0 : ℝ) ≤
        GenLimit.PatientScope.prefixCount (Q ∩ K) n +
          hnumFinite.toFinset.card by positivity)
      hcount hnR hden
    simpa only [source, target, error, add_div] using hratio
  unfold GenLimit.PatientScope.relativeLowerDensity
  exact liminf_le_of_eventually_le_add_vanishing source target error
    (fun n => relativeRatio_nonneg _ _ n)
    (fun n => relativeRatio_nonneg _ _ n)
    (fun n => relativeRatio_le_one (Set.inter_subset_right) n)
    herror hcompare

theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinf
  let O := oracleOf family hinf
  obtain ⟨gen, hgen⟩ := hpositive
    (GenLimit.InfiniteContamination.finiteExpansionLanguage O)
    (GenLimit.InfiniteContamination.finiteExpansionLanguage_infinite O)
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  obtain ⟨hcomplete, hnoise⟩ := hpresentation
  obtain ⟨j, hP⟩ := exists_expansion_index O hcomplete hnoise
  obtain ⟨output, hfollow, hnovelExpanded, hdensityExpanded⟩ :=
    hgen j input hP
  let R := GenLimit.InfiniteContamination.finiteExpansionLanguage O j
  have hfiniteRange : (Set.range input \ family i).Finite :=
    finite_range_diff_of_occurrence_noise hnoise
  have hfiniteR : (R \ family i).Finite := by
    change (GenLimit.InfiniteContamination.finiteExpansionLanguage O j \
      family i).Finite
    rw [← hP]
    exact hfiniteRange
  have hsubset : family i ⊆ R := by
    intro x hx
    change x ∈ GenLimit.InfiniteContamination.finiteExpansionLanguage O j
    rw [← hP]
    exact hcomplete hx
  refine ⟨output, hfollow, ?_, ?_⟩
  · exact novelGenerates_of_finite_extraneous hP hfiniteR hnovelExpanded
  · exact hdensityExpanded.trans
      (relativeLowerDensity_mono_finite_extension
        hsubset hfiniteR (hinf i))

theorem stage3_result : Stage3Case025.MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
