import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Combinatorics.Colex

open Stage3Case025

namespace Case025

open GenLimit

noncomputable def extendPrefix {t : ℕ} (xs : Fin t → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t then xs ⟨n, h⟩ else 0

lemma sample_eq_of_prefix_eq {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, (h n hn).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, h n hn⟩

lemma consistent_iff_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t i : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_eq_of_prefix_eq h]

lemma recursiveCritical_iff_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    ∀ i, GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero =>
        simpa only [GenLimit.RecursiveCritical] using
          consistent_iff_of_prefix_eq C h (i := 0)
    | succ i =>
        simp only [GenLimit.RecursiveCritical]
        rw [consistent_iff_of_prefix_eq C h]
        constructor
        · rintro ⟨hc, hsub⟩
          refine ⟨hc, ?_⟩
          intro j hj hjcrit
          exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjcrit)
        · rintro ⟨hc, hsub⟩
          refine ⟨hc, ?_⟩
          intro j hj hjcrit
          exact hsub j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjcrit)

lemma consistentIndices_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t scope : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.consistentIndices C a t scope =
      GenLimit.PatientMachine.consistentIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_consistentIndices]
  rw [consistent_iff_of_prefix_eq C h]

lemma criticalIndices_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t scope : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.criticalIndices C a t scope =
      GenLimit.PatientMachine.criticalIndices C b t scope := by
  ext i
  simp only [GenLimit.PatientMachine.mem_criticalIndices]
  rw [recursiveCritical_iff_of_prefix_eq C h]

lemma survivingCriticalIndices_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
      GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
  have hprev : ∀ n, n < t → a n = b n :=
    fun n hn => h n (Nat.lt.step hn)
  ext i
  simp only [GenLimit.PatientMachine.mem_survivingCriticalIndices]
  rw [recursiveCritical_iff_of_prefix_eq C hprev,
    recursiveCritical_iff_of_prefix_eq C h]

lemma highestCritical_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.highestCritical C a t scope fallback =
      GenLimit.PatientMachine.highestCritical C b t scope fallback := by
  simp only [GenLimit.PatientMachine.highestCritical]
  rw [criticalIndices_eq_of_prefix_eq C h]

lemma highestSurvivor_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
      GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
  simp only [GenLimit.PatientMachine.highestSurvivor]
  rw [survivingCriticalIndices_eq_of_prefix_eq C h]

lemma lowestConsistentInScope_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t scope fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistentInScope C a t scope fallback =
      GenLimit.PatientMachine.lowestConsistentInScope C b t scope fallback := by
  simp only [GenLimit.PatientMachine.lowestConsistentInScope]
  rw [consistentIndices_eq_of_prefix_eq C h]

lemma lowestConsistent_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t fallback : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.lowestConsistent C a t fallback =
      GenLimit.PatientMachine.lowestConsistent C b t fallback := by
  classical
  by_cases ha : ∃ i, GenLimit.Consistent C a t i
  · have hb : ∃ i, GenLimit.Consistent C b t i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (consistent_iff_of_prefix_eq C h).1 hi⟩
    simp only [GenLimit.PatientMachine.lowestConsistent, dif_pos ha, dif_pos hb]
    apply le_antisymm
    · exact Nat.find_min' ha
        ((consistent_iff_of_prefix_eq C h).2 (Nat.find_spec hb))
    · exact Nat.find_min' hb
        ((consistent_iff_of_prefix_eq C h).1 (Nat.find_spec ha))
  · have hb : ¬∃ i, GenLimit.Consistent C b t i := by
      rintro ⟨i, hi⟩
      exact ha ⟨i, (consistent_iff_of_prefix_eq C h).2 hi⟩
    simp [GenLimit.PatientMachine.lowestConsistent, ha, hb]

lemma stableDecision_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t : ℕ} (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.stableDecision C a t old =
      GenLimit.PatientMachine.stableDecision C b t old := by
  simp only [GenLimit.PatientMachine.stableDecision]
  split
  · simp only [highestCritical_eq_of_prefix_eq C h]
  · rfl

lemma backtrackDecision_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t : ℕ} (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.backtrackDecision C a t old =
      GenLimit.PatientMachine.backtrackDecision C b t old := by
  classical
  by_cases hallA : ∃ j, GenLimit.Consistent C a (t + 1) j
  · have hallB : ∃ j, GenLimit.Consistent C b (t + 1) j := by
      obtain ⟨j, hj⟩ := hallA
      exact ⟨j, (consistent_iff_of_prefix_eq C h).1 hj⟩
    simp only [GenLimit.PatientMachine.backtrackDecision]
    simp only [consistentIndices_eq_of_prefix_eq C h,
      survivingCriticalIndices_eq_of_prefix_eq C h,
      highestSurvivor_eq_of_prefix_eq C h,
      lowestConsistentInScope_eq_of_prefix_eq C h,
      lowestConsistent_eq_of_prefix_eq C h, hallA, hallB]
  · have hallB : ¬∃ j, GenLimit.Consistent C b (t + 1) j := by
      rintro ⟨j, hj⟩
      exact hallA ⟨j, (consistent_iff_of_prefix_eq C h).2 hj⟩
    simp only [GenLimit.PatientMachine.backtrackDecision]
    simp only [consistentIndices_eq_of_prefix_eq C h,
      survivingCriticalIndices_eq_of_prefix_eq C h,
      highestSurvivor_eq_of_prefix_eq C h,
      lowestConsistentInScope_eq_of_prefix_eq C h,
      lowestConsistent_eq_of_prefix_eq C h, hallA, hallB]

lemma decide_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    {a b : ℕ → ℕ} {t : ℕ} (old : GenLimit.PatientMachine.State)
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  unfold GenLimit.PatientMachine.decide
  rw [consistent_iff_of_prefix_eq C h]
  split
  · exact stableDecision_eq_of_prefix_eq C old h
  · exact backtrackDecision_eq_of_prefix_eq C old h

lemma leastAvailable_eq_of_prefix_eq (C : GenLimit.LanguageFamily)
    (hinf : ∀ i, (C i).Infinite) {a b : ℕ → ℕ} {t : ℕ}
    (used : Finset ℕ) (focus : ℕ) (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.leastAvailable C hinf a t used focus =
      GenLimit.PatientMachine.leastAvailable C hinf b t used focus := by
  classical
  apply le_antisymm
  · apply Nat.find_min'
    have hb := GenLimit.PatientMachine.leastAvailable_spec C hinf b t used focus
    exact ⟨hb.1, by rw [sample_eq_of_prefix_eq h]; exact hb.2.1, hb.2.2⟩
  · apply Nat.find_min'
    have ha := GenLimit.PatientMachine.leastAvailable_spec C hinf a t used focus
    exact ⟨ha.1, by rw [← sample_eq_of_prefix_eq h]; exact ha.2.1, ha.2.2⟩

lemma run_eq_of_prefix_eq (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} :
    ∀ t, (∀ n, n < t → a n = b n) →
      GenLimit.PatientMachine.run O a t = GenLimit.PatientMachine.run O b t := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      have hprev : ∀ n, n < t → a n = b n := fun n hn => h n (Nat.lt.step hn)
      have hr := ih hprev
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ, hr]
      have hd := decide_eq_of_prefix_eq O.language
        (GenLimit.PatientMachine.run O b t) h
      simp only [GenLimit.PatientMachine.processRound, hd]
      simp only [leastAvailable_eq_of_prefix_eq O.language O.infinite'
        (GenLimit.PatientMachine.run O b t).used
        (GenLimit.PatientMachine.decide O.language b t
          (GenLimit.PatientMachine.run O b t)).focus h]

lemma output_eq_of_prefix_eq (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_prefix_eq O (t + 1) h]

noncomputable def oracleOfFamily (family : ℕ → GenLimit.Language)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily := by
  classical
  exact
    { language := family
      infinite' := hinf
      query i x := decide (x ∈ family i)
      query_spec i x := by simp }

noncomputable def onlinePatient (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (extendPrefix xs) t

lemma follows_onlinePatient (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (onlinePatient O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  symm
  apply output_eq_of_prefix_eq
  intro n hn
  simp [extendPrefix, hn]

end Case025

/-- Section 4's positive-presentation engine. -/
theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  classical
  intro family hinf
  let O : GenLimit.OracleFamily := Case025.oracleOfFamily family hinf
  refine ⟨Case025.onlinePatient O, ?_⟩
  intro i input hP
  have hPO : GenLimit.Presents input (O.language i) := by
    simpa [O, Case025.oracleOfFamily] using hP
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, Case025.follows_onlinePatient O input, ?_, ?_⟩
  · obtain ⟨hgen, _⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hPO
    rcases hgen with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
    refine ⟨?_, ?_, hnovel⟩
    · simpa [O, Case025.oracleOfFamily, output] using hmem
    · intro hx
      rw [GenLimit.mem_sample_iff] at hx
      obtain ⟨s, hs, hsi⟩ := hx
      exact hfresh s (Nat.lt_succ_iff.mp hs) hsi
  · simpa [GenLimit.PatientMachine.patientLowerDensity, O,
      Case025.oracleOfFamily, output]
      using GenLimit.PatientMachine.patientScope_lowerDensity_half O input hPO

namespace Case025

open Filter
open scoped Topology

noncomputable def finiteAddFamily
    (family : ℕ → GenLimit.Language) (n : ℕ) : GenLimit.Language :=
  family (Nat.unpair n).1 ∪
    (Finset.equivBitIndices (Nat.unpair n).2 : Set ℕ)

lemma finiteAddFamily_infinite (family : ℕ → GenLimit.Language)
    (hinf : ∀ i, (family i).Infinite) (n : ℕ) :
    (finiteAddFamily family n).Infinite := by
  exact (hinf (Nat.unpair n).1).mono Set.subset_union_left

lemma finiteAddFamily_pair (family : ℕ → GenLimit.Language)
    (i : ℕ) (F : Finset ℕ) :
    finiteAddFamily family
        (Nat.pair i (Finset.equivBitIndices.symm F)) =
      family i ∪ (F : Set ℕ) := by
  simp [finiteAddFamily, Nat.unpair_pair]

lemma relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

lemma relativeRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hn]
  · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n

lemma prefixCount_le_add_finite
    {A B F : Set ℕ} (hsub : A ⊆ B ∪ F) (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hF.toFinset.card := by
  classical
  let a := GenLimit.PatientScope.prefixFinset A n
  let b := GenLimit.PatientScope.prefixFinset B n
  let f := GenLimit.PatientScope.prefixFinset F n
  have hab : a ⊆ b ∪ f := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    rcases hsub hx'.2 with hxB | hxF
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxF⟩)
  have hfcard : f.card ≤ hF.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hF |>.2
      (GenLimit.PatientScope.mem_prefixFinset.mp hx).2
  change a.card ≤ b.card + hF.toFinset.card
  exact (Finset.card_le_card hab).trans
    ((Finset.card_union_le b f).trans (Nat.add_le_add_left hfcard _))

lemma relativeLowerDensity_le_of_finite_extension
    {A B K L : Set ℕ}
    (hAK : A ⊆ K) (hBL : B ⊆ L) (hKL : K ⊆ L)
    (hBA : (B \ A).Finite) (hKinf : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity B L ≤
      GenLimit.PatientScope.relativeLowerDensity A K := by
  let error : ℕ → ℝ := fun n =>
    (hBA.toFinset.card : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcount := GenLimit.PatientScope.tendsto_prefixCount_atTop hKinf
  have hcast : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have herror : Tendsto error atTop (𝓝 0) := by
    exact Filter.Tendsto.const_div_atTop hcast (hBA.toFinset.card : ℝ)
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hcount.eventually (eventually_gt_atTop 0)
  have hratio : ∀ᶠ n : ℕ in atTop,
      (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount L n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount A n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) + error n := by
    filter_upwards [hpositive] with n hn
    have hden : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount L n :=
      GenLimit.PatientScope.prefixCount_mono hKL n
    have hnum : GenLimit.PatientScope.prefixCount B n ≤
        GenLimit.PatientScope.prefixCount A n + hBA.toFinset.card := by
      apply prefixCount_le_add_finite (F := B \ A) (hF := hBA)
      intro x hx
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr ⟨hx, hxA⟩
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdenR : (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        GenLimit.PatientScope.prefixCount L n := by
      exact_mod_cast hden
    have hnumR : (GenLimit.PatientScope.prefixCount B n : ℝ) ≤
        GenLimit.PatientScope.prefixCount A n + hBA.toFinset.card := by
      exact_mod_cast hnum
    calc
      (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount L n : ℝ)
          ≤ (GenLimit.PatientScope.prefixCount B n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
                exact div_le_div_of_nonneg_left (by positivity) hnR hdenR
      _ ≤ ((GenLimit.PatientScope.prefixCount A n : ℝ) +
              hBA.toFinset.card) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
              exact div_le_div_of_nonneg_right hnumR hnR.le
      _ = (GenLimit.PatientScope.prefixCount A n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) + error n := by
            simp only [error]
            rw [add_div]
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (relativeRatio_le_one hAK))
    (isBoundedUnder_of ⟨0, relativeRatio_nonneg A K⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop,
      r < (GenLimit.PatientScope.prefixCount B n : ℝ) /
        (GenLimit.PatientScope.prefixCount L n : ℝ) :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, relativeRatio_nonneg B L⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hratio] with n hrn hen hrat
  linarith

end Case025

/-- Section 5's finite-noise transfer. -/
theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  classical
  intro h family hinf
  let expanded : ℕ → GenLimit.Language := Case025.finiteAddFamily family
  have hexpanded : ∀ j, (expanded j).Infinite := by
    intro j
    exact Case025.finiteAddFamily_infinite family hinf j
  obtain ⟨gen, hgen⟩ := h expanded hexpanded
  refine ⟨gen, ?_⟩
  intro i input hcontam
  rcases hcontam with ⟨hcover, hviol⟩
  let noiseSet : Set ℕ := Set.range input \ family i
  have hnoiseFinite : noiseSet.Finite := by
    unfold noiseSet
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hviol.image input
  let noise : Finset ℕ := hnoiseFinite.toFinset
  let j : ℕ := Nat.pair i (Finset.equivBitIndices.symm noise)
  have hnoiseCoe : (noise : Set ℕ) = noiseSet := by
    exact Set.Finite.coe_toFinset hnoiseFinite
  have hrange : Set.range input = family i ∪ noiseSet := by
    ext x
    constructor
    · intro hx
      by_cases hxi : x ∈ family i
      · exact Or.inl hxi
      · exact Or.inr ⟨hx, hxi⟩
    · rintro (hxi | hxnoise)
      · exact hcover hxi
      · exact hxnoise.1
  have hpresents : GenLimit.Presents input (expanded j) := by
    rw [show expanded j = family i ∪ (noise : Set ℕ) by
      exact Case025.finiteAddFamily_pair family i noise]
    rw [hnoiseCoe]
    exact hrange
  obtain ⟨output, hfollow, hnovelExpanded, hdensityExpanded⟩ :=
    hgen j input hpresents
  refine ⟨output, hfollow, ?_, ?_⟩
  · obtain ⟨Tgen, hTgen⟩ := hnovelExpanded
    obtain ⟨Tseen, hTseenGeneric⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample
        (stream := input) (L := Set.range input) rfl noise (by
          intro x hx
          have hxNoise : x ∈ noiseSet := by
            rw [← hnoiseCoe]
            exact hx
          exact hxNoise.1)
    have hTseen : noise ⊆ GenLimit.sample input Tseen := by
      intro x hx
      have hxGeneric := hTseenGeneric hx
      rw [GenLimit.Generic.mem_sample_iff] at hxGeneric
      rw [GenLimit.mem_sample_iff]
      exact hxGeneric
    refine ⟨max Tgen Tseen, ?_⟩
    intro t ht
    have htgen : Tgen ≤ t := (Nat.le_max_left _ _).trans ht
    have htseen : Tseen ≤ t + 1 :=
      (Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)
    obtain ⟨hmemExpanded, hfresh, hdistinct⟩ := hTgen t htgen
    refine ⟨?_, hfresh, hdistinct⟩
    rw [show expanded j = family i ∪ (noise : Set ℕ) by
      exact Case025.finiteAddFamily_pair family i noise] at hmemExpanded
    rcases hmemExpanded with hmem | hmemNoise
    · exact hmem
    · exact False.elim (hfresh
        (GenLimit.sample_mono htseen (hTseen hmemNoise)))
  · have htransfer := Case025.relativeLowerDensity_le_of_finite_extension
      (A := GenLimit.GeneratorFirst input output ∩ family i)
      (B := GenLimit.GeneratorFirst input output ∩ expanded j)
      (K := family i) (L := expanded j)
      (hAK := Set.inter_subset_right)
      (hBL := Set.inter_subset_right)
      (hKL := by
        rw [show expanded j = family i ∪ (noise : Set ℕ) by
          exact Case025.finiteAddFamily_pair family i noise]
        exact Set.subset_union_left)
      (hBA := by
        apply noise.finite_toSet.subset
        intro x hx
        have hxExpanded : x ∈ expanded j := hx.1.2
        have hxNotBase : x ∉ family i := by
          intro hxi
          exact hx.2 ⟨hx.1.1, hxi⟩
        rw [show expanded j = family i ∪ (noise : Set ℕ) by
          exact Case025.finiteAddFamily_pair family i noise] at hxExpanded
        exact hxExpanded.resolve_left hxNotBase)
      (hKinf := hinf i)
    exact hdensityExpanded.trans htransfer

/-- Primary endpoint. -/
theorem stage3_result : MainClaim := by
  exact stage3_finite_noise_transfer stage3_positive_engine
