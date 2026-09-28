import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open Stage3Case025

namespace Stage3Case025Proof

noncomputable def oracleOfFamily (family : ℕ → Language)
    (hInfinite : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

private theorem sample_eq_of_prefix_eq
    {a b : ℕ → ℕ} {t : ℕ} (h : ∀ n, n < t → a n = b n) :
    GenLimit.sample a t = GenLimit.sample b t := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

private theorem consistent_iff_of_prefix_eq
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.Consistent C a t i ↔ GenLimit.Consistent C b t i := by
  simp only [GenLimit.Consistent, sample_eq_of_prefix_eq h]

private theorem recursiveCritical_iff_of_prefix_eq
    {C : GenLimit.LanguageFamily} {a b : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa [GenLimit.RecursiveCritical] using
        consistent_iff_of_prefix_eq (C := C) (i := 0) h
    | succ i =>
      simp only [GenLimit.RecursiveCritical]
      rw [consistent_iff_of_prefix_eq (C := C) (i := i + 1) h]
      constructor <;> rintro ⟨hc, hcrit⟩ <;> refine ⟨hc, ?_⟩
      · intro j hj hjcrit
        exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).2 hjcrit)
      · intro j hj hjcrit
        exact hcrit j hj ((ih j (Nat.lt_succ_of_le hj)).1 hjcrit)

private theorem processRound_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n)
    (old : GenLimit.PatientMachine.State) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  classical
  have hs : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
    sample_eq_of_prefix_eq h
  have hc : ∀ i,
      GenLimit.Consistent O.language a (t + 1) i ↔
        GenLimit.Consistent O.language b (t + 1) i :=
    fun i => consistent_iff_of_prefix_eq h
  have hct : ∀ i,
      GenLimit.RecursiveCritical O.language a t i ↔
        GenLimit.RecursiveCritical O.language b t i := by
    intro i
    apply recursiveCritical_iff_of_prefix_eq
    intro n hn
    exact h n (lt_trans hn (Nat.lt_succ_self t))
  have hcs : ∀ i,
      GenLimit.RecursiveCritical O.language a (t + 1) i ↔
        GenLimit.RecursiveCritical O.language b (t + 1) i :=
    fun i => recursiveCritical_iff_of_prefix_eq h
  have hconsistent : ∀ scope,
      GenLimit.PatientMachine.consistentIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.consistentIndices O.language b (t + 1) scope := by
    intro scope
    simp only [GenLimit.PatientMachine.consistentIndices]
    congr 1
    funext i
    exact propext (hc i)
  have hcritical : ∀ scope,
      GenLimit.PatientMachine.criticalIndices O.language a (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices O.language b (t + 1) scope := by
    intro scope
    simp only [GenLimit.PatientMachine.criticalIndices]
    congr 1
    funext i
    exact propext (hcs i)
  have hsurviving : ∀ scope,
      GenLimit.PatientMachine.survivingCriticalIndices O.language a t scope =
        GenLimit.PatientMachine.survivingCriticalIndices O.language b t scope := by
    intro scope
    simp only [GenLimit.PatientMachine.survivingCriticalIndices]
    congr 1
    funext i
    exact propext (and_congr (hct i) (hcs i))
  have hhighCritical : ∀ scope fallback,
      GenLimit.PatientMachine.highestCritical O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical O.language b (t + 1) scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.highestCritical]
    rw [hcritical]
  have hhighSurvivor : ∀ scope fallback,
      GenLimit.PatientMachine.highestSurvivor O.language a t scope fallback =
        GenLimit.PatientMachine.highestSurvivor O.language b t scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.highestSurvivor]
    rw [hsurviving]
  have hlowScope : ∀ scope fallback,
      GenLimit.PatientMachine.lowestConsistentInScope O.language a (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope O.language b (t + 1) scope fallback := by
    intro scope fallback
    simp only [GenLimit.PatientMachine.lowestConsistentInScope]
    rw [hconsistent]
  have hlowGlobal : ∀ fallback,
      GenLimit.PatientMachine.lowestConsistent O.language a (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent O.language b (t + 1) fallback := by
    intro fallback
    unfold GenLimit.PatientMachine.lowestConsistent
    by_cases ha : ∃ i, GenLimit.Consistent O.language a (t + 1) i
    · have hb : ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        obtain ⟨i, hi⟩ := ha
        exact ⟨i, (hc i).1 hi⟩
      simp only [ha, hb, dif_pos]
      apply Nat.find_congr (Nat.find_spec ha)
      intro n hn
      exact hc n
    · have hb : ¬ ∃ i, GenLimit.Consistent O.language b (t + 1) i := by
        rintro ⟨i, hi⟩
        exact ha ⟨i, (hc i).2 hi⟩
      simp [ha, hb]
  have hstable :
      GenLimit.PatientMachine.stableDecision O.language a t old =
        GenLimit.PatientMachine.stableDecision O.language b t old := by
    simp only [GenLimit.PatientMachine.stableDecision, hhighCritical]
  have hexistsConsistent :
      (∃ j, GenLimit.Consistent O.language a (t + 1) j) ↔
        ∃ j, GenLimit.Consistent O.language b (t + 1) j := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (hc j).1 hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, (hc j).2 hj⟩
  have hbacktrack :
      GenLimit.PatientMachine.backtrackDecision O.language a t old =
        GenLimit.PatientMachine.backtrackDecision O.language b t old := by
    simp only [GenLimit.PatientMachine.backtrackDecision, hconsistent,
      hsurviving, hhighSurvivor, hlowScope, hlowGlobal, hexistsConsistent]
  have hdecision :
      GenLimit.PatientMachine.decide O.language a t old =
        GenLimit.PatientMachine.decide O.language b t old := by
    unfold GenLimit.PatientMachine.decide
    by_cases ha : GenLimit.Consistent O.language a (t + 1) old.focus
    · have hb := (hc old.focus).1 ha
      simp [ha, hb, hstable]
    · have hb : ¬ GenLimit.Consistent O.language b (t + 1) old.focus :=
        fun hbad => ha ((hc old.focus).2 hbad)
      simp [ha, hb, hbacktrack]
  have hleast : ∀ focus,
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a
          (t + 1) old.used focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b
          (t + 1) old.used focus := by
    intro focus
    apply Nat.le_antisymm
    · apply GenLimit.PatientMachine.leastAvailable_minimal
        O.language O.infinite' a (t + 1) old.used focus
        (GenLimit.PatientMachine.leastAvailable O.language O.infinite'
          b (t + 1) old.used focus)
      simpa only [GenLimit.PatientMachine.Available, hs] using
        GenLimit.PatientMachine.leastAvailable_spec O.language O.infinite'
          b (t + 1) old.used focus
    · apply GenLimit.PatientMachine.leastAvailable_minimal
        O.language O.infinite' b (t + 1) old.used focus
        (GenLimit.PatientMachine.leastAvailable O.language O.infinite'
          a (t + 1) old.used focus)
      simpa only [GenLimit.PatientMachine.Available, ← hs] using
        GenLimit.PatientMachine.leastAvailable_spec O.language O.infinite'
          a (t + 1) old.used focus

  simp only [GenLimit.PatientMachine.processRound, hdecision, hleast]

private theorem run_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → a n = b n) :
    GenLimit.PatientMachine.run O a t =
      GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, ih]
      · exact processRound_eq_of_prefix_eq O h _
      · intro n hn
        exact h n (lt_trans hn (Nat.lt_succ_self t))

private theorem output_eq_of_prefix_eq
    (O : GenLimit.OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → a n = b n) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  simp only [GenLimit.PatientMachine.output, run_eq_of_prefix_eq O h]

private def extendPrefix {t : ℕ} (input : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then input ⟨n, h⟩ else 0

noncomputable def onlinePatient (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t input _ => GenLimit.PatientMachine.output O (extendPrefix input) t

private theorem follows_onlinePatient (O : GenLimit.OracleFamily)
    (input : Stream) :
    Follows (onlinePatient O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  apply output_eq_of_prefix_eq
  intro n hn
  simp [extendPrefix, hn]

private theorem exists_expansion_index
    (O : GenLimit.OracleFamily) {z : ℕ} {input : Stream}
    (hpres : CompleteFiniteOccurrencePresentation input (O.language z)) :
    ∃ j,
      GenLimit.InfiniteContamination.finiteExpansionBaseIndex j = z ∧
      GenLimit.Presents input
        ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) ∧
      O.language z ⊆
        (GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j ∧
      (((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) \
        O.language z).Finite := by
  classical
  let noise := GenLimit.InfiniteContamination.displayedNoise input (O.language z)
  have hnoise : noise.Finite :=
    GenLimit.InfiniteContamination.displayedNoise_finite hpres.2
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (z, Finset.equivBitIndices.symm hnoise.toFinset,
      Finset.equivBitIndices.symm ∅)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  have hp : GenLimit.Presents input
      ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) := by
    change Set.range input =
      GenLimit.InfiniteContamination.finiteExpansionLanguage O j
    have hadd : (↑hnoise.toFinset : Set ℕ) = noise :=
      Set.Finite.coe_toFinset hnoise
    rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
    simp only [j, data,
      GenLimit.InfiniteContamination.finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    rw [hadd]
    ext x
    simp only [GenLimit.InfiniteContamination.finiteExpansion, noise,
      GenLimit.InfiniteContamination.displayedNoise, Set.mem_diff,
      Set.mem_union, Set.mem_range, Finset.coe_empty, Set.mem_empty_iff_false,
      not_false_eq_true, and_true]
    constructor
    · intro hx
      by_cases hxK : x ∈ O.language z
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
    · rintro (hxK | ⟨hx, _⟩)
      · exact hpres.1 hxK
      · exact hx
  refine ⟨j, ?_, hp, ?_, ?_⟩
  · simp [GenLimit.InfiniteContamination.finiteExpansionBaseIndex, j, data]
  · rw [← hp]
    exact hpres.1
  · rw [← hp]
    exact hnoise

private theorem prefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + (A \ B).ncard := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  let a := (Finset.range n).filter fun x => x ∈ A
  let b := (Finset.range n).filter fun x => x ∈ B
  let d := (Finset.range n).filter fun x => x ∈ A \ B
  have hsub : a ⊆ b ∪ d := by
    intro x hx
    simp only [a, b, d, Finset.mem_filter, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hd : d.card ≤ (A \ B).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfinite]
    apply Finset.card_le_card
    intro x hx
    simp only [d, Finset.mem_filter] at hx
    exact Set.Finite.mem_toFinset hfinite |>.2 hx.2
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le b d).trans (Nat.add_le_add_left hd _))

private theorem relativeLowerDensity_le_of_finite_super
    {A K E : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ E) E ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
      GenLimit.PatientScope.prefixCount E n
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  let error : ℕ → ℝ := fun n =>
    ((E \ K).ncard : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  have hcount : ∀ n,
      GenLimit.PatientScope.prefixCount (A ∩ E) n ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + (E \ K).ncard := by
    intro n
    have hdiff : ((A ∩ E) \ (A ∩ K)).Finite := by
      apply hfinite.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hc := prefixCount_le_add_ncard_diff hdiff n
    have hncard : ((A ∩ E) \ (A ∩ K)).ncard ≤ (E \ K).ncard := by
      apply Set.ncard_le_ncard
      · intro x hx
        exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
      · exact hfinite
    omega
  have herror : Tendsto error atTop (nhds 0) := by
    have hden := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hden)
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    (GenLimit.PatientScope.tendsto_prefixCount_atTop hK).eventually
      (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hden : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount E n :=
      GenLimit.PatientScope.prefixCount_mono hKE n
    have hnum : (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) ≤
        GenLimit.PatientScope.prefixCount (A ∩ K) n + (E \ K).ncard := by
      exact_mod_cast hcount n
    dsimp [source, target, error]
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          GenLimit.PatientScope.prefixCount E n ≤
        (GenLimit.PatientScope.prefixCount (A ∩ E) n : ℝ) /
          GenLimit.PatientScope.prefixCount K n := by
            apply div_le_div_of_nonneg_left
            · positivity
            · exact hnR
            · exact_mod_cast hden
      _ ≤ ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) +
            (E \ K).ncard) /
          GenLimit.PatientScope.prefixCount K n := by
            exact div_le_div_of_nonneg_right hnum hnR.le
      _ = (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n +
          ((E \ K).ncard : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by
            rw [add_div]
  have htarget_nonneg : ∀ n, (0 : ℝ) ≤ target n := by
    intro n
    dsimp [target]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htarget_le_one : ∀ n, target n ≤ (1 : ℝ) := by
    intro n
    have hcount_le := GenLimit.PatientScope.prefixCount_mono
      (Set.inter_subset_right : A ∩ K ⊆ K) n
    dsimp [target]
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · have hnum : GenLimit.PatientScope.prefixCount (A ∩ K) n = 0 := by
        omega
      simp [hn, hnum]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast hcount_le
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff'
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨(0 : ℝ), htarget_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, fun n => by dsimp [source]; positivity⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hn herr hp
  linarith

end Stage3Case025Proof

open Stage3Case025Proof

theorem stage3_result : Stage3Case025.MainClaim := by
  intro family hInfinite
  let O := oracleOfFamily family hInfinite
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨onlinePatient E, ?_⟩
  intro i input hpres
  obtain ⟨j, _hbase, hpresents, hsubset, hfinite⟩ :=
    exists_expansion_index O hpres
  let output := GenLimit.PatientMachine.output E input
  have hpatient :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      E input hpresents
  obtain ⟨⟨Tgenerate, hgenerate⟩, hdensity⟩ := hpatient
  obtain ⟨Tseen, hseen⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hpresents hfinite.toFinset (by
      intro x hx
      exact ((Set.Finite.mem_toFinset hfinite).mp hx).1)
  refine ⟨output, follows_onlinePatient E input, ?_, ?_⟩
  · refine ⟨max Tgenerate Tseen, ?_⟩
    intro t ht
    have htGenerate : Tgenerate ≤ t := (Nat.le_max_left _ _).trans ht
    have htSeen : Tseen ≤ t + 1 :=
      (Nat.le_max_right _ _).trans (ht.trans (Nat.le_succ t))
    have hg := hgenerate t htGenerate
    have hseenNow : hfinite.toFinset ⊆ GenLimit.sample input (t + 1) := by
      intro x hx
      apply GenLimit.sample_mono htSeen
      simpa [GenLimit.sample, GenLimit.Generic.sample] using hseen hx
    refine ⟨?_, ?_, hg.2.2⟩
    · by_contra hout
      have hbad : output t ∈ hfinite.toFinset :=
        (Set.Finite.mem_toFinset hfinite).mpr ⟨hg.1, hout⟩
      have hmem := hseenNow hbad
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hmem
      exact hg.2.1 s (Nat.lt_succ_iff.mp hs) heq
    · intro hmem
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hmem
      exact hg.2.1 s (Nat.lt_succ_iff.mp hs) heq
  · have htransfer := relativeLowerDensity_le_of_finite_super
      (A := GenLimit.GeneratorFirst input output)
      (K := O.language i) (E := E.language j)
      (O.infinite' i) hsubset hfinite
    exact hdensity.trans htransfer
