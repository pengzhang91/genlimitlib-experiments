import Stage3Model
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import Mathlib.Data.Nat.Nth

open Set
open GenLimit
open GenLimit.Generic

namespace Test

noncomputable def extend {n : ℕ} (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if h : k < n then xs ⟨k,h⟩ else 0

noncomputable def patientGen (O : OracleFamily) : Generator ℕ :=
  fun n xs => match n with
  | 0 => 0
  | t+1 => PatientMachine.output O (extend xs) t

lemma sample_extend {n m : ℕ} (xs : Fin n → ℕ) (h : m ≤ n) :
    Generic.sample (extend xs) m = Generic.sequenceSample (fun i : Fin m => xs ⟨i, lt_of_lt_of_le i.isLt h⟩) := by
  classical
  ext x
  simp only [Generic.mem_sample_iff, Generic.mem_sequenceSample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k,hk⟩, ?_⟩
    simp [extend, lt_of_lt_of_le hk h]
  · rintro ⟨k, rfl⟩
    refine ⟨k, k.isLt, ?_⟩
    simp [extend, lt_of_lt_of_le k.isLt h]

lemma sample_eq_of_eq_lt {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) :
    GenLimit.sample a n = GenLimit.sample b n := by
  classical
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k,hk,ha⟩
    exact ⟨k,hk,(h k hk).symm.trans ha⟩
  · rintro ⟨k,hk,hb⟩
    exact ⟨k,hk,(h k hk).trans hb⟩

lemma consistent_iff_of_sample_eq (C : LanguageFamily) {a b : ℕ → ℕ} {n i : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    Consistent C a n i ↔ Consistent C b n i := by
  unfold Consistent
  rw [h]

lemma recursiveCritical_iff_of_sample_eq (C : LanguageFamily)
    {a b : ℕ → ℕ} {n : ℕ}
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    ∀ i, RecursiveCritical C a n i ↔ RecursiveCritical C b n i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [RecursiveCritical] using consistent_iff_of_sample_eq C h
      | succ i =>
          simp only [RecursiveCritical]
          rw [consistent_iff_of_sample_eq C h]
          constructor <;> rintro ⟨hc, hr⟩ <;> refine ⟨hc, ?_⟩
          · intro j hj hjc
            exact hr j hj ((ih j (by omega)).mpr hjc)
          · intro j hj hjc
            exact hr j hj ((ih j (by omega)).mp hjc)

lemma decide_eq_of_samples
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : PatientMachine.State)
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t+1) = GenLimit.sample b (t+1)) :
    PatientMachine.decide O.language a t old = PatientMachine.decide O.language b t old := by
  classical
  have hc1 : ∀ i, Consistent O.language a (t+1) i ↔ Consistent O.language b (t+1) i :=
    fun i => consistent_iff_of_sample_eq O.language h1
  have hr0 := recursiveCritical_iff_of_sample_eq O.language h0
  have hr1 := recursiveCritical_iff_of_sample_eq O.language h1
  have hcon : PatientMachine.consistentIndices O.language a (t+1) old.scope =
      PatientMachine.consistentIndices O.language b (t+1) old.scope := by
    ext i
    simp only [PatientMachine.mem_consistentIndices, hc1]
  have hcrit : PatientMachine.criticalIndices O.language a (t+1) (old.scope+1) =
      PatientMachine.criticalIndices O.language b (t+1) (old.scope+1) := by
    ext i
    simp only [PatientMachine.mem_criticalIndices, hr1]
  have hsurv : PatientMachine.survivingCriticalIndices O.language a t old.scope =
      PatientMachine.survivingCriticalIndices O.language b t old.scope := by
    ext i
    simp only [PatientMachine.mem_survivingCriticalIndices, hr0, hr1]
  have hhigh : PatientMachine.highestCritical O.language a (t+1) (old.scope+1) old.focus =
      PatientMachine.highestCritical O.language b (t+1) (old.scope+1) old.focus := by
    unfold PatientMachine.highestCritical
    rw [hcrit]
  have hsurvHigh : PatientMachine.highestSurvivor O.language a t old.scope old.focus =
      PatientMachine.highestSurvivor O.language b t old.scope old.focus := by
    unfold PatientMachine.highestSurvivor
    rw [hsurv]
  have hlowScope : PatientMachine.lowestConsistentInScope O.language a (t+1) old.scope old.focus =
      PatientMachine.lowestConsistentInScope O.language b (t+1) old.scope old.focus := by
    unfold PatientMachine.lowestConsistentInScope
    rw [hcon]
  have hlow : PatientMachine.lowestConsistent O.language a (t+1) old.focus =
      PatientMachine.lowestConsistent O.language b (t+1) old.focus := by
    by_cases ha : ∃ i, Consistent O.language a (t+1) i
    · have hb : ∃ i, Consistent O.language b (t+1) i := by
        rcases ha with ⟨i, hi⟩
        exact ⟨i, (hc1 i).mp hi⟩
      simp only [PatientMachine.lowestConsistent, ha, hb, ↓reduceDIte]
      apply Nat.find_congr (Nat.find_spec ha)
      intro n _hn
      exact hc1 n
    · have hb : ¬ ∃ i, Consistent O.language b (t+1) i := by
        intro hb
        rcases hb with ⟨i, hi⟩
        exact ha ⟨i, (hc1 i).mpr hi⟩
      simp [PatientMachine.lowestConsistent, ha, hb]
  unfold PatientMachine.decide PatientMachine.stableDecision PatientMachine.backtrackDecision
  rw [hc1 old.focus]
  split
  · simp only [hhigh]
  · simp only [hcon, hsurv, hsurvHigh, hlowScope, hlow, hc1]

lemma leastAvailable_eq_of_sample_eq
    (O : OracleFamily) {a b : ℕ → ℕ} (n : ℕ) (used : Finset ℕ) (focus : ℕ)
    (h : GenLimit.sample a n = GenLimit.sample b n) :
    PatientMachine.leastAvailable O.language O.infinite' a n used focus =
      PatientMachine.leastAvailable O.language O.infinite' b n used focus := by
  classical
  let ha := PatientMachine.available_exists O.language O.infinite' a n used focus
  let hb := PatientMachine.available_exists O.language O.infinite' b n used focus
  change Nat.find ha = Nat.find hb
  apply Nat.find_congr (Nat.find_spec ha)
  intro x _hx
  unfold PatientMachine.Available
  rw [h]

lemma processRound_eq_of_samples
    (O : OracleFamily) {a b : ℕ → ℕ} (t : ℕ)
    (old : PatientMachine.State)
    (h0 : GenLimit.sample a t = GenLimit.sample b t)
    (h1 : GenLimit.sample a (t+1) = GenLimit.sample b (t+1)) :
    PatientMachine.processRound O a t old = PatientMachine.processRound O b t old := by
  classical
  have hd := decide_eq_of_samples O t old h0 h1
  have hx := leastAvailable_eq_of_sample_eq O (t+1) old.used
    (PatientMachine.decide O.language b t old).focus h1
  simp only [PatientMachine.processRound]
  rw [hd, hx]

lemma run_eq_of_eq_lt (O : OracleFamily) {a b : ℕ → ℕ} (n : ℕ)
    (h : ∀ k, k < n → a k = b k) :
    PatientMachine.run O a n = PatientMachine.run O b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      have hr := ih (fun k hk => h k (Nat.lt.step hk))
      rw [hr]
      apply processRound_eq_of_samples O
      · apply sample_eq_of_eq_lt
        exact fun k hk => h k (Nat.lt.step hk)
      · apply sample_eq_of_eq_lt
        exact h

lemma patientGen_output (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Generic.output (patientGen O) stream (t+1) =
      PatientMachine.output O stream t := by
  unfold Generic.output patientGen
  simp only
  unfold PatientMachine.output
  rw [run_eq_of_eq_lt O (n := t+1)]
  intro k hk
  simp [extend, hk]

end Test

open Filter
open scoped Topology

namespace Test

lemma relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

lemma relativeRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hz]
  · rw [div_le_one (by positivity)]
    exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAK n

lemma relativeLowerDensity_le_of_eventually_ratio_le
    (source output K : Set ℕ) (hK : K.Infinite)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hsource : source ⊆ K) (houtput : output ⊆ K)
    (hprefix : ∀ᶠ n : ℕ in atTop,
      (GenLimit.PatientScope.prefixCount source n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount output n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) + error n) :
    GenLimit.PatientScope.relativeLowerDensity source K ≤
      GenLimit.PatientScope.relativeLowerDensity output K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => relativeRatio_le_one houtput n))
    (isBoundedUnder_of ⟨0, fun n => relativeRatio_nonneg output K n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrDensity⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop,
      r < (GenLimit.PatientScope.prefixCount source n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) :=
    eventually_lt_of_lt_liminf hrDensity
      (isBoundedUnder_of ⟨0, fun n => relativeRatio_nonneg source K n⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr he hp
  linarith

lemma prefixCount_le_add_finite
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  have hsub :
      (Finset.range n).filter (fun x => x ∈ A) ⊆
        (Finset.range n).filter (fun x => x ∈ B) ∪ hfinite.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    by_cases hB : x ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx.1, hB⟩)
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset hfinite).mpr ⟨hx.2, hB⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma relativeLowerDensity_eq_of_finite_symmetricDifference
    {A B K : Set ℕ} (hK : K.Infinite)
    (hA : A ⊆ K) (hB : B ⊆ K)
    (hAB : (A \ B).Finite) (hBA : (B \ A).Finite) :
    GenLimit.PatientScope.relativeLowerDensity A K =
      GenLimit.PatientScope.relativeLowerDensity B K := by
  have hcast : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop := by
    simpa [Function.comp_apply] using
      tendsto_natCast_atTop_atTop.comp
        (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
  apply le_antisymm
  · have hc : Tendsto (fun _ : ℕ => (hAB.toFinset.card : ℝ)) atTop
        (𝓝 (hAB.toFinset.card : ℝ)) := tendsto_const_nhds
    have herr : Tendsto
        (fun n => (hAB.toFinset.card : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop (𝓝 0) :=
      hc.div_atTop hcast
    apply relativeLowerDensity_le_of_eventually_ratio_le A B K hK
      _ herr hA hB
    filter_upwards with n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · rw [← add_div]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast prefixCount_le_add_finite hAB n)
        (by positivity)
  · have hc : Tendsto (fun _ : ℕ => (hBA.toFinset.card : ℝ)) atTop
        (𝓝 (hBA.toFinset.card : ℝ)) := tendsto_const_nhds
    have herr : Tendsto
        (fun n => (hBA.toFinset.card : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop (𝓝 0) :=
      hc.div_atTop hcast
    apply relativeLowerDensity_le_of_eventually_ratio_le B A K hK
      _ herr hB hA
    filter_upwards with n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · rw [← add_div]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast prefixCount_le_add_finite hBA n)
        (by positivity)

lemma relativeLowerDensity_antitone_denominator
    {A K E : Set ℕ} (hA : A ⊆ K) (hKE : K ⊆ E) (hE : E.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity A E ≤
      GenLimit.PatientScope.relativeLowerDensity A K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · filter_upwards with n
    have hden := GenLimit.PatientScope.prefixCount_mono hKE n
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · have ha : GenLimit.PatientScope.prefixCount A n = 0 :=
        Nat.eq_zero_of_le_zero (hk ▸ GenLimit.PatientScope.prefixCount_mono hA n)
      simp [ha]
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by exact_mod_cast hden)
  · exact isBoundedUnder_of ⟨0, fun n => relativeRatio_nonneg A E n⟩
  · exact isCoboundedUnder_ge_of_le atTop
      (fun n => relativeRatio_le_one hA n)

noncomputable def familyOracle (family : ℕ → Set ℕ)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

lemma finiteContamination_of_bounded
    {input : ℕ → ℕ} {K : Set ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration input K := by
  rcases h with ⟨hinj, hcover, F, hF, hcard⟩
  refine ⟨hinj, ?_, ?_⟩
  · apply (GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective hinj).mpr
    rw [← hF]
    exact F.finite_toSet
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [Set.diff_eq_empty.mpr hcover]
    exact Set.finite_empty

lemma generatorFirst_congr {input out₁ out₂ : ℕ → ℕ}
    (h : ∀ t, out₁ t = out₂ t) :
    GenLimit.GeneratorFirst input out₁ = GenLimit.GeneratorFirst input out₂ := by
  ext x
  simp only [GenLimit.GeneratorFirst, Set.mem_setOf_eq]
  constructor <;> rintro ⟨t, ht, hf⟩ <;> refine ⟨t, ?_, hf⟩
  · exact (h t).symm.trans ht
  · exact (h t).trans ht

lemma countable_half_density : Stage3Case019.CountableClause := by
  intro q family hinf
  let O := familyOracle family hinf
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGen E, ?_⟩
  intro i input hinput
  have hcontam := finiteContamination_of_bounded hinput
  obtain ⟨j, hj, hpresents⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hrun := GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
    E input hpresents
  have hout : ∀ t, Stage3Case019.outputAfterInput (patientGen E) input t =
      GenLimit.PatientMachine.output E input t := fun t => patientGen_output E input t
  constructor
  · obtain ⟨T, hT⟩ := hrun.1
    have hnoise : (E.language j \ family i).Finite := by
      rw [hpresents.symm]
      rcases hinput.2.2 with ⟨F, hF, _⟩
      rw [← hF]
      exact F.finite_toSet
    obtain ⟨Tseen, hTseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample
        hpresents hnoise.toFinset (by
          intro x hx
          exact ((Set.Finite.mem_toFinset hnoise).mp hx).1)
    refine ⟨max T Tseen, ?_⟩
    intro t ht
    have hh := hT t ((Nat.le_max_left _ _).trans ht)
    have hseen : hnoise.toFinset ⊆ GenLimit.Generic.sample input (t+1) := by
      intro x hx
      exact GenLimit.Generic.sample_mono
        ((Nat.le_max_right _ _).trans ht |>.trans (Nat.le_succ t)) (hTseen hx)
    rw [hout t]
    refine ⟨?_, ?_, ?_⟩
    · by_contra hnot
      have hbad : GenLimit.PatientMachine.output E input t ∈ hnoise.toFinset :=
        (Set.Finite.mem_toFinset hnoise).mpr ⟨hh.1, hnot⟩
      have hsample := hseen hbad
      obtain ⟨s, hs, heq⟩ := GenLimit.Generic.mem_sample_iff.mp hsample
      exact hh.2.1 s (Nat.lt_succ_iff.mp hs) heq
    · intro hsample
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hh.2.1 s (Nat.lt_succ_iff.mp hs) heq
    · intro s hs
      rw [hout s]
      exact hh.2.2 s hs
  · let D := GenLimit.GeneratorFirst input
      (Stage3Case019.outputAfterInput (patientGen E) input)
    let D' := GenLimit.GeneratorFirst input (GenLimit.PatientMachine.output E input)
    have hDD : D = D' := generatorFirst_congr hout
    have hEeq : E.language j = Set.range input := hpresents.symm
    have hKsub : family i ⊆ E.language j := by
      rw [hEeq]
      exact hinput.2.1
    have hnoise : (E.language j \ family i).Finite := by
      rw [hEeq]
      rcases hinput.2.2 with ⟨F, hF, _⟩
      rw [← hF]
      exact F.finite_toSet
    have hnum :
        GenLimit.PatientScope.relativeLowerDensity (D' ∩ E.language j) (E.language j) =
        GenLimit.PatientScope.relativeLowerDensity (D' ∩ family i) (E.language j) := by
      apply relativeLowerDensity_eq_of_finite_symmetricDifference (E.infinite' j)
      · exact Set.inter_subset_right
      · exact Set.inter_subset_right.trans hKsub
      · apply hnoise.subset
        intro x hx
        exact ⟨hx.1.2, fun hK => hx.2 ⟨hx.1.1, hK⟩⟩
      · rw [Set.diff_eq_empty.mpr]
        · exact Set.finite_empty
        · intro x hx
          exact ⟨hx.1, hKsub hx.2⟩
        
    change (1 / 2 : ℝ) ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ family i) (family i)
    calc
      (1 / 2 : ℝ) ≤
          GenLimit.PatientScope.relativeLowerDensity (D' ∩ E.language j) (E.language j) := by
        simpa [GenLimit.PatientMachine.patientLowerDensity] using hrun.2
      _ = GenLimit.PatientScope.relativeLowerDensity (D' ∩ family i) (E.language j) := hnum
      _ ≤ GenLimit.PatientScope.relativeLowerDensity (D' ∩ family i) (family i) :=
        relativeLowerDensity_antitone_denominator
          Set.inter_subset_right hKsub (E.infinite' j)
      _ = GenLimit.PatientScope.relativeLowerDensity (D ∩ family i) (family i) := by rw [hDD]

end Test


open Set Filter
open scoped Topology
open GenLimit GenLimit.Generic

namespace Test

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

noncomputable def uncountableEmbedding (q : ℕ) (A : Set ℕ) : Set ℤ :=
  (↑(omissionMarkerFinset q) : Set ℤ) ∪ positiveIntegers ∪ negativeCode '' A

lemma uncountableEmbedding_mem (q : ℕ) (A : Set ℕ) :
    uncountableEmbedding q A ∈ finiteOmissionClass q := by
  left
  refine ⟨?_, 0, ?_⟩
  · intro z hz; exact Or.inl (Or.inl hz)
  · rintro z ⟨k, rfl⟩
    simpa using Or.inl (Or.inr (positiveCode_mem k))

lemma uncountableEmbedding_injective (q : ℕ) :
    Function.Injective (uncountableEmbedding q) := by
  intro A B h
  ext n
  have hneg : negativeCode n ∉ (↑(omissionMarkerFinset q) : Set ℤ) :=
    negativeCode_not_marker q n
  have hnotpos : negativeCode n ∉ positiveIntegers := by
    exact Int.not_lt_of_ge (Int.le_of_lt (negativeCode_mem n))
  have hiff (C : Set ℕ) : negativeCode n ∈ uncountableEmbedding q C ↔ n ∈ C := by
    simp [uncountableEmbedding, hneg, hnotpos,
      Set.mem_image, negativeCode_injective.eq_iff]
  rw [← hiff A, h, hiff B]

lemma finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hc
  have hrange : (Set.range (uncountableEmbedding q)).Countable :=
    hc.mono (by rintro _ ⟨A, rfl⟩; exact uncountableEmbedding_mem q A)
  have huniv : (Set.univ : Set (Set ℕ)).Countable := by
    apply Set.countable_of_injective_of_countable_image
      (s := (Set.univ : Set (Set ℕ)))
      (f := uncountableEmbedding q)
    · exact (uncountableEmbedding_injective q).injOn
    · simpa only [Set.image_univ] using hrange
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (Set.countable_univ_iff.mp huniv)

lemma separation_negative (q : ℕ) (gen : Generator ℤ) :
    ∃ K ∈ finiteOmissionClass q, ∃ input : Stream ℤ,
      InjectiveValueContaminatedPresentationAtMost input K (q+1) ∧
      ¬Stage3Case019.SampleFreshGeneratesAfterInput
        input (Stage3Case019.outputAfterInput gen input) K := by
  by_contra h
  push_neg at h
  apply finiteNoiseLevel_lower q
  refine ⟨gen, ?_⟩
  intro K hK input hinput
  exact h K hK input hinput

end Test

namespace Test

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

noncomputable def missingIndex (code : ℕ → ℤ) (n : ℕ) {m : ℕ}
    (xs : Fin m → ℤ) : ℕ :=
  Nat.nth (fun k => code k ∉ GenLimit.Generic.sequenceSample xs) n

lemma missingSet_infinite (code : ℕ → ℤ) (hcode : Function.Injective code)
    {m : ℕ} (xs : Fin m → ℤ) :
    {k | code k ∉ GenLimit.Generic.sequenceSample xs}.Infinite := by
  have hfin : {k | code k ∈ GenLimit.Generic.sequenceSample xs}.Finite :=
    (GenLimit.Generic.sequenceSample xs).finite_toSet.preimage hcode.injOn
  simpa only [Set.compl_setOf] using hfin.infinite_compl

lemma missingIndex_missing (code : ℕ → ℤ) (hcode : Function.Injective code)
    (n : ℕ) {m : ℕ} (xs : Fin m → ℤ) :
    code (missingIndex code n xs) ∉ GenLimit.Generic.sequenceSample xs := by
  exact Nat.nth_mem_of_infinite (missingSet_infinite code hcode xs) n

lemma missingIndex_ge (code : ℕ → ℤ) (hcode : Function.Injective code)
    (n : ℕ) {m : ℕ} (xs : Fin m → ℤ) :
    n ≤ missingIndex code n xs := by
  exact Nat.le_nth (fun hf => (missingSet_infinite code hcode xs) hf |>.elim)

lemma count_pred_mono {p r : ℕ → Prop} [DecidablePred p] [DecidablePred r]
    (hpr : ∀ k, p k → r k) (n : ℕ) : Nat.count p n ≤ Nat.count r n := by
  simp only [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨hk.1, hpr k hk.2⟩

lemma missingIndex_strict_stream (code : ℕ → ℤ) (hcode : Function.Injective code)
    (stream : ℕ → ℤ) {s t : ℕ} (hst : s < t) :
    missingIndex code (s+1) (fun k : Fin (s+1) => stream k) <
      missingIndex code (t+1) (fun k : Fin (t+1) => stream k) := by
  classical
  let ps : ℕ → Prop := fun k => code k ∉ GenLimit.Generic.sample stream (s+1)
  let pt : ℕ → Prop := fun k => code k ∉ GenLimit.Generic.sample stream (t+1)
  have hsampS : GenLimit.Generic.sequenceSample (fun k : Fin (s+1) => stream k) =
      GenLimit.Generic.sample stream (s+1) := GenLimit.Generic.sequenceSample_prefix _ _
  have hsampT : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => stream k) =
      GenLimit.Generic.sample stream (t+1) := GenLimit.Generic.sequenceSample_prefix _ _
  have hps : {k | ps k}.Infinite := by
    simpa [ps, hsampS] using missingSet_infinite code hcode
      (fun k : Fin (s+1) => stream k)
  have hpt : {k | pt k}.Infinite := by
    simpa [pt, hsampT] using missingSet_infinite code hcode
      (fun k : Fin (t+1) => stream k)
  have hsub : ∀ k, pt k → ps k := by
    intro k hk hmem
    exact hk (GenLimit.Generic.sample_mono (by omega) hmem)
  rw [missingIndex, missingIndex, hsampS, hsampT]
  change Nat.nth ps (s+1) < Nat.nth pt (t+1)
  by_contra hnot
  have hle : Nat.nth pt (t+1) ≤ Nat.nth ps (s+1) := Nat.le_of_not_gt hnot
  have hc1 : Nat.count pt (Nat.nth pt (t+1)) ≤
      Nat.count ps (Nat.nth pt (t+1)) := count_pred_mono hsub _
  have hc2 : Nat.count ps (Nat.nth pt (t+1)) ≤
      Nat.count ps (Nat.nth ps (s+1)) := Nat.count_monotone ps hle
  rw [Nat.count_nth_of_infinite hpt] at hc1
  rw [Nat.count_nth_of_infinite hps] at hc2
  omega

noncomputable def denseNoiseSweepGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    if omissionMarkerFinset q ⊆ GenLimit.Generic.sequenceSample xs then
      positiveCode (missingIndex positiveCode n xs)
    else
      negativeCode (missingIndex negativeCode n xs)

end Test

namespace Test

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

lemma denseNoiseSweep_first_novel
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input) K := by
  obtain ⟨hmarkers, j, htail⟩ := hK
  obtain ⟨Td, hTd⟩ := allMarkers_eventually_observed hinput hmarkers
  refine ⟨max Td j, ?_⟩
  intro t ht
  have hdetect : omissionMarkerFinset q ⊆ observedThrough input t :=
    hTd t ((Nat.le_max_left _ _).trans ht)
  have hsample : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => input k) =
      observedThrough input t := GenLimit.Generic.sequenceSample_prefix _ _
  have hout : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input t =
      positiveCode (missingIndex positiveCode (t+1)
        (fun k : Fin (t+1) => input k)) := by
    simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
      denseNoiseSweepGenerator, hsample, hdetect]
  rw [hout]
  constructor
  · apply htail
    refine ⟨missingIndex positiveCode (t+1) (fun k : Fin (t+1) => input k) - j, ?_⟩
    have hge := missingIndex_ge positiveCode positiveCode_injective (t+1)
      (fun k : Fin (t+1) => input k)
    change positiveCode (j + (missingIndex positiveCode (t+1)
      (fun k : Fin (t+1) => input k) - j)) = _
    rw [Nat.add_sub_of_le]
    omega
  constructor
  · simpa [hsample] using
      missingIndex_missing positiveCode positiveCode_injective (t+1)
        (fun k : Fin (t+1) => input k)
  · intro s hs
    have hsampleS : GenLimit.Generic.sequenceSample (fun k : Fin (s+1) => input k) =
        observedThrough input s := GenLimit.Generic.sequenceSample_prefix _ _
    by_cases hdetectS : omissionMarkerFinset q ⊆ observedThrough input s
    · have houtS : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input s =
          positiveCode (missingIndex positiveCode (s+1)
            (fun k : Fin (s+1) => input k)) := by
        simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
          denseNoiseSweepGenerator, hsampleS, hdetectS]
      rw [houtS]
      exact fun heq => (ne_of_lt
        (missingIndex_strict_stream positiveCode positiveCode_injective input hs))
          (positiveCode_injective heq)
    · have houtS : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input s =
          negativeCode (missingIndex negativeCode (s+1)
            (fun k : Fin (s+1) => input k)) := by
        simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
          denseNoiseSweepGenerator, hsampleS, hdetectS]
      rw [houtS]
      intro heq
      have hn := negativeCode_mem (missingIndex negativeCode (s+1)
        (fun k : Fin (s+1) => input k))
      have hp := positiveCode_mem (missingIndex positiveCode (t+1)
        (fun k : Fin (t+1) => input k))
      rw [heq] at hn
      exact (Int.not_lt_of_ge (Int.le_of_lt hp)) hn

lemma denseNoiseSweep_second_novel
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    Stage3Case019.NovelGeneratesAfterInput input
      (Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input) K := by
  refine ⟨0, ?_⟩
  intro t _
  have hno : ¬omissionMarkerFinset q ⊆ observedThrough input t :=
    not_allMarkers_observed_second hK hinput t
  have hsample : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => input k) =
      observedThrough input t := GenLimit.Generic.sequenceSample_prefix _ _
  have hout : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input t =
      negativeCode (missingIndex negativeCode (t+1)
        (fun k : Fin (t+1) => input k)) := by
    simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
      denseNoiseSweepGenerator, hsample, hno]
  rw [hout]
  constructor
  · exact hK.1 (negativeCode_mem _)
  constructor
  · simpa [hsample] using
      missingIndex_missing negativeCode negativeCode_injective (t+1)
        (fun k : Fin (t+1) => input k)
  · intro s hs
    have hnoS : ¬omissionMarkerFinset q ⊆ observedThrough input s :=
      not_allMarkers_observed_second hK hinput s
    have hsampleS : GenLimit.Generic.sequenceSample (fun k : Fin (s+1) => input k) =
        observedThrough input s := GenLimit.Generic.sequenceSample_prefix _ _
    have houtS : Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input s =
        negativeCode (missingIndex negativeCode (s+1)
          (fun k : Fin (s+1) => input k)) := by
      simp [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
        denseNoiseSweepGenerator, hsampleS, hnoS]
    rw [houtS]
    exact fun heq => (ne_of_lt
      (missingIndex_strict_stream negativeCode negativeCode_injective input hs))
        (negativeCode_injective heq)

end Test

namespace Test

lemma sequenceSample_card_le {α : Type*}
    {m : ℕ} (xs : Fin m → α) :
    (GenLimit.Generic.sequenceSample xs).card ≤ m := by
  classical
  unfold GenLimit.Generic.sequenceSample
  exact Finset.card_image_le.trans (by simp)

lemma missingIndex_le_add (code : ℕ → ℤ) (hcode : Function.Injective code)
    (n : ℕ) {m : ℕ} (xs : Fin m → ℤ) :
    missingIndex code n xs ≤ n + m := by
  classical
  let sample := GenLimit.Generic.sequenceSample xs
  let p : ℕ → Prop := fun k => code k ∉ sample
  let present := (Finset.range (n+m+1)).filter (fun k => code k ∈ sample)
  have himage : present.image code ⊆ sample := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    exact (Finset.mem_filter.mp hk).2
  have hpresent : present.card ≤ m := by
    calc
      present.card = (present.image code).card :=
        (Finset.card_image_iff.mpr (fun a _ b _ hab => hcode hab)).symm
      _ ≤ sample.card := Finset.card_le_card himage
      _ ≤ m := sequenceSample_card_le xs
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.range (n+m+1)) (p := fun k => code k ∈ sample)
  have hcount : n < Nat.count p (n+m+1) := by
    rw [Nat.count_eq_card_filter_range]
    change n < ((Finset.range (n+m+1)).filter fun k => code k ∉ sample).card
    change n < ((Finset.range (n+m+1)).filter fun k => ¬code k ∈ sample).card
    dsimp [present] at hpresent
    rw [Finset.card_range] at hpartition
    omega
  have hlt : Nat.nth p n < n+m+1 := Nat.nth_lt_of_lt_count hcount
  simpa [missingIndex, p, sample] using Nat.lt_succ_iff.mp hlt

lemma balanced_negativeCode (n : ℕ) :
    Stage3Case019.balanced (2*n+1) = GenLimit.UnionClosedness.negativeCode n := by
  simp [Stage3Case019.balanced, GenLimit.UnionClosedness.negativeCode, Int.negSucc_eq]

lemma balanced_positiveCode (n : ℕ) :
    Stage3Case019.balanced (2*n+2) = GenLimit.UnionClosedness.positiveCode n := by
  simp [Stage3Case019.balanced, GenLimit.UnionClosedness.positiveCode]
  omega

end Test

namespace Test

lemma relativeLowerDensity_quarter_of_counting
    {A K : Set ℕ} (hK : K.Infinite) (hA : A ⊆ K) (C : ℕ)
    (hcount : ∀ n, GenLimit.PatientScope.prefixCount K n ≤
      4 * GenLimit.PatientScope.prefixCount A n + C) :
    (1 / 4 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity A K := by
  let N := GenLimit.PatientScope.prefixCount K
  let D := GenLimit.PatientScope.prefixCount A
  let g : ℕ → ℝ := fun n => (1/4 : ℝ) - (C : ℝ) / (4 * (N n : ℝ))
  have hN : Tendsto N atTop atTop :=
    GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcast : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have herr : Tendsto (fun n => (C : ℝ) / (4 * (N n : ℝ))) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (C : ℝ)) atTop (𝓝 (C : ℝ)) := tendsto_const_nhds
    have hfour : Tendsto (fun n => 4 * (N n : ℝ)) atTop atTop :=
      hcast.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
    exact hc.div_atTop hfour
  have hg : Tendsto g atTop (𝓝 (1/4 : ℝ)) := by
    simpa [g] using tendsto_const_nhds.sub herr
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      g n ≤ (D n : ℝ) / (N n : ℝ) := by
    filter_upwards [hNpos] with n hn
    have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
    have hcR : (N n : ℝ) ≤ 4 * (D n : ℝ) + C := by
      exact_mod_cast hcount n
    dsimp [g]
    rw [le_div_iff₀ hnR]
    field_simp [hnR.ne']
    nlinarith
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1/4 : ℝ) ≤ liminf (fun n => (D n : ℝ) / (N n : ℝ)) atTop
  calc
    (1/4 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf hcompare hg.isBoundedUnder_ge
      (isCoboundedUnder_ge_of_le atTop (fun n => relativeRatio_le_one hA n))

lemma rank_mem_generatorFirst
    {gen : Generator ℤ} {input : Stream ℤ} {K : Set ℤ} {T t r : ℕ}
    (hgood : ∀ u, T ≤ u →
      Stage3Case019.outputAfterInput gen input u ∈ K ∧
      Stage3Case019.outputAfterInput gen input u ∉ GenLimit.Generic.sample input (u+1) ∧
      ∀ s, s < u → Stage3Case019.outputAfterInput gen input s ≠
        Stage3Case019.outputAfterInput gen input u)
    (hT : T ≤ t)
    (hr : Stage3Case019.balanced r =
      Stage3Case019.outputAfterInput gen input t) :
    r ∈ Stage3Case019.balancedRanks
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput gen input) ∩ K) := by
  have ht := hgood t hT
  change Stage3Case019.balanced r ∈
    Stage3Case019.GeneratorFirstOn input
      (Stage3Case019.outputAfterInput gen input) ∩ K
  rw [hr]
  refine ⟨?_, ht.1⟩
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  apply ht.2.1
  exact GenLimit.Generic.mem_sample_iff.mpr
    ⟨s, Nat.lt_succ_iff.mpr hs, heq⟩

end Test

namespace Test

lemma prefixCount_quarter_bound
    {A K : Set ℕ} (T : ℕ) (rank : ℕ → ℕ)
    (hrank : ∀ t, T ≤ t → rank t ∈ A)
    (hbound : ∀ t, T ≤ t → rank t < 4*t+7)
    (hinj : Set.InjOn rank {t | T ≤ t}) :
    ∀ n, GenLimit.PatientScope.prefixCount K n ≤
      4 * GenLimit.PatientScope.prefixCount A n + (4*T+7) := by
  classical
  intro n
  let rounds := Finset.Ico T (n/4-1)
  have hsubset : rounds.image rank ⊆
      (Finset.range n).filter (fun k => k ∈ A) := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    have ht' := Finset.mem_Ico.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hrank t ht'.1⟩
    have hb := hbound t ht'.1
    omega
  have himage : (rounds.image rank).card = rounds.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    apply hinj
    · exact Finset.mem_Ico.mp ha |>.1
    · exact Finset.mem_Ico.mp hb |>.1
    · exact hab
  have hcard : rounds.card ≤ GenLimit.PatientScope.prefixCount A n := by
    unfold GenLimit.PatientScope.prefixCount
    rw [← himage]
    exact Finset.card_le_card hsubset
  have hrounds : rounds.card = n/4-1-T := by
    simp [rounds]
  have hKn : GenLimit.PatientScope.prefixCount K n ≤ n := by
    unfold GenLimit.PatientScope.prefixCount
    exact (Finset.card_filter_le _ _).trans (by simp)
  rw [hrounds] at hcard
  have hdiv : n % 4 + 4 * (n / 4) = n := Nat.mod_add_div n 4
  omega

end Test

namespace Test

open GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

lemma first_balancedRanks_infinite {q : ℕ} {K : Set ℤ}
    (hK : K ∈ finiteOmissionFirstClass q) :
    (Stage3Case019.balancedRanks K).Infinite := by
  obtain ⟨_, j, htail⟩ := hK
  have hinj : Function.Injective (fun k : ℕ => 2*(j+k)+2) := by
    intro a b hab
    dsimp at hab
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro r ⟨k, rfl⟩
  change Stage3Case019.balanced (2*(j+k)+2) ∈ K
  rw [balanced_positiveCode]
  exact htail ⟨k, rfl⟩

lemma second_balancedRanks_infinite {q : ℕ} {K : Set ℤ}
    (hK : K ∈ finiteOmissionSecondClass q) :
    (Stage3Case019.balancedRanks K).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => 2*k+1) := by
    intro a b hab
    dsimp at hab
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro r ⟨k, rfl⟩
  change Stage3Case019.balanced (2*k+1) ∈ K
  rw [balanced_negativeCode]
  exact hK.1 (negativeCode_mem k)

lemma denseNoiseSweep_first_density
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionFirstClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    (1/4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input) ∩ K) K := by
  let output := Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input
  let A := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn input output ∩ K)
  let KR := Stage3Case019.balancedRanks K
  obtain ⟨Tnov, hnov⟩ := denseNoiseSweep_first_novel hK hinput
  have hmarkers := hK.1
  obtain ⟨Td, hTd⟩ := allMarkers_eventually_observed hinput hmarkers
  let T := max Tnov Td
  let rank : ℕ → ℕ := fun t =>
    2 * missingIndex positiveCode (t+1) (fun k : Fin (t+1) => input k) + 2
  have hrank : ∀ t, T ≤ t → rank t ∈ A := by
    intro t ht
    have hdetect : omissionMarkerFinset q ⊆ observedThrough input t :=
      hTd t ((Nat.le_max_right _ _).trans ht)
    have hsample : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => input k) =
        observedThrough input t := GenLimit.Generic.sequenceSample_prefix _ _
    have hout : output t = positiveCode
        (missingIndex positiveCode (t+1) (fun k : Fin (t+1) => input k)) := by
      simp [output, Stage3Case019.outputAfterInput, GenLimit.Generic.output,
        denseNoiseSweepGenerator, hsample, hdetect]
    apply rank_mem_generatorFirst hnov ((Nat.le_max_left _ _).trans ht)
    dsimp [rank]
    rw [balanced_positiveCode]
    exact hout.symm
  have hbound : ∀ t, T ≤ t → rank t < 4*t+7 := by
    intro t _
    have hb := missingIndex_le_add positiveCode positiveCode_injective (t+1)
      (fun k : Fin (t+1) => input k)
    dsimp [rank]
    omega
  have hinj : Set.InjOn rank {t | T ≤ t} := by
    intro s hs t ht heq
    dsimp [rank] at heq
    have hidx : missingIndex positiveCode (s+1) (fun k : Fin (s+1) => input k) =
        missingIndex positiveCode (t+1) (fun k : Fin (t+1) => input k) := by omega
    by_contra hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact (ne_of_lt (missingIndex_strict_stream positiveCode positiveCode_injective input hlt)) hidx
    · exact (ne_of_lt (missingIndex_strict_stream positiveCode positiveCode_injective input hgt)) hidx.symm
  have hcount := prefixCount_quarter_bound (K := KR) T rank hrank hbound hinj
  unfold Stage3Case019.balancedRelativeLowerDensity
  apply relativeLowerDensity_quarter_of_counting (A := A) (K := KR)
    (first_balancedRanks_infinite hK) (C := 4*T+7)
  · intro r hr
    exact hr.2
  · exact hcount

lemma denseNoiseSweep_second_density
    {q : ℕ} {K : Set ℤ} (hK : K ∈ finiteOmissionSecondClass q)
    {input : Stream ℤ}
    (hinput : InjectiveValueContaminatedPresentationAtMost input K q) :
    (1/4 : ℝ) ≤ Stage3Case019.balancedRelativeLowerDensity
      (Stage3Case019.GeneratorFirstOn input
        (Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input) ∩ K) K := by
  let output := Stage3Case019.outputAfterInput (denseNoiseSweepGenerator q) input
  let A := Stage3Case019.balancedRanks
    (Stage3Case019.GeneratorFirstOn input output ∩ K)
  let KR := Stage3Case019.balancedRanks K
  obtain ⟨Tnov, hnov⟩ := denseNoiseSweep_second_novel hK hinput
  let rank : ℕ → ℕ := fun t =>
    2 * missingIndex negativeCode (t+1) (fun k : Fin (t+1) => input k) + 1
  have hrank : ∀ t, Tnov ≤ t → rank t ∈ A := by
    intro t ht
    have hno : ¬omissionMarkerFinset q ⊆ observedThrough input t :=
      not_allMarkers_observed_second hK hinput t
    have hsample : GenLimit.Generic.sequenceSample (fun k : Fin (t+1) => input k) =
        observedThrough input t := GenLimit.Generic.sequenceSample_prefix _ _
    have hout : output t = negativeCode
        (missingIndex negativeCode (t+1) (fun k : Fin (t+1) => input k)) := by
      simp [output, Stage3Case019.outputAfterInput, GenLimit.Generic.output,
        denseNoiseSweepGenerator, hsample, hno]
    apply rank_mem_generatorFirst hnov ht
    dsimp [rank]
    rw [balanced_negativeCode]
    exact hout.symm
  have hbound : ∀ t, Tnov ≤ t → rank t < 4*t+7 := by
    intro t _
    have hb := missingIndex_le_add negativeCode negativeCode_injective (t+1)
      (fun k : Fin (t+1) => input k)
    dsimp [rank]
    omega
  have hinj : Set.InjOn rank {t | Tnov ≤ t} := by
    intro s hs t ht heq
    dsimp [rank] at heq
    have hidx : missingIndex negativeCode (s+1) (fun k : Fin (s+1) => input k) =
        missingIndex negativeCode (t+1) (fun k : Fin (t+1) => input k) := by omega
    by_contra hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact (ne_of_lt (missingIndex_strict_stream negativeCode negativeCode_injective input hlt)) hidx
    · exact (ne_of_lt (missingIndex_strict_stream negativeCode negativeCode_injective input hgt)) hidx.symm
  have hcount := prefixCount_quarter_bound (K := KR) Tnov rank hrank hbound hinj
  unfold Stage3Case019.balancedRelativeLowerDensity
  apply relativeLowerDensity_quarter_of_counting (A := A) (K := KR)
    (second_balancedRanks_infinite hK) (C := 4*Tnov+7)
  · intro r hr
    exact hr.2
  · exact hcount

end Test

namespace Test

open GenLimit.NoiseLossFeedback

lemma separation_clause : Stage3Case019.SeparationClause := by
  intro q
  refine ⟨finiteOmissionClass q, finiteOmissionClass_not_countable q,
    finiteOmissionClass_uus q, ?_, separation_negative q⟩
  refine ⟨denseNoiseSweepGenerator q, ?_⟩
  intro K hK input hinput
  rcases hK with hfirst | hsecond
  · exact ⟨denseNoiseSweep_first_novel hfirst hinput,
      denseNoiseSweep_first_density hfirst hinput⟩
  · exact ⟨denseNoiseSweep_second_novel hsecond hinput,
      denseNoiseSweep_second_density hsecond hinput⟩

end Test

theorem stage3_result : Stage3Case019.MainClaim :=
  ⟨Test.countable_half_density, Test.separation_clause⟩
