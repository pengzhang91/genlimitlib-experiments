import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Theorem41Cardinality
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Case019

open GenLimit
open Stage3Case019

noncomputable def oracleOfFamily
    (family : GenLimit.Generic.LanguageFamily ℕ)
    (hinf : ∀ i, (family i).Infinite) : OracleFamily where
  language := family
  infinite' := hinf
  query i x := by classical exact if x ∈ family i then true else false
  query_spec i x := by classical simp

noncomputable def extendFin {α : Type*} [Inhabited α]
    {n : ℕ} (xs : Fin n → α) : ℕ → α :=
  fun k => if h : k < n then xs ⟨k, h⟩ else default

private theorem extendFin_eq {α : Type*} [Inhabited α]
    {n : ℕ} (xs : Fin n → α) {k : ℕ} (hk : k < n) :
    extendFin xs k = xs ⟨k, hk⟩ := by
  simp [extendFin, hk]

private theorem sample_congr_of_eq
    {a b : ℕ → ℕ} {u : ℕ} (h : ∀ k, k < u → a k = b k) :
    GenLimit.sample a u = GenLimit.sample b u := by
  ext x
  simp only [GenLimit.mem_sample_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k hk⟩

private theorem recursiveCritical_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {u : ℕ}
    (h : ∀ k, k < u → a k = b k) (i : ℕ) :
    RecursiveCritical C a u i ↔ RecursiveCritical C b u i := by
  have hs : GenLimit.sample a u = GenLimit.sample b u := sample_congr_of_eq h
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [RecursiveCritical, Consistent, hs]
      | succ n =>
          simp only [RecursiveCritical, Consistent, hs]
          constructor
          · rintro ⟨hc, hr⟩
            refine ⟨hc, ?_⟩
            intro j hj hjc
            exact hr j hj ((ih j (by omega)).2 hjc)
          · rintro ⟨hc, hr⟩
            refine ⟨hc, ?_⟩
            intro j hj hjc
            exact hr j hj ((ih j (by omega)).1 hjc)

private theorem criticalIndices_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {u scope : ℕ}
    (h : ∀ k, k < u → a k = b k) :
    PatientMachine.criticalIndices C a u scope =
      PatientMachine.criticalIndices C b u scope := by
  classical
  unfold PatientMachine.criticalIndices
  apply Finset.filter_congr
  intro i hi
  exact recursiveCritical_congr C h i

private theorem survivingCriticalIndices_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {t scope : ℕ}
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.survivingCriticalIndices C a t scope =
      PatientMachine.survivingCriticalIndices C b t scope := by
  classical
  unfold PatientMachine.survivingCriticalIndices
  apply Finset.filter_congr
  intro i hi
  exact and_congr
    (recursiveCritical_congr C (fun k hk => h k (by omega)) i)
    (recursiveCritical_congr C h i)

private theorem consistentIndices_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {u scope : ℕ}
    (h : ∀ k, k < u → a k = b k) :
    PatientMachine.consistentIndices C a u scope =
      PatientMachine.consistentIndices C b u scope := by
  classical
  have hs := sample_congr_of_eq h
  unfold PatientMachine.consistentIndices Consistent
  rw [hs]

private theorem patient_lowestConsistent_congr
    (C : GenLimit.LanguageFamily) {a b : ℕ → ℕ} {u fallback : ℕ}
    (h : ∀ k, k < u → a k = b k) :
    PatientMachine.lowestConsistent C a u fallback =
      PatientMachine.lowestConsistent C b u fallback := by
  classical
  have hs := sample_congr_of_eq h
  have hpred : ∀ i, Consistent C a u i ↔ Consistent C b u i := by
    intro i
    simp only [Consistent, hs]
  by_cases ha : ∃ i, Consistent C a u i
  · have hb : ∃ i, Consistent C b u i := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, (hpred i).mp hi⟩
    simp only [PatientMachine.lowestConsistent]
    rw [dif_pos ha, dif_pos hb]
    exact Nat.find_congr' (fun {i} => hpred i)
  · have hb : ¬ ∃ i, Consistent C b u i := by
      intro hb
      obtain ⟨i, hi⟩ := hb
      exact ha ⟨i, (hpred i).mpr hi⟩
    simp [PatientMachine.lowestConsistent, ha, hb]

private theorem patient_decide_congr
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ} (old : PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.decide O.language a t old =
      PatientMachine.decide O.language b t old := by
  have hs1 := sample_congr_of_eq h
  have hcons := consistentIndices_congr O.language (scope := old.scope) h
  have hcrit := criticalIndices_congr O.language (scope := old.scope + 1) h
  have hsurv := survivingCriticalIndices_congr O.language (scope := old.scope) h
  have hglobal : (∃ i, Consistent O.language a (t + 1) i) ↔
      ∃ i, Consistent O.language b (t + 1) i := by
    simp only [Consistent, hs1]
  have hglobalEq : (∃ i, Consistent O.language a (t + 1) i) =
      (∃ i, Consistent O.language b (t + 1) i) := propext hglobal
  have hfocus : Consistent O.language a (t + 1) old.focus ↔
      Consistent O.language b (t + 1) old.focus := by
    simp only [Consistent, hs1]
  have hlow := patient_lowestConsistent_congr O.language h (fallback := old.focus)
  unfold PatientMachine.decide
  by_cases hf : Consistent O.language a (t + 1) old.focus
  · rw [if_pos hf, if_pos (hfocus.mp hf)]
    simp only [PatientMachine.stableDecision, PatientMachine.highestCritical]
    simp [hcrit]
  · rw [if_neg hf, if_neg (fun hb => hf (hfocus.mpr hb))]
    simp only [PatientMachine.backtrackDecision,
      PatientMachine.highestSurvivor, PatientMachine.lowestConsistentInScope]
    rw [hcons, hsurv, hlow, hglobalEq]

private theorem patient_leastAvailable_congr
    (O : OracleFamily) {a b : ℕ → ℕ} {u : ℕ}
    (h : ∀ k, k < u → a k = b k) (used : Finset ℕ) (focus : ℕ) :
    PatientMachine.leastAvailable O.language O.infinite' a u used focus =
      PatientMachine.leastAvailable O.language O.infinite' b u used focus := by
  have hs := sample_congr_of_eq h
  apply Nat.le_antisymm
  · apply PatientMachine.leastAvailable_minimal
    simpa only [PatientMachine.Available, hs] using
      PatientMachine.leastAvailable_spec O.language O.infinite' b u used focus
  · apply PatientMachine.leastAvailable_minimal
    simpa only [PatientMachine.Available, hs] using
      PatientMachine.leastAvailable_spec O.language O.infinite' a u used focus

private theorem patient_processRound_congr
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ} (old : PatientMachine.State)
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.processRound O a t old =
      PatientMachine.processRound O b t old := by
  simp only [PatientMachine.processRound]
  rw [patient_decide_congr O old h]
  rw [patient_leastAvailable_congr O h]

private theorem patient_run_congr
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k < t → a k = b k) :
    PatientMachine.run O a t = PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [PatientMachine.run_succ, PatientMachine.run_succ]
      have hprev : ∀ k, k < t → a k = b k := fun k hk => h k (by omega)
      rw [ih hprev]
      exact patient_processRound_congr O (PatientMachine.run O b t) h

private theorem patient_output_congr
    (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ}
    (h : ∀ k, k ≤ t → a k = b k) :
    PatientMachine.output O a t = PatientMachine.output O b t := by
  unfold PatientMachine.output
  rw [patient_run_congr O (t := t + 1) (fun k hk => h k (by omega))]

noncomputable def patientGenerator
    (O : OracleFamily) : Stage3Case019.Generator ℕ :=
  fun n xs =>
    if h : n = 0 then 0
    else PatientMachine.output O (extendFin xs) (n - 1)

private theorem outputAfterInput_patientGenerator
    (O : OracleFamily) (input : Stage3Case019.Stream ℕ) (t : ℕ) :
    outputAfterInput (patientGenerator O) input t =
      PatientMachine.output O input t := by
  unfold outputAfterInput GenLimit.Generic.output patientGenerator
  rw [dif_neg (by omega : t + 1 ≠ 0)]
  simp only [Nat.add_sub_cancel]
  apply patient_output_congr
  intro k hk
  simp [extendFin, show k < t + 1 by omega]

end Case019

namespace Case019

open GenLimit
open Stage3Case019

private theorem prefixCount_finite_le
    {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    PatientScope.prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold PatientScope.prefixCount PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  exact Set.Finite.mem_toFinset hF |>.2 hx.2

private theorem prefixCount_inter_super_le
    (D K E : Set ℕ) (hKE : K ⊆ E) (hfinite : (E \ K).Finite) (n : ℕ) :
    PatientScope.prefixCount (D ∩ E) n ≤
      PatientScope.prefixCount (D ∩ K) n + hfinite.toFinset.card := by
  classical
  let left := PatientScope.prefixFinset (D ∩ E) n
  let main := PatientScope.prefixFinset (D ∩ K) n
  let extra := PatientScope.prefixFinset (E \ K) n
  have hsubset : left ⊆ main ∪ extra := by
    intro x hx
    have hx' := PatientScope.mem_prefixFinset.mp hx
    by_cases hxK : x ∈ K
    · apply Finset.mem_union_left
      exact PatientScope.mem_prefixFinset.mpr
        ⟨hx'.1, hx'.2.1, hxK⟩
    · apply Finset.mem_union_right
      exact PatientScope.mem_prefixFinset.mpr
        ⟨hx'.1, hx'.2.2, hxK⟩
  change left.card ≤ main.card + hfinite.toFinset.card
  calc
    left.card ≤ (main ∪ extra).card := Finset.card_le_card hsubset
    _ ≤ main.card + extra.card := Finset.card_union_le _ _
    _ ≤ main.card + hfinite.toFinset.card :=
      Nat.add_le_add_left (prefixCount_finite_le hfinite n) _

private theorem liminf_le_of_eventually_le_add_zero
    (u v e : ℕ → ℝ)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1)
    (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n ≤ 1)
    (he : Tendsto e atTop (nhds 0))
    (hcomp : ∀ᶠ n in atTop, u n ≤ v n + e n) :
    liminf u atTop ≤ liminf v atTop := by
  apply le_of_forall_lt_imp_le_of_dense
  intro y hy
  obtain ⟨r, hyr, hry⟩ := exists_between hy
  have huEventually : ∀ᶠ n in atTop, r < u n :=
    eventually_lt_of_lt_liminf hry
      (isBoundedUnder_of ⟨0, hu0⟩)
  have heEventually : ∀ᶠ n in atTop, e n < r - y := by
    have : 0 < r - y := by linarith
    exact he.eventually (Iio_mem_nhds this)
  by_contra hyle
  have hvlt : liminf v atTop < y := lt_of_not_ge hyle
  have hvFrequently : ∃ᶠ n in atTop, v n < y :=
    frequently_lt_of_liminf_lt
      (isCoboundedUnder_ge_of_le atTop hv1) hvlt
  have hcontra := hvFrequently.and_eventually
    (huEventually.and (heEventually.and hcomp))
  exact hcontra (Eventually.of_forall fun n hn => by
    rcases hn with ⟨hvy, hru, her, huv⟩
    linarith)

private theorem relativeLowerDensity_transfer_finite_super
    (D K E : Set ℕ) (hKinf : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    PatientScope.relativeLowerDensity (D ∩ E) E ≤
      PatientScope.relativeLowerDensity (D ∩ K) K := by
  let u : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (D ∩ E) n : ℝ) /
      (PatientScope.prefixCount E n : ℝ)
  let v : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) /
      (PatientScope.prefixCount E n : ℝ)
  have hEinf : E.Infinite := hKinf.mono hKE
  have hcast : Tendsto (fun n =>
      (PatientScope.prefixCount E n : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (PatientScope.tendsto_prefixCount_atTop hEinf)
  have he : Tendsto e atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcast
  have hu0 : ∀ n, 0 ≤ u n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hu1 : ∀ n, u n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount E n = 0
    · simp [u, hn]
    · dsimp [u]
      rw [div_le_one (by positivity)]
      exact_mod_cast PatientScope.prefixCount_mono Set.inter_subset_right n
  have hv0 : ∀ n, 0 ≤ v n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hv1 : ∀ n, v n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount K n = 0
    · simp [v, hn]
    · dsimp [v]
      rw [div_le_one (by positivity)]
      exact_mod_cast PatientScope.prefixCount_mono Set.inter_subset_right n
  have hcomp : ∀ᶠ n in atTop, u n ≤ v n + e n := by
    have hKpos : ∀ᶠ n in atTop, 0 < PatientScope.prefixCount K n :=
      (PatientScope.tendsto_prefixCount_atTop hKinf).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hKpos] with n hn
    have hEpos : 0 < PatientScope.prefixCount E n :=
      lt_of_lt_of_le hn (PatientScope.prefixCount_mono hKE n)
    have hnum := prefixCount_inter_super_le D K E hKE hfinite n
    have hden := PatientScope.prefixCount_mono hKE n
    dsimp [u, v, e]
    have hnumR :
        (PatientScope.prefixCount (D ∩ E) n : ℝ) ≤
          PatientScope.prefixCount (D ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hnum
    have hdenR :
        (PatientScope.prefixCount K n : ℝ) ≤
          PatientScope.prefixCount E n := by
      exact_mod_cast hden
    have hmain :
        (PatientScope.prefixCount (D ∩ K) n : ℝ) /
            PatientScope.prefixCount E n ≤
          (PatientScope.prefixCount (D ∩ K) n : ℝ) /
            PatientScope.prefixCount K n := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hdenR
    have hfirst :
        (PatientScope.prefixCount (D ∩ E) n : ℝ) /
            PatientScope.prefixCount E n ≤
          (PatientScope.prefixCount (D ∩ K) n : ℝ) /
              PatientScope.prefixCount E n +
            (hfinite.toFinset.card : ℝ) /
              PatientScope.prefixCount E n := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hnumR (by positivity)
    exact hfirst.trans (add_le_add_right hmain _)
  unfold PatientScope.relativeLowerDensity
  exact liminf_le_of_eventually_le_add_zero u v e hu0 hu1 hv0 hv1 he hcomp

private theorem contaminated_as_finite_expansion
    {family : Generic.LanguageFamily ℕ} (hinf : ∀ i, (family i).Infinite)
    {i q : ℕ} {input : Generic.Stream ℕ}
    (hp : Generic.InjectiveValueContaminatedPresentationAtMost input (family i) q) :
    ∃ j,
      Generic.Presents input
        ((InfiniteContamination.finiteExpansionOracleFamily
          (oracleOfFamily family hinf)).language j) ∧
      family i ⊆
        (InfiniteContamination.finiteExpansionOracleFamily
          (oracleOfFamily family hinf)).language j ∧
      (((InfiniteContamination.finiteExpansionOracleFamily
          (oracleOfFamily family hinf)).language j) \ family i).Finite := by
  have hnoise : (Set.range input \ family i).Finite := by
    obtain ⟨F, hF, _⟩ := hp.2.2
    rw [← hF]
    exact F.finite_toSet
  have hcontam : InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
      input (family i) := by
    refine ⟨hp.1, ?_, ?_⟩
    · exact (InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective
        hp.1).mpr hnoise
    · have hempty : family i \ Set.range input = ∅ :=
        Set.diff_eq_empty.mpr hp.2.1
      simpa [InfiniteContamination.FiniteOmissions, hempty]
  obtain ⟨j, hjbase, hjP⟩ :=
    InfiniteContamination.exists_finiteExpansion_index_for_stream
      (oracleOfFamily family hinf) hcontam
  refine ⟨j, hjP, ?_, ?_⟩
  · rw [← hjP]
    exact hp.2.1
  · rw [← hjP]
    exact hnoise

private theorem countableHalfDensity (q : ℕ) : CountableHalfDensity q := by
  intro family hinf
  let O := oracleOfFamily family hinf
  let E := InfiniteContamination.finiteExpansionOracleFamily O
  refine ⟨patientGenerator E, ?_⟩
  intro i input hp
  obtain ⟨j, hjP, hsubset, hfinite⟩ :=
    contaminated_as_finite_expansion hinf hp
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity E input hjP
  have hout : outputAfterInput (patientGenerator E) input =
      PatientMachine.output E input :=
    funext (outputAfterInput_patientGenerator E input)
  rw [hout]
  constructor
  · obtain ⟨T, hT⟩ := hrun.1
    let badTimes : Set ℕ :=
      (PatientMachine.output E input) ⁻¹' (E.language j \ family i)
    have houtInjective : Function.Injective (PatientMachine.output E input) := by
      intro a b hab
      rcases lt_trichotomy a b with hablt | rfl | hbalt
      · exact False.elim (PatientMachine.output_ne_of_lt E input hablt hab)
      · rfl
      · exact False.elim (PatientMachine.output_ne_of_lt E input hbalt hab.symm)
    have hbadFinite : badTimes.Finite := by
      exact hfinite.preimage (Set.injOn_of_injective houtInjective)
    obtain ⟨d, hd⟩ := Finset.exists_nat_subset_range hbadFinite.toFinset
    refine ⟨max T d, ?_⟩
    intro t ht
    obtain ⟨hmemE, hfresh, hnovel⟩ := hT t (le_trans (le_max_left _ _) ht)
    have hnotNoise : PatientMachine.output E input t ∉ E.language j \ family i := by
      intro hnoise
      have htbad : t ∈ hbadFinite.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact hnoise
      have htd : t < d := by simpa using hd htbad
      exact (Nat.not_lt_of_ge (le_trans (le_max_right _ _) ht)) htd
    have hmemK : PatientMachine.output E input t ∈ family i := by
      by_contra hnotK
      exact hnotNoise ⟨hmemE, hnotK⟩
    have hfreshSet : PatientMachine.output E input t ∉
        GenLimit.sample input (t + 1) := by
      intro hsample
      obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
      exact hfresh s (by omega) heq
    exact ⟨hmemK, hfreshSet, hnovel⟩
  · exact hrun.2.trans
      (relativeLowerDensity_transfer_finite_super
        (GeneratorFirst input (PatientMachine.output E input))
        (family i) (E.language j) (hinf i) hsubset hfinite)

end Case019

namespace Case019

open GenLimit
open Stage3Case019

/-- Checked first component of the main claim. -/
theorem stage3_countable_half_density : CountableClause := by
  intro q
  exact countableHalfDensity q

private def secondEncodedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  GenLimit.UnionClosedness.negativeIntegers ∪
    Set.range (fun n : S =>
      GenLimit.UnionClosedness.positiveCode (q + 1 + n.1))

private theorem secondEncodedLanguage_mem (q : ℕ) (S : Set ℕ) :
    secondEncodedLanguage q S ∈
      NoiseLossFeedback.finiteOmissionClass q := by
  right
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hmarker
    rcases hz with hzneg | ⟨n, rfl⟩
    · exact (Int.not_lt_of_ge
        (NoiseLossFeedback.omissionMarker_nonnegative hmarker)) hzneg
    · obtain ⟨k, hk, heq⟩ :=
        NoiseLossFeedback.mem_omissionMarkerFinset_iff.mp hmarker
      have : (k : ℤ) = (q + 1 + n.1 + 1 : ℕ) := by
        simpa [GenLimit.UnionClosedness.positiveCode] using heq
      exact (by omega)

private theorem secondEncodedLanguage_injective (q : ℕ) :
    Function.Injective (secondEncodedLanguage q) := by
  classical
  intro S T hST
  ext n
  have hprobe := Set.ext_iff.mp hST
    (GenLimit.UnionClosedness.positiveCode (q + 1 + n))
  have hpositive :
      GenLimit.UnionClosedness.positiveCode (q + 1 + n) ∉
        GenLimit.UnionClosedness.negativeIntegers := by
    simp [GenLimit.UnionClosedness.positiveCode,
      GenLimit.UnionClosedness.negativeIntegers]
    omega
  have hmem (U : Set ℕ) :
      GenLimit.UnionClosedness.positiveCode (q + 1 + n) ∈
          secondEncodedLanguage q U ↔ n ∈ U := by
    simp only [secondEncodedLanguage, Set.mem_union, hpositive, false_or,
      Set.mem_range]
    constructor
    · rintro ⟨m, hm⟩
      have hindex := GenLimit.UnionClosedness.positiveCode_injective hm
      have : m.1 = n := by omega
      simpa [this] using m.2
    · intro hn
      exact ⟨⟨n, hn⟩, rfl⟩
  rw [hmem S, hmem T] at hprobe
  exact hprobe

private theorem finiteOmissionClass_uncountable (q : ℕ) :
    ¬(NoiseLossFeedback.finiteOmissionClass q).Countable := by
  intro hcountable
  let f : Set ℕ → NoiseLossFeedback.finiteOmissionClass q :=
    fun S => ⟨secondEncodedLanguage q S, secondEncodedLanguage_mem q S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply secondEncodedLanguage_injective q
    exact congrArg Subtype.val hST
  letI : Countable (NoiseLossFeedback.finiteOmissionClass q) :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

private theorem adjacentLevel_failure (q : ℕ) (gen : Generator ℤ) :
    ∃ K ∈ NoiseLossFeedback.finiteOmissionClass q,
      ∃ input : Stream ℤ,
        Generic.InjectiveValueContaminatedPresentationAtMost input K (q + 1) ∧
          ¬SampleFreshGeneratesAfterInput
            input (outputAfterInput gen input) K := by
  have hnot :
      ¬NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel gen
        (NoiseLossFeedback.finiteOmissionClass q) (q + 1) := by
    intro hgen
    exact NoiseLossFeedback.finiteNoiseLevel_lower q ⟨gen, hgen⟩
  simp only [NoiseLossFeedback.IsLimitGeneratorWithNoiseLevel] at hnot
  push_neg at hnot
  obtain ⟨K, hK, input, hp, hfail⟩ := hnot
  refine ⟨K, hK, input, hp, ?_⟩
  intro hsuccess
  obtain ⟨T, hT⟩ := hsuccess
  obtain ⟨t, ht, hbad⟩ := hfail T
  exact hbad (hT t ht)

end Case019

namespace Case019

open GenLimit
open Stage3Case019

private def positiveIndex : ℤ → ℕ
  | Int.ofNat 0 => 0
  | Int.ofNat (n + 1) => n
  | Int.negSucc _ => 0

private def negativeIndex : ℤ → ℕ
  | Int.negSucc n => n
  | Int.ofNat _ => 0

@[simp] private theorem positiveIndex_positiveCode (n : ℕ) :
    positiveIndex (UnionClosedness.positiveCode n) = n := by
  rfl

@[simp] private theorem negativeIndex_negativeCode (n : ℕ) :
    negativeIndex (UnionClosedness.negativeCode n) = n := by
  rfl

private theorem positiveCode_positiveIndex_of_positive
    {z : ℤ} (hz : 0 < z) :
    UnionClosedness.positiveCode (positiveIndex z) = z := by
  cases z with
  | ofNat n =>
      cases n with
      | zero => simp at hz
      | succ n => rfl
  | negSucc n => simp at hz

private theorem negativeCode_negativeIndex_of_negative
    {z : ℤ} (hz : z < 0) :
    UnionClosedness.negativeCode (negativeIndex z) = z := by
  cases z with
  | ofNat n => exact False.elim ((Int.ofNat_zero_le n).not_lt hz)
  | negSucc n => rfl

noncomputable def universalOracle : OracleFamily :=
  oracleOfFamily (fun _ => Set.univ) (fun _ => Set.infinite_univ)

noncomputable def cofiniteOracle : OracleFamily :=
  InfiniteContamination.finiteExpansionOracleFamily universalOracle

private theorem exists_cofiniteOracle_index
    (stream : Stream ℕ) (hmissing : (Set.univ \ Set.range stream).Finite) :
    ∃ j, Generic.Presents stream (cofiniteOracle.language j) := by
  let remove : Finset ℕ := hmissing.toFinset
  let data : InfiniteContamination.FiniteExpansionCode :=
    (0, Finset.equivBitIndices.symm ∅,
      Finset.equivBitIndices.symm remove)
  let j := InfiniteContamination.encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  change Set.range stream =
    InfiniteContamination.finiteExpansionLanguage universalOracle j
  rw [InfiniteContamination.finiteExpansionLanguage]
  simp only [j, data, InfiniteContamination.finiteExpansionCode_encode,
    Equiv.apply_symm_apply]
  simp only [InfiniteContamination.finiteExpansion]
  have huniv : universalOracle.language 0 = (Set.univ : Set ℕ) := by
    rfl
  rw [huniv]
  simp only [Finset.coe_empty, Set.union_empty]
  ext n
  simp only [Set.mem_diff, Set.mem_univ, true_and]
  change n ∈ Set.range stream ↔ n ∉ hmissing.toFinset
  rw [Set.Finite.mem_toFinset]
  simp

private theorem positive_missing_finite
    {K : Set ℤ} {input : Stream ℤ}
    (hcover : K ⊆ Set.range input)
    (htail : ∃ j, UnionClosedness.positiveTail j ⊆ K) :
    (Set.univ \ Set.range (fun t => positiveIndex (input t))).Finite := by
  obtain ⟨j, hj⟩ := htail
  apply (Set.finite_Iio j).subset
  intro n hn
  simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_range] at hn
  by_contra hnj
  have hjn : j ≤ n := Nat.le_of_not_gt hnj
  have hpos : UnionClosedness.positiveCode n ∈ K := by
    apply hj
    exact ⟨n - j, by
      apply Int.ofNat_inj.mpr
      omega⟩
  obtain ⟨t, ht⟩ := hcover hpos
  exact hn ⟨t, by simpa [ht]⟩

private theorem negative_range_univ
    {K : Set ℤ} {input : Stream ℤ}
    (hcover : K ⊆ Set.range input)
    (hneg : UnionClosedness.negativeIntegers ⊆ K) :
    Set.range (fun t => negativeIndex (input t)) = Set.univ := by
  ext n
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨t, ht⟩ := hcover (hneg (UnionClosedness.negativeCode_mem n))
  exact ⟨t, by simpa [ht]⟩

noncomputable def signedPatientGenerator (q : ℕ) : Generator ℤ :=
  fun n xs =>
    if NoiseLossFeedback.omissionMarkerFinset q ⊆ Generic.sequenceSample xs then
      UnionClosedness.positiveCode
        (patientGenerator cofiniteOracle n (fun k => positiveIndex (xs k)))
    else
      UnionClosedness.negativeCode
        (patientGenerator cofiniteOracle n (fun k => negativeIndex (xs k)))

private theorem signedPatient_positive_output
    (q : ℕ) (input : Stream ℤ) {t : ℕ}
    (hdetect : NoiseLossFeedback.omissionMarkerFinset q ⊆
      NoiseLossFeedback.observedThrough input t) :
    outputAfterInput (signedPatientGenerator q) input t =
      UnionClosedness.positiveCode
        (PatientMachine.output cofiniteOracle
          (fun s => positiveIndex (input s)) t) := by
  unfold outputAfterInput Generic.output signedPatientGenerator
  rw [if_pos]
  · congr 1
    exact outputAfterInput_patientGenerator cofiniteOracle
      (fun s => positiveIndex (input s)) t
  · simpa [NoiseLossFeedback.observedThrough,
      Generic.sequenceSample_prefix] using hdetect

private theorem signedPatient_negative_output
    (q : ℕ) (input : Stream ℤ) {t : ℕ}
    (hdetect : ¬NoiseLossFeedback.omissionMarkerFinset q ⊆
      NoiseLossFeedback.observedThrough input t) :
    outputAfterInput (signedPatientGenerator q) input t =
      UnionClosedness.negativeCode
        (PatientMachine.output cofiniteOracle
          (fun s => negativeIndex (input s)) t) := by
  unfold outputAfterInput Generic.output signedPatientGenerator
  rw [if_neg]
  · congr 1
    exact outputAfterInput_patientGenerator cofiniteOracle
      (fun s => negativeIndex (input s)) t
  · simpa [NoiseLossFeedback.observedThrough,
      Generic.sequenceSample_prefix] using hdetect

end Case019

namespace Case019

open GenLimit
open Stage3Case019

private theorem positiveIndex_range_diff_finite
    {K : Set ℤ} {input : Stream ℤ}
    (hnoise : (Set.range input \ K).Finite) :
    (Set.range (fun t => positiveIndex (input t)) \
      {n | UnionClosedness.positiveCode n ∈ K}).Finite := by
  let F : Set ℕ := insert 0 (positiveIndex '' (Set.range input \ K))
  have hF : F.Finite := (hnoise.image positiveIndex).insert 0
  apply hF.subset
  rintro n ⟨⟨t, rfl⟩, hnK⟩
  by_cases hn : positiveIndex (input t) = 0
  · exact Set.mem_insert_iff.mpr (Or.inl hn)
  · apply Set.mem_insert_iff.mpr
    right
    refine ⟨input t, ?_, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    intro hinK
    apply hnK
    have hpos : 0 < input t := by
      cases h : input t with
      | ofNat m =>
          cases m with
          | zero => simp [positiveIndex, h] at hn
          | succ m => simp
      | negSucc m => simp [positiveIndex, h] at hn
    change UnionClosedness.positiveCode (positiveIndex (input t)) ∈ K
    rw [positiveCode_positiveIndex_of_positive hpos]
    exact hinK

private theorem signedPatient_first_novel
    (q : ℕ) {K : Set ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionFirstClass q)
    (input : Stream ℤ)
    (hp : Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input
      (outputAfterInput (signedPatientGenerator q) input) K := by
  let sideInput : Stream ℕ := fun t => positiveIndex (input t)
  let P : Set ℕ := {n | UnionClosedness.positiveCode n ∈ K}
  have hmissing := positive_missing_finite hp.2.1 hK.2
  obtain ⟨j, hj⟩ := exists_cofiniteOracle_index sideInput hmissing
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity
    cofiniteOracle sideInput hj
  obtain ⟨Td, hTd⟩ :=
    NoiseLossFeedback.allMarkers_eventually_observed hp hK.1
  have hnoise : (Set.range input \ K).Finite := by
    obtain ⟨F, hF, _⟩ := hp.2.2
    rw [← hF]
    exact F.finite_toSet
  have hRP : (cofiniteOracle.language j \ P).Finite := by
    rw [← hj]
    exact positiveIndex_range_diff_finite hnoise
  let badTimes : Set ℕ :=
    (PatientMachine.output cofiniteOracle sideInput) ⁻¹'
      (cofiniteOracle.language j \ P)
  have houtInjective :
      Function.Injective (PatientMachine.output cofiniteOracle sideInput) := by
    intro a b hab
    rcases lt_trichotomy a b with hablt | rfl | hbalt
    · exact False.elim
        (PatientMachine.output_ne_of_lt cofiniteOracle sideInput hablt hab)
    · rfl
    · exact False.elim
        (PatientMachine.output_ne_of_lt cofiniteOracle sideInput hbalt hab.symm)
  have hbadFinite : badTimes.Finite :=
    hRP.preimage (Set.injOn_of_injective houtInjective)
  obtain ⟨d, hd⟩ := Finset.exists_nat_subset_range hbadFinite.toFinset
  obtain ⟨Tv, hTv⟩ := hrun.1
  refine ⟨max Td (max Tv d), ?_⟩
  intro t ht
  have hdetect := hTd t (le_trans (le_max_left _ _) ht)
  have hout := signedPatient_positive_output q input hdetect
  have hvalid := hTv t
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) ht))
  have htgeD : d ≤ t :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) ht)
  have hnotBad :
      PatientMachine.output cofiniteOracle sideInput t ∉
        cofiniteOracle.language j \ P := by
    intro hbad
    have htbad : t ∈ hbadFinite.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hbad
    exact (Nat.not_lt_of_ge htgeD) (by simpa using hd htbad)
  have hmemP : PatientMachine.output cofiniteOracle sideInput t ∈ P := by
    by_contra hnotP
    exact hnotBad ⟨hvalid.1, hnotP⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    exact hmemP
  · intro hsample
    obtain ⟨s, hs, heq⟩ := Generic.mem_sample_iff.mp hsample
    have heqIndex : sideInput s =
        PatientMachine.output cofiniteOracle sideInput t := by
      dsimp [sideInput]
      rw [heq, hout, positiveIndex_positiveCode]
    exact PatientMachine.stream_ne_output cofiniteOracle sideInput t s
      (by omega) heqIndex
  · intro s hs
    by_cases hsDetect : NoiseLossFeedback.omissionMarkerFinset q ⊆
        NoiseLossFeedback.observedThrough input s
    · rw [signedPatient_positive_output q input hsDetect, hout]
      intro heq
      exact PatientMachine.output_ne_of_lt cofiniteOracle sideInput hs
        (UnionClosedness.positiveCode_injective heq)
    · rw [signedPatient_negative_output q input hsDetect, hout]
      exact ne_of_lt (lt_trans
        (UnionClosedness.negativeCode_mem _)
        (UnionClosedness.positiveCode_mem _))

private theorem signedPatient_second_novel
    (q : ℕ) {K : Set ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionSecondClass q)
    (input : Stream ℤ)
    (hp : Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input
      (outputAfterInput (signedPatientGenerator q) input) K := by
  let sideInput : Stream ℕ := fun t => negativeIndex (input t)
  have hno := NoiseLossFeedback.not_allMarkers_observed_second hK hp
  refine ⟨0, ?_⟩
  intro t _
  have hout := signedPatient_negative_output q input (hno t)
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    exact hK.1 (UnionClosedness.negativeCode_mem _)
  · intro hsample
    obtain ⟨s, hs, heq⟩ := Generic.mem_sample_iff.mp hsample
    have heqIndex : sideInput s =
        PatientMachine.output cofiniteOracle sideInput t := by
      dsimp [sideInput]
      rw [heq, hout, negativeIndex_negativeCode]
    exact PatientMachine.stream_ne_output cofiniteOracle sideInput t s
      (by omega) heqIndex
  · intro s hs
    rw [signedPatient_negative_output q input (hno s), hout]
    intro heq
    exact PatientMachine.output_ne_of_lt cofiniteOracle sideInput hs
      (UnionClosedness.negativeCode_injective heq)

end Case019


namespace Case019

open GenLimit
open Stage3Case019

private theorem balanced_negativeCode (n : ℕ) :
    balanced (2 * n + 1) = UnionClosedness.negativeCode n := by
  simp [balanced, UnionClosedness.negativeCode]
  rw [Int.negSucc_eq]
  omega

private theorem balanced_positiveCode (n : ℕ) :
    balanced (2 * n + 2) = UnionClosedness.positiveCode n := by
  simp [balanced, UnionClosedness.positiveCode]
  omega

private theorem positive_prefix_embed
    (A : Set ℕ) (D : Set ℤ)
    (hmap : ∀ n, n ∈ A → UnionClosedness.positiveCode n ∈ D)
    (m N : ℕ) (hN : 2 * m + 2 ≤ N) :
    PatientScope.prefixCount A m ≤
      PatientScope.prefixCount (balancedRanks D) N := by
  classical
  let f : ℕ → ℕ := fun n => 2 * n + 2
  let source := PatientScope.prefixFinset A m
  let target := PatientScope.prefixFinset (balancedRanks D) N
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    omega
  have hsub : source.image f ⊆ target := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    have hn' := PatientScope.mem_prefixFinset.mp hn
    apply PatientScope.mem_prefixFinset.mpr
    constructor
    · dsimp [f]
      omega
    · change balanced (f n) ∈ D
      rw [show f n = 2 * n + 2 by rfl, balanced_positiveCode]
      exact hmap n hn'.2
  change source.card ≤ target.card
  rw [← Finset.card_image_of_injective source hf]
  exact Finset.card_le_card hsub

private theorem negative_prefix_embed
    (A : Set ℕ) (D : Set ℤ)
    (hmap : ∀ n, n ∈ A → UnionClosedness.negativeCode n ∈ D)
    (m N : ℕ) (hN : 2 * m + 2 ≤ N) :
    PatientScope.prefixCount A m ≤
      PatientScope.prefixCount (balancedRanks D) N := by
  classical
  let f : ℕ → ℕ := fun n => 2 * n + 1
  let source := PatientScope.prefixFinset A m
  let target := PatientScope.prefixFinset (balancedRanks D) N
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    omega
  have hsub : source.image f ⊆ target := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    have hn' := PatientScope.mem_prefixFinset.mp hn
    apply PatientScope.mem_prefixFinset.mpr
    constructor
    · dsimp [f]
      omega
    · change balanced (f n) ∈ D
      rw [show f n = 2 * n + 1 by rfl, balanced_negativeCode]
      exact hmap n hn'.2
  change source.card ≤ target.card
  rw [← Finset.card_image_of_injective source hf]
  exact Finset.card_le_card hsub

private theorem prefixCount_diff_finite
    (A F : Set ℕ) (hF : F.Finite) (n : ℕ) :
    PatientScope.prefixCount A n ≤
      PatientScope.prefixCount (A \ F) n + hF.toFinset.card := by
  classical
  let left := PatientScope.prefixFinset A n
  let main := PatientScope.prefixFinset (A \ F) n
  let extra := PatientScope.prefixFinset F n
  have hsubset : left ⊆ main ∪ extra := by
    intro x hx
    have hx' := PatientScope.mem_prefixFinset.mp hx
    by_cases hxF : x ∈ F
    · apply Finset.mem_union_right
      exact PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxF⟩
    · apply Finset.mem_union_left
      exact PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hx'.2, hxF⟩
  change left.card ≤ main.card + hF.toFinset.card
  calc
    left.card ≤ (main ∪ extra).card := Finset.card_le_card hsubset
    _ ≤ main.card + extra.card := Finset.card_union_le _ _
    _ ≤ main.card + hF.toFinset.card :=
      Nat.add_le_add_left (prefixCount_finite_le hF n) _

private theorem relativeLowerDensity_diff_finite
    (A P F : Set ℕ) (hAP : A ⊆ P)
    (hPinf : P.Infinite) (hF : F.Finite) :
    PatientScope.relativeLowerDensity A P ≤
      PatientScope.relativeLowerDensity (A \ F) P := by
  let u : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount A n : ℝ) /
      (PatientScope.prefixCount P n : ℝ)
  let v : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (A \ F) n : ℝ) /
      (PatientScope.prefixCount P n : ℝ)
  let e : ℕ → ℝ := fun n =>
    (hF.toFinset.card : ℝ) /
      (PatientScope.prefixCount P n : ℝ)
  have hcast : Tendsto (fun n =>
      (PatientScope.prefixCount P n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (PatientScope.tendsto_prefixCount_atTop hPinf)
  have he : Tendsto e atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hu1 : ∀ n, u n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount P n = 0
    · simp [u, hn]
    · dsimp [u]
      rw [div_le_one (by positivity)]
      exact_mod_cast PatientScope.prefixCount_mono hAP n
  have hv0 : ∀ n, 0 ≤ v n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hv1 : ∀ n, v n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount P n = 0
    · simp [v, hn]
    · dsimp [v]
      rw [div_le_one (by positivity)]
      exact_mod_cast PatientScope.prefixCount_mono (by
        intro x hx
        exact hAP hx.1) n
  have hcomp : ∀ᶠ n in atTop, u n ≤ v n + e n := by
    have hpos : ∀ᶠ n in atTop, 0 < PatientScope.prefixCount P n :=
      (PatientScope.tendsto_prefixCount_atTop hPinf).eventually
        (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hcount := prefixCount_diff_finite A F hF n
    dsimp [u, v, e]
    rw [div_add_div_same]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount)
      (Nat.cast_nonneg _)
  unfold PatientScope.relativeLowerDensity
  exact liminf_le_of_eventually_le_add_zero u v e hu0 hu1 hv0 hv1 he hcomp

private theorem cofinite_infinite
    (P : Set ℕ) (hmissing : (Set.univ \ P).Finite) : P.Infinite := by
  intro hP
  have hunivInf : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
  apply hunivInf
  have huniv : (Set.univ : Set ℕ) = P ∪ (Set.univ \ P) := by
    ext n
    by_cases hn : n ∈ P <;> simp [hn]
  rw [huniv]
  exact hP.union hmissing

private theorem balanced_density_transfer
    (P A : Set ℕ) (K D : Set ℤ)
    (hmissing : (Set.univ \ P).Finite)
    (hAP : A ⊆ P) (hDK : D ⊆ K)
    (hembed : ∀ m N, 2 * m + 2 ≤ N →
      PatientScope.prefixCount A m ≤
        PatientScope.prefixCount (balancedRanks D) N)
    (hdensity : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity A P) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity D K := by
  classical
  let φ : ℕ → ℕ := fun n => n / 2 - 1
  let u : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount A n : ℝ) /
      (PatientScope.prefixCount P n : ℝ)
  let v : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount (balancedRanks D) n : ℝ) /
      (PatientScope.prefixCount (balancedRanks K) n : ℝ)
  let c : ℕ := hmissing.toFinset.card
  let e : ℕ → ℝ := fun n =>
    ((2 * c + 3 : ℕ) : ℝ) /
      (PatientScope.prefixCount P (φ n) : ℝ)
  have hPinf := cofinite_infinite P hmissing
  have hφ : Tendsto φ atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (2 * (b + 1))] with n hn
    have hdiv : b + 1 ≤ n / 2 := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    dsimp [φ]
    omega
  have hcast : Tendsto (fun n =>
      (PatientScope.prefixCount P (φ n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      ((PatientScope.tendsto_prefixCount_atTop hPinf).comp hφ)
  have he : Tendsto e atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hv0 : ∀ n, 0 ≤ v n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hv1 : ∀ n, v n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount (balancedRanks K) n = 0
    · simp [v, hn]
    · dsimp [v]
      rw [div_le_one (by positivity)]
      exact_mod_cast PatientScope.prefixCount_mono (by
        intro x hx
        exact hDK hx) n
  have hcomp : ∀ᶠ n in atTop, u (φ n) ≤ 2 * v n + e n := by
    have hp : ∀ᶠ n in atTop, 0 < PatientScope.prefixCount P (φ n) :=
      ((PatientScope.tendsto_prefixCount_atTop hPinf).comp hφ).eventually
        (eventually_gt_atTop 0)
    filter_upwards [eventually_ge_atTop 2, hp] with n hn hp
    let m := φ n
    let a := PatientScope.prefixCount A m
    let pcount := PatientScope.prefixCount P m
    let d := PatientScope.prefixCount (balancedRanks D) n
    let kcount := PatientScope.prefixCount (balancedRanks K) n
    have hrank : 2 * m + 2 ≤ n := by
      dsimp [m, φ]
      omega
    have had : a ≤ d := hembed m n hrank
    have hap : a ≤ pcount := PatientScope.prefixCount_mono hAP m
    have hdk : d ≤ kcount := PatientScope.prefixCount_mono (by
      intro x hx
      exact hDK hx) n
    have hkn : kcount ≤ n := by
      dsimp [kcount]
      unfold PatientScope.prefixCount PatientScope.prefixFinset
      simpa using Finset.card_filter_le (Finset.range n)
        (fun x => x ∈ balancedRanks K)
    have hpm : pcount ≤ m := by
      dsimp [pcount]
      unfold PatientScope.prefixCount PatientScope.prefixFinset
      simpa using Finset.card_filter_le (Finset.range m) (fun x => x ∈ P)
    have hmn : m ≤ n := by
      dsimp [m, φ]
      omega
    have hpn : pcount ≤ n := le_trans hpm hmn
    have hmcount : m ≤ pcount + c := by
      have hcount := prefixCount_inter_super_le
        Set.univ P Set.univ (by simp) hmissing m
      rw [Set.univ_inter, show PatientScope.prefixCount Set.univ m = m by
        simp [PatientScope.prefixCount, PatientScope.prefixFinset]] at hcount
      simpa [pcount, c] using hcount
    have hnmp : n ≤ 2 * pcount + (2 * c + 3) := by
      have hnm : n ≤ 2 * m + 3 := by
        dsimp [m, φ]
        omega
      omega
    have hnpos : 0 < n := by omega
    by_cases hkzero : kcount = 0
    · have hd0 : d = 0 := Nat.eq_zero_of_le_zero (by simpa [hkzero] using hdk)
      have ha0 : a = 0 := Nat.eq_zero_of_le_zero (by simpa [hd0] using had)
      simp [u, v, e, m, a, d, kcount, ha0, hd0, hkzero]
      positivity
    · have hkpos : 0 < kcount := Nat.pos_of_ne_zero hkzero
      have htarget : (a : ℝ) / (n : ℝ) ≤ (d : ℝ) / (kcount : ℝ) := by
        calc
          (a : ℝ) / (n : ℝ) ≤ (d : ℝ) / (n : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast had)
              (Nat.cast_nonneg _)
          _ ≤ (d : ℝ) / (kcount : ℝ) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _)
              (by exact_mod_cast hkpos) (by exact_mod_cast hkn)
      have hfirst : (a : ℝ) / (pcount : ℝ) ≤
          2 * ((a : ℝ) / (n : ℝ)) +
            ((2 * c + 3 : ℕ) : ℝ) / (pcount : ℝ) := by
        have hpR : (0 : ℝ) < pcount := by exact_mod_cast hp
        have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
        have hapR : (a : ℝ) ≤ pcount := by exact_mod_cast hap
        have hpnR : (pcount : ℝ) ≤ n := by exact_mod_cast hpn
        have hboundR : (n : ℝ) ≤
            2 * (pcount : ℝ) + ((2 * c + 3 : ℕ) : ℝ) := by
          exact_mod_cast hnmp
        rw [div_le_iff₀ hpR]
        field_simp [hnR.ne']
        nlinarith [mul_le_mul_of_nonneg_left hboundR (Nat.cast_nonneg a),
          mul_le_mul_of_nonneg_right hapR (Nat.cast_nonneg (2 * c + 3)),
          mul_le_mul_of_nonneg_right hpnR (Nat.cast_nonneg (2 * c + 3))]
      dsimp [u, v, e, m, a, pcount, d, kcount]
      exact hfirst.trans (add_le_add_right (mul_le_mul_of_nonneg_left htarget
        (by norm_num : (0 : ℝ) ≤ 2)) _)
  unfold balancedRelativeLowerDensity PatientScope.relativeLowerDensity
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop hv1)
    (isBoundedUnder_of ⟨0, hv0⟩)).2
  intro y hy
  have hscaled : 2 * y < liminf u atTop := by
    have hdensity' : (1 / 2 : ℝ) ≤ liminf u atTop := by
      simpa [PatientScope.relativeLowerDensity, u] using hdensity
    nlinarith
  obtain ⟨r, hyr, hrDensity⟩ := exists_between hscaled
  have hrEventually : ∀ᶠ n in atTop, r < u n :=
    eventually_lt_of_lt_liminf hrDensity
      (isBoundedUnder_of ⟨0, hu0⟩)
  have hrComposed : ∀ᶠ n in atTop, r < u (φ n) := hφ hrEventually
  have heEventually : ∀ᶠ n in atTop, e n < r - 2 * y := by
    have : 0 < r - 2 * y := by linarith
    exact he.eventually (Iio_mem_nhds this)
  filter_upwards [hrComposed, heEventually, hcomp] with n hr heSmall hcompare
  nlinarith

end Case019


namespace Case019

open GenLimit
open Stage3Case019

private theorem signedPatient_first_density
    (q : ℕ) {K : Set ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionFirstClass q)
    (input : Stream ℤ)
    (hp : Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input
        (outputAfterInput (signedPatientGenerator q) input) ∩ K) K := by
  let sideInput : Stream ℕ := fun t => positiveIndex (input t)
  let sideOutput : Stream ℕ := PatientMachine.output cofiniteOracle sideInput
  let P : Set ℕ := {n | UnionClosedness.positiveCode n ∈ K}
  let E : Set ℕ := Set.range sideInput
  have hmissing := positive_missing_finite hp.2.1 hK.2
  obtain ⟨j, hj⟩ := exists_cofiniteOracle_index sideInput hmissing
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity
    cofiniteOracle sideInput hj
  obtain ⟨Td, hTd⟩ :=
    NoiseLossFeedback.allMarkers_eventually_observed hp hK.1
  have hnoise : (Set.range input \ K).Finite := by
    obtain ⟨F, hF, _⟩ := hp.2.2
    rw [← hF]
    exact F.finite_toSet
  have hEP : (E \ P).Finite := by
    dsimp [E]
    exact positiveIndex_range_diff_finite hnoise
  have hPE : P ⊆ E := by
    intro n hn
    obtain ⟨t, ht⟩ := hp.2.1 hn
    exact ⟨t, by simpa [sideInput, ht]⟩
  have hPmissing : (Set.univ \ P).Finite := by
    obtain ⟨r, hr⟩ := hK.2
    apply (Set.finite_Iio r).subset
    intro n hn
    by_contra hnr
    have hrn : r ≤ n := Nat.le_of_not_gt hnr
    apply hn.2
    change UnionClosedness.positiveCode n ∈ K
    apply hr
    exact ⟨n - r, by
      apply Int.ofNat_inj.mpr
      omega⟩
  have hPinf : P.Infinite := cofinite_infinite P hPmissing
  let B : Set ℕ := GeneratorFirst sideInput sideOutput ∩ P
  have hBhalf : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity B P := by
    have htransfer := relativeLowerDensity_transfer_finite_super
      (GeneratorFirst sideInput sideOutput) P E hPinf hPE hEP
    have hpatient : (1 / 2 : ℝ) ≤
        PatientScope.relativeLowerDensity
          (GeneratorFirst sideInput sideOutput ∩ E) E := by
      have h := hrun.2
      unfold PatientMachine.patientLowerDensity at h
      rw [← hj] at h
      simpa [sideOutput, E] using h
    exact hpatient.trans (by simpa [B] using htransfer)
  let F : Set ℕ := sideOutput '' Set.Iio Td
  have hF : F.Finite := (Set.finite_Iio Td).image sideOutput
  let A : Set ℕ := B \ F
  have hAB : A ⊆ P := by
    intro n hn
    exact hn.1.2
  have hAhalf : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity A P := by
    exact hBhalf.trans (relativeLowerDensity_diff_finite B P F
      (by intro n hn; exact hn.2) hPinf hF)
  let D : Set ℤ := GeneratorFirstOn input
    (outputAfterInput (signedPatientGenerator q) input) ∩ K
  have hmap : ∀ n, n ∈ A → UnionClosedness.positiveCode n ∈ D := by
    intro n hn
    obtain ⟨⟨t, htOut, htFresh⟩, hnP⟩ := hn.1
    have ht : Td ≤ t := by
      by_contra hnot
      apply hn.2
      exact ⟨t, Nat.lt_of_not_ge hnot, htOut⟩
    refine ⟨?_, hnP⟩
    refine ⟨t, ?_, ?_⟩
    · rw [signedPatient_positive_output q input (hTd t ht)]
      congr 1
    · intro s hs heq
      apply htFresh s hs
      dsimp [sideInput]
      rw [heq, positiveIndex_positiveCode]
  apply balanced_density_transfer P A K D
  · exact hPmissing
  · exact hAB
  · exact Set.inter_subset_right
  · intro m N hN
    exact positive_prefix_embed A D hmap m N hN
  · exact hAhalf

private theorem signedPatient_second_density
    (q : ℕ) {K : Set ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionSecondClass q)
    (input : Stream ℤ)
    (hp : Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
      (GeneratorFirstOn input
        (outputAfterInput (signedPatientGenerator q) input) ∩ K) K := by
  let sideInput : Stream ℕ := fun t => negativeIndex (input t)
  let sideOutput : Stream ℕ := PatientMachine.output cofiniteOracle sideInput
  have hrange : Set.range sideInput = Set.univ :=
    negative_range_univ hp.2.1 hK.1
  have hmissing : (Set.univ \ Set.range sideInput).Finite := by
    rw [hrange]
    simp
  obtain ⟨j, hj⟩ := exists_cofiniteOracle_index sideInput hmissing
  have hrun := PatientMachine.patientScope_generation_and_lowerDensity
    cofiniteOracle sideInput hj
  have hno := NoiseLossFeedback.not_allMarkers_observed_second hK hp
  let A : Set ℕ := GeneratorFirst sideInput sideOutput ∩ Set.univ
  let D : Set ℤ := GeneratorFirstOn input
    (outputAfterInput (signedPatientGenerator q) input) ∩ K
  have hmap : ∀ n, n ∈ A → UnionClosedness.negativeCode n ∈ D := by
    intro n hn
    obtain ⟨t, htOut, htFresh⟩ := hn.1
    refine ⟨?_, hK.1 (UnionClosedness.negativeCode_mem n)⟩
    refine ⟨t, ?_, ?_⟩
    · rw [signedPatient_negative_output q input (hno t)]
      congr 1
    · intro s hs heq
      apply htFresh s hs
      dsimp [sideInput]
      rw [heq, negativeIndex_negativeCode]
  have hAhalf : (1 / 2 : ℝ) ≤
      PatientScope.relativeLowerDensity A Set.univ := by
    have h := hrun.2
    unfold PatientMachine.patientLowerDensity at h
    rw [← hj, hrange] at h
    simpa [A, sideOutput] using h
  apply balanced_density_transfer Set.univ A K D
  · simp
  · intro n _
    trivial
  · exact Set.inter_subset_right
  · intro m N hN
    exact negative_prefix_embed A D hmap m N hN
  · exact hAhalf

private theorem signedPatient_success
    (q : ℕ) {K : Set ℤ}
    (hK : K ∈ NoiseLossFeedback.finiteOmissionClass q)
    (input : Stream ℤ)
    (hp : Generic.InjectiveValueContaminatedPresentationAtMost input K q) :
    NovelGeneratesAfterInput input
        (outputAfterInput (signedPatientGenerator q) input) K ∧
      (1 / 4 : ℝ) ≤ balancedRelativeLowerDensity
        (GeneratorFirstOn input
          (outputAfterInput (signedPatientGenerator q) input) ∩ K) K := by
  rcases hK with hfirst | hsecond
  · exact ⟨signedPatient_first_novel q hfirst input hp,
      signedPatient_first_density q hfirst input hp⟩
  · exact ⟨signedPatient_second_novel q hsecond input hp,
      signedPatient_second_density q hsecond input hp⟩

/-- Checked uncountable adjacent-level separation component. -/
theorem stage3_uncountable_separation : SeparationClause := by
  intro q
  refine ⟨NoiseLossFeedback.finiteOmissionClass q,
    finiteOmissionClass_uncountable q,
    NoiseLossFeedback.finiteOmissionClass_uus q,
    ?_, adjacentLevel_failure q⟩
  exact ⟨signedPatientGenerator q, fun K hK input hp =>
    signedPatient_success q hK input hp⟩

end Case019

theorem stage3_result : Stage3Case019.MainClaim :=
  ⟨Case019.stage3_countable_half_density,
    Case019.stage3_uncountable_separation⟩
