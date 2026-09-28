import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency
import GenLimit.Paper12_NoiseLossAndFeedback.FiniteNoiseSeparation
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality

open Set Filter
open scoped Topology

namespace Stage3Case019Proof

open GenLimit GenLimit.PatientMachine

noncomputable def oracleOfFamily
    (family : Stage3Case019.LanguageFamily ℕ)
    (hinf : ∀ i, (family i).Infinite) : GenLimit.OracleFamily where
  language := family
  infinite' := hinf
  query i x := by classical exact if x ∈ family i then true else false
  query_spec i x := by classical simp


open GenLimit GenLimit.PatientMachine

lemma sample_eq_of_eq_lt {a b : ℕ → ℕ} {n : ℕ}
    (h : ∀ k, k < n → a k = b k) : sample a n = sample b n := by
  classical
  unfold sample
  apply Finset.image_congr
  intro k hk
  exact h k (Finset.mem_range.mp hk)

lemma consistent_congr {C : LanguageFamily} {a b : ℕ → ℕ} {n i : ℕ}
    (hs : sample a n = sample b n) :
    Consistent C a n i ↔ Consistent C b n i := by
  simp [Consistent, hs]

lemma recursiveCritical_congr {C : LanguageFamily} {a b : ℕ → ℕ} {n : ℕ}
    (hs : sample a n = sample b n) :
    ∀ i, RecursiveCritical C a n i ↔ RecursiveCritical C b n i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simpa [RecursiveCritical] using (consistent_congr (i := 0) hs)
    | succ i =>
      simp only [RecursiveCritical]
      constructor
      · rintro ⟨hc, hsub⟩
        refine ⟨(consistent_congr hs).mp hc, ?_⟩
        intro j hj hcrit
        exact hsub j hj ((ih j (by omega)).mpr hcrit)
      · rintro ⟨hc, hsub⟩
        refine ⟨(consistent_congr hs).mpr hc, ?_⟩
        intro j hj hcrit
        exact hsub j hj ((ih j (by omega)).mp hcrit)

lemma decision_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ k, k < t + 1 → a k = b k) :
    PatientMachine.decide O.language a t old =
      PatientMachine.decide O.language b t old := by
  classical
  have hs : sample a (t+1) = sample b (t+1) := sample_eq_of_eq_lt h
  have hs0 : sample a t = sample b t :=
    sample_eq_of_eq_lt (fun k hk => h k (lt_trans hk (Nat.lt_succ_self t)))
  have hc : ∀ i, Consistent O.language a (t+1) i ↔
      Consistent O.language b (t+1) i := fun i => consistent_congr hs
  have hr : ∀ i, RecursiveCritical O.language a (t+1) i ↔
      RecursiveCritical O.language b (t+1) i := recursiveCritical_congr hs
  have hr0 : ∀ i, RecursiveCritical O.language a t i ↔
      RecursiveCritical O.language b t i := recursiveCritical_congr hs0
  have hcf : (fun i => Consistent O.language a (t+1) i) =
      (fun i => Consistent O.language b (t+1) i) := funext (fun i => propext (hc i))
  have hrf : (fun i => RecursiveCritical O.language a (t+1) i) =
      (fun i => RecursiveCritical O.language b (t+1) i) := funext (fun i => propext (hr i))
  have hr0f : (fun i => RecursiveCritical O.language a t i) =
      (fun i => RecursiveCritical O.language b t i) := funext (fun i => propext (hr0 i))
  simp only [PatientMachine.decide, stableDecision, backtrackDecision,
    highestCritical, highestSurvivor, lowestConsistentInScope,
    lowestConsistent, consistentIndices, survivingCriticalIndices,
    criticalIndices, hcf, hrf, hr0f, hc]

lemma leastAvailable_congr (O : OracleFamily) {a b : ℕ → ℕ} {n : ℕ}
    (hs : sample a n = sample b n) (used : Finset ℕ) (focus : ℕ) :
    leastAvailable O.language O.infinite' a n used focus =
      leastAvailable O.language O.infinite' b n used focus := by
  classical
  unfold leastAvailable
  apply Nat.find_congr (Nat.find_spec (available_exists O.language O.infinite' a n used focus))
  intro x _
  simp [Available, hs]

lemma processRound_congr (O : OracleFamily) {a b : ℕ → ℕ} {t : ℕ} {old : State}
    (h : ∀ k, k < t + 1 → a k = b k) :
    processRound O a t old = processRound O b t old := by
  classical
  have hs : sample a (t+1) = sample b (t+1) := sample_eq_of_eq_lt h
  have hd := decision_congr (old := old) O h
  simp only [processRound]
  rw [hd]
  rw [leastAvailable_congr O hs]

lemma run_congr (O : OracleFamily) {a b : ℕ → ℕ} :
    ∀ n, (∀ k, k < n → a k = b k) → run O a n = run O b n := by
  intro n
  induction n with
  | zero => intro; rfl
  | succ n ih =>
      intro h
      rw [run_succ, run_succ, ih (fun k hk => h k (Nat.lt.step hk))]
      exact processRound_congr O h



def prefixStream {n : ℕ} (xs : Fin n → ℕ) : ℕ → ℕ :=
  fun k => if h : k < n then xs ⟨k, h⟩ else 0

noncomputable def patientGenerator (O : OracleFamily) : GenLimit.Generic.Generator ℕ
  | 0, _ => 0
  | t + 1, xs => PatientMachine.output O (prefixStream xs) t

theorem output_patientGenerator (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    Stage3Case019.outputAfterInput (patientGenerator O) stream t =
      PatientMachine.output O stream t := by
  have hp : ∀ k, k < t + 1 → prefixStream (fun i : Fin (t + 1) => stream i) k = stream k := by
    intro k hk
    simp [prefixStream, hk]
  have hr := run_congr O (n := t + 1) hp
  simp only [Stage3Case019.outputAfterInput, GenLimit.Generic.output,
    patientGenerator]
  unfold PatientMachine.output
  rw [hr]

theorem finiteNoiseFiniteOmission_of_bounded
    {stream : ℕ → ℕ} {K : Set ℕ} {q : ℕ}
    (h : GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
      stream K q) :
    GenLimit.InfiniteContamination.FiniteNoiseFiniteOmissionEnumeration
      stream K := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.finiteNoise_iff_valuesOutside_finite_of_injective h.1]
    obtain ⟨F, hF, _⟩ := h.2.2
    rw [← hF]
    exact F.finite_toSet
  · unfold GenLimit.InfiniteContamination.FiniteOmissions
    rw [show K \ Set.range stream = ∅ by exact Set.diff_eq_empty.mpr h.2.1]
    exact Set.finite_empty

theorem novel_patient
    (O : GenLimit.OracleFamily) {stream : ℕ → ℕ} {j : ℕ}
    (hP : GenLimit.Presents stream (O.language j)) :
    GenLimit.NovelGeneratesInLimit stream
      (Stage3Case019.outputAfterInput (patientGenerator O) stream)
      (O.language j) := by
  obtain ⟨⟨T, hgen⟩, _⟩ :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O stream hP
  refine ⟨T, ?_⟩
  intro t ht
  rcases hgen t ht with ⟨hmem, hfresh, hnew⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [output_patientGenerator] using hmem
  · intro hsample
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
    exact hfresh s (Nat.le_of_lt_succ hs) (heq.trans (output_patientGenerator O stream t))
  · simpa [output_patientGenerator] using hnew

theorem patient_density
    (O : GenLimit.OracleFamily) {stream : ℕ → ℕ} {j : ℕ}
    (hP : GenLimit.Presents stream (O.language j)) :
    (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity
      (GenLimit.GeneratorFirst stream
        (Stage3Case019.outputAfterInput (patientGenerator O) stream) ∩
        O.language j) (O.language j) := by
  have h := GenLimit.PatientMachine.patientScope_lowerDensity_half O stream hP
  have hout :
      Stage3Case019.outputAfterInput (patientGenerator O) stream =
        PatientMachine.output O stream :=
    funext (output_patientGenerator O stream)
  rw [hout]
  exact h

open GenLimit.PatientScope

lemma prefixCount_le_add_of_subset_union_finite
    {A B F : Set ℕ} (hF : F.Finite) (hsub : A ⊆ B ∪ F) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hF.toFinset.card := by
  classical
  unfold prefixCount
  calc
    (prefixFinset A n).card ≤
        (prefixFinset B n ∪ hF.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := mem_prefixFinset.mp hx
      rcases hsub hx'.2 with hxB | hxF
      · exact Finset.mem_union_left _ (mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
      · exact Finset.mem_union_right _ (hF.mem_toFinset.mpr hxF)
    _ ≤ (prefixFinset B n).card + hF.toFinset.card := Finset.card_union_le _ _

lemma relativeLowerDensity_finite_transfer
    {A K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfin : (R \ K).Finite) (hAR : A ⊆ R) :
    relativeLowerDensity A R ≤ relativeLowerDensity (A ∩ K) K := by
  let c := hfin.toFinset.card
  let f : ℕ → ℝ := fun n => (prefixCount A n : ℝ) / (prefixCount R n : ℝ)
  let g : ℕ → ℝ := fun n => (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n => (c : ℝ) / (prefixCount R n : ℝ)
  have hR : R.Infinite := hK.mono hKR
  have hcount : ∀ n, prefixCount A n ≤ prefixCount (A ∩ K) n + c := by
    intro n
    apply prefixCount_le_add_of_subset_union_finite hfin
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx, hxK⟩
    · exact Or.inr ⟨hAR hx, hxK⟩
  have hden : ∀ n, prefixCount K n ≤ prefixCount R n :=
    fun n => prefixCount_mono hKR n
  have hcompare : ∀ᶠ n : ℕ in atTop, f n ≤ g n + e n := by
    have hkpos : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
      (tendsto_prefixCount_atTop hK).eventually (eventually_gt_atTop 0)
    filter_upwards [hkpos] with n hn
    have hrpos : 0 < prefixCount R n := lt_of_lt_of_le hn (hden n)
    have hkR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hrR : (0 : ℝ) < prefixCount R n := by exact_mod_cast hrpos
    have hcR : (prefixCount A n : ℝ) ≤
        prefixCount (A ∩ K) n + c := by exact_mod_cast hcount n
    have hnumNonneg : (0 : ℝ) ≤ prefixCount (A ∩ K) n := by positivity
    have hfrac : (prefixCount (A ∩ K) n : ℝ) / prefixCount R n ≤
        (prefixCount (A ∩ K) n : ℝ) / prefixCount K n := by
      exact div_le_div_of_nonneg_left hnumNonneg hkR (by exact_mod_cast hden n)
    dsimp [f, g, e]
    calc
      (prefixCount A n : ℝ) / prefixCount R n ≤
          ((prefixCount (A ∩ K) n : ℝ) + c) / prefixCount R n :=
        div_le_div_of_nonneg_right hcR hrR.le
      _ = (prefixCount (A ∩ K) n : ℝ) / prefixCount R n +
          (c : ℝ) / prefixCount R n := by rw [add_div]
      _ ≤ (prefixCount (A ∩ K) n : ℝ) / prefixCount K n +
          (c : ℝ) / prefixCount R n := add_le_add_right hfrac _
  have he : Tendsto e atTop (𝓝 0) := by
    have hcast : Tendsto (fun n => (prefixCount R n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_prefixCount_atTop hR)
    simpa [e] using tendsto_const_nhds.div_atTop hcast
  have hf_nonneg : ∀ n, 0 ≤ f n := by intro n; positivity
  have hf_le_one : ∀ n, f n ≤ 1 := by
    intro n
    by_cases hn : prefixCount R n = 0
    · simp [f, hn]
    · have hr : (0 : ℝ) < prefixCount R n := by exact_mod_cast Nat.pos_of_ne_zero hn
      change (prefixCount A n : ℝ) / prefixCount R n ≤ 1
      rw [div_le_one hr]
      exact_mod_cast prefixCount_mono hAR n
  have hg_nonneg : ∀ n, 0 ≤ g n := by intro n; positivity
  have hg_le_one : ∀ n, g n ≤ 1 := by
    intro n
    by_cases hn : prefixCount K n = 0
    · simp [g, hn]
    · have hk : (0 : ℝ) < prefixCount K n := by exact_mod_cast Nat.pos_of_ne_zero hn
      change (prefixCount (A ∩ K) n : ℝ) / prefixCount K n ≤ 1
      rw [div_le_one hk]
      exact_mod_cast prefixCount_mono (Set.inter_subset_right) n
  have he_nonneg : ∀ n, 0 ≤ e n := by intro n; positivity
  have he_le : ∀ᶠ n : ℕ in atTop, e n ≤ 1 :=
    (he.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)).mono (by
      intro n hn
      have := abs_lt.mp hn
      linarith [he_nonneg n])
  have hlim : liminf f atTop ≤ liminf (g + e) atTop :=
    liminf_le_liminf hcompare
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hf_nonneg))
      (isCoboundedUnder_ge_of_eventually_le atTop
        ((Eventually.of_forall hg_le_one).and he_le |>.mono (by
          intro n hn
          change g n + e n ≤ 2
          linarith)))
  have hadd : liminf (g + e) atTop ≤ limsup e atTop + liminf g atTop := by
    simpa [add_comm] using
      (liminf_add_le (f := atTop) (u := e) (v := g)
        (isBoundedUnder_of_eventually_ge (Eventually.of_forall he_nonneg))
        (isBoundedUnder_of_eventually_le he_le)
        (isBoundedUnder_of_eventually_ge (Eventually.of_forall hg_nonneg))
        (isCoboundedUnder_ge_of_eventually_le atTop
          (Eventually.of_forall hg_le_one)))
  have heSup : limsup e atTop = 0 := he.limsup_eq
  change liminf f atTop ≤ liminf g atTop
  calc
    liminf f atTop ≤ liminf (g + e) atTop := hlim
    _ ≤ limsup e atTop + liminf g atTop := hadd
    _ = liminf g atTop := by rw [heSup, zero_add]


open GenLimit GenLimit.NoiseLossFeedback GenLimit.UnionClosedness

noncomputable def codedLanguage (q : ℕ) (S : Set ℕ) : Set ℤ :=
  negativeIntegers ∪ {z | ∃ n ∈ S, positiveCode (q + 1 + n) = z}

lemma codedLanguage_mem_second (q : ℕ) (S : Set ℕ) :
    codedLanguage q S ∈ finiteOmissionSecondClass q := by
  constructor
  · exact Set.subset_union_left
  · rw [Set.disjoint_left]
    intro z hz hmarker
    rcases hz with hzneg | ⟨n, hn, rfl⟩
    · exact (Int.not_lt_of_ge (omissionMarker_nonnegative hmarker)) hzneg
    · obtain ⟨k, hk, heq⟩ := mem_omissionMarkerFinset_iff.mp hmarker
      have heq' : Int.ofNat k = Int.ofNat (q + 1 + n + 1) := by
        simpa [positiveCode] using heq
      have heqNat := Int.ofNat_inj.mp heq'
      omega

lemma mem_codedLanguage_positive (q n : ℕ) (S : Set ℕ) :
    positiveCode (q + 1 + n) ∈ codedLanguage q S ↔ n ∈ S := by
  constructor
  · intro h
    rcases h with hneg | ⟨m, hm, heq⟩
    · exfalso
      simp [negativeIntegers, positiveCode] at hneg
      omega
    · have : q + 1 + m = q + 1 + n := positiveCode_injective heq
      simpa [Nat.add_left_cancel_iff] using (show m = n by omega) ▸ hm
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

lemma codedLanguage_injective (q : ℕ) : Function.Injective (codedLanguage q) := by
  intro S T hST
  ext n
  rw [← mem_codedLanguage_positive q n S, hST, mem_codedLanguage_positive q n T]

lemma finiteOmissionClass_not_countable (q : ℕ) :
    ¬(finiteOmissionClass q).Countable := by
  intro hcount
  have hrange : (Set.range (codedLanguage q)).Countable := by
    apply hcount.mono
    rintro K ⟨S, rfl⟩
    exact Or.inr (codedLanguage_mem_second q S)
  have himage : ((codedLanguage q) '' (Set.univ : Set (Set ℕ))).Countable := by
    simpa [Set.image_univ] using hrange
  have huniv : (Set.univ : Set (Set ℕ)).Countable :=
    Set.countable_of_injective_of_countable_image
      (codedLanguage_injective q).injOn himage
  exact GenLimit.UnionClosedness.powerSet_not_countable ℕ
    (Set.countable_univ_iff.mp huniv)


open GenLimit GenLimit.NoiseLossFeedback

theorem negative_part (q : ℕ) :
    ∀ gen : Stage3Case019.Generator ℤ,
      ∃ K ∈ finiteOmissionClass q, ∃ input : Stage3Case019.Stream ℤ,
        GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost
            input K (q + 1) ∧
          ¬Stage3Case019.SampleFreshGeneratesAfterInput
            input (Stage3Case019.outputAfterInput gen input) K := by
  intro gen
  have h := finiteNoiseLevel_lower q
  rw [GeneratableInLimitWithNoiseLevel, not_exists] at h
  have hg := h gen
  unfold IsLimitGeneratorWithNoiseLevel at hg
  push_neg at hg
  obtain ⟨K, hK, input, hinput, hfail⟩ := hg
  refine ⟨K, hK, input, hinput, ?_⟩
  intro hsuccess
  obtain ⟨T, hT⟩ := hsuccess
  obtain ⟨t, ht, hbad⟩ := hfail T
  exact hbad (hT t ht)


end Stage3Case019Proof

open Stage3Case019

theorem stage3_countable_half_density : CountableClause := by
  intro q family hinf
  let O := Stage3Case019Proof.oracleOfFamily family hinf
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  let gen : Generator ℕ := Stage3Case019Proof.patientGenerator E
  refine ⟨gen, ?_⟩
  intro i input hinput
  have hcontam := Stage3Case019Proof.finiteNoiseFiniteOmission_of_bounded hinput
  obtain ⟨j, hj, hP⟩ :=
    GenLimit.InfiniteContamination.exists_finiteExpansion_index_for_stream O hcontam
  have hnovelRange := Stage3Case019Proof.novel_patient E hP
  have hdenseRange := Stage3Case019Proof.patient_density E hP
  let out := Stage3Case019.outputAfterInput gen input
  have hout : out = GenLimit.PatientMachine.output E input := by
    funext t
    exact Stage3Case019Proof.output_patientGenerator E input t
  have houtInjective : Function.Injective out := by
    rw [hout]
    exact GenLimit.PatientMachine.output_injective E input
  have hKR : family i ⊆ E.language j := by
    rw [← hP]
    exact hinput.2.1
  have hdiff : (E.language j \ family i).Finite := by
    rw [← hP]
    obtain ⟨F, hF, _⟩ := hinput.2.2
    rw [← hF]
    exact F.finite_toSet
  have hbadTimes : (out ⁻¹' (E.language j \ family i)).Finite :=
    hdiff.preimage houtInjective.injOn
  obtain ⟨N, hN⟩ := hbadTimes.bddAbove
  rcases hnovelRange with ⟨T, hT⟩
  constructor
  · refine ⟨max T (N + 1), ?_⟩
    intro t ht
    have hlate := hT t (le_trans (le_max_left _ _) ht)
    refine ⟨?_, hlate.2.1, hlate.2.2⟩
    by_contra hnotK
    have htBad : t ∈ out ⁻¹' (E.language j \ family i) :=
      ⟨hlate.1, hnotK⟩
    have htN := hN htBad
    have hNt : N + 1 ≤ t := le_trans (le_max_right _ _) ht
    omega
  · have htransfer := Stage3Case019Proof.relativeLowerDensity_finite_transfer
      (A := GenLimit.GeneratorFirst input out ∩ E.language j)
      (K := family i) (R := E.language j) (hinf i) hKR hdiff
      Set.inter_subset_right
    have hnum :
        (GenLimit.GeneratorFirst input out ∩ E.language j) ∩ family i =
          GenLimit.GeneratorFirst input out ∩ family i := by
      ext x
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hxG, _⟩, hxK⟩
        exact ⟨hxG, hxK⟩
      · rintro ⟨hxG, hxK⟩
        exact ⟨⟨hxG, hKR hxK⟩, hxK⟩
    change (1 / 2 : ℝ) ≤ GenLimit.PatientScope.relativeLowerDensity
      (GenLimit.GeneratorFirst input out ∩ family i) (family i)
    rw [← hnum]
    exact hdenseRange.trans htransfer

theorem stage3_uncountable_separation : SeparationClause := by
  intro q
  refine ⟨GenLimit.NoiseLossFeedback.finiteOmissionClass q,
    Stage3Case019Proof.finiteOmissionClass_not_countable q,
    GenLimit.NoiseLossFeedback.finiteOmissionClass_uus q, ?_,
    Stage3Case019Proof.negative_part q⟩
  sorry

theorem stage3_result : MainClaim := by
  exact ⟨stage3_countable_half_density, stage3_uncountable_separation⟩
