import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable def oracleOfFamily
    (family : ℕ → Language) (hinfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hinfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

lemma sample_eq_of_eqOn_lt {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.sample a t = GenLimit.sample b t := by
  unfold GenLimit.sample
  apply Finset.image_congr
  intro s hs
  exact h s (Finset.mem_range.mp hs)

lemma consistent_eq_of_sample_eq (C : GenLimit.LanguageFamily)
    {a b : Stream} {t : ℕ}
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.Consistent C a t = GenLimit.Consistent C b t := by
  funext i
  apply propext
  simp only [GenLimit.Consistent, h]

lemma recursiveCritical_iff_of_consistent_eq
    (C : GenLimit.LanguageFamily) {a b : Stream} {t i : ℕ}
    (h : GenLimit.Consistent C a t = GenLimit.Consistent C b t) :
    GenLimit.RecursiveCritical C a t i ↔
      GenLimit.RecursiveCritical C b t i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simp [GenLimit.RecursiveCritical, h]
      | succ i =>
          rw [GenLimit.RecursiveCritical, GenLimit.RecursiveCritical]
          constructor
          · rintro ⟨hcon, hsub⟩
            refine ⟨?_, ?_⟩
            · simpa [h] using hcon
            · intro j hj hjcrit
              apply hsub j hj
              exact (ih j (by omega)).2 hjcrit
          · rintro ⟨hcon, hsub⟩
            refine ⟨?_, ?_⟩
            · simpa [h] using hcon
            · intro j hj hjcrit
              apply hsub j hj
              exact (ih j (by omega)).1 hjcrit

lemma recursiveCritical_eq_of_consistent_eq
    (C : GenLimit.LanguageFamily) {a b : Stream} {t : ℕ}
    (h : GenLimit.Consistent C a t = GenLimit.Consistent C b t) :
    GenLimit.RecursiveCritical C a t = GenLimit.RecursiveCritical C b t := by
  funext i
  exact propext (recursiveCritical_iff_of_consistent_eq C h)

lemma decide_eq_of_prefix
    (C : GenLimit.LanguageFamily) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.decide C a t old =
      GenLimit.PatientMachine.decide C b t old := by
  have hs_t : GenLimit.sample a t = GenLimit.sample b t :=
    sample_eq_of_eqOn_lt (fun s hs => h s (Nat.lt.step hs))
  have hs_succ : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
    sample_eq_of_eqOn_lt h
  have hc_t := consistent_eq_of_sample_eq C hs_t
  have hc_succ := consistent_eq_of_sample_eq C hs_succ
  have hr_t := recursiveCritical_eq_of_consistent_eq C hc_t
  have hr_succ := recursiveCritical_eq_of_consistent_eq C hc_succ
  have hci : ∀ scope,
      GenLimit.PatientMachine.criticalIndices C a (t + 1) scope =
        GenLimit.PatientMachine.criticalIndices C b (t + 1) scope := by
    intro scope
    unfold GenLimit.PatientMachine.criticalIndices
    rw [hr_succ]
  have hsi : ∀ scope,
      GenLimit.PatientMachine.survivingCriticalIndices C a t scope =
        GenLimit.PatientMachine.survivingCriticalIndices C b t scope := by
    intro scope
    unfold GenLimit.PatientMachine.survivingCriticalIndices
    rw [hr_t, hr_succ]
  have hconi : ∀ scope,
      GenLimit.PatientMachine.consistentIndices C a (t + 1) scope =
        GenLimit.PatientMachine.consistentIndices C b (t + 1) scope := by
    intro scope
    unfold GenLimit.PatientMachine.consistentIndices
    rw [hc_succ]
  have hhighest : ∀ scope fallback,
      GenLimit.PatientMachine.highestCritical C a (t + 1) scope fallback =
        GenLimit.PatientMachine.highestCritical C b (t + 1) scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.highestCritical
    rw [hci]
  have hsurvivor : ∀ scope fallback,
      GenLimit.PatientMachine.highestSurvivor C a t scope fallback =
        GenLimit.PatientMachine.highestSurvivor C b t scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.highestSurvivor
    rw [hsi]
  have hlowestScope : ∀ scope fallback,
      GenLimit.PatientMachine.lowestConsistentInScope C a (t + 1) scope fallback =
        GenLimit.PatientMachine.lowestConsistentInScope C b (t + 1) scope fallback := by
    intro scope fallback
    unfold GenLimit.PatientMachine.lowestConsistentInScope
    rw [hconi]
  have hlowest : ∀ fallback,
      GenLimit.PatientMachine.lowestConsistent C a (t + 1) fallback =
        GenLimit.PatientMachine.lowestConsistent C b (t + 1) fallback := by
    intro fallback
    unfold GenLimit.PatientMachine.lowestConsistent
    rw [hc_succ]
  have hstable :
      GenLimit.PatientMachine.stableDecision C a t old =
        GenLimit.PatientMachine.stableDecision C b t old := by
    unfold GenLimit.PatientMachine.stableDecision
    split <;> simp only
    rw [hhighest]
  have hbacktrack :
      GenLimit.PatientMachine.backtrackDecision C a t old =
        GenLimit.PatientMachine.backtrackDecision C b t old := by
    unfold GenLimit.PatientMachine.backtrackDecision
    rw [hconi]
    by_cases hcon :
        (GenLimit.PatientMachine.consistentIndices C b (t + 1) old.scope).Nonempty
    · simp only [hcon, ↓reduceDIte]
      rw [hsi]
      by_cases hsurv :
          (GenLimit.PatientMachine.survivingCriticalIndices C b t old.scope).Nonempty
      · simp only [hsurv, if_pos]
        rw [hsurvivor]
      · simp only [hsurv]
        rw [hlowestScope]
        simp
    · simp only [hcon, ↓reduceDIte]
      rw [hlowest, hc_succ]
  unfold GenLimit.PatientMachine.decide
  rw [hc_succ, hstable, hbacktrack]

lemma leastAvailable_eq_of_sample_eq
    (O : GenLimit.OracleFamily) {a b : Stream} (t : ℕ)
    (used : Finset ℕ) (focus : ℕ)
    (h : GenLimit.sample a t = GenLimit.sample b t) :
    GenLimit.PatientMachine.leastAvailable O.language O.infinite' a t used focus =
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' b t used focus := by
  apply Nat.le_antisymm
  · apply GenLimit.PatientMachine.leastAvailable_minimal
    have ha := GenLimit.PatientMachine.leastAvailable_spec
      O.language O.infinite' b t used focus
    simpa only [GenLimit.PatientMachine.Available, h] using ha
  · apply GenLimit.PatientMachine.leastAvailable_minimal
    have ha := GenLimit.PatientMachine.leastAvailable_spec
      O.language O.infinite' a t used focus
    simpa only [GenLimit.PatientMachine.Available, h] using ha

lemma processRound_eq_of_prefix
    (O : GenLimit.OracleFamily) {a b : Stream} (t : ℕ)
    (old : GenLimit.PatientMachine.State)
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.processRound O a t old =
      GenLimit.PatientMachine.processRound O b t old := by
  have hs : GenLimit.sample a (t + 1) = GenLimit.sample b (t + 1) :=
    sample_eq_of_eqOn_lt h
  have hd := decide_eq_of_prefix O.language t old h
  have hleast :
      GenLimit.PatientMachine.leastAvailable O.language O.infinite' a (t + 1)
          old.used (GenLimit.PatientMachine.decide O.language b t old).focus =
        GenLimit.PatientMachine.leastAvailable O.language O.infinite' b (t + 1)
          old.used (GenLimit.PatientMachine.decide O.language b t old).focus :=
    leastAvailable_eq_of_sample_eq O (t + 1) old.used _ hs
  unfold GenLimit.PatientMachine.processRound
  simp only [hd, hleast]

lemma run_eq_of_prefix
    (O : GenLimit.OracleFamily) {a b : Stream} {t : ℕ}
    (h : ∀ s, s < t → a s = b s) :
    GenLimit.PatientMachine.run O a t =
      GenLimit.PatientMachine.run O b t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [GenLimit.PatientMachine.run_succ, GenLimit.PatientMachine.run_succ]
      rw [ih (fun s hs => h s (Nat.lt.step hs))]
      exact processRound_eq_of_prefix O t _ h

lemma patient_output_eq_of_prefix
    (O : GenLimit.OracleFamily) {a b : Stream} (t : ℕ)
    (h : ∀ s, s < t + 1 → a s = b s) :
    GenLimit.PatientMachine.output O a t =
      GenLimit.PatientMachine.output O b t := by
  unfold GenLimit.PatientMachine.output
  rw [run_eq_of_prefix O h]

noncomputable def extendHistory {t : ℕ} (history : Fin (t + 1) → ℕ) : Stream :=
  fun s => if hs : s < t + 1 then history ⟨s, hs⟩ else 0

noncomputable def patientOnlineGenerator (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t history _ =>
    GenLimit.PatientMachine.output O (extendHistory history) t

lemma patientOnlineGenerator_follows
    (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnlineGenerator O) input
      (GenLimit.PatientMachine.output O input) := by
  intro t
  apply patient_output_eq_of_prefix O t
  intro s hs
  simp [extendHistory, hs]



lemma patient_prefixCount_le_add_ncard_diff
    {A B : Language} (hfinite : (A \ B).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := GenLimit.PatientScope.prefixFinset A n
  let bPrefix := GenLimit.PatientScope.prefixFinset B n
  have hsub : aPrefix ⊆ bPrefix ∪ hfinite.toFinset := by
    intro x hx
    have hxA := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxA.1, hxB⟩)
    · exact Finset.mem_union_right _
        (Set.Finite.mem_toFinset hfinite |>.2 ⟨hxA.2, hxB⟩)
  have hcard := Finset.card_le_card hsub
  exact (by
    simpa [aPrefix, bPrefix, GenLimit.PatientScope.prefixCount] using
      hcard.trans (Finset.card_union_le bPrefix hfinite.toFinset))

lemma relativeLowerDensity_mono_finite_extension
    {Q K R : Language} (hKR : K ⊆ R) (hfinite : (R \ K).Finite)
    (hK : K.Infinite) :
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
  let c : ℕ := hnumFinite.toFinset.card
  let error : ℕ → ℝ := fun n =>
    (c : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcastK : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcastK
  have hKpos : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hcountK.eventually (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hKpos] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdenNat :
        GenLimit.PatientScope.prefixCount K n ≤
          GenLimit.PatientScope.prefixCount R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hdenR :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount R n := by
      exact_mod_cast hdenNat
    have hnumNat :
        GenLimit.PatientScope.prefixCount (Q ∩ R) n ≤
          GenLimit.PatientScope.prefixCount (Q ∩ K) n + c := by
      simpa [c] using patient_prefixCount_le_add_ncard_diff hnumFinite n
    have hnumR :
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (Q ∩ K) n + c := by
      exact_mod_cast hnumNat
    have hdenRpos :
        (0 : ℝ) < GenLimit.PatientScope.prefixCount R n :=
      lt_of_lt_of_le hnR hdenR
    calc
      source n ≤
          (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hnR
        · exact hdenR
      _ ≤
          ((GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) + c) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        exact div_le_div_of_nonneg_right hnumR hnR.le
      _ = target n + error n := by
        rw [add_div]
  have htargetNonneg : ∀ n, 0 ≤ target n := by
    intro n
    positivity
  have htargetLeOne : ∀ n, target n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [target, hn]
    · have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      change
        (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one hnR]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  have hsourceNonneg : ∀ n, 0 ≤ source n := by
    intro n
    positivity
  have hsourceLeOne : ∀ n, source n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount R n = 0
    · simp [source, hn]
    · have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      change
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
          (GenLimit.PatientScope.prefixCount R n : ℝ) ≤ 1
      rw [div_le_one hnR]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htargetLeOne)
    (isBoundedUnder_of ⟨0, htargetNonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrSource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrSource
      (isBoundedUnder_of ⟨0, hsourceNonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr herr hp
  linarith

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hinfinite
  let O := oracleOfFamily family hinfinite
  refine ⟨patientOnlineGenerator O, ?_⟩
  intro i input hpresents
  let output := GenLimit.PatientMachine.output O input
  have hrun :=
    GenLimit.PatientMachine.patientScope_generation_and_lowerDensity
      O input (z := i) hpresents
  refine ⟨output, patientOnlineGenerator_follows O input, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hrun.1
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hrepeat⟩ := hT t ht
    refine ⟨hmem, ?_, hrepeat⟩
    intro hsample
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
    exact hfresh s (by omega) heq
  · simpa [GenLimit.PatientMachine.patientLowerDensity, O, output] using hrun.2


theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hinfinite
  let O := oracleOfFamily family hinfinite
  let E := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hpositive E.language E.infinite'
  refine ⟨gen, ?_⟩
  intro i input hpres
  have hnoise : (Set.range input \ family i).Finite := by
    rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
    exact hpres.2.image input
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode :=
    (i, Finset.equivBitIndices.symm hnoise.toFinset,
      Finset.equivBitIndices.symm (∅ : Finset ℕ))
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  have hlang : E.language j = Set.range input := by
    change GenLimit.InfiniteContamination.finiteExpansionLanguage O j =
      Set.range input
    rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
    simp only [j, data,
      GenLimit.InfiniteContamination.finiteExpansionCode_encode,
      Equiv.apply_symm_apply]
    have hadd : (↑hnoise.toFinset : Set ℕ) = Set.range input \ family i :=
      Set.Finite.coe_toFinset hnoise
    rw [hadd]
    ext x
    simp only [GenLimit.InfiniteContamination.finiteExpansion,
      Set.mem_diff, Set.mem_union, Set.mem_range]
    change
      ((x ∈ family i ∨ (∃ a, input a = x) ∧ x ∉ family i) ∧
        x ∉ (↑(∅ : Finset ℕ) : Set ℕ)) ↔ ∃ a, input a = x
    simp only [Finset.coe_empty, Set.mem_empty_iff_false, not_false_eq_true,
      and_true]
    constructor
    · rintro (hx | ⟨hx, -⟩)
      · exact hpres.1 hx
      · exact hx
    · intro hx
      by_cases hxK : x ∈ family i
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  have hpresents : GenLimit.Presents input (E.language j) := by
    exact hlang.symm
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · obtain ⟨Tvalid, hTvalid⟩ := hnovel
    obtain ⟨Tseen, hTseen⟩ :=
      GenLimit.Generic.finset_eventually_subset_sample
        (stream := input) (L := Set.range input)
        (GenLimit.InfiniteContamination.stream_presents_range input)
        hnoise.toFinset (by
          intro x hx
          exact (Set.Finite.mem_toFinset hnoise |>.1 hx).1)
    refine ⟨max Tvalid Tseen, ?_⟩
    intro t ht
    have htValid : Tvalid ≤ t := (Nat.le_max_left _ _).trans ht
    have htSeen : Tseen ≤ t := (Nat.le_max_right _ _).trans ht
    obtain ⟨hmem, hfresh, hrepeat⟩ := hTvalid t htValid
    refine ⟨?_, hfresh, hrepeat⟩
    rw [hlang] at hmem
    by_contra hout
    have hbad : output t ∈ hnoise.toFinset :=
      (Set.Finite.mem_toFinset hnoise).2 ⟨hmem, hout⟩
    have hseenGeneric : output t ∈ GenLimit.Generic.sample input Tseen :=
      hTseen hbad
    have hseen : output t ∈ GenLimit.sample input Tseen := by
      simpa [GenLimit.Generic.sample, GenLimit.sample] using hseenGeneric
    exact hfresh (GenLimit.sample_mono (by omega) hseen)
  · have htransfer := relativeLowerDensity_mono_finite_extension
      (Q := GenLimit.GeneratorFirst input output)
      (K := family i) (R := Set.range input)
      hpres.1 hnoise (hinfinite i)
    rw [hlang] at hdensity
    exact hdensity.trans htransfer

end Stage3Case025
