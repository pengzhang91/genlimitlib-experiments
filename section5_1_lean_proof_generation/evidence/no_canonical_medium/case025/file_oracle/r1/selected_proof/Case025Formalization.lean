import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Logic.Encodable.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter

namespace Stage3Case025

open GenLimit

noncomputable section

private theorem sample_eq_of_prefix {s₁ s₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → s₁ n = s₂ n) :
    sample s₁ t = sample s₂ t := by
  classical
  ext x
  simp only [mem_sample_iff]
  constructor <;> rintro ⟨n, hn, rfl⟩
  · exact ⟨n, hn, (h n hn).symm⟩
  · exact ⟨n, hn, h n hn⟩

private theorem consistent_congr {C : LanguageFamily} {s₁ s₂ : ℕ → ℕ} {t i : ℕ}
    (h : ∀ n, n < t → s₁ n = s₂ n) :
    Consistent C s₁ t i ↔ Consistent C s₂ t i := by
  unfold Consistent
  rw [sample_eq_of_prefix h]

private theorem recursiveCritical_congr {C : LanguageFamily} {s₁ s₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t → s₁ n = s₂ n) :
    ∀ i, RecursiveCritical C s₁ t i ↔ RecursiveCritical C s₂ t i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero => simpa [RecursiveCritical] using consistent_congr (C := C) (i := 0) h
      | succ i =>
          simp only [RecursiveCritical]
          rw [consistent_congr (C := C) (i := i + 1) h]
          constructor <;> rintro ⟨hc, H⟩
          · exact ⟨hc, fun j hj hjc => H j hj ((ih j (by omega)).mpr hjc)⟩
          · exact ⟨hc, fun j hj hjc => H j hj ((ih j (by omega)).mp hjc)⟩

private theorem decide_congr_prefix (O : OracleFamily) {s₁ s₂ : ℕ → ℕ}
    (t : ℕ) (old : PatientMachine.State)
    (h : ∀ n, n < t + 1 → s₁ n = s₂ n) :
    PatientMachine.decide O.language s₁ t old =
      PatientMachine.decide O.language s₂ t old := by
  classical
  have hpre : ∀ n, n < t → s₁ n = s₂ n :=
    fun n hn => h n (Nat.lt_succ_of_lt hn)
  have hcon : ∀ i, Consistent O.language s₁ (t + 1) i ↔
      Consistent O.language s₂ (t + 1) i := fun i => consistent_congr h
  have hcrit : ∀ i, RecursiveCritical O.language s₁ (t + 1) i ↔
      RecursiveCritical O.language s₂ (t + 1) i := recursiveCritical_congr h
  have hcritPre : ∀ i, RecursiveCritical O.language s₁ t i ↔
      RecursiveCritical O.language s₂ t i := recursiveCritical_congr hpre
  have hcset : PatientMachine.consistentIndices O.language s₁ (t + 1) old.scope =
      PatientMachine.consistentIndices O.language s₂ (t + 1) old.scope := by
    ext i
    simp [hcon]
  have hcrset : ∀ scope,
      PatientMachine.criticalIndices O.language s₁ (t + 1) scope =
        PatientMachine.criticalIndices O.language s₂ (t + 1) scope := by
    intro scope
    ext i
    simp [hcrit]
  have hsurv : PatientMachine.survivingCriticalIndices O.language s₁ t old.scope =
      PatientMachine.survivingCriticalIndices O.language s₂ t old.scope := by
    ext i
    simp [hcritPre, hcrit]
  have hglobal : (∃ i, Consistent O.language s₁ (t + 1) i) ↔
      ∃ i, Consistent O.language s₂ (t + 1) i := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hcon i).mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hcon i).mpr hi⟩
  by_cases hc₁ : Consistent O.language s₁ (t + 1) old.focus
  · have hc₂ := (hcon old.focus).mp hc₁
    simp only [PatientMachine.decide, if_pos hc₁, if_pos hc₂]
    unfold PatientMachine.stableDecision PatientMachine.highestCritical
    simp [hcrset]
  · have hc₂ : ¬ Consistent O.language s₂ (t + 1) old.focus :=
      fun hs => hc₁ ((hcon old.focus).mpr hs)
    have hlow :
        PatientMachine.lowestConsistent O.language s₁ (t + 1) old.focus =
          PatientMachine.lowestConsistent O.language s₂ (t + 1) old.focus := by
      unfold PatientMachine.lowestConsistent
      by_cases hex₁ : ∃ i, Consistent O.language s₁ (t + 1) i
      · have hex₂ := hglobal.mp hex₁
        rw [dif_pos hex₁, dif_pos hex₂]
        apply Nat.find_congr (Nat.find_spec hex₁)
        intro n hn
        exact hcon n
      · have hex₂ : ¬ ∃ i, Consistent O.language s₂ (t + 1) i :=
          fun he => hex₁ (hglobal.mpr he)
        rw [dif_neg hex₁, dif_neg hex₂]
    have hhigh :
        PatientMachine.highestSurvivor O.language s₁ t old.scope old.focus =
          PatientMachine.highestSurvivor O.language s₂ t old.scope old.focus := by
      unfold PatientMachine.highestSurvivor
      rw [hsurv]
    have hlowScope :
        PatientMachine.lowestConsistentInScope O.language s₁ (t + 1) old.scope old.focus =
          PatientMachine.lowestConsistentInScope O.language s₂ (t + 1) old.scope old.focus := by
      unfold PatientMachine.lowestConsistentInScope
      rw [hcset]
    simp only [PatientMachine.decide, if_neg hc₁, if_neg hc₂]
    unfold PatientMachine.backtrackDecision
    rw [hcset, hsurv, hlow, hhigh, hlowScope, propext hglobal]

private theorem leastAvailable_congr_prefix (O : OracleFamily) {s₁ s₂ : ℕ → ℕ}
    (t : ℕ) (used : Finset ℕ) (focus : ℕ)
    (h : ∀ n, n < t → s₁ n = s₂ n) :
    PatientMachine.leastAvailable O.language O.infinite' s₁ t used focus =
      PatientMachine.leastAvailable O.language O.infinite' s₂ t used focus := by
  classical
  have hs : sample s₁ t = sample s₂ t := sample_eq_of_prefix h
  unfold PatientMachine.leastAvailable
  apply Nat.find_congr
    (Nat.find_spec (PatientMachine.available_exists O.language O.infinite' s₁ t used focus))
  intro n hn
  unfold PatientMachine.Available
  rw [hs]

private theorem run_congr_prefix (O : OracleFamily) {s₁ s₂ : ℕ → ℕ} :
    ∀ t, (∀ n, n < t → s₁ n = s₂ n) →
      PatientMachine.run O s₁ t = PatientMachine.run O s₂ t := by
  intro t
  induction t with
  | zero => intro; rfl
  | succ t ih =>
      intro h
      have hpre : ∀ n, n < t → s₁ n = s₂ n :=
        fun n hn => h n (Nat.lt_succ_of_lt hn)
      have hr := ih hpre
      rw [PatientMachine.run_succ, PatientMachine.run_succ, hr]
      have hd := decide_congr_prefix O t (PatientMachine.run O s₂ t) h
      let d := PatientMachine.decide O.language s₂ t (PatientMachine.run O s₂ t)
      have hx := leastAvailable_congr_prefix O (t + 1)
        (PatientMachine.run O s₂ t).used d.focus h
      unfold PatientMachine.processRound
      simp only [hd]
      simpa only [d] using congrArg (fun x =>
        { scope := d.scope
          tau := d.tau
          age := if d.focus = (PatientMachine.run O s₂ t).focus then
            (PatientMachine.run O s₂ t).age + 1 else 1
          focus := d.focus
          used := insert x (PatientMachine.run O s₂ t).used
          lastOutput := some x
          move := d.move : PatientMachine.State }) hx

private theorem output_congr_prefix (O : OracleFamily) {s₁ s₂ : ℕ → ℕ} {t : ℕ}
    (h : ∀ n, n < t + 1 → s₁ n = s₂ n) :
    PatientMachine.output O s₁ t = PatientMachine.output O s₂ t := by
  unfold PatientMachine.output
  rw [run_congr_prefix O (t + 1) h]

private def completion {t : ℕ} (xs : Fin (t + 1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

private def onlineOfOracle (O : OracleFamily) : OnlineGenerator :=
  fun t xs _ => PatientMachine.output O (completion xs) t

private theorem follows_onlineOfOracle (O : OracleFamily) (input : Stream) :
    Follows (onlineOfOracle O) input (PatientMachine.output O input) := by
  intro t
  apply output_congr_prefix O
  intro n hn
  simp [completion, hn]

private noncomputable def oracleOfFamily (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) : OracleFamily := by
  classical
  exact {
  language := family
  infinite' := hinf
  query i x := decide (x ∈ family i)
  query_spec i x := by simp }

private theorem positive_engine : PositivePresentationHalfDensity := by
  intro family hinf
  let O := oracleOfFamily family hinf
  refine ⟨onlineOfOracle O, ?_⟩
  intro i input hP
  refine ⟨PatientMachine.output O input, follows_onlineOfOracle O input, ?_, ?_⟩
  · obtain ⟨⟨T, hT⟩, -⟩ := PatientMachine.patientScope_generation_and_lowerDensity O input hP
    exact ⟨T, fun t ht => by
      obtain ⟨hmem, hin, hout⟩ := hT t ht
      exact ⟨hmem, by
        intro hx
        rw [mem_sample_iff] at hx
        obtain ⟨s, hs, heq⟩ := hx
        exact hin s (Nat.le_of_lt_succ hs) heq, hout⟩⟩
  · exact PatientMachine.patientScope_lowerDensity_half O input hP

private def decodedFinset (n : ℕ) : Finset ℕ :=
  ((Encodable.decode n : Option (List ℕ)).getD []).toFinset

private def expandedFamily (family : ℕ → Language) : ℕ → Language :=
  fun n => family n.unpair.1 ∪ (decodedFinset n.unpair.2 : Set ℕ)

private theorem expanded_infinite (family : ℕ → Language)
    (hinf : ∀ i, (family i).Infinite) :
    ∀ n, (expandedFamily family n).Infinite := by
  intro n
  exact (hinf n.unpair.1).mono Set.subset_union_left

private theorem range_diff_finite {input : Stream} {K : Language}
    (hbad : GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)) :
    (Set.range input \ K).Finite := by
  rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
  exact hbad.image input

private theorem presents_expansion {input : Stream} {K : Language}
    (hcover : K ⊆ Set.range input) :
    GenLimit.Presents input (K ∪ (Set.range input \ K)) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩
  · exact Set.union_subset hcover Set.diff_subset

private theorem eventual_avoids_finite {input output : Stream} {L F : Language}
    (hgen : NovelGeneratesInLimit input output L) (hF : F.Finite) :
    ∃ T, ∀ t, T ≤ t → output t ∉ F := by
  obtain ⟨T, hT⟩ := hgen
  let S : Set ℕ := {t | T ≤ t ∧ output t ∈ F}
  have hSinj : Set.InjOn output S := by
    intro a ha b hb hab
    by_cases hab' : a = b
    · exact hab'
    rcases le_total a b with hab_le | hba_le
    · have halt : a < b := lt_of_le_of_ne hab_le hab'
      exact False.elim ((hT b hb.1).2.2 a halt hab)
    · have hblt : b < a := lt_of_le_of_ne hba_le (Ne.symm hab')
      exact False.elim ((hT a ha.1).2.2 b hblt hab.symm)
  have hSfinite : S.Finite :=
    Set.Finite.of_injOn (fun t ht => ht.2) hSinj hF
  obtain ⟨B, hB⟩ := hSfinite.bddAbove
  refine ⟨max T (B + 1), ?_⟩
  intro t ht htF
  have htS : t ∈ S := ⟨le_trans (le_max_left _ _) ht, htF⟩
  have htle : t ≤ B := hB htS
  omega

private theorem prefixCount_le_add_finite
    {A B F : Language} (hsub : A ⊆ B ∪ F) (hF : F.Finite) (n : ℕ) :
    PatientScope.prefixCount A n ≤
      PatientScope.prefixCount B n + hF.toFinset.card := by
  classical
  unfold PatientScope.prefixCount
  have hprefix : PatientScope.prefixFinset A n ⊆
      PatientScope.prefixFinset B n ∪ hF.toFinset := by
    intro x hx
    have hx' := PatientScope.mem_prefixFinset.mp hx
    rcases hsub hx'.2 with hxB | hxF
    · exact Finset.mem_union_left _ (PatientScope.mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset hF).2 hxF)
  exact (Finset.card_le_card hprefix).trans
    (Finset.card_union_le (PatientScope.prefixFinset B n) hF.toFinset)

private theorem relativeLowerDensity_transfer
    {A B K L : Language} (hK : K.Infinite)
    (hA : A ⊆ L) (hB : B ⊆ K) (hF : (A \ B).Finite)
    (hKL : K ⊆ L) :
    PatientScope.relativeLowerDensity A L ≤
      PatientScope.relativeLowerDensity B K := by
  let sourceRatio : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount A n : ℝ) / (PatientScope.prefixCount L n : ℝ)
  let targetRatio : ℕ → ℝ := fun n =>
    (PatientScope.prefixCount B n : ℝ) / (PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hF.toFinset.card : ℝ) / (PatientScope.prefixCount K n : ℝ)
  have hcount := PatientScope.tendsto_prefixCount_atTop hK
  have hcountR : Tendsto (fun n => (PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcountR
  have hprefix : ∀ᶠ n : ℕ in atTop,
      sourceRatio n ≤ targetRatio n + error n := by
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < PatientScope.prefixCount K n :=
      hcount.eventually (eventually_gt_atTop 0)
    filter_upwards [hpos] with n hn
    have hnR : (0 : ℝ) < PatientScope.prefixCount K n := by exact_mod_cast hn
    have hden : PatientScope.prefixCount K n ≤ PatientScope.prefixCount L n :=
      PatientScope.prefixCount_mono hKL n
    have hnum : PatientScope.prefixCount A n ≤
        PatientScope.prefixCount B n + hF.toFinset.card := by
      apply prefixCount_le_add_finite (F := A \ B) (hF := hF)
      intro x hx
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · exact Or.inr ⟨hx, hxB⟩
    have hdenR : (0 : ℝ) < PatientScope.prefixCount L n :=
      lt_of_lt_of_le hnR (by exact_mod_cast hden)
    have hnumR : (PatientScope.prefixCount A n : ℝ) ≤
        PatientScope.prefixCount B n + hF.toFinset.card := by exact_mod_cast hnum
    calc
      sourceRatio n ≤
          (PatientScope.prefixCount A n : ℝ) /
            (PatientScope.prefixCount K n : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) hnR (by exact_mod_cast hden)
      _ ≤ ((PatientScope.prefixCount B n : ℝ) + hF.toFinset.card) /
            (PatientScope.prefixCount K n : ℝ) :=
        div_le_div_of_nonneg_right hnumR hnR.le
      _ = targetRatio n + error n := by rw [add_div]
  have hsource_nonneg : ∀ n, 0 ≤ sourceRatio n := fun n => by positivity
  have htarget_nonneg : ∀ n, 0 ≤ targetRatio n := fun n => by positivity
  have htarget_le_one : ∀ n, targetRatio n ≤ 1 := by
    intro n
    by_cases hn : PatientScope.prefixCount K n = 0
    · simp [targetRatio, hn]
    · have hnR : (0 : ℝ) < PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      dsimp [targetRatio]
      rw [div_le_one hnR]
      exact_mod_cast PatientScope.prefixCount_mono hB n
  unfold PatientScope.relativeLowerDensity
  change liminf sourceRatio atTop ≤ liminf targetRatio atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop htarget_le_one)
    (isBoundedUnder_of ⟨0, htarget_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < sourceRatio n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hnr hne hle
  linarith

private theorem novel_union_finite {input output : Stream} {K F : Language}
    (hgen : NovelGeneratesInLimit input output (K ∪ F)) (hF : F.Finite) :
    NovelGeneratesInLimit input output K := by
  obtain ⟨U, hU⟩ := eventual_avoids_finite hgen hF
  obtain ⟨T, hT⟩ := hgen
  refine ⟨max T U, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t (le_trans (le_max_left _ _) ht)
  exact ⟨hmem.resolve_right (hU t (le_trans (le_max_right _ _) ht)), hfresh, hnovel⟩

theorem main_claim_proof : MainClaim := by
  intro family hinf
  obtain ⟨gen, hgen⟩ := positive_engine
    (expandedFamily family) (expanded_infinite family hinf)
  refine ⟨gen, ?_⟩
  intro i input hpres
  let K : Language := family i
  let F : Language := Set.range input \ K
  have hF : F.Finite := by
    exact range_diff_finite hpres.2
  let code : ℕ := Encodable.encode hF.toFinset.toList
  let j : ℕ := Nat.pair i code
  have hexpand : expandedFamily family j = K ∪ F := by
    simp [expandedFamily, j, code, decodedFinset, K, F]
  have hpresents : Presents input (expandedFamily family j) := by
    rw [hexpand]
    exact presents_expansion hpres.1
  obtain ⟨output, hfollows, hnovel, hdensity⟩ := hgen j input hpresents
  refine ⟨output, hfollows, ?_, ?_⟩
  · rw [hexpand] at hnovel
    exact novel_union_finite hnovel hF
  · have htransfer :
        PatientScope.relativeLowerDensity
            (GeneratorFirst input output ∩ (K ∪ F)) (K ∪ F) ≤
          PatientScope.relativeLowerDensity
            (GeneratorFirst input output ∩ K) K := by
      apply relativeLowerDensity_transfer (hK := hinf i)
        (hF := ?_) (hKL := Set.subset_union_left)
      · exact Set.inter_subset_right
      · exact Set.inter_subset_right
      · apply hF.subset
        intro x hx
        rcases hx.1.2 with hxK | hxF
        · exact False.elim (hx.2 ⟨hx.1.1, hxK⟩)
        · exact hxF
    rw [hexpand] at hdensity
    exact hdensity.trans htransfer

end

end Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025.main_claim_proof
