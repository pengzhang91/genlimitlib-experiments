import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable def oracleOf
    (family : ℕ → Language) (hInfinite : ∀ i, (family i).Infinite) :
    GenLimit.OracleFamily where
  language := family
  infinite' := hInfinite
  query i x := by
    classical
    exact if x ∈ family i then true else false
  query_spec i x := by
    classical
    simp

def extendCurrent {t : ℕ} (xs : Fin (t + 1) → ℕ) : Stream :=
  fun n => if h : n < t + 1 then xs ⟨n, h⟩ else 0

theorem extendCurrent_eq {t : ℕ} (xs : Fin (t + 1) → ℕ) (n : ℕ)
    (hn : n < t + 1) :
    extendCurrent xs n = xs ⟨n, hn⟩ := by
  simp [extendCurrent, hn]

private theorem patient_run_congr
    (O : GenLimit.OracleFamily) (stream₁ stream₂ : Stream) :
    ∀ t, (∀ n, n < t → stream₁ n = stream₂ n) →
      GenLimit.PatientMachine.run O stream₁ t =
        GenLimit.PatientMachine.run O stream₂ t := by
  classical
  intro t
  induction t with
  | zero =>
      intro _
      rfl
  | succ t ih =>
      intro hprefix
      have hrun := ih (fun n hn => hprefix n (Nat.lt_succ_of_lt hn))
      have hsample_t : GenLimit.sample stream₁ t = GenLimit.sample stream₂ t := by
        ext x
        simp only [GenLimit.mem_sample_iff]
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n, hn, (hprefix n (Nat.lt_succ_of_lt hn)).symm⟩
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n, hn, hprefix n (Nat.lt_succ_of_lt hn)⟩
      have hsample_succ :
          GenLimit.sample stream₁ (t + 1) =
            GenLimit.sample stream₂ (t + 1) := by
        ext x
        simp only [GenLimit.mem_sample_iff]
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n, hn, (hprefix n hn).symm⟩
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n, hn, hprefix n hn⟩
      have hconsistent_t (i : ℕ) :
          GenLimit.Consistent O.language stream₁ t i ↔
            GenLimit.Consistent O.language stream₂ t i := by
        simp only [GenLimit.Consistent, hsample_t]
      have hconsistent_succ (i : ℕ) :
          GenLimit.Consistent O.language stream₁ (t + 1) i ↔
            GenLimit.Consistent O.language stream₂ (t + 1) i := by
        simp only [GenLimit.Consistent, hsample_succ]
      have hcritical_t (i : ℕ) :
          GenLimit.RecursiveCritical O.language stream₁ t i ↔
            GenLimit.RecursiveCritical O.language stream₂ t i := by
        induction i using Nat.strong_induction_on with
        | h i ih =>
            cases i with
            | zero => simpa [GenLimit.RecursiveCritical] using hconsistent_t 0
            | succ i =>
                simp only [GenLimit.RecursiveCritical, hconsistent_t]
                constructor
                · rintro ⟨hcon, hrest⟩
                  refine ⟨hcon, ?_⟩
                  intro j hj hjcrit
                  exact hrest j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
                · rintro ⟨hcon, hrest⟩
                  refine ⟨hcon, ?_⟩
                  intro j hj hjcrit
                  exact hrest j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)
      have hcritical_succ (i : ℕ) :
          GenLimit.RecursiveCritical O.language stream₁ (t + 1) i ↔
            GenLimit.RecursiveCritical O.language stream₂ (t + 1) i := by
        induction i using Nat.strong_induction_on with
        | h i ih =>
            cases i with
            | zero => simpa [GenLimit.RecursiveCritical] using hconsistent_succ 0
            | succ i =>
                simp only [GenLimit.RecursiveCritical, hconsistent_succ]
                constructor
                · rintro ⟨hcon, hrest⟩
                  refine ⟨hcon, ?_⟩
                  intro j hj hjcrit
                  exact hrest j hj ((ih j (Nat.lt_succ_of_le hj)).mpr hjcrit)
                · rintro ⟨hcon, hrest⟩
                  refine ⟨hcon, ?_⟩
                  intro j hj hjcrit
                  exact hrest j hj ((ih j (Nat.lt_succ_of_le hj)).mp hjcrit)
      have hconsistent_t_fun :
          GenLimit.Consistent O.language stream₁ t =
            GenLimit.Consistent O.language stream₂ t := by
        funext i
        exact propext (hconsistent_t i)
      have hconsistent_succ_fun :
          GenLimit.Consistent O.language stream₁ (t + 1) =
            GenLimit.Consistent O.language stream₂ (t + 1) := by
        funext i
        exact propext (hconsistent_succ i)
      have hcritical_t_fun :
          GenLimit.RecursiveCritical O.language stream₁ t =
            GenLimit.RecursiveCritical O.language stream₂ t := by
        funext i
        exact propext (hcritical_t i)
      have hcritical_succ_fun :
          GenLimit.RecursiveCritical O.language stream₁ (t + 1) =
            GenLimit.RecursiveCritical O.language stream₂ (t + 1) := by
        funext i
        exact propext (hcritical_succ i)
      have hdecide (old : GenLimit.PatientMachine.State) :
          GenLimit.PatientMachine.decide O.language stream₁ t old =
            GenLimit.PatientMachine.decide O.language stream₂ t old := by
        unfold GenLimit.PatientMachine.decide
          GenLimit.PatientMachine.stableDecision
          GenLimit.PatientMachine.backtrackDecision
          GenLimit.PatientMachine.highestCritical
          GenLimit.PatientMachine.highestSurvivor
          GenLimit.PatientMachine.lowestConsistentInScope
          GenLimit.PatientMachine.lowestConsistent
          GenLimit.PatientMachine.consistentIndices
          GenLimit.PatientMachine.criticalIndices
          GenLimit.PatientMachine.survivingCriticalIndices
        rw [hconsistent_succ_fun, hcritical_succ_fun, hcritical_t_fun]
      have havailable (used : Finset ℕ) (focus : ℕ) :
          GenLimit.PatientMachine.Available O.language stream₁ (t + 1) used focus =
            GenLimit.PatientMachine.Available O.language stream₂ (t + 1) used focus := by
        funext x
        apply propext
        simp only [GenLimit.PatientMachine.Available, hsample_succ]
      have hleast (used : Finset ℕ) (focus : ℕ) :
          GenLimit.PatientMachine.leastAvailable O.language O.infinite'
              stream₁ (t + 1) used focus =
            GenLimit.PatientMachine.leastAvailable O.language O.infinite'
              stream₂ (t + 1) used focus := by
        unfold GenLimit.PatientMachine.leastAvailable
        apply Nat.find_congr (Nat.find_spec
          (GenLimit.PatientMachine.available_exists O.language O.infinite'
            stream₁ (t + 1) used focus))
        intro n _
        exact Iff.of_eq (congrFun (havailable used focus) n)
      rw [GenLimit.PatientMachine.run_succ,
        GenLimit.PatientMachine.run_succ, hrun]
      unfold GenLimit.PatientMachine.processRound
      rw [hdecide]
      simp only [hleast]


private theorem patient_output_congr
    (O : GenLimit.OracleFamily) (stream₁ stream₂ : Stream) (t : ℕ)
    (hprefix : ∀ n, n < t + 1 → stream₁ n = stream₂ n) :
    GenLimit.PatientMachine.output O stream₁ t =
      GenLimit.PatientMachine.output O stream₂ t := by
  unfold GenLimit.PatientMachine.output
  rw [patient_run_congr O stream₁ stream₂ (t + 1) hprefix]

noncomputable def patientOnline (O : GenLimit.OracleFamily) : OnlineGenerator :=
  fun t xs _ => GenLimit.PatientMachine.output O (extendCurrent xs) t

theorem patientOnline_follows (O : GenLimit.OracleFamily) (input : Stream) :
    Follows (patientOnline O) input (GenLimit.PatientMachine.output O input) := by
  intro t
  apply patient_output_congr
  intro n hn
  symm
  exact extendCurrent_eq (fun i : Fin (t + 1) => input i) n hn

theorem stage3_positive_engine : PositivePresentationHalfDensity := by
  intro family hInfinite
  let O := oracleOf family hInfinite
  refine ⟨patientOnline O, ?_⟩
  intro i input hP
  let output := GenLimit.PatientMachine.output O input
  refine ⟨output, patientOnline_follows O input, ?_, ?_⟩
  · obtain ⟨⟨T, hNovel⟩, _⟩ :=
      GenLimit.PatientMachine.patientScope_generation_and_lowerDensity O input hP
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfresh, hdistinct⟩ := hNovel t ht
    refine ⟨hmem, ?_, hdistinct⟩
    intro hseen
    rw [GenLimit.mem_sample_iff] at hseen
    obtain ⟨s, hs, heq⟩ := hseen
    exact hfresh s (Nat.lt_succ_iff.mp hs) heq
  · simpa [output, O] using
      GenLimit.PatientMachine.patientScope_lowerDensity_half O input hP


private theorem exists_expansion_index
    (O : GenLimit.OracleFamily) (i : ℕ) (input : Stream)
    (hcomplete : O.language i ⊆ Set.range input)
    (hfinite : GenLimit.Generic.FinitelyManyViolations input
      (fun x => x ∈ O.language i)) :
    ∃ j, GenLimit.Presents input
      ((GenLimit.InfiniteContamination.finiteExpansionOracleFamily O).language j) := by
  classical
  let noise := GenLimit.InfiniteContamination.displayedNoise input (O.language i)
  have hnoise : noise.Finite := by
    unfold noise
    rw [GenLimit.InfiniteContamination.displayedNoise_eq_image_badTimes]
    exact hfinite.image input
  let addCode := Finset.equivBitIndices.symm hnoise.toFinset
  let data : GenLimit.InfiniteContamination.FiniteExpansionCode := (i, addCode, 0)
  let j := GenLimit.InfiniteContamination.encodeFiniteExpansionCode data
  refine ⟨j, ?_⟩
  change Set.range input =
    GenLimit.InfiniteContamination.finiteExpansionLanguage O j
  rw [GenLimit.InfiniteContamination.finiteExpansionLanguage]
  simp only [j, data,
    GenLimit.InfiniteContamination.finiteExpansionCode_encode,
    addCode, Equiv.apply_symm_apply]
  have hnoiseCoe : (↑hnoise.toFinset : Set ℕ) = noise :=
    Set.Finite.coe_toFinset hnoise
  rw [hnoiseCoe]
  have homit : GenLimit.InfiniteContamination.displayedOmissions input
      (O.language i) = ∅ := by
    exact Set.diff_eq_empty.mpr hcomplete
  have hexpand :=
    GenLimit.InfiniteContamination.finiteExpansion_displayedNoise_displayedOmissions
      input (O.language i)
  rw [homit] at hexpand
  simpa [GenLimit.InfiniteContamination.finiteExpansion] using hexpand.symm


private theorem prefixCount_inter_extension_le
    (Q K R : Set ℕ) (hfinite : (R \ K).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Q ∩ R) n ≤
      GenLimit.PatientScope.prefixCount (Q ∩ K) n + (R \ K).ncard := by
  classical
  let left := GenLimit.PatientScope.prefixFinset (Q ∩ R) n
  let right := GenLimit.PatientScope.prefixFinset (Q ∩ K) n
  have hsub : left ⊆ right ∪ hfinite.toFinset := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    by_cases hxK : x ∈ K
    · apply Finset.mem_union_left
      exact GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hx'.1, hx'.2.1, hxK⟩
    · apply Finset.mem_union_right
      simpa using (show x ∈ hfinite.toFinset from
        (Set.Finite.mem_toFinset hfinite).mpr ⟨hx'.2.2, hxK⟩)
  change left.card ≤ right.card + (R \ K).ncard
  calc
    left.card ≤ (right ∪ hfinite.toFinset).card := Finset.card_le_card hsub
    _ ≤ right.card + hfinite.toFinset.card := Finset.card_union_le _ _
    _ = right.card + (R \ K).ncard := by
      rw [Set.ncard_eq_toFinset_card (R \ K) hfinite]

private theorem relativeLowerDensity_finite_extension
    (Q K R : Set ℕ) (hK : K.Infinite) (hKR : K ⊆ R)
    (hfinite : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let ratioR : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
      (GenLimit.PatientScope.prefixCount R n : ℝ)
  let ratioK : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    ((R \ K).ncard : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcountK := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hcountKReal : Tendsto (fun n =>
      (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcountKReal
  have hKpos : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hcountK.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop, ratioR n - error n ≤ ratioK n := by
    filter_upwards [hKpos] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdenNat : GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount R n :=
      GenLimit.PatientScope.prefixCount_mono hKR n
    have hdenR : (0 : ℝ) < GenLimit.PatientScope.prefixCount R n := by
      exact_mod_cast lt_of_lt_of_le hn hdenNat
    have hnumNat := prefixCount_inter_extension_le Q K R hfinite n
    have hnumR :
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) ≤
          (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) +
            ((R \ K).ncard : ℝ) := by
      exact_mod_cast hnumNat
    have hnonneg : (0 : ℝ) ≤
        GenLimit.PatientScope.prefixCount (Q ∩ R) n := by positivity
    dsimp [ratioR, ratioK, error]
    apply (sub_le_iff_le_add).2
    have hfirst :
        (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
            (GenLimit.PatientScope.prefixCount R n : ℝ) ≤
          (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
      exact div_le_div_of_nonneg_left hnonneg hnR (by exact_mod_cast hdenNat)
    calc
      (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
          (GenLimit.PatientScope.prefixCount R n : ℝ)
        ≤ (GenLimit.PatientScope.prefixCount (Q ∩ R) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := hfirst
      _ ≤ ((GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) +
            ((R \ K).ncard : ℝ)) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
          exact div_le_div_of_nonneg_right hnumR hnR.le
      _ = (GenLimit.PatientScope.prefixCount (Q ∩ K) n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) +
          ((R \ K).ncard : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
          rw [add_div]
  have hratioR_nonneg : ∀ n, 0 ≤ ratioR n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hratioR_le_one : ∀ n, ratioR n ≤ 1 := by
    intro n
    dsimp [ratioR]
    by_cases hz : GenLimit.PatientScope.prefixCount R n = 0
    · simp [hz]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  have hnegError_le : ∀ n, -((R \ K).ncard : ℝ) ≤ -error n := by
    intro n
    dsimp [error]
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · have hden : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have hc : (0 : ℝ) ≤ (R \ K).ncard := by positivity
      have := div_le_self hc hden
      linarith
  have hnegError_nonpos : ∀ n, -error n ≤ 0 := by
    intro n
    exact neg_nonpos.mpr (div_nonneg (by positivity) (by positivity))
  have hsum :
      liminf ratioR atTop + liminf (fun n => -error n) atTop ≤
        liminf (fun n => ratioR n + -error n) atTop := by
    apply le_liminf_add
    · exact isBoundedUnder_of_eventually_ge (Eventually.of_forall hratioR_nonneg)
    · exact isBoundedUnder_of_eventually_le (Eventually.of_forall hratioR_le_one)
    · exact isBoundedUnder_of_eventually_ge (Eventually.of_forall hnegError_le)
    · exact isCoboundedUnder_ge_of_le atTop hnegError_nonpos
  have hnegError : Tendsto (fun n => -error n) atTop (𝓝 0) := by
    simpa using herror.neg
  have hlimCompare :
      liminf (fun n => ratioR n + -error n) atTop ≤ liminf ratioK atTop := by
    apply liminf_le_liminf
    · simpa [sub_eq_add_neg] using hcompare
    · apply isBoundedUnder_of
      refine ⟨-((R \ K).ncard : ℝ), ?_⟩
      intro n
      have hlow := hnegError_le n
      have hnonneg := hratioR_nonneg n
      linarith
    · apply isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ))
      intro n
      dsimp [ratioK]
      by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hz]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hz)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  change liminf ratioR atTop ≤ liminf ratioK atTop
  calc
    liminf ratioR atTop = liminf ratioR atTop + liminf (fun n => -error n) atTop := by
      rw [hnegError.liminf_eq]
      simp
    _ ≤ liminf (fun n => ratioR n + -error n) atTop := hsum
    _ ≤ liminf ratioK atTop := hlimCompare


theorem stage3_finite_noise_transfer : FiniteNoiseTransferPrinciple := by
  intro hpositive family hInfinite
  let O := oracleOf family hInfinite
  let expanded := GenLimit.InfiniteContamination.finiteExpansionOracleFamily O
  obtain ⟨gen, hgen⟩ := hpositive expanded.language expanded.infinite'
  refine ⟨gen, ?_⟩
  intro i input hpresentation
  obtain ⟨j, hjPresents⟩ :=
    exists_expansion_index O i input hpresentation.1 hpresentation.2
  obtain ⟨output, hFollows, hNovelExpanded, hDensityExpanded⟩ :=
    hgen j input hjPresents
  let K := family i
  let R := expanded.language j
  have hRPresents : GenLimit.Presents input R := by
    simpa [R, expanded] using hjPresents
  have hKR : K ⊆ R := by
    intro x hx
    rw [← hRPresents]
    exact hpresentation.1 hx
  have hfinite : (R \ K).Finite := by
    have hvalues : (Set.range input \ K).Finite := by
      rw [GenLimit.Generic.valuesOutside_eq_image_violationIndices]
      exact hpresentation.2.image input
    rw [hRPresents] at hvalues
    simpa [K] using hvalues
  refine ⟨output, hFollows, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := hNovelExpanded
    let badTimes : Set ℕ := {t | T ≤ t ∧ output t ∈ R \ K}
    have hinjective : Set.InjOn output {t | T ≤ t} := by
      intro a ha b hb hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hablt | hbalt
      · exact (hT b hb).2.2 a hablt hab
      · exact (hT a ha).2.2 b hbalt hab.symm
    have hbadImage : (output '' badTimes).Finite := by
      apply hfinite.subset
      rintro x ⟨t, ht, rfl⟩
      exact ht.2
    have hbadFinite : badTimes.Finite := by
      apply hbadImage.of_finite_image
      intro a ha b hb hab
      exact hinjective ha.1 hb.1 hab
    have heventually : ∀ᶠ t : ℕ in atTop, t ∉ badTimes :=
      (Set.Finite.eventually_cofinite_notMem hbadFinite).filter_mono
        atTop_le_cofinite
    obtain ⟨Tbad, hTbad⟩ := eventually_atTop.mp heventually
    refine ⟨max T Tbad, ?_⟩
    intro t ht
    have htT : T ≤ t := (Nat.le_max_left T Tbad).trans ht
    have htBad : Tbad ≤ t := (Nat.le_max_right T Tbad).trans ht
    obtain ⟨hR, hfresh, hdistinct⟩ := hT t htT
    refine ⟨?_, hfresh, hdistinct⟩
    by_contra hnotK
    exact hTbad t htBad ⟨htT, hR, hnotK⟩
  · have htransfer := relativeLowerDensity_finite_extension
      (GenLimit.GeneratorFirst input output) K R
      (by simpa [K] using hInfinite i) hKR hfinite
    exact hDensityExpanded.trans (by simpa [K, R] using htransfer)

end Stage3Case025

theorem stage3_result : Stage3Case025.MainClaim := by
  exact Stage3Case025.stage3_finite_noise_transfer
    Stage3Case025.stage3_positive_engine
