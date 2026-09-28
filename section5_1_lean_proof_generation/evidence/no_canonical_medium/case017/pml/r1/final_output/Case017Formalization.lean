import Stage3Model
import GenLimit.Paper39_DenseGeneration.Partial.Trace
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Stage3Case017Proof

open GenLimit

noncomputable def finiteCore {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image xs ∪ Finset.univ.image ys

noncomputable def available {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ finiteCore family xs ∧ z ∉ forbidden xs ys

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    Stage3Case017.OnlineGenerator := fun _ xs ys => by
  classical
  exact if h : ∃ z, available family xs ys z then Nat.find h
    else Nat.find (Set.infinite_univ.exists_notMem_finset (forbidden xs ys))

 theorem greedyGenerator_fresh {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    greedyGenerator family t xs ys ∉ forbidden xs ys := by
  classical
  simp only [greedyGenerator]
  split
  · exact (Nat.find_spec ‹∃ z, available family xs ys z›).2
  · exact (Nat.find_spec
      (Set.infinite_univ.exists_notMem_finset (forbidden xs ys))).2

 theorem greedyGenerator_spec {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, available family xs ys z) :
    available family xs ys (greedyGenerator family t xs ys) := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_spec h

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
 decreasing_by exact i.isLt

 theorem trajectory_follows (gen : Stage3Case017.OnlineGenerator)
    (input : Stage3Case017.Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

 theorem trajectory_fresh_input {m : ℕ} (family : Fin m → Language)
    (input : Stage3Case017.Stream) {t s : ℕ} (hs : s ≤ t) :
    input s ≠ trajectory (greedyGenerator family) input t := by
  have hfresh := greedyGenerator_fresh family
    (xs := fun i : Fin (t + 1) => input i)
    (ys := fun i : Fin t => trajectory (greedyGenerator family) input i)
  rw [trajectory]
  intro heq
  apply hfresh
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨⟨s, Nat.lt_succ_of_le hs⟩, Finset.mem_univ _, heq⟩

 theorem trajectory_fresh_output {m : ℕ} (family : Fin m → Language)
    (input : Stage3Case017.Stream) {t s : ℕ} (hs : s < t) :
    trajectory (greedyGenerator family) input s ≠
      trajectory (greedyGenerator family) input t := by
  have hfresh := greedyGenerator_fresh family
    (xs := fun i : Fin (t + 1) => input i)
    (ys := fun i : Fin t => trajectory (greedyGenerator family) input i)
  intro heq
  apply hfresh
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _,
    heq.trans (trajectory.eq_def _ _ _)⟩

 theorem streamIn_iff_prefixes {m : ℕ} (family : Fin m → Language)
    (input : Stage3Case017.Stream) (j : Fin m) :
    GenLimit.Generic.StreamIn input (family j) ↔
      ∀ t, ∀ i : Fin (t + 1), input i ∈ family j := by
  constructor
  · intro h t i
    exact h ⟨i, rfl⟩
  · intro h z hz
    obtain ⟨n, rfl⟩ := hz
    exact h n ⟨n, Nat.lt_succ_self n⟩

 theorem finite_version_space_stabilizes {m : ℕ}
    (family : Fin m → Language) (input : Stage3Case017.Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hbadExists : ∀ j, ¬ GenLimit.Generic.StreamIn input (family j) →
      ∃ n, input n ∉ family j := by
    intro j h
    obtain ⟨z, ⟨n, rfl⟩, hn⟩ := Set.not_subset.mp h
    exact ⟨n, hn⟩
  let badTime : Fin m → ℕ := fun j =>
    if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Classical.choose (hbadExists j h)
  let T := Finset.univ.sup badTime
  refine ⟨T, ?_⟩
  intro t ht j
  constructor
  · intro hpref
    by_contra hbad
    have hchosen : input (badTime j) ∉ family j := by
      simp only [badTime, dif_neg hbad]
      exact Classical.choose_spec (hbadExists j hbad)
    have hle : badTime j ≤ T := Finset.le_sup (Finset.mem_univ j)
    exact hchosen (hpref ⟨badTime j, Nat.lt_succ_of_le (hle.trans ht)⟩)
  · intro hall i
    exact hall ⟨i, rfl⟩

 theorem finiteCore_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stage3Case017.Stream)
    {t T : ℕ}
    (hstable : ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T ≤ t) :
    finiteCore family (fun i : Fin (t + 1) => input i) =
      Stage3Case017.informationCore family input := by
  ext z
  simp only [finiteCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((hstable t ht j).2 hj)
  · intro hz j hj
    exact hz j ((hstable t ht j).1 hj)

 theorem exists_available {m : ℕ} (family : Fin m → Language)
    (input output : Stage3Case017.Stream) {t T : ℕ}
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (hstable : ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T ≤ t) :
    ∃ z, available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i) z := by
  obtain ⟨z, hzcore, hznot⟩ := hcore.exists_notMem_finset
    (forbidden (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i))
  refine ⟨z, ?_, hznot⟩
  rw [finiteCore_eq_informationCore family input hstable ht]
  exact hzcore

 theorem output_spec_after_stable {m : ℕ} (family : Fin m → Language)
    (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j))
    {t : ℕ} (ht : T ≤ t) :
    available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (greedyGenerator family) input i)
      (trajectory (greedyGenerator family) input t) := by
  have hex := exists_available family input
    (trajectory (greedyGenerator family) input) hcore hstable ht
  rw [trajectory]
  exact greedyGenerator_spec family
    (xs := fun i : Fin (t + 1) => input i)
    (ys := fun i : Fin t => trajectory (greedyGenerator family) input i) hex

 theorem output_mem_core_after_stable {m : ℕ} (family : Fin m → Language)
    (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j))
    {t : ℕ} (ht : T ≤ t) :
    trajectory (greedyGenerator family) input t ∈
      Stage3Case017.informationCore family input := by
  have hs := (output_spec_after_stable family input hcore hstable ht).1
  rwa [finiteCore_eq_informationCore family input hstable ht] at hs

 theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) :
    Stage3Case017.informationCore family input ⊆
      GenLimit.AdversaryFirst input (trajectory (greedyGenerator family) input) ∪
        GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  classical
  intro z hz
  by_cases hin : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input
      (trajectory (greedyGenerator family) input) hin
  · by_cases hout : z ∈ Set.range (trajectory (greedyGenerator family) input)
    · obtain ⟨t, ht⟩ := hout
      exact Set.mem_union_right _ ⟨t, ht, fun s hs hsi => hin ⟨s, hsi⟩⟩
    · exfalso
      have hnone : ∀ t, trajectory (greedyGenerator family) input t ≠ z := by
        intro t ht
        exact hout ⟨t, ht⟩
      let f : Fin (z + 1) → Fin z := fun k =>
        ⟨trajectory (greedyGenerator family) input (T + k), by
          have hzavail : available family
              (fun i : Fin ((T + k) + 1) => input i)
              (fun i : Fin (T + k) => trajectory (greedyGenerator family) input i) z := by
            refine ⟨?_, ?_⟩
            · rw [finiteCore_eq_informationCore family input hstable
                (show T ≤ T + k from Nat.le_add_right T k)]
              exact hz
            · intro hzforbid
              rcases Finset.mem_union.mp hzforbid with hzin | hzout
              · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hzin
                exact hin ⟨i, hi⟩
              · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hzout
                exact (hnone i) hi
          have hle : trajectory (greedyGenerator family) input (T + k) ≤ z := by
            rw [trajectory, greedyGenerator, dif_pos ⟨z, hzavail⟩]
            exact Nat.find_min' _ hzavail
          exact lt_of_le_of_ne hle (hnone (T + k))⟩
      have hfinj : Function.Injective f := by
        intro a b hab
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with hablt | hbalt
        · exact trajectory_fresh_output family input
            (show T + a < T + b by omega) (Fin.ext_iff.mp hab)
        · exact trajectory_fresh_output family input
            (show T + b < T + a by omega) (Fin.ext_iff.mp hab).symm
      have hcard := Fintype.card_le_of_injective f hfinj
      simp at hcard

 theorem previous_output_lt {m : ℕ} (family : Fin m → Language)
    (input : Stage3Case017.Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T t : ℕ}
    (hstable : ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T < t)
    (hatt : input t ∈ GenLimit.AdversaryFirst input
      (trajectory (greedyGenerator family) input))
    (hfresh : input t ∉ GenLimit.sample input t) :
    trajectory (greedyGenerator family) input (t - 1) < input t := by
  classical
  have hprevT : T ≤ t - 1 := by omega
  have hxcore : input t ∈ Stage3Case017.informationCore family input := by
    intro j hj
    exact hj ⟨t, rfl⟩
  have hxavail : available family
      (fun i : Fin ((t - 1) + 1) => input i)
      (fun i : Fin (t - 1) => trajectory (greedyGenerator family) input i)
      (input t) := by
    refine ⟨?_, ?_⟩
    · rw [finiteCore_eq_informationCore family input hstable hprevT]
      exact hxcore
    · intro hforbid
      rcases Finset.mem_union.mp hforbid with hin | hout
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hin
        exact hfresh (GenLimit.mem_sample_iff.mpr ⟨i, by omega, hi⟩)
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hout
        obtain ⟨q, hqt, hno⟩ := hatt
        have hq : q = t := hinj hqt
        subst q
        exact (hno i (by omega)) hi
  have hle : trajectory (greedyGenerator family) input (t - 1) ≤ input t := by
    rw [trajectory, greedyGenerator, dif_pos ⟨input t, hxavail⟩]
    exact Nat.find_min' _ hxavail
  have hne : trajectory (greedyGenerator family) input (t - 1) ≠ input t := by
    obtain ⟨q, hqt, hno⟩ := hatt
    have hq : q = t := hinj hqt
    subst q
    exact hno (t - 1) (by omega)
  exact lt_of_le_of_ne hle hne

 theorem relativeLowerDensity_mono_left {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · exact Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact Filter.isCoboundedUnder_ge_of_le Filter.atTop (fun n => by
      show (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · have hbzero : GenLimit.PatientScope.prefixCount B n = 0 := by
          have hle := GenLimit.PatientScope.prefixCount_mono hBK n
          omega
        simp [hzero, hbzero]
      · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
          exact_mod_cast Nat.pos_of_ne_zero hzero
        exact (div_le_one hpos).2 (by
          exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n))

 theorem succeeds {m : ℕ} (family : Fin m → Language) :
    Stage3Case017.SucceedsFor family (greedyGenerator family) := by
  intro input hinj hpartial hcore
  let output := trajectory (greedyGenerator family) input
  obtain ⟨T, hstable⟩ := finite_version_space_stabilizes family input
  refine ⟨output, trajectory_follows _ _, ?_⟩
  intro j hj
  have hcoreSub : Stage3Case017.informationCore family input ⊆ family j :=
    fun _ hz => hz j hj
  have hnovel : GenLimit.NovelGeneratesInLimit input output (family j) := by
    refine ⟨T, ?_⟩
    intro t ht
    refine ⟨hcoreSub (output_mem_core_after_stable family input hcore hstable ht), ?_, ?_⟩
    · intro hmem
      rw [GenLimit.mem_sample_iff] at hmem
      obtain ⟨s, hs, heq⟩ := hmem
      exact (trajectory_fresh_input family input (Nat.le_of_lt_succ hs)) heq
    · intro s hs
      exact trajectory_fresh_output family input hs
  refine ⟨hnovel, ?_⟩
  let G : GenLimit.PartialEnumeration.PartialGameTrace := {
    target := family j
    enumerated := Set.range input
    enumerated_subset_target := hj
    adversary := input
    generator := output
    presents := rfl
    fresh_adversary := fun t s hst => trajectory_fresh_input family input hst
    fresh_generator := fun t s hst => trajectory_fresh_output family input hst
    validFrom := T
    eventual_target := fun t ht =>
      hcoreSub (output_mem_core_after_stable family input hcore hstable ht)
  }
  have hcompare : G.HasPredecessorComparison (∅ : Set ℕ) := by
    intro t ht hatt hfresh _
    exact previous_output_lt family input hinj hcore hstable ht hatt hfresh
  have hemptyPrefix : ∀ n, GenLimit.PatientScope.prefixCount (∅ : Set ℕ) n ≤ 0 := by
    intro n
    simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  let P0 := G.toCertificate (∅ : Set ℕ) (by simp) hcompare (fun _ => 0) hemptyPrefix
  let P : GenLimit.PatientScope.PartialEnumerationCertificate :=
    { P0 with
      enumerated := Stage3Case017.informationCore family input
      enumerated_subset_target := hcoreSub
      enumerated_covered := core_covered family input hcore hstable }
  have htargetInfinite : P.target.Infinite := by
    simpa [P, P0, G] using hcore.mono hcoreSub
  have hlog : ∀ n, GenLimit.PatientScope.prefixCount P.switchLoss n ≤
      Nat.log2 (P.targetCount n) := by
    intro n
    change GenLimit.PatientScope.prefixCount (∅ : Set ℕ) n ≤
      Nat.log2 (GenLimit.PatientScope.prefixCount (family j) n)
    simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
  have hhalf := P.theorem_3_17 htargetInfinite hlog
  have hhalf' :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    simpa [P, P0, G, GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity,
      GenLimit.PartialEnumeration.PartialGameTrace.defender] using hhalf
  have hmissingSub :
      Stage3Case017.informationCore family input \ Set.range input ⊆
        GenLimit.GeneratorFirst input output ∩ family j := by
    intro z hz
    refine ⟨?_, hcoreSub hz.1⟩
    rcases core_covered family input hcore hstable hz.1 with hA | hG
    · exfalso
      obtain ⟨t, ht, -⟩ := hA
      exact hz.2 ⟨t, ht⟩
    · exact hG
  have hmissing := relativeLowerDensity_mono_left hmissingSub Set.inter_subset_right
  exact max_le hhalf' hmissing

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  exact ⟨Stage3Case017Proof.greedyGenerator family,
    Stage3Case017Proof.succeeds family⟩
