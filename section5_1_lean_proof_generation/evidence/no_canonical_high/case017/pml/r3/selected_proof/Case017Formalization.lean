import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Case017Proof

open Stage3Case017

noncomputable def finiteCore {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin t → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def available {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ finiteCore family xs ∧ (∀ i, xs i ≠ z) ∧ (∀ i, ys i ≠ z)

noncomputable def coreGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : ∃ z, available family xs ys z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream
  | t => gen t (fun i => input i) (fun i => trajectory gen input i)

@[simp] theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

theorem finiteCore_mono_prefix {m : ℕ} {family : Fin m → Language}
    {s t : ℕ} (hst : s ≤ t) (input : Stream) :
    finiteCore family (fun i : Fin (s + 1) => input i) ⊆
      finiteCore family (fun i : Fin (t + 1) => input i) := by
  intro z hz j hj
  apply hz j
  intro i
  exact hj ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hst)⟩

theorem finiteCore_subset_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) (t : ℕ) :
    finiteCore family (fun i : Fin (t + 1) => input i) ⊆
      informationCore family input := by
  intro z hz j hj
  apply hz j
  intro i
  exact hj ⟨i, rfl⟩

theorem exists_core_stabilization {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      finiteCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  let bad : Finset (Fin m) := Finset.univ.filter fun j =>
    ¬ GenLimit.Generic.StreamIn input (family j)
  have hw : ∀ j ∈ bad, ∃ n, input n ∉ family j := by
    intro j hj
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [GenLimit.Generic.StreamIn, Set.range_subset_iff] at hj
    simpa using hj
  let witness : Fin m → ℕ := fun j =>
    if hj : j ∈ bad then Nat.find (hw j hj) else 0
  have hwitness : ∀ j ∈ bad, input (witness j) ∉ family j := by
    intro j hj
    simp only [witness, dif_pos hj]
    exact Nat.find_spec (hw j hj)
  let T := bad.sup witness
  refine ⟨T, ?_⟩
  intro t ht
  apply Set.Subset.antisymm
  · exact finiteCore_subset_informationCore family input t
  · intro z hz j hpref
    by_contra hnot
    have hjbad : j ∈ bad := by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hstream
      exact hnot (hz j hstream)
    have hwle : witness j ≤ T := Finset.le_sup hjbad
    have hwit : witness j < t + 1 := by omega
    exact hwitness j hjbad (hpref ⟨witness j, hwit⟩)

theorem generator_spec_of_available {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, available family xs ys z) :
    available family xs ys (coreGenerator family t xs ys) := by
  classical
  simp only [coreGenerator, dif_pos h]
  exact Nat.find_spec h

theorem generator_minimal {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hz : available family xs ys z) :
    coreGenerator family t xs ys ≤ z := by
  classical
  have h : ∃ z, available family xs ys z := ⟨z, hz⟩
  simp only [coreGenerator, dif_pos h]
  exact Nat.find_min' h hz


theorem exists_available_of_core_infinite {m : ℕ}
    (family : Fin m → Language) {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hcore : (finiteCore family xs).Infinite) :
    ∃ z, available family xs ys z := by
  classical
  let used := GenLimit.Generic.sequenceSample xs ∪
    GenLimit.Generic.sequenceSample ys
  obtain ⟨z, hzcore, hzused⟩ := hcore.exists_notMem_finset used
  refine ⟨z, hzcore, ?_, ?_⟩
  · intro i hxi
    apply hzused
    apply Finset.mem_union_left
    rw [GenLimit.Generic.mem_sequenceSample_iff]
    exact ⟨i, hxi⟩
  · intro i hyi
    apply hzused
    apply Finset.mem_union_right
    rw [GenLimit.Generic.mem_sequenceSample_iff]
    exact ⟨i, hyi⟩

theorem trajectory_available_after_stabilization {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      finiteCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input) :
    ∀ t, T ≤ t →
      available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (coreGenerator family) input i)
        (trajectory (coreGenerator family) input t) := by
  intro t ht
  have hfinite :
      (finiteCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hstable t ht]
    exact hcore
  have hexists := exists_available_of_core_infinite family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (coreGenerator family) input i) hfinite
  rw [trajectory]
  exact generator_spec_of_available family _ _ hexists

theorem trajectory_novel_after_stabilization {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      finiteCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input) :
    ∀ t, T ≤ t →
      trajectory (coreGenerator family) input t ∈ informationCore family input ∧
      (∀ s, s ≤ t → input s ≠ trajectory (coreGenerator family) input t) ∧
      (∀ s, s < t → trajectory (coreGenerator family) input s ≠
        trajectory (coreGenerator family) input t) := by
  intro t ht
  have ha := trajectory_available_after_stabilization family input hcore hstable t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [← hstable t ht]
    exact ha.1
  · intro s hst
    exact ha.2.1 ⟨s, Nat.lt_succ_of_le hst⟩
  · intro s hst
    exact ha.2.2 ⟨s, hst⟩

theorem trajectory_novel_in_target {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      finiteCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (coreGenerator family) input) (family j) := by
  refine ⟨T, ?_⟩
  intro t ht
  have hn := trajectory_novel_after_stabilization family input hcore hstable t ht
  refine ⟨?_, ?_, hn.2.2⟩
  · exact hn.1 j hj
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact hn.2.1 s (Nat.le_of_lt_succ hs) heq

theorem missing_core_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      finiteCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (coreGenerator family) input) := by
  intro z hz
  have hzinput : ∀ s, input s ≠ z := by
    intro s heq
    exact hz.2 ⟨s, heq⟩
  by_contra hzfirst
  have hzout : z ∉ Set.range (trajectory (coreGenerator family) input) := by
    intro hout
    obtain ⟨t, ht⟩ := hout
    apply hzfirst
    refine ⟨t, ht, ?_⟩
    intro s hs
    exact hzinput s
  have hround : ∀ i : Fin (z + 1),
      trajectory (coreGenerator family) input (T + i) < z := by
    intro i
    let t := T + (i : ℕ)
    have ht : T ≤ t := Nat.le_add_right T i
    have ha := trajectory_available_after_stabilization family input hcore hstable t ht
    have hzavail : available family
        (fun k : Fin (t + 1) => input k)
        (fun k : Fin t => trajectory (coreGenerator family) input k) z := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hstable t ht]
        exact hz.1
      · intro k
        exact hzinput k
      · intro k heq
        exact hzout ⟨k, heq⟩
    have hle : trajectory (coreGenerator family) input t ≤ z := by
      rw [trajectory]
      exact generator_minimal family _ _ hzavail
    have hne : trajectory (coreGenerator family) input t ≠ z := by
      intro heq
      exact hzout ⟨t, heq⟩
    exact lt_of_le_of_ne hle hne
  let f : Fin (z + 1) → Fin z := fun i =>
    ⟨trajectory (coreGenerator family) input (T + i), hround i⟩
  have hf : Function.Injective f := by
    intro i k hik
    by_contra hne
    rcases lt_or_gt_of_ne hne with hik' | hki'
    · have havail := trajectory_available_after_stabilization family input hcore hstable
        (T + k) (Nat.le_add_right T k)
      have hneq := havail.2.2
        ⟨T + i, by omega⟩
      exact hneq (Fin.ext_iff.mp hik)
    · have havail := trajectory_available_after_stabilization family input hcore hstable
        (T + i) (Nat.le_add_right T i)
      have hneq := havail.2.2
        ⟨T + k, by omega⟩
      exact hneq (Fin.ext_iff.mp hik).symm
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard


noncomputable def firstInputTime (input : Stream) (x : ℕ) : ℕ := by
  classical
  exact if h : x ∈ Set.range input then Nat.find h else 0

theorem firstInputTime_spec {input : Stream} {x : ℕ}
    (hx : x ∈ Set.range input) : input (firstInputTime input x) = x := by
  classical
  simp only [firstInputTime, dif_pos hx]
  exact Nat.find_spec hx

theorem firstInputTime_min {input : Stream} {x s : ℕ}
    (hx : x ∈ Set.range input) (hs : input s = x) :
    firstInputTime input x ≤ s := by
  classical
  simp only [firstInputTime, dif_pos hx]
  exact Nat.find_min' hx hs

noncomputable def predecessorOutput {m : ℕ} (family : Fin m → Language)
    (input : Stream) (x : ℕ) : ℕ :=
  trajectory (coreGenerator family) input (firstInputTime input x - 1)

theorem core_prefix_count_bound {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hinput : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      finiteCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j))
    (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (coreGenerator family) input) ∩
          family j) n + (T + 1) := by
  classical
  let I := informationCore family input
  let D := GenLimit.GeneratorFirst input
    (trajectory (coreGenerator family) input) ∩ family j
  let IP := GenLimit.PatientScope.prefixFinset I n
  let DP := GenLimit.PatientScope.prefixFinset D n
  let earlySample := GenLimit.Generic.sequenceSample
    (fun i : Fin (T + 1) => input i)
  let early := IP ∩ earlySample
  let late := IP \ (DP ∪ early)
  have hdecomp : IP ⊆ (DP ∪ early) ∪ late := by
    intro x hx
    by_cases hmem : x ∈ DP ∪ early
    · exact Finset.mem_union_left _ hmem
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hmem⟩)
  have hearly : early.card ≤ T + 1 := by
    have hinj : Function.Injective (fun i : Fin (T + 1) => input i) := by
      intro a b hab
      exact Fin.ext (hinput hab)
    calc
      early.card ≤ earlySample.card := Finset.card_le_card Finset.inter_subset_right
      _ = T + 1 := by
        simpa only [earlySample] using
          (GenLimit.Generic.sequenceSample_card_of_injective
            (xs := fun i : Fin (T + 1) => input i) hinj)
  have hlate : late.card ≤ DP.card := by
    apply Finset.card_le_card_of_injOn (predecessorOutput family input)
    · intro x hx
      have hxlate := Finset.mem_sdiff.mp hx
      have hxIP := GenLimit.PatientScope.mem_prefixFinset.mp hxlate.1
      have hxnot := hxlate.2
      have hxnotDP : x ∉ DP := by
        intro hxDP
        exact hxnot (Finset.mem_union_left _ hxDP)
      have hxnotearly : x ∉ early := by
        intro hxearly
        exact hxnot (Finset.mem_union_right _ hxearly)
      have hxnotD : x ∉ D := by
        intro hxD
        exact hxnotDP (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxIP.1, hxD⟩)
      have hxnotFirst : x ∉ GenLimit.GeneratorFirst input
          (trajectory (coreGenerator family) input) := by
        intro hxfirst
        exact hxnotD ⟨hxfirst, hxIP.2 j hj⟩
      have hxrange : x ∈ Set.range input := by
        by_contra hxrange
        have hxmissing : x ∈ I \ Set.range input := ⟨hxIP.2, hxrange⟩
        exact hxnotFirst
          (missing_core_subset_generatorFirst family input hcore hstable hxmissing)
      let t := firstInputTime input x
      have htx : input t = x := firstInputTime_spec hxrange
      have htT : T < t := by
        by_contra hnotlt
        have ht : t < T + 1 := by omega
        apply hxnotearly
        apply Finset.mem_inter.mpr
        refine ⟨hxlate.1, ?_⟩
        rw [GenLimit.Generic.mem_sequenceSample_iff]
        exact ⟨⟨t, ht⟩, htx⟩
      have hround : T ≤ t - 1 := by omega
      have havail := trajectory_available_after_stabilization family input hcore hstable
        (t - 1) hround
      have hxavail : available family
          (fun k : Fin ((t - 1) + 1) => input k)
          (fun k : Fin (t - 1) => trajectory (coreGenerator family) input k) x := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hstable (t - 1) hround]
          exact hxIP.2
        · intro k heq
          have htle : t ≤ k := firstInputTime_min hxrange heq
          omega
        · intro k heq
          apply hxnotFirst
          refine ⟨k, heq, ?_⟩
          intro s hs heqInput
          have htle : t ≤ s := firstInputTime_min hxrange heqInput
          omega
      have hpartnerLe : predecessorOutput family input x ≤ x := by
        simp only [predecessorOutput, t]
        rw [trajectory]
        exact generator_minimal family _ _ hxavail
      have hpartnerFirst : predecessorOutput family input x ∈
          GenLimit.GeneratorFirst input (trajectory (coreGenerator family) input) := by
        refine ⟨t - 1, rfl, ?_⟩
        intro s hs
        exact havail.2.1 ⟨s, by omega⟩
      have hpartnerCore : predecessorOutput family input x ∈ I := by
        simpa only [predecessorOutput, t] using
          (trajectory_novel_after_stabilization family input hcore hstable
            (t - 1) hround).1
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      refine ⟨lt_of_le_of_lt hpartnerLe hxIP.1, hpartnerFirst, ?_⟩
      exact hpartnerCore j hj
    · intro x hx y hy hxy
      have hxlate := Finset.mem_sdiff.mp hx
      have hylate := Finset.mem_sdiff.mp hy
      have hxIP := GenLimit.PatientScope.mem_prefixFinset.mp hxlate.1
      have hyIP := GenLimit.PatientScope.mem_prefixFinset.mp hylate.1
      have hxnotD : x ∉ D := by
        intro hxD
        exact hxlate.2 (Finset.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxIP.1, hxD⟩))
      have hynotD : y ∉ D := by
        intro hyD
        exact hylate.2 (Finset.mem_union_left _
          (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hyIP.1, hyD⟩))
      have hxrange : x ∈ Set.range input := by
        by_contra hr
        have hfirst := missing_core_subset_generatorFirst family input hcore hstable
          ⟨hxIP.2, hr⟩
        exact hxnotD ⟨hfirst, hxIP.2 j hj⟩
      have hyrange : y ∈ Set.range input := by
        by_contra hr
        have hfirst := missing_core_subset_generatorFirst family input hcore hstable
          ⟨hyIP.2, hr⟩
        exact hynotD ⟨hfirst, hyIP.2 j hj⟩
      let tx := firstInputTime input x
      let ty := firstInputTime input y
      have htx : input tx = x := firstInputTime_spec hxrange
      have hty : input ty = y := firstInputTime_spec hyrange
      have htxT : T < tx := by
        by_contra hnot
        have hmemEarly : x ∈ early := by
          apply Finset.mem_inter.mpr
          refine ⟨hxlate.1, ?_⟩
          rw [GenLimit.Generic.mem_sequenceSample_iff]
          exact ⟨⟨tx, by omega⟩, htx⟩
        exact hxlate.2 (Finset.mem_union_right _ hmemEarly)
      have htyT : T < ty := by
        by_contra hnot
        have hmemEarly : y ∈ early := by
          apply Finset.mem_inter.mpr
          refine ⟨hylate.1, ?_⟩
          rw [GenLimit.Generic.mem_sequenceSample_iff]
          exact ⟨⟨ty, by omega⟩, hty⟩
        exact hylate.2 (Finset.mem_union_right _ hmemEarly)
      have htime : tx = ty := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have ha := trajectory_available_after_stabilization family input hcore hstable
            (ty - 1) (by omega)
          have hneq := ha.2.2 ⟨tx - 1, by omega⟩
          exact hneq hxy
        · have ha := trajectory_available_after_stabilization family input hcore hstable
            (tx - 1) (by omega)
          have hneq := ha.2.2 ⟨ty - 1, by omega⟩
          exact hneq hxy.symm
      rw [← htx, ← hty, htime]
  calc
    GenLimit.PatientScope.prefixCount I n = IP.card := rfl
    _ ≤ ((DP ∪ early) ∪ late).card := Finset.card_le_card hdecomp
    _ ≤ (DP ∪ early).card + late.card := Finset.card_union_le _ _
    _ ≤ (DP.card + early.card) + late.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (DP.card + (T + 1)) + DP.card := by omega
    _ = 2 * DP.card + (T + 1) := by omega
    _ = 2 * GenLimit.PatientScope.prefixCount D n + (T + 1) := rfl

theorem half_core_density_bound {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hinput : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      finiteCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (coreGenerator family) input) ∩
          family j) (family j) := by
  apply GenLimit.PatientScope.partialDensity_of_counting
    (GenLimit.PatientScope.prefixCount (family j))
    (GenLimit.PatientScope.prefixCount (informationCore family input))
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (trajectory (coreGenerator family) input) ∩
        family j)) (T + 1)
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop
      ((Set.infinite_range_of_injective hinput).mono hj)
  · intro n
    apply GenLimit.PatientScope.prefixCount_mono
    intro x hx
    exact hx j hj
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have h := core_prefix_count_bound family input hinput hcore hstable j hj n
    omega


theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · apply Filter.Eventually.of_forall
    intro n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
    · exact Nat.cast_nonneg _
  · apply isBoundedUnder_of_eventually_ge
    apply Filter.Eventually.of_forall
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply isCoboundedUnder_ge_of_le atTop
    intro n
    show (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ (1 : ℝ)
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

theorem missing_core_density_bound {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      finiteCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (coreGenerator family) input) ∩
          family j) (family j) := by
  apply relativeLowerDensity_mono
  · intro x hx
    exact ⟨missing_core_subset_generatorFirst family input hcore hstable hx,
      hx.1 j hj⟩
  · exact Set.inter_subset_right

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  refine ⟨Case017Proof.coreGenerator family, ?_⟩
  intro input hinput hexists hcore
  obtain ⟨T, hstable⟩ := Case017Proof.exists_core_stabilization family input
  let output := Case017Proof.trajectory (Case017Proof.coreGenerator family) input
  refine ⟨output, ?_, ?_⟩
  · exact Case017Proof.trajectory_follows _ _
  · intro j hj
    refine ⟨?_, ?_⟩
    · exact Case017Proof.trajectory_novel_in_target family input hcore hstable j hj
    · apply max_le
      · exact Case017Proof.half_core_density_bound
          family input hinput hcore hstable j hj
      · exact Case017Proof.missing_core_density_bound
          family input hcore hstable j hj
