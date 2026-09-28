import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Case017Proof

abbrev Language := Stage3Case017.Language
abbrev Stream := Stage3Case017.Stream
abbrev OnlineGenerator := Stage3Case017.OnlineGenerator

noncomputable def usedAt {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

noncomputable def activeCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def preferred {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ activeCore family xs ∧ z ∉ usedAt xs ys

noncomputable def chooseOutput {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : ℕ := by
  classical
  by_cases h : ∃ z, preferred family xs ys z
  · exact Nat.find h
  · exact Nat.find (Set.Finite.exists_not_mem (usedAt xs ys).finite_toSet)

noncomputable def generator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := fun _ xs ys => chooseOutput family xs ys

noncomputable def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t

@[simp] theorem run_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    run gen input t = gen t (fun i => input i) (fun i => run gen input i) := by
  rw [run]

theorem follows_run (gen : OnlineGenerator) (input : Stream) :
    Stage3Case017.Follows gen input (run gen input) := by
  intro t
  exact run_eq gen input t

theorem chooseOutput_not_used {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    chooseOutput family xs ys ∉ usedAt xs ys := by
  classical
  unfold chooseOutput
  split_ifs with h
  · exact (Nat.find_spec h).2
  · exact Nat.find_spec (Set.Finite.exists_not_mem (usedAt xs ys).finite_toSet)

theorem chooseOutput_preferred {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, preferred family xs ys z) :
    preferred family xs ys (chooseOutput family xs ys) := by
  classical
  simp only [chooseOutput, dif_pos h]
  exact Nat.find_spec h

theorem chooseOutput_le {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hz : preferred family xs ys z) :
    chooseOutput family xs ys ≤ z := by
  classical
  unfold chooseOutput
  split_ifs with h
  · exact Nat.find_min' h hz
  · exact False.elim (h ⟨z, hz⟩)

theorem output_ne_input_up_to {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s ≤ t) :
    run (generator family) input t ≠ input s := by
  rw [run_eq]
  intro heq
  have hnot := chooseOutput_not_used family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (generator family) input i)
  apply hnot
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, Finset.mem_univ _, heq.symm⟩

theorem output_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (run (generator family) input) := by
  intro s t hst
  apply le_antisymm
  · by_contra hnot
    have hlt : t < s := Nat.lt_of_not_ge hnot
    rw [run_eq] at hst
    have hnotused := chooseOutput_not_used family
      (fun i : Fin (s + 1) => input i)
      (fun i : Fin s => run (generator family) input i)
    apply hnotused
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨⟨t, hlt⟩, Finset.mem_univ _, hst.symm⟩
  · by_contra hnot
    have hlt : s < t := Nat.lt_of_not_ge hnot
    rw [run_eq (generator family) input t] at hst
    have hnotused := chooseOutput_not_used family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (generator family) input i)
    apply hnotused
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨⟨s, hlt⟩, Finset.mem_univ _, hst⟩

theorem range_run_eq_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range (run (generator family) input) =
      GenLimit.GeneratorFirst input (run (generator family) input) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, rfl, ?_⟩
    intro s hs
    exact (output_ne_input_up_to family input t s hs).symm
  · rintro ⟨t, ht, -⟩
    exact ⟨t, ht⟩

noncomputable def badWitness {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  by_cases h : GenLimit.Generic.StreamIn input (family j)
  · exact 0
  · exact Nat.find (by
      obtain ⟨z, ⟨t, rfl⟩, hz⟩ := Set.not_subset.mp h
      exact ⟨t, hz⟩)

noncomputable def stabilizationTime {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) : ℕ :=
  (Finset.univ.image (badWitness family input)).max'
    (by
      haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
      obtain ⟨j⟩ := inferInstanceAs (Nonempty (Fin m))
      exact ⟨badWitness family input j, Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, rfl⟩⟩)

theorem le_stabilizationTime {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) (j : Fin m) :
    badWitness family input j ≤ stabilizationTime hm family input := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem active_iff_streamIn {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream)
    {t : ℕ} (ht : stabilizationTime hm family input ≤ t) (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  classical
  constructor
  · intro hp z hz
    obtain ⟨s, rfl⟩ := hz
    by_cases h : GenLimit.Generic.StreamIn input (family j)
    · exact h ⟨s, rfl⟩
    · have hw : input (badWitness family input j) ∉ family j := by
        simp only [badWitness, h, ↓reduceDIte]
        exact Nat.find_spec (by
          obtain ⟨z, ⟨q, rfl⟩, hz⟩ := Set.not_subset.mp h
          exact ⟨q, hz⟩)
      have hle : badWitness family input j ≤ t :=
        le_trans (le_stabilizationTime hm family input j) ht
      exact False.elim (hw (hp ⟨_, Nat.lt_succ_iff.mpr hle⟩))
  · intro hs i
    exact hs ⟨i, rfl⟩

theorem activeCore_eq_informationCore {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream)
    {t : ℕ} (ht : stabilizationTime hm family input ≤ t) :
    activeCore family (fun i : Fin (t + 1) => input i) =
      Stage3Case017.informationCore family input := by
  ext z
  simp only [activeCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((active_iff_streamIn hm family input ht j).2 hj)
  · intro hz j hj
    exact hz j ((active_iff_streamIn hm family input ht j).1 hj)

theorem preferred_of_core_not_announced {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) {z t : ℕ}
    (ht : stabilizationTime hm family input ≤ t)
    (hz : z ∈ Stage3Case017.informationCore family input)
    (hx : z ∉ Set.range input)
    (hy : z ∉ Set.range (run (generator family) input)) :
    preferred family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (generator family) input i) z := by
  constructor
  · rw [activeCore_eq_informationCore hm family input ht]
    exact hz
  · intro hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hu
      exact hx ⟨i, hi⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hu
      exact hy ⟨i, hi⟩

theorem core_element_announced {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) {z : ℕ}
    (hz : z ∈ Stage3Case017.informationCore family input) :
    z ∈ Set.range input ∪ Set.range (run (generator family) input) := by
  classical
  by_cases hx : z ∈ Set.range input
  · exact Set.mem_union_left _ hx
  · apply Set.mem_union_right
    by_contra hy
    let T := stabilizationTime hm family input
    let f : Fin (z + 2) → Fin (z + 1) := fun i =>
      ⟨run (generator family) input (T + i), Nat.lt_succ_iff.mpr (by
        rw [run_eq]
        exact chooseOutput_le family
          (fun q : Fin (T + i + 1) => input q)
          (fun q : Fin (T + i) => run (generator family) input q)
          (preferred_of_core_not_announced hm family input
            (show T ≤ T + i by omega) hz hx hy))⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      have htimes := output_injective family input (congrArg Fin.val hij)
      omega
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hcard
    omega

theorem core_covered_by_first {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) :
    Stage3Case017.informationCore family input ⊆
      GenLimit.AdversaryFirst input (run (generator family) input) ∪
        Set.range (run (generator family) input) := by
  intro z hz
  rcases core_element_announced hm family input hz with hx | hy
  · have hfirst := GenLimit.range_subset_first_announcements
      input (run (generator family) input) hx
    rcases hfirst with ha | hg
    · exact Set.mem_union_left _ ha
    · apply Set.mem_union_right
      rw [range_run_eq_generatorFirst family input]
      exact hg
  · exact Set.mem_union_right _ hy

theorem informationCore_subset {m : ℕ} {family : Fin m → Language}
    {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    Stage3Case017.informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

theorem eventual_output_in_core {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    ∀ t, stabilizationTime hm family input ≤ t →
      run (generator family) input t ∈
        Stage3Case017.informationCore family input := by
  intro t ht
  rw [run_eq]
  have hex : ∃ z, preferred family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (generator family) input i) z := by
    obtain ⟨z, hzcore, hzused⟩ :=
      hcore.exists_not_mem_finset
        (usedAt (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => run (generator family) input i))
    exact ⟨z, by
      constructor
      · rw [activeCore_eq_informationCore hm family input ht]
        exact hzcore
      · exact hzused⟩
  have hp := chooseOutput_preferred family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (generator family) input i) hex
  change chooseOutput family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (generator family) input i) ∈
      Stage3Case017.informationCore family input
  rw [← activeCore_eq_informationCore hm family input ht]
  exact hp.1

theorem novel_generation {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (run (generator family) input)
      (family j) := by
  refine ⟨stabilizationTime hm family input, ?_⟩
  intro t ht
  have hmemcore := eventual_output_in_core hm family input hcore t ht
  refine ⟨informationCore_subset hj hmemcore, ?_, ?_⟩
  · intro hsamp
    rw [GenLimit.mem_sample_iff] at hsamp
    obtain ⟨s, hs, heq⟩ := hsamp
    exact output_ne_input_up_to family input t s (by omega) heq.symm
  · intro s hs heq
    exact (Nat.ne_of_lt hs) (output_injective family input heq)

noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

noncomputable def partner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (z : ℕ) : ℕ :=
  run (generator family) input (firstInputTime input z - 1)

noncomputable def earlySet {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) : Finset ℕ :=
  (Finset.range (stabilizationTime hm family input + 1)).image input

theorem firstInputTime_spec {input : Stream} {z : ℕ}
    (hz : z ∈ Set.range input) : input (firstInputTime input z) = z := by
  classical
  simp only [firstInputTime, hz, ↓reduceDIte]
  exact Nat.find_spec hz

theorem firstInputTime_min {input : Stream} {z s : ℕ}
    (hz : z ∈ Set.range input) (hs : input s = z) :
    firstInputTime input z ≤ s := by
  classical
  simp only [firstInputTime, hz, ↓reduceDIte]
  exact Nat.find_min' hz hs

theorem attacker_implies_input {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) {z : ℕ}
    (hz : z ∈ Stage3Case017.informationCore family input \ Set.range (run (generator family) input)) :
    z ∈ Set.range input := by
  rcases core_element_announced hm family input hz.1 with hx | hy
  · exact hx
  · exact False.elim (hz.2 hy)

theorem core_infinite_of_input_injective {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hinput : Function.Injective input) :
    (Stage3Case017.informationCore family input).Infinite := by
  apply (Set.infinite_range_of_injective hinput).mono
  intro z hz j hj
  obtain ⟨t, rfl⟩ := hz
  exact hj ⟨t, rfl⟩

theorem partner_properties {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream)
    (hinput : Function.Injective input) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker
      (family j)
      (Stage3Case017.informationCore family input \ Set.range (run (generator family) input))
      ∅ (earlySet hm family input)) :
    partner family input z ∈
        Set.range (run (generator family) input) ∩
          Stage3Case017.informationCore family input ∧
      partner family input z < z := by
  classical
  have hzatt : z ∈ Stage3Case017.informationCore family input \ Set.range (run (generator family) input) := hz.1.1
  have hzinput := attacker_implies_input hm family input hzatt
  let q := firstInputTime input z
  have hqspec : input q = z := firstInputTime_spec hzinput
  have hqT : stabilizationTime hm family input < q := by
    by_contra hnot
    have hmem : z ∈ earlySet hm family input := by
      apply Finset.mem_image.mpr
      exact ⟨q, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hnot)), hqspec⟩
    exact hz.2 (Set.mem_union_left _ hmem)
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hqT
  have hpref : preferred family
      (fun i : Fin ((q - 1) + 1) => input i)
      (fun i : Fin (q - 1) => run (generator family) input i) z := by
    constructor
    · rw [activeCore_eq_informationCore hm family input
        (show stabilizationTime hm family input ≤ q - 1 by omega)]
      exact hzatt.1
    · intro hu
      rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hu
        have hqi := firstInputTime_min hzinput hi
        omega
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hu
        exact hzatt.2 ⟨i, hi⟩
  have hle : partner family input z ≤ z := by
    unfold partner
    rw [run_eq]
    exact chooseOutput_le family
      (fun i : Fin ((q - 1) + 1) => input i)
      (fun i : Fin (q - 1) => run (generator family) input i) hpref
  have hmemcore : partner family input z ∈
      Stage3Case017.informationCore family input := by
    unfold partner
    exact eventual_output_in_core hm family input
      (core_infinite_of_input_injective family input hinput)
      (q - 1) (by omega)
  constructor
  · exact ⟨⟨q - 1, rfl⟩, hmemcore⟩
  · exact lt_of_le_of_ne hle (fun heq => hzatt.2 ⟨q - 1, heq⟩)

theorem partner_injective_on {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream)
    (hinput : Function.Injective input) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    Set.InjOn (partner family input)
      (GenLimit.PatientScope.ordinaryAttacker
        (family j)
        (Stage3Case017.informationCore family input \ Set.range (run (generator family) input))
        ∅ (earlySet hm family input)) := by
  intro x hx y hy hxy
  have hxatt := hx.1.1
  have hyatt := hy.1.1
  have hxinput := attacker_implies_input hm family input hxatt
  have hyinput := attacker_implies_input hm family input hyatt
  have htimes := output_injective family input hxy
  have hxT : stabilizationTime hm family input < firstInputTime input x := by
    by_contra hnot
    exact hx.2 (Set.mem_union_left _ (Finset.mem_image.mpr
      ⟨firstInputTime input x, Finset.mem_range.mpr
        (Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hnot)), firstInputTime_spec hxinput⟩))
  have hyT : stabilizationTime hm family input < firstInputTime input y := by
    by_contra hnot
    exact hy.2 (Set.mem_union_left _ (Finset.mem_image.mpr
      ⟨firstInputTime input y, Finset.mem_range.mpr
        (Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hnot)), firstInputTime_spec hyinput⟩))
  have hq : firstInputTime input x = firstInputTime input y := by
    unfold partner at htimes
    omega
  calc
    x = input (firstInputTime input x) := (firstInputTime_spec hxinput).symm
    _ = input (firstInputTime input y) := by rw [hq]
    _ = y := firstInputTime_spec hyinput

noncomputable def densityCertificate {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream)
    (hinput : Function.Injective input) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.PartialEnumerationCertificate where
  target := family j
  enumerated := Stage3Case017.informationCore family input
  enumerated_subset_target := informationCore_subset hj
  attacker := Stage3Case017.informationCore family input \ Set.range (run (generator family) input)
  defender := Set.range (run (generator family) input)
  output := run (generator family) input
  output_range := rfl
  output_injective := output_injective family input
  validFrom := stabilizationTime hm family input
  eventual_target := fun t ht => informationCore_subset hj
    (eventual_output_in_core hm family input
      (core_infinite_of_input_injective family input hinput) t ht)
  enumerated_covered := by
    intro z hz
    by_cases hy : z ∈ Set.range (run (generator family) input)
    · exact Set.mem_union_right _ hy
    · exact Set.mem_union_left _ ⟨hz, hy⟩
  attacker_subset_target := fun z hz => informationCore_subset hj hz.1
  ownership_disjoint := Set.disjoint_sdiff_left
  earlyAttacker := earlySet hm family input
  switchLoss := ∅
  switchLoss_subset := by simp
  partner := partner family input
  partner_mem := fun z hz => by
    have hp := (partner_properties hm family input hinput j hj hz).1
    exact ⟨hp.1, informationCore_subset hj hp.2⟩
  partner_lt := fun z hz => (partner_properties hm family input hinput j hj hz).2
  partner_injective := partner_injective_on hm family input hinput j hj
  switchBudget := fun _ => 0
  switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall (fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _))
  · exact Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  · have hratio : ∀ n,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
      intro n
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
    exact Filter.isCoboundedUnder_ge_of_le Filter.atTop hratio

theorem missing_core_subset_output {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      Set.range (run (generator family) input) ∩ family j := by
  intro z hz
  have hann := core_element_announced hm family input hz.1
  rcases hann with hx | hy
  · exact False.elim (hz.2 hx)
  · exact ⟨hy, informationCore_subset hj hz.1⟩

theorem half_density_bound {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hinput : Function.Injective input)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (Set.range (run (generator family) input) ∩ family j) (family j) := by
  let P := densityCertificate hm family input hinput j hj
  have h := GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17
    P (hfamily j) (by
      intro n
      simp [P, densityCertificate, GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset,
        GenLimit.PatientScope.PartialEnumerationCertificate.targetCount])
  simpa [P, densityCertificate,
    GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity] using h

theorem density_bound {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hinput : Function.Injective input)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input \ Set.range input)
          (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input (run (generator family) input) ∩
            family j) (family j) := by
  rw [← range_run_eq_generatorFirst family input]
  apply max_le
  · exact half_density_bound hm family hfamily input hinput j hj
  · apply relativeLowerDensity_mono
      (missing_core_subset_output hm family input j hj)
    exact Set.inter_subset_right

end Case017Proof

open Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨generator family, ?_⟩
  intro input hinput _ hcore
  refine ⟨run (generator family) input, follows_run _ _, ?_⟩
  intro j hj
  exact ⟨novel_generation hm family input hcore j hj,
    density_bound hm family hfamily input hinput j hj⟩
