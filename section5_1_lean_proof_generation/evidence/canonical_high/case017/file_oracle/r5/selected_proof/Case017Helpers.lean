import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Stage3Case017Proof

abbrev Language := Stage3Case017.Language
abbrev Stream := Stage3Case017.Stream
abbrev OnlineGenerator := Stage3Case017.OnlineGenerator

noncomputable def prefixCompatible {t m : ℕ}
    (xs : Fin t → ℕ) (family : Fin m → Language) (j : Fin m) : Prop :=
  ∀ i, xs i ∈ family j

noncomputable def currentCore {t m : ℕ}
    (family : Fin m → Language) (xs : Fin t → ℕ) : Language :=
  {z | ∀ j, prefixCompatible xs family j → z ∈ family j}

noncomputable def usableCore {t m : ℕ}
    (family : Fin m → Language) (xs : Fin t → ℕ) : Language := by
  classical
  exact if (currentCore family xs).Infinite then currentCore family xs else Set.univ

noncomputable def used {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs ∪ GenLimit.Generic.sequenceSample ys

noncomputable def leastFresh (S : Language) (U : Finset ℕ) : ℕ :=
  sInf {z | z ∈ S ∧ z ∉ U}

noncomputable def familyGenerator {m : ℕ}
    (family : Fin m → Language) : OnlineGenerator :=
  fun _ xs ys => leastFresh (usableCore family xs) (used xs ys)

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

@[simp] theorem trajectory_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory]

 theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory_eq gen input t

 theorem usableCore_infinite {t m : ℕ}
    (family : Fin m → Language) (xs : Fin t → ℕ) :
    (usableCore family xs).Infinite := by
  classical
  unfold usableCore
  split_ifs with h
  · exact h
  · exact Set.infinite_univ

 theorem available_nonempty {S : Language} (hS : S.Infinite) (U : Finset ℕ) :
    ({z | z ∈ S ∧ z ∉ U} : Set ℕ).Nonempty := by
  obtain ⟨z, hzS, hzU⟩ := hS.exists_not_mem_finset U
  exact ⟨z, hzS, hzU⟩

 theorem leastFresh_mem {S : Language} (hS : S.Infinite) (U : Finset ℕ) :
    leastFresh S U ∈ S := by
  have hne := available_nonempty hS U
  exact (Nat.sInf_mem hne).1

 theorem leastFresh_not_mem {S : Language} (hS : S.Infinite) (U : Finset ℕ) :
    leastFresh S U ∉ U := by
  have hne := available_nonempty hS U
  exact (Nat.sInf_mem hne).2

 theorem leastFresh_le {S : Language} (U : Finset ℕ) {z : ℕ}
    (hzS : z ∈ S) (hzU : z ∉ U) :
    leastFresh S U ≤ z := by
  exact Nat.sInf_le ⟨hzS, hzU⟩

 theorem familyGenerator_mem_usable {t m : ℕ}
    (family : Fin m → Language) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    familyGenerator family t xs ys ∈ usableCore family xs := by
  exact leastFresh_mem (usableCore_infinite family xs) (used xs ys)

 theorem familyGenerator_fresh_input {t m : ℕ}
    (family : Fin m → Language) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (i : Fin (t + 1)) :
    familyGenerator family t xs ys ≠ xs i := by
  intro h
  have hnot := leastFresh_not_mem (usableCore_infinite family xs) (used xs ys)
  apply hnot
  rw [show leastFresh (usableCore family xs) (used xs ys) = xs i by
    simpa [familyGenerator] using h]
  exact Finset.mem_union_left _
    (GenLimit.Generic.mem_sequenceSample_iff.mpr ⟨i, rfl⟩)

 theorem familyGenerator_fresh_output {t m : ℕ}
    (family : Fin m → Language) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (i : Fin t) :
    familyGenerator family t xs ys ≠ ys i := by
  intro h
  have hnot := leastFresh_not_mem (usableCore_infinite family xs) (used xs ys)
  apply hnot
  rw [show leastFresh (usableCore family xs) (used xs ys) = ys i by
    simpa [familyGenerator] using h]
  exact Finset.mem_union_right _
    (GenLimit.Generic.mem_sequenceSample_iff.mpr ⟨i, rfl⟩)

 theorem familyGenerator_le_available {t m : ℕ}
    (family : Fin m → Language) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    {z : ℕ} (hz : z ∈ usableCore family xs)
    (hx : ∀ i, z ≠ xs i) (hy : ∀ i, z ≠ ys i) :
    familyGenerator family t xs ys ≤ z := by
  apply leastFresh_le (used xs ys) hz
  intro hmem
  rcases Finset.mem_union.mp hmem with hmem | hmem
  · obtain ⟨i, hi⟩ := GenLimit.Generic.mem_sequenceSample_iff.mp hmem
    exact hx i hi.symm
  · obtain ⟨i, hi⟩ := GenLimit.Generic.mem_sequenceSample_iff.mp hmem
    exact hy i hi.symm

 theorem eventually_currentCore_eq {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      currentCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input := by
  classical
  have hj : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      (prefixCompatible (fun i : Fin (t + 1) => input i) family j ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hstream : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, ?_⟩
      intro t _
      constructor
      · intro _
        exact hstream
      · intro _ i
        exact hstream ⟨i, rfl⟩
    · simp only [GenLimit.Generic.StreamIn, Set.range_subset_iff] at hstream
      push_neg at hstream
      obtain ⟨q, hq⟩ := hstream
      refine ⟨q, ?_⟩
      intro t ht
      constructor
      · intro hp
        exfalso
        exact hq (hp ⟨q, Nat.lt_succ_of_le ht⟩)
      · intro hs
        exact False.elim (hq (hs ⟨q, rfl⟩))
  choose T hT using hj
  refine ⟨Finset.univ.sup T, ?_⟩
  intro t ht
  ext z
  simp only [currentCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hs
    apply hz j
    exact (hT j t (le_trans (Finset.le_sup (Finset.mem_univ j)) ht)).2 hs
  · intro hz j hp
    apply hz j
    exact (hT j t (le_trans (Finset.le_sup (Finset.mem_univ j)) ht)).1 hp

 theorem eventually_usableCore_eq {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      usableCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_currentCore_eq family input
  refine ⟨T, ?_⟩
  intro t ht
  rw [usableCore, hT t ht, if_pos hcore]


 theorem trajectory_fresh_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s ≤ t) :
    trajectory (familyGenerator family) input t ≠ input s := by
  rw [trajectory_eq]
  exact familyGenerator_fresh_input family _ _ ⟨s, Nat.lt_succ_of_le hs⟩

 theorem trajectory_fresh_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s < t) :
    trajectory (familyGenerator family) input t ≠
      trajectory (familyGenerator family) input s := by
  rw [trajectory_eq]
  exact familyGenerator_fresh_output family _ _ ⟨s, hs⟩

 theorem trajectory_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Function.Injective (trajectory (familyGenerator family) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact trajectory_fresh_output family input t s hlt hst.symm
  · exact trajectory_fresh_output family input s t hgt hst

 theorem core_subset_target {m : ℕ} {family : Fin m → Language}
    {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    Stage3Case017.informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

 theorem eventual_output_mem_core {m : ℕ} (family : Fin m → Language)
    (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      trajectory (familyGenerator family) input t ∈
        Stage3Case017.informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_usableCore_eq family input hcore
  refine ⟨T, ?_⟩
  intro t ht
  rw [trajectory_eq]
  have hmem := familyGenerator_mem_usable family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (familyGenerator family) input i)
  rwa [hT t ht] at hmem

 theorem novelGeneratesInLimit {m : ℕ} (family : Fin m → Language)
    (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (familyGenerator family) input) (family j) := by
  obtain ⟨T, hT⟩ := eventual_output_mem_core family input hcore
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨core_subset_target hj (hT t ht), ?_, ?_⟩
  · intro hsample
    obtain ⟨s, hs, heq⟩ := GenLimit.mem_sample_iff.mp hsample
    exact trajectory_fresh_input family input t s (Nat.le_of_lt_succ hs) heq.symm
  · intro s hs
    exact (trajectory_fresh_output family input t s hs).symm

 theorem core_element_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ Stage3Case017.informationCore family input) :
    z ∈ Set.range input ∨
      z ∈ Set.range (trajectory (familyGenerator family) input) := by
  classical
  by_contra hnot
  push_neg at hnot
  obtain ⟨hnotInput, hnotOutput⟩ := hnot
  obtain ⟨T, hT⟩ := eventually_usableCore_eq family input hcore
  let tail : ℕ → ℕ := fun q => trajectory (familyGenerator family) input (T + q)
  have htail_inj : Function.Injective tail := by
    intro a b hab
    have := trajectory_injective family input hab
    omega
  have htail_le : ∀ q, tail q ≤ z := by
    intro q
    have hstable :
        usableCore family (fun i : Fin (T + q + 1) => input i) =
          Stage3Case017.informationCore family input := hT (T + q) (by omega)
    dsimp [tail]
    rw [trajectory_eq]
    apply familyGenerator_le_available family
    · rwa [hstable]
    · intro i heq
      exact hnotInput ⟨i, heq.symm⟩
    · intro i heq
      exact hnotOutput ⟨i, heq.symm⟩
  have hrangeInfinite : (Set.range tail).Infinite :=
    Set.infinite_range_of_injective htail_inj
  have hrangeSubset : Set.range tail ⊆ Set.Iic z := by
    rintro _ ⟨q, rfl⟩
    exact htail_le q
  exact hrangeInfinite ((Set.finite_Iic z).subset hrangeSubset)

 theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  intro z hz
  have hann := core_element_announced family input hcore hz.1
  rcases hann with hin | hout
  · exact False.elim (hz.2 hin)
  · obtain ⟨t, ht⟩ := hout
    refine ⟨t, ht, ?_⟩
    intro s _ his
    exact hz.2 ⟨s, his⟩

 theorem core_subset_first_announcements {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input ⊆
      GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∪
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  intro z hz
  by_cases hin : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input
      (trajectory (familyGenerator family) input) hin
  · exact Set.mem_union_right _
      (core_diff_range_subset_generatorFirst family input hcore ⟨hz, hin⟩)


noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ :=
  sInf {t | input t = z}

 theorem firstInput_spec {input : Stream} {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  exact Nat.sInf_mem hz

 theorem firstInput_le {input : Stream} {z t : ℕ} (ht : input t = z) :
    firstInput input z ≤ t := by
  exact Nat.sInf_le ht

 theorem firstInput_injective_on_range {input : Stream} :
    Set.InjOn (firstInput input) (Set.range input) := by
  intro z hz w hw hzw
  rw [← firstInput_spec hz, ← firstInput_spec hw, hzw]

 theorem output_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    trajectory (familyGenerator family) input t ∈
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hs
  exact (trajectory_fresh_input family input t s hs).symm

 theorem firstInput_no_earlier_output {input output : Stream} {z : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) :
    ∀ s, s < firstInput input z → output s ≠ z := by
  obtain ⟨t, ht, hbefore⟩ := hz
  have hfirst : firstInput input z ≤ t := firstInput_le ht
  intro s hs
  exact hbefore s (lt_of_lt_of_le hs hfirst)

 theorem prefix_partition {m : ℕ} (family : Fin m → Language)
    (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount
        (GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∩
          Stage3Case017.informationCore family input) n +
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
          Stage3Case017.informationCore family input) n =
      GenLimit.PatientScope.prefixCount
        (Stage3Case017.informationCore family input) n := by
  classical
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n
  let E := GenLimit.PatientScope.prefixFinset
    (Stage3Case017.informationCore family input) n
  have hunion : A ∪ D = E := by
    ext z
    simp only [A, D, E, Finset.mem_union, GenLimit.PatientScope.mem_prefixFinset,
      Set.mem_inter_iff]
    constructor
    · rintro (⟨hzn, -, hz⟩ | ⟨hzn, -, hz⟩)
      · exact ⟨hzn, hz⟩
      · exact ⟨hzn, hz⟩
    · intro hz
      have hown := core_subset_first_announcements family input hcore hz.2
      rcases hown with hA | hD
      · exact Or.inl ⟨hz.1, hA, hz.2⟩
      · exact Or.inr ⟨hz.1, hD, hz.2⟩
  have hdisj : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro z hzA hzD
    have hzA' := (GenLimit.PatientScope.mem_prefixFinset.mp hzA).2.1
    have hzD' := (GenLimit.PatientScope.mem_prefixFinset.mp hzD).2.1
    exact Set.disjoint_left.mp
      (GenLimit.adversaryFirst_disjoint_generatorFirst input
        (trajectory (familyGenerator family) input)) hzA' hzD'
  change A.card + D.card = E.card
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

 theorem adversary_prefix_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (T : ℕ)
    (hstable : ∀ t, T ≤ t →
      usableCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input)
    (n : ℕ) :
    GenLimit.PatientScope.prefixCount
        (GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∩
          Stage3Case017.informationCore family input) n ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
          Stage3Case017.informationCore family input) n + T + 1 := by
  classical
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n
  let early := A.filter (fun z => firstInput input z < T)
  let late := A.filter (fun z => T ≤ firstInput input z)
  have hsplit : early ∪ late = A := by
    ext z
    simp only [early, late, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
    · intro hz
      by_cases hzt : firstInput input z < T
      · exact Or.inl ⟨hz, hzt⟩
      · exact Or.inr ⟨hz, Nat.le_of_not_gt hzt⟩
  have hdisj : Disjoint early late := by
    rw [Finset.disjoint_left]
    intro z hzE hzL
    exact (Finset.mem_filter.mp hzL).2.not_lt (Finset.mem_filter.mp hzE).2
  have hearly : early.card ≤ T := by
    have hmap : Set.MapsTo (firstInput input) (↑early : Set ℕ) (↑(Finset.range T) : Set ℕ) := by
      intro z hz
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2
    exact le_trans
      (Finset.card_le_card_of_injOn (firstInput input) hmap (by
        intro z hz w hw hzw
        apply firstInput_injective_on_range
        · obtain ⟨q, hq, -⟩ :=
            (GenLimit.PatientScope.mem_prefixFinset.mp
              (Finset.mem_filter.mp hz).1).2.1
          exact ⟨q, hq⟩
        · obtain ⟨q, hq, -⟩ :=
            (GenLimit.PatientScope.mem_prefixFinset.mp
              (Finset.mem_filter.mp hw).1).2.1
          exact ⟨q, hq⟩
        · exact hzw))
      (by simp)
  have hlate : late.card ≤ D.card + 1 := by
    by_cases hl : late.Nonempty
    · let times := late.image (firstInput input)
      have htimes : times.Nonempty := hl.image _
      let qmax := times.max' htimes
      have hqmem : qmax ∈ times := Finset.max'_mem times htimes
      obtain ⟨zmax, hzmaxLate, hzmaxTime⟩ := Finset.mem_image.mp hqmem
      have hzmaxA : zmax ∈ A := (Finset.mem_filter.mp hzmaxLate).1
      have hzmaxAdv : zmax ∈ GenLimit.AdversaryFirst input
          (trajectory (familyGenerator family) input) :=
        (GenLimit.PatientScope.mem_prefixFinset.mp hzmaxA).2.1
      have hmap : Set.MapsTo
          (fun z => trajectory (familyGenerator family) input (firstInput input z))
          (↑(late.erase zmax) : Set ℕ) (↑D : Set ℕ) := by
        intro z hzErase
        have hzLate := (Finset.mem_erase.mp hzErase).2
        have hzNe := (Finset.mem_erase.mp hzErase).1
        have hzA : z ∈ A := (Finset.mem_filter.mp hzLate).1
        have hzAdv : z ∈ GenLimit.AdversaryFirst input
            (trajectory (familyGenerator family) input) :=
          (GenLimit.PatientScope.mem_prefixFinset.mp hzA).2.1
        have hzCore : z ∈ Stage3Case017.informationCore family input :=
          (GenLimit.PatientScope.mem_prefixFinset.mp hzA).2.2
        have hzBound : z < n := (GenLimit.PatientScope.mem_prefixFinset.mp hzA).1
        have hzTimeMem : firstInput input z ∈ times :=
          Finset.mem_image.mpr ⟨z, hzLate, rfl⟩
        have hzTimeLe : firstInput input z ≤ qmax := Finset.le_max' times _ hzTimeMem
        have hzTimeLt : firstInput input z < qmax := by
          apply lt_of_le_of_ne hzTimeLe
          intro heq
          apply hzNe
          have hzRange : z ∈ Set.range input := by
            obtain ⟨q, hq, -⟩ := hzAdv
            exact ⟨q, hq⟩
          have hzmaxRange : zmax ∈ Set.range input := by
            obtain ⟨q, hq, -⟩ := hzmaxAdv
            exact ⟨q, hq⟩
          rw [← firstInput_spec hzRange, ← firstInput_spec hzmaxRange,
            heq, hzmaxTime]
        have hzmaxCore : zmax ∈ Stage3Case017.informationCore family input :=
          (GenLimit.PatientScope.mem_prefixFinset.mp hzmaxA).2.2
        have hzmaxBound : zmax < n :=
          (GenLimit.PatientScope.mem_prefixFinset.mp hzmaxA).1
        have hzmaxNoInput : ∀ i : Fin (firstInput input z + 1), zmax ≠ input i := by
          intro i heq
          have hfirstLe : firstInput input zmax ≤ i := firstInput_le heq.symm
          rw [hzmaxTime] at hfirstLe
          omega
        have hzmaxNoOutput : ∀ i : Fin (firstInput input z),
            zmax ≠ trajectory (familyGenerator family) input i := by
          intro i heq
          exact (firstInput_no_earlier_output hzmaxAdv i
            (by rw [hzmaxTime]; omega)) heq.symm
        have htimeT : T ≤ firstInput input z := (Finset.mem_filter.mp hzLate).2
        have houtLe :
            trajectory (familyGenerator family) input (firstInput input z) ≤ zmax := by
          rw [trajectory_eq]
          apply familyGenerator_le_available family
          · rw [hstable _ htimeT]
            exact hzmaxCore
          · exact hzmaxNoInput
          · exact hzmaxNoOutput
        apply GenLimit.PatientScope.mem_prefixFinset.mpr
        refine ⟨lt_of_le_of_lt houtLe hzmaxBound, output_generatorFirst family input _, ?_⟩
        have houtCore := familyGenerator_mem_usable family
          (fun i : Fin (firstInput input z + 1) => input i)
          (fun i : Fin (firstInput input z) =>
            trajectory (familyGenerator family) input i)
        rw [hstable _ htimeT] at houtCore
        change trajectory (familyGenerator family) input (firstInput input z) ∈
          Stage3Case017.informationCore family input
        rw [trajectory_eq]
        exact houtCore
      have hinjMap : Set.InjOn
          (fun z => trajectory (familyGenerator family) input (firstInput input z))
          (↑(late.erase zmax) : Set ℕ) := by
        intro z _ w _ hzw
        apply firstInput_injective_on_range
        · obtain ⟨q, hq, -⟩ :=
            (GenLimit.PatientScope.mem_prefixFinset.mp
              (Finset.mem_filter.mp (Finset.mem_erase.mp ‹z ∈ (↑(late.erase zmax) : Set ℕ)›).2).1).2.1
          exact ⟨q, hq⟩
        · obtain ⟨q, hq, -⟩ :=
            (GenLimit.PatientScope.mem_prefixFinset.mp
              (Finset.mem_filter.mp (Finset.mem_erase.mp ‹w ∈ (↑(late.erase zmax) : Set ℕ)›).2).1).2.1
          exact ⟨q, hq⟩
        · exact trajectory_injective family input hzw
      have herase := Finset.card_le_card_of_injOn _ hmap hinjMap
      have hzmaxMem : zmax ∈ late := hzmaxLate
      have heraseCard := Finset.card_erase_add_one hzmaxMem
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty] at hl
      simp [hl]
  change A.card ≤ D.card + T + 1
  have hcard : early.card + late.card = A.card := by
    rw [← hsplit, Finset.card_union_of_disjoint hdisj]
  omega


 theorem core_count_le_twice_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    ∃ r, ∀ n,
      GenLimit.PatientScope.prefixCount
          (Stage3Case017.informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
            family j) n + r := by
  obtain ⟨T, hT⟩ := eventually_usableCore_eq family input hcore
  refine ⟨T + 1, ?_⟩
  intro n
  let A := GenLimit.PatientScope.prefixCount
    (GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n
  let G := GenLimit.PatientScope.prefixCount
    (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
      Stage3Case017.informationCore family input) n
  let D := GenLimit.PatientScope.prefixCount
    (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
      family j) n
  have hpart : A + G = GenLimit.PatientScope.prefixCount
      (Stage3Case017.informationCore family input) n :=
    prefix_partition family input hcore n
  have hA : A ≤ G + T + 1 :=
    adversary_prefix_bound family input hinj hcore T hT n
  have hGD : G ≤ D := by
    apply GenLimit.PatientScope.prefixCount_mono
    intro z hz
    exact ⟨hz.1, core_subset_target hj hz.2⟩
  dsimp only [A, G, D] at hpart hA hGD ⊢
  omega

 theorem half_density_bound {m : ℕ}
    (family : Fin m → Language) (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
          family j) (family j) := by
  obtain ⟨r, hcount⟩ :=
    core_count_le_twice_generatorFirst family input hinj hcore hj
  apply GenLimit.PatientScope.partialDensity_of_counting
    (GenLimit.PatientScope.prefixCount (family j))
    (GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input))
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
        family j)) r
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hfamily j)
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono (core_subset_target hj) n
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have h := hcount n
    omega

 theorem relativeLowerDensity_mono_left {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · exact isBoundedUnder_of_eventually_ge <|
      Filter.Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hle : ∀ n,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
      intro n
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
    exact isCoboundedUnder_ge_of_le Filter.atTop hle

 theorem missing_core_density_bound {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
          family j) (family j) := by
  apply relativeLowerDensity_mono_left
  · intro z hz
    exact ⟨core_diff_range_subset_generatorFirst family input hcore hz,
      core_subset_target hj hz.1⟩
  · exact Set.inter_subset_right

 theorem density_bound {m : ℕ}
    (family : Fin m → Language) (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input \ Set.range input) (family j)) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩
          family j) (family j) := by
  exact max_le
    (half_density_bound family hfamily input hinj hcore hj)
    (missing_core_density_bound family input hcore hj)

end Stage3Case017Proof
