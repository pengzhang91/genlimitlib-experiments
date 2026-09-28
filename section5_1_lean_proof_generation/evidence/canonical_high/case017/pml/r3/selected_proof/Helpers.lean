import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Case017Proof

open Stage3Case017

noncomputable def finiteValues {n : ℕ} (xs : Fin n → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs

noncomputable def usedValues {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : Finset ℕ :=
  finiteValues input ∪ finiteValues output

def currentCore {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, input i ∈ family j) → z ∈ family j}

noncomputable def leastFresh (S : Language) (hS : S.Infinite)
    (used : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (hS.exists_notMem_finset used)

theorem leastFresh_spec (S : Language) (hS : S.Infinite)
    (used : Finset ℕ) :
    leastFresh S hS used ∈ S ∧ leastFresh S hS used ∉ used := by
  classical
  exact Nat.find_spec (hS.exists_notMem_finset used)

theorem leastFresh_le (S : Language) (hS : S.Infinite)
    (used : Finset ℕ) {z : ℕ} (hzS : z ∈ S) (hz : z ∉ used) :
    leastFresh S hS used ≤ z := by
  classical
  exact Nat.find_min' (hS.exists_notMem_finset used) ⟨hzS, hz⟩

noncomputable def onlineGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t input output =>
    let used := usedValues input output
    if hcore : (currentCore family input).Infinite then
      leastFresh (currentCore family input) hcore used
    else
      leastFresh Set.univ Set.infinite_univ used

noncomputable def histories (gen : OnlineGenerator) (input : Stream) :
    (n : ℕ) → (Fin n → ℕ)
  | 0 => fun i => Fin.elim0 i
  | n + 1 => fun i =>
      if h : i.val < n then
        histories gen input n ⟨i.val, h⟩
      else
        gen n (fun j => input j) (histories gen input n)

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => histories gen input (t + 1) ⟨t, Nat.lt_succ_self t⟩

theorem histories_eq_trajectory (gen : OnlineGenerator) (input : Stream)
    {n : ℕ} (i : Fin n) :
    histories gen input n i = trajectory gen input i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      change (if h : i.val < n then histories gen input n ⟨i.val, h⟩
        else gen n (fun j => input j) (histories gen input n)) = _
      split
      · exact ih ⟨i.val, by assumption⟩
      · have hi : i.val = n := by omega
        rw [hi]
        unfold trajectory
        rw [histories]
        simp

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory, histories]
  simp only [lt_self_iff_false, ↓reduceDIte]
  congr 1
  funext i
  exact histories_eq_trajectory gen input i

theorem onlineGenerator_fresh {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    onlineGenerator family t input output ∉ usedValues input output := by
  classical
  simp only [onlineGenerator]
  split <;> exact (leastFresh_spec _ _ _).2

theorem onlineGenerator_mem_core {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ)
    (hcore : (currentCore family input).Infinite) :
    onlineGenerator family t input output ∈ currentCore family input := by
  classical
  simp only [onlineGenerator, dif_pos hcore]
  exact (leastFresh_spec _ _ _).1

theorem onlineGenerator_le {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ)
    (hcore : (currentCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ currentCore family input)
    (hzfresh : z ∉ usedValues input output) :
    onlineGenerator family t input output ≤ z := by
  classical
  simp only [onlineGenerator, dif_pos hcore]
  exact leastFresh_le _ hcore _ hzcore hzfresh

end Case017Proof

namespace Case017Proof

open Stage3Case017

variable {m : ℕ} (family : Fin m → Language) (input : Stream)

local notation "out" => trajectory (onlineGenerator family) input

 theorem trajectory_not_input (t s : ℕ) (hs : s ≤ t) :
    input s ≠ out t := by
  intro heq
  have hfresh : out t ∉ usedValues (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => out i) := by
    rw [trajectory_follows (onlineGenerator family) input t]
    exact onlineGenerator_fresh family t _ _
  apply hfresh
  apply Finset.mem_union_left
  change out t ∈ GenLimit.Generic.sequenceSample (fun i : Fin (t + 1) => input i)
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  exact ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, heq⟩

 theorem trajectory_not_previous (t s : ℕ) (hs : s < t) :
    out s ≠ out t := by
  intro heq
  have hfresh : out t ∉ usedValues (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => out i) := by
    rw [trajectory_follows (onlineGenerator family) input t]
    exact onlineGenerator_fresh family t _ _
  apply hfresh
  apply Finset.mem_union_right
  change out t ∈ GenLimit.Generic.sequenceSample (fun i : Fin t => out i)
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  exact ⟨⟨s, hs⟩, heq⟩

 theorem trajectory_injective : Function.Injective out := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact trajectory_not_previous family input t s hlt hst
  · exact trajectory_not_previous family input s t hgt hst.symm

 theorem generatorFirst_output (t : ℕ) :
    out t ∈ GenLimit.GeneratorFirst input out := by
  refine ⟨t, rfl, ?_⟩
  intro s hs
  exact trajectory_not_input family input t s hs

 theorem currentCore_subset_of_streamIn {t : ℕ} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    currentCore family (fun i : Fin (t + 1) => input i) ⊆ family j := by
  intro z hz
  apply hz j
  intro i
  exact hj ⟨i, rfl⟩

 theorem informationCore_subset_of_streamIn {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

 theorem exists_core_stabilization :
    ∃ T, ∀ t, T ≤ t →
      currentCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  have hindex : ∀ j : Fin m, ∃ T : ℕ, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hj : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, ?_⟩
      intro t ht
      constructor
      · intro hprefix
        exact hj
      · intro hstream i
        exact hstream ⟨i, rfl⟩
    · have hbad : ∃ s, input s ∉ family j := by
        simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using hj
      obtain ⟨s, hs⟩ := hbad
      refine ⟨s, ?_⟩
      intro t hst
      constructor
      · intro hprefix
        exact False.elim (hs (hprefix ⟨s, Nat.lt_succ_iff.mpr hst⟩))
      · intro hstream
        exact False.elim (hj hstream)
  choose bound hbound using hindex
  refine ⟨∑ j : Fin m, bound j, ?_⟩
  intro t ht
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    apply hz j
    exact (hbound j t (le_trans (Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) ht)).2 hj
  · intro hz j hj
    apply hz j
    exact (hbound j t (le_trans (Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) ht)).1 hj

 theorem eventual_core_output
    (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      out t ∈ informationCore family input ∧
      (∀ z, z ∈ informationCore family input →
        z ∉ usedValues (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => out i) → out t ≤ z) := by
  obtain ⟨T, hT⟩ := exists_core_stabilization family input
  refine ⟨T, ?_⟩
  intro t ht
  have heq := hT t ht
  have hinfinite :
      (currentCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [heq]
    exact hcore
  constructor
  · rw [trajectory_follows (onlineGenerator family) input t]
    rw [← heq]
    exact onlineGenerator_mem_core family t _ _ hinfinite
  · intro z hz hzfresh
    rw [trajectory_follows (onlineGenerator family) input t]
    apply onlineGenerator_le family t _ _ hinfinite
    · rwa [heq]
    · exact hzfresh

end Case017Proof

namespace Case017Proof

open Stage3Case017

noncomputable def firstInput (input : Stream) (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = x then Nat.find h else 0

theorem firstInput_spec {input : Stream} {x : ℕ} (hx : x ∈ Set.range input) :
    input (firstInput input x) = x := by
  classical
  obtain ⟨t, ht⟩ := hx
  rw [firstInput]
  simp only [dif_pos (show ∃ q, input q = x from ⟨t, ht⟩)]
  exact Nat.find_spec (show ∃ q, input q = x from ⟨t, ht⟩)

theorem firstInput_le {input : Stream} {x t : ℕ} (ht : input t = x) :
    firstInput input x ≤ t := by
  classical
  rw [firstInput]
  simp only [dif_pos (show ∃ q, input q = x from ⟨t, ht⟩)]
  exact Nat.find_min' (show ∃ q, input q = x from ⟨t, ht⟩) ht

theorem attacker_no_output_before_first {input output : Stream} {x : ℕ}
    (hx : x ∈ GenLimit.AdversaryFirst input output) :
    ∀ s, s < firstInput input x → output s ≠ x := by
  rintro s hs
  obtain ⟨t, htx, hno⟩ := hx
  exact hno s (lt_of_lt_of_le hs (firstInput_le htx))

theorem core_not_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (onlineGenerator family) input) := by
  intro z hz
  let output := trajectory (onlineGenerator family) input
  have hnotInput : z ∉ Set.range input := hz.2
  by_contra hnotGF
  have hnotOutput : z ∉ Set.range output := by
    rintro ⟨t, ht⟩
    apply hnotGF
    refine ⟨t, ht, ?_⟩
    intro s hs hsz
    exact hnotInput ⟨s, hsz⟩
  obtain ⟨T, hT⟩ := eventual_core_output family input hcore
  let values := (Finset.range (z + 2)).image (fun k => output (T + k))
  have hcard : values.card = z + 2 := by
    change ((Finset.range (z + 2)).image (fun k => output (T + k))).card = _
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      exact Nat.add_left_cancel (trajectory_injective family input hab)
  have hsubset : values ⊆ Finset.range (z + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_iff.mpr
    apply (hT (T + k) (Nat.le_add_right T k)).2 z hz.1
    intro hzused
    rcases Finset.mem_union.mp hzused with hzIn | hzOut
    · change z ∈ GenLimit.Generic.sequenceSample
        (fun i : Fin (T + k + 1) => input i) at hzIn
      rw [GenLimit.Generic.mem_sequenceSample_iff] at hzIn
      obtain ⟨i, hi⟩ := hzIn
      exact hnotInput ⟨i, hi⟩
    · change z ∈ GenLimit.Generic.sequenceSample
        (fun i : Fin (T + k) => output i) at hzOut
      rw [GenLimit.Generic.mem_sequenceSample_iff] at hzOut
      obtain ⟨i, hi⟩ := hzOut
      exact hnotOutput ⟨i, hi⟩
  have := Finset.card_le_card hsubset
  simp only [hcard, Finset.card_range] at this
  omega

theorem attacker_prefix_count_le {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ n,
      GenLimit.PatientScope.prefixCount
          (GenLimit.AdversaryFirst input
            (trajectory (onlineGenerator family) input) ∩
            informationCore family input) n ≤
        GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input
            (trajectory (onlineGenerator family) input) ∩
            informationCore family input) n + T + 1 := by
  classical
  let output := trajectory (onlineGenerator family) input
  obtain ⟨T, hT⟩ := eventual_core_output family input hcore
  refine ⟨T, ?_⟩
  intro n
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ informationCore family input) n
  let early := A.filter (fun x => firstInput input x < T)
  let late := A.filter (fun x => T ≤ firstInput input x)
  have hcover : A ⊆ early ∪ late := by
    intro x hx
    by_cases hxt : firstInput input x < T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxt⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, by omega⟩)
  have hearly : early.card ≤ T := by
    rw [← Finset.card_range T]
    apply Finset.card_le_card_of_injOn (firstInput input)
    · intro x hx
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
    · intro x hx y hy hxy
      have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp
        (Finset.mem_filter.mp hx).1).2.1
      have hyA := (GenLimit.PatientScope.mem_prefixFinset.mp
        (Finset.mem_filter.mp hy).1).2.1
      have hxspec := firstInput_spec (input := input) (x := x)
        ⟨Classical.choose hxA, (Classical.choose_spec hxA).1⟩
      have hyspec := firstInput_spec (input := input) (x := y)
        ⟨Classical.choose hyA, (Classical.choose_spec hyA).1⟩
      rw [hxy] at hxspec
      exact hxspec.symm.trans hyspec
  have hlate : late.card ≤ D.card + 1 := by
    by_cases hempty : late.Nonempty
    · let times := late.image (firstInput input)
      have htimeInj : Set.InjOn (firstInput input) (↑late : Set ℕ) := by
        intro x hx y hy hxy
        have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hx).1).2.1
        have hyA := (GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hy).1).2.1
        have hxspec := firstInput_spec (input := input) (x := x)
          ⟨Classical.choose hxA, (Classical.choose_spec hxA).1⟩
        have hyspec := firstInput_spec (input := input) (x := y)
          ⟨Classical.choose hyA, (Classical.choose_spec hyA).1⟩
        rw [hxy] at hxspec
        exact hxspec.symm.trans hyspec
      have htimesNonempty : times.Nonempty := hempty.image _
      let qmax := times.max' htimesNonempty
      have herase : (times.erase qmax).card + 1 = times.card :=
        Finset.card_erase_add_one (Finset.max'_mem times htimesNonempty)
      have himage : times.card = late.card :=
        Finset.card_image_of_injOn htimeInj
      have hmap : (times.erase qmax).card ≤ D.card := by
        apply Finset.card_le_card_of_injOn output
        · intro q hq
          have hqTimes : q ∈ times := (Finset.mem_erase.mp hq).2
          have hqNe : q ≠ qmax := (Finset.mem_erase.mp hq).1
          rw [Finset.mem_image] at hqTimes
          obtain ⟨x, hxlate, hqx⟩ := hqTimes
          have hmaxMem : qmax ∈ times := Finset.max'_mem times htimesNonempty
          rw [Finset.mem_image] at hmaxMem
          obtain ⟨y, hylate, hqy⟩ := hmaxMem
          have hqle : q ≤ qmax := Finset.le_max' times q
            ((Finset.mem_erase.mp hq).2)
          have hqlt : q < qmax := lt_of_le_of_ne hqle hqNe
          have hxparts := GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_filter.mp hxlate).1
          have hyparts := GenLimit.PatientScope.mem_prefixFinset.mp
            (Finset.mem_filter.mp hylate).1
          have hqT : T ≤ q := by
            calc
              T ≤ firstInput input x := (Finset.mem_filter.mp hxlate).2
              _ = q := hqx
          have hyFresh : y ∉ usedValues
              (fun i : Fin (q + 1) => input i)
              (fun i : Fin q => output i) := by
            intro hyused
            rcases Finset.mem_union.mp hyused with hyInput | hyOutput
            · change y ∈ GenLimit.Generic.sequenceSample
                (fun i : Fin (q + 1) => input i) at hyInput
              rw [GenLimit.Generic.mem_sequenceSample_iff] at hyInput
              obtain ⟨i, hi⟩ := hyInput
              have hitime : i.val = firstInput input y := by
                apply hinj
                rw [hi]
                exact (firstInput_spec (input := input)
                  ⟨Classical.choose hyparts.2.1,
                    (Classical.choose_spec hyparts.2.1).1⟩).symm
              rw [hqy] at hitime
              omega
            · change y ∈ GenLimit.Generic.sequenceSample
                (fun i : Fin q => output i) at hyOutput
              rw [GenLimit.Generic.mem_sequenceSample_iff] at hyOutput
              obtain ⟨i, hi⟩ := hyOutput
              have hbefore : i.val < firstInput input y := by
                rw [hqy]
                exact lt_trans i.isLt hqlt
              exact attacker_no_output_before_first hyparts.2.1 i hbefore hi
          apply GenLimit.PatientScope.mem_prefixFinset.mpr
          refine ⟨?_, generatorFirst_output family input q, (hT q hqT).1⟩
          have hle := (hT q hqT).2 y hyparts.2.2 hyFresh
          exact lt_of_le_of_lt hle hyparts.1
        · intro q hq r hr hqr
          exact trajectory_injective family input hqr
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty]
      omega
  change A.card ≤ D.card + T + 1
  calc
    A.card ≤ (early ∪ late).card := Finset.card_le_card hcover
    _ ≤ early.card + late.card := Finset.card_union_le _ _
    _ ≤ T + (D.card + 1) := Nat.add_le_add hearly hlate
    _ = D.card + T + 1 := by omega

end Case017Proof

namespace Case017Proof

open Filter
open scoped Topology
open Stage3Case017

 theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
      · exact Nat.cast_nonneg _
  · exact isBoundedUnder_of ⟨0, fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  · exact isCoboundedUnder_ge_of_le atTop (fun n =>
      show ((GenLimit.PatientScope.prefixCount B n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) ≤ (1 : ℝ) from by
        by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
        · have hzero : GenLimit.PatientScope.prefixCount B n = 0 := by
            have hle := GenLimit.PatientScope.prefixCount_mono hBK n
            omega
          simp [hn, hzero]
        · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
          exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n)

 theorem core_density_half {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input
          (trajectory (onlineGenerator family) input) ∩ family j) (family j) := by
  let output := trajectory (onlineGenerator family) input
  let I := informationCore family input
  let K := family j
  let AF := GenLimit.AdversaryFirst input output
  let GF := GenLimit.GeneratorFirst input output
  obtain ⟨T, hA⟩ := attacker_prefix_count_le family input hinj hcore
  apply GenLimit.PatientScope.partialDensity_of_counting
    (fun n => GenLimit.PatientScope.prefixCount K n)
    (fun n => GenLimit.PatientScope.prefixCount I n)
    (fun n => GenLimit.PatientScope.prefixCount (GF ∩ K) n)
    (T + 1)
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hfamily j)
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono
      (informationCore_subset_of_streamIn family input hj) n
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    let IP := GenLimit.PatientScope.prefixFinset I n
    let AP := GenLimit.PatientScope.prefixFinset (AF ∩ I) n
    let DP := GenLimit.PatientScope.prefixFinset (GF ∩ I) n
    have hcoverI : I ⊆ AF ∪ GF := by
      intro z hz
      by_cases hzrange : z ∈ Set.range input
      · exact GenLimit.range_subset_first_announcements input output hzrange
      · exact Set.mem_union_right _
          (core_not_range_subset_generatorFirst family input hcore ⟨hz, hzrange⟩)
    have hIP : IP.card ≤ AP.card + DP.card := by
      have hsubset : IP ⊆ AP ∪ DP := by
        intro z hz
        have hzparts := GenLimit.PatientScope.mem_prefixFinset.mp hz
        rcases hcoverI hzparts.2 with hzA | hzD
        · exact Finset.mem_union_left _
            (GenLimit.PatientScope.mem_prefixFinset.mpr
              ⟨hzparts.1, hzA, hzparts.2⟩)
        · exact Finset.mem_union_right _
            (GenLimit.PatientScope.mem_prefixFinset.mpr
              ⟨hzparts.1, hzD, hzparts.2⟩)
      exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
    have hAD : AP.card ≤ DP.card + T + 1 := hA n
    have hDmono : DP.card ≤
        GenLimit.PatientScope.prefixCount (GF ∩ K) n := by
      apply GenLimit.PatientScope.prefixCount_mono
      intro z hz
      show z ∈ GF ∩ K
      exact And.intro hz.1
        (informationCore_subset_of_streamIn family input hj hz.2)
    change IP.card ≤ 2 * GenLimit.PatientScope.prefixCount (GF ∩ K) n +
      (T + 1) + Nat.log2 (GenLimit.PatientScope.prefixCount K n)
    omega

 theorem novel_generation {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (onlineGenerator family) input) (family j) := by
  obtain ⟨T, hT⟩ := eventual_core_output family input hcore
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨informationCore_subset_of_streamIn family input hj (hT t ht).1, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact trajectory_not_input family input t s (Nat.le_of_lt_succ hs) heq
  · intro s hs
    exact trajectory_not_previous family input t s hs

 theorem succeeds {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite) :
    SucceedsFor family (onlineGenerator family) := by
  intro input hinj hexists hcore
  let output := trajectory (onlineGenerator family) input
  refine ⟨output, trajectory_follows (onlineGenerator family) input, ?_⟩
  intro j hj
  refine ⟨novel_generation family input hcore hj, ?_⟩
  have hhalf := core_density_half family hfamily input hinj hcore hj
  have hmissingSubset :
      informationCore family input \ Set.range input ⊆
        GenLimit.GeneratorFirst input output ∩ family j := by
    intro z hz
    exact ⟨core_not_range_subset_generatorFirst family input hcore hz,
      informationCore_subset_of_streamIn family input hj hz.1⟩
  have hmissing := relativeLowerDensity_mono hmissingSubset Set.inter_subset_right
  exact max_le hhalf hmissing

end Case017Proof
