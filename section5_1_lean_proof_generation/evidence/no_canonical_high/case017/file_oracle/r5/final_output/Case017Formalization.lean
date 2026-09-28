import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology BigOperators

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def prefixCore {m t : ℕ} (family : Fin m → Language)
    (input : Fin t → ℕ) : Language :=
  {z | ∀ j, (∀ i, input i ∈ family j) → z ∈ family j}

def Available {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ prefixCore family input ∧
    (∀ i, input i ≠ z) ∧
    (∀ i, output i ≠ z)

noncomputable def generator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun _ input output =>
    if h : ∃ z, Available family input output z then Nat.find h else 0

theorem generator_available {m t : ℕ} {family : Fin m → Language}
    {input : Fin (t + 1) → ℕ} {output : Fin t → ℕ}
    (h : ∃ z, Available family input output z) :
    Available family input output (generator family t input output) := by
  classical
  simp only [generator, dif_pos h]
  exact Nat.find_spec h

theorem eventually_prefix_compatible {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hpoint : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases h : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, fun _ _ => ⟨fun _ => h, ?_⟩⟩
      intro _ i
      exact h ⟨i, rfl⟩
    · rw [GenLimit.Generic.StreamIn] at h
      obtain ⟨z, ⟨s, rfl⟩, hnot⟩ := Set.not_subset.mp h
      refine ⟨s, ?_⟩
      intro t hst
      constructor
      · intro hall
        exact False.elim (hnot (hall ⟨s, Nat.lt_succ_of_le hst⟩))
      · intro hstream
        exact False.elim (h hstream)
  let bound : Fin m → ℕ := fun j => Classical.choose (hpoint j)
  refine ⟨∑ j, bound j, ?_⟩
  intro t ht j
  have hj : bound j ≤ ∑ k, bound k := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact Classical.choose_spec (hpoint j) t (le_trans hj ht)

theorem prefixCore_eventually_eq {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_prefix_compatible family input
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  simp only [prefixCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((hT t ht j).2 hj)
  · intro hz j hj
    exact hz j ((hT t ht j).1 hj)

theorem exists_available {m t : ℕ} {family : Fin m → Language}
    {input : Fin (t + 1) → ℕ} {output : Fin t → ℕ}
    (hcore : (prefixCore family input).Infinite) :
    ∃ z, Available family input output z := by
  classical
  let used : Finset ℕ :=
    GenLimit.Generic.sequenceSample input ∪
      GenLimit.Generic.sequenceSample output
  obtain ⟨z, hzcore, hzused⟩ := hcore.exists_not_mem_finset used
  refine ⟨z, hzcore, ?_, ?_⟩
  · intro i hi
    apply hzused
    apply Finset.mem_union_left
    rw [GenLimit.Generic.mem_sequenceSample_iff]
    exact ⟨i, hi⟩
  · intro i hi
    apply hzused
    apply Finset.mem_union_right
    rw [GenLimit.Generic.mem_sequenceSample_iff]
    exact ⟨i, hi⟩

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => Nat.strongRecOn t (fun t previous =>
    gen t (fun i => input i) (fun i => previous i i.isLt))

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]
  rw [Nat.strongRecOn_eq]
  congr 1

noncomputable def useTime (input output : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ s, input s = z then Nat.find h + 1
    else if h : ∃ s, output s = z then Nat.find h + 1 else 0

theorem used_before_useTime {input output : Stream} {z : ℕ}
    (hused : z ∈ Set.range input ∪ Set.range output) :
    (∃ i : Fin (useTime input output z), input i = z) ∨
      (∃ i : Fin (useTime input output z), output i = z) := by
  classical
  rcases hused with hin | hout
  · obtain ⟨s, hs⟩ := hin
    have hex : ∃ q, input q = z := ⟨s, hs⟩
    left
    refine ⟨⟨Nat.find hex, ?_⟩, Nat.find_spec hex⟩
    simp [useTime, hex]
  · by_cases hex : ∃ q, input q = z
    · left
      refine ⟨⟨Nat.find hex, ?_⟩, Nat.find_spec hex⟩
      simp [useTime, hex]
    · obtain ⟨s, hs⟩ := hout
      have hey : ∃ q, output q = z := ⟨s, hs⟩
      right
      refine ⟨⟨Nat.find hey, ?_⟩, Nat.find_spec hey⟩
      simp [useTime, hex, hey]

theorem useTime_le_sum {input output : Stream} {z w : ℕ} (hw : w < z) :
    useTime input output w ≤ ∑ q ∈ Finset.range z, useTime input output q := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hw)

theorem core_diff_range_subset_output {m : ℕ}
    (family : Fin m → Language) (input output : Stream)
    (hfollow : Follows (generator family) input output)
    (hcoreInfinite : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆ Set.range output := by
  classical
  obtain ⟨T, hT⟩ := prefixCore_eventually_eq family input
  intro z hz
  induction z using Nat.strong_induction_on with
  | h z ih =>
      by_contra hzout
      have hcover : ∀ w, w < z → w ∈ informationCore family input →
          w ∈ Set.range input ∪ Set.range output := by
        intro w hw hwcore
        by_cases hwin : w ∈ Set.range input
        · exact Or.inl hwin
        · exact Or.inr (ih w hw ⟨hwcore, hwin⟩)
      let S := ∑ q ∈ Finset.range z, useTime input output q
      let t := max T S
      have htT : T ≤ t := Nat.le_max_left _ _
      have hcoreEq := hT t htT
      have hprefixInfinite :
          (prefixCore family (fun i : Fin (t + 1) => input i)).Infinite := by
        rw [hcoreEq]
        exact hcoreInfinite
      have hex := exists_available (family := family)
        (input := fun i : Fin (t + 1) => input i)
        (output := fun i : Fin t => output i) hprefixInfinite
      have houtAvail : Available family (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => output i) (output t) := by
        rw [hfollow t]
        exact generator_available hex
      have hzAvail : Available family (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => output i) z := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hcoreEq]
          exact hz.1
        · intro i hi
          exact hz.2 ⟨i, hi⟩
        · intro i hi
          exact hzout ⟨i, hi⟩
      have houtLe : output t ≤ z := by
        rw [hfollow t, generator, dif_pos hex]
        exact Nat.find_min' hex hzAvail
      have houtNotLt : ¬ output t < z := by
        intro houtLt
        have houtCore : output t ∈ informationCore family input := by
          rw [← hcoreEq]
          exact houtAvail.1
        have hused := used_before_useTime
          (hcover (output t) houtLt houtCore)
        have htime : useTime input output (output t) ≤ t := by
          exact le_trans (useTime_le_sum houtLt) (Nat.le_max_right _ _)
        rcases hused with hin | hout
        · obtain ⟨i, hi⟩ := hin
          exact houtAvail.2.1 ⟨i, lt_of_lt_of_le i.isLt (le_trans htime (Nat.le_succ t))⟩ hi
        · obtain ⟨i, hi⟩ := hout
          exact houtAvail.2.2 ⟨i, lt_of_lt_of_le i.isLt htime⟩ hi
      have houtEq : output t = z := by omega
      exact hzout ⟨t, houtEq⟩

theorem eventual_available {m : ℕ} (family : Fin m → Language)
    (input output : Stream)
    (hfollow : Follows (generator family) input output)
    (hcoreInfinite : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      Available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => output i) (output t) := by
  obtain ⟨T, hT⟩ := prefixCore_eventually_eq family input
  refine ⟨T, ?_⟩
  intro t ht
  have hprefixInfinite :
      (prefixCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hT t ht]
    exact hcoreInfinite
  have hex := exists_available (family := family)
    (input := fun i : Fin (t + 1) => input i)
    (output := fun i : Fin t => output i) hprefixInfinite
  rw [hfollow t]
  exact generator_available hex

def tailOutput (T : ℕ) (output : Stream) : Stream :=
  fun n => output (T + n)

theorem tailOutput_injective {m : ℕ} {family : Fin m → Language}
    {input output : Stream} {T : ℕ}
    (havailable : ∀ t, T ≤ t →
      Available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => output i) (output t)) :
    Function.Injective (tailOutput T output) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · have havail := havailable (T + b) (Nat.le_add_right T b)
    exact havail.2.2 ⟨T + a, Nat.add_lt_add_left hablt T⟩ hab
  · have havail := havailable (T + a) (Nat.le_add_right T a)
    exact havail.2.2 ⟨T + b, Nat.add_lt_add_left hbalt T⟩ hab.symm

theorem tailOutput_subset_core {m : ℕ} {family : Fin m → Language}
    {input output : Stream} {T : ℕ}
    (hcoreEq : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (havailable : ∀ t, T ≤ t →
      Available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => output i) (output t)) :
    Set.range (tailOutput T output) ⊆ informationCore family input := by
  rintro z ⟨n, rfl⟩
  rw [← hcoreEq (T + n) (Nat.le_add_right T n)]
  exact (havailable (T + n) (Nat.le_add_right T n)).1

theorem tailOutput_subset_generatorFirst {m : ℕ}
    {family : Fin m → Language} {input output : Stream} {T : ℕ}
    (havailable : ∀ t, T ≤ t →
      Available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => output i) (output t)) :
    Set.range (tailOutput T output) ⊆ GenLimit.GeneratorFirst input output := by
  rintro z ⟨n, rfl⟩
  refine ⟨T + n, rfl, ?_⟩
  intro s hs
  exact (havailable (T + n) (Nat.le_add_right T n)).2.1
    ⟨s, Nat.lt_succ_of_le hs⟩

theorem core_subset_of_compatible {m : ℕ} {family : Fin m → Language}
    {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

theorem core_diff_range_subset_generatorFirst {m : ℕ}
    {family : Fin m → Language} {input output : Stream}
    (hfollow : Follows (generator family) input output)
    (hcoreInfinite : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input output := by
  intro z hz
  obtain ⟨t, ht⟩ := core_diff_range_subset_output family input output
    hfollow hcoreInfinite hz
  refine ⟨t, ht, ?_⟩
  intro s hs hin
  exact hz.2 ⟨s, hin⟩

noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ q, input q = z then Nat.find h else 0

theorem firstInputTime_spec {input : Stream} {z : ℕ}
    (h : ∃ q, input q = z) : input (firstInputTime input z) = z := by
  classical
  simp only [firstInputTime, dif_pos h]
  exact Nat.find_spec h

theorem firstInputTime_eq {input : Stream} (hinj : Function.Injective input)
    {z q : ℕ} (hq : input q = z) : firstInputTime input z = q := by
  apply hinj
  rw [firstInputTime_spec ⟨q, hq⟩]
  exact hq.symm

theorem relativeLowerDensity_mono_left {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · apply isBoundedUnder_of_eventually_ge
    exact Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hratio : ∀ n,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ (1 : ℝ) := by
      intro n
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · have hBn : GenLimit.PatientScope.prefixCount B n = 0 := by
          exact Nat.eq_zero_of_le_zero
            (hn ▸ GenLimit.PatientScope.prefixCount_mono hBK n)
        simp [hn, hBn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
    exact isCoboundedUnder_ge_of_le atTop hratio
theorem half_core_density {m : ℕ} {family : Fin m → Language}
    {input output : Stream} (hinj : Function.Injective input)
    (hfollow : Follows (generator family) input output)
    (hcoreInfinite : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j))
    (hfamilyInfinite : (family j).Infinite) :
    (1 / 2 : ℝ) *
        GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
  classical
  obtain ⟨Tc, hcoreEq0⟩ := prefixCore_eventually_eq family input
  obtain ⟨Ta, havailable0⟩ := eventual_available family input output
    hfollow hcoreInfinite
  let T := max Tc Ta
  have hcoreEq : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
    intro t ht
    exact hcoreEq0 t (le_trans (Nat.le_max_left _ _) ht)
  have havailable : ∀ t, T ≤ t →
      Available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => output i) (output t) := by
    intro t ht
    exact havailable0 t (le_trans (Nat.le_max_right _ _) ht)
  let D : Set ℕ := Set.range (tailOutput T output)
  let A : Set ℕ := informationCore family input \ D
  let early : Finset ℕ := GenLimit.sample input (T + 1) ∪ GenLimit.sample output T
  let partner : ℕ → ℕ := fun z => output (firstInputTime input z - 1)
  have htailInj : Function.Injective (tailOutput T output) :=
    tailOutput_injective havailable
  have hDcore : D ⊆ informationCore family input := by
    exact tailOutput_subset_core hcoreEq havailable
  have hDK : D ⊆ family j := Set.Subset.trans hDcore
    (core_subset_of_compatible hj)
  have hDfirst : D ⊆ GenLimit.GeneratorFirst input output :=
    tailOutput_subset_generatorFirst havailable
  have hinputOrd : ∀ x,
      x ∈ GenLimit.PatientScope.ordinaryAttacker
        (family j) A (∅ : Set ℕ) early →
      ∃ q, input q = x := by
    intro x hx
    have hxA : x ∈ A := hx.1.1
    have hxcore : x ∈ informationCore family input := hxA.1
    have hxnotD : x ∉ D := hxA.2
    have hxnotEarly : x ∉ early := by
      intro he
      exact hx.2 (Or.inl he)
    by_contra hxin
    have hxout := core_diff_range_subset_output family input output
      hfollow hcoreInfinite ⟨hxcore, hxin⟩
    obtain ⟨q, hq⟩ := hxout
    by_cases hqT : q < T
    · apply hxnotEarly
      apply Finset.mem_union_right
      rw [GenLimit.mem_sample_iff]
      exact ⟨q, hqT, hq⟩
    · apply hxnotD
      refine ⟨q - T, ?_⟩
      simp only [tailOutput]
      rw [Nat.add_sub_of_le (Nat.le_of_not_gt hqT)]
      exact hq
  have htimeOrd : ∀ x (hx : x ∈ GenLimit.PatientScope.ordinaryAttacker
      (family j) A (∅ : Set ℕ) early),
      T + 1 ≤ firstInputTime input x := by
    intro x hx
    have hex := hinputOrd x hx
    have hxnotEarly : x ∉ early := by
      intro he
      exact hx.2 (Or.inl he)
    apply Nat.le_of_not_gt
    intro hlt
    apply hxnotEarly
    apply Finset.mem_union_left
    rw [GenLimit.mem_sample_iff]
    exact ⟨firstInputTime input x, hlt, firstInputTime_spec hex⟩
  have hxAvailable : ∀ x (hx : x ∈ GenLimit.PatientScope.ordinaryAttacker
      (family j) A (∅ : Set ℕ) early),
      Available family
        (fun i : Fin ((firstInputTime input x - 1) + 1) => input i)
        (fun i : Fin (firstInputTime input x - 1) => output i) x := by
    intro x hx
    let q := firstInputTime input x
    have hex := hinputOrd x hx
    have hqspec : input q = x := firstInputTime_spec hex
    have hqLower : T + 1 ≤ q := htimeOrd x hx
    have hqT : T ≤ q - 1 := by omega
    have hxA : x ∈ A := hx.1.1
    have hxnotD : x ∉ D := hxA.2
    have hxnotEarly : x ∉ early := by
      intro he
      exact hx.2 (Or.inl he)
    refine ⟨?_, ?_, ?_⟩
    · rw [hcoreEq (q - 1) hqT]
      exact hxA.1
    · intro i hi
      have hiq : (i : ℕ) = q := hinj (hi.trans hqspec.symm)
      omega
    · intro i hi
      by_cases hiT : (i : ℕ) < T
      · apply hxnotEarly
        apply Finset.mem_union_right
        rw [GenLimit.mem_sample_iff]
        exact ⟨i, hiT, hi⟩
      · apply hxnotD
        refine ⟨(i : ℕ) - T, ?_⟩
        simp only [tailOutput]
        rw [Nat.add_sub_of_le (Nat.le_of_not_gt hiT)]
        exact hi
  have hpartnerMem : ∀ x (hx : x ∈ GenLimit.PatientScope.ordinaryAttacker
      (family j) A (∅ : Set ℕ) early), partner x ∈ D ∩ family j := by
    intro x hx
    have hqLower := htimeOrd x hx
    have hqT : T ≤ firstInputTime input x - 1 := by omega
    have hpD : partner x ∈ D := by
      refine ⟨(firstInputTime input x - 1) - T, ?_⟩
      simp only [tailOutput, partner]
      rw [Nat.add_sub_of_le hqT]
    exact ⟨hpD, hDK hpD⟩
  have hpartnerLt : ∀ x (hx : x ∈ GenLimit.PatientScope.ordinaryAttacker
      (family j) A (∅ : Set ℕ) early), partner x < x := by
    intro x hx
    let q := firstInputTime input x
    have hqLower : T + 1 ≤ q := htimeOrd x hx
    have hqT : T ≤ q - 1 := by omega
    have hexAvail : ∃ z, Available family
        (fun i : Fin ((q - 1) + 1) => input i)
        (fun i : Fin (q - 1) => output i) z :=
      ⟨x, hxAvailable x hx⟩
    have hle : partner x ≤ x := by
      change output (q - 1) ≤ x
      rw [hfollow (q - 1), generator, dif_pos hexAvail]
      exact Nat.find_min' hexAvail (hxAvailable x hx)
    have hne : partner x ≠ x := by
      intro heq
      apply hx.1.1.2
      rw [← heq]
      exact (hpartnerMem x hx).1
    omega
  have hpartnerInj : Set.InjOn partner
      (GenLimit.PatientScope.ordinaryAttacker
        (family j) A (∅ : Set ℕ) early) := by
    intro x hx y hy hxy
    let qx := firstInputTime input x
    let qy := firstInputTime input y
    have hqx : T ≤ qx - 1 := by
      have := htimeOrd x hx
      omega
    have hqy : T ≤ qy - 1 := by
      have := htimeOrd y hy
      omega
    have htailEq : tailOutput T output ((qx - 1) - T) =
        tailOutput T output ((qy - 1) - T) := by
      simp only [tailOutput]
      rw [Nat.add_sub_of_le hqx, Nat.add_sub_of_le hqy]
      simpa [partner, qx, qy] using hxy
    have hqeq : qx = qy := by
      have hsub : (qx - 1) - T = (qy - 1) - T := htailInj htailEq
      have hprev : qx - 1 = qy - 1 := by
        calc
          qx - 1 = T + ((qx - 1) - T) := (Nat.add_sub_of_le hqx).symm
          _ = T + ((qy - 1) - T) := by rw [hsub]
          _ = qy - 1 := Nat.add_sub_of_le hqy
      have hqxpos : 0 < qx := lt_of_lt_of_le (Nat.zero_lt_succ T) (htimeOrd x hx)
      have hqypos : 0 < qy := lt_of_lt_of_le (Nat.zero_lt_succ T) (htimeOrd y hy)
      omega
    calc
      x = input qx := by
        simpa [qx] using (firstInputTime_spec (hinputOrd x hx)).symm
      _ = input qy := by rw [hqeq]
      _ = y := by
        simpa [qy] using firstInputTime_spec (hinputOrd y hy)
  let P : GenLimit.PatientScope.PartialEnumerationCertificate :=
    { target := family j
      enumerated := informationCore family input
      enumerated_subset_target := core_subset_of_compatible hj
      attacker := A
      defender := D
      output := tailOutput T output
      output_range := rfl
      output_injective := htailInj
      validFrom := 0
      eventual_target := fun t _ => hDK ⟨t, rfl⟩
      enumerated_covered := by
        intro x hx
        by_cases hxD : x ∈ D
        · exact Or.inr hxD
        · exact Or.inl ⟨hx, hxD⟩
      attacker_subset_target := fun _ hx =>
        (core_subset_of_compatible hj) hx.1
      ownership_disjoint := by
        rw [Set.disjoint_left]
        intro x hxA hxD
        exact hxA.2 hxD
      earlyAttacker := early
      switchLoss := ∅
      switchLoss_subset := by simp
      partner := partner
      partner_mem := hpartnerMem
      partner_lt := hpartnerLt
      partner_injective := hpartnerInj
      switchBudget := fun _ => 0
      switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset] }
  have hhalf := P.theorem_3_17 hfamilyInfinite (by
    intro n
    simp [P, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset])
  have htailMono : GenLimit.PatientScope.relativeLowerDensity
      (D ∩ family j) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    apply relativeLowerDensity_mono_left
    · intro x hx
      exact ⟨hDfirst hx.1, hx.2⟩
    · exact Set.inter_subset_right
  exact le_trans (by simpa [P, GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity]
    using hhalf) htailMono

theorem novel_generation {m : ℕ} {family : Fin m → Language}
    {input output : Stream}
    (hfollow : Follows (generator family) input output)
    (hcoreInfinite : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input output (family j) := by
  obtain ⟨T, hT⟩ := eventual_available family input output hfollow hcoreInfinite
  refine ⟨T, ?_⟩
  intro t ht
  have havail := hT t ht
  refine ⟨?_, ?_, ?_⟩
  · exact havail.1 j (fun i => hj ⟨i, rfl⟩)
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, hvalue⟩ := hsample
    exact havail.2.1 ⟨s, hs⟩ hvalue
  · intro s hs
    exact havail.2.2 ⟨s, hs⟩
end Stage3Case017Proof


theorem stage3_result : Stage3Case017.MainClaim := by
  intro m _ family hfamilyInfinite
  refine ⟨Stage3Case017Proof.generator family, ?_⟩
  intro input hinjective _ hcoreInfinite
  let output := Stage3Case017Proof.trajectory
    (Stage3Case017Proof.generator family) input
  have hfollow : Stage3Case017.Follows
      (Stage3Case017Proof.generator family) input output :=
    Stage3Case017Proof.trajectory_follows _ _
  refine ⟨output, hfollow, ?_⟩
  intro j hj
  refine ⟨Stage3Case017Proof.novel_generation hfollow hcoreInfinite hj, ?_⟩
  apply max_le
  · exact Stage3Case017Proof.half_core_density hinjective hfollow
      hcoreInfinite hj (hfamilyInfinite j)
  · apply Stage3Case017Proof.relativeLowerDensity_mono_left
    · intro z hz
      refine ⟨?_, Stage3Case017Proof.core_subset_of_compatible hj hz.1⟩
      exact Stage3Case017Proof.core_diff_range_subset_generatorFirst
        hfollow hcoreInfinite hz
    · exact Set.inter_subset_right
