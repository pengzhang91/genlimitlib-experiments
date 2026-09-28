import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def prefixCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin t → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def used {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

noncomputable def activeSet {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language := by
  classical
  exact if (prefixCore family xs).Infinite then prefixCore family xs else Set.univ

theorem activeSet_infinite {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : (activeSet family xs).Infinite := by
  classical
  by_cases h : (prefixCore family xs).Infinite
  · simpa [activeSet, h] using h
  · simpa [activeSet, h] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun _ xs ys =>
    Nat.find ((activeSet_infinite family xs).exists_notMem_finset (used xs ys))

theorem familyGenerator_mem_activeSet {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    familyGenerator family t xs ys ∈ activeSet family xs := by
  classical
  simpa [familyGenerator] using (Nat.find_spec
    ((activeSet_infinite family xs).exists_notMem_finset (used xs ys))).1

theorem familyGenerator_not_used {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    familyGenerator family t xs ys ∉ used xs ys := by
  classical
  simpa [familyGenerator] using (Nat.find_spec
    ((activeSet_infinite family xs).exists_notMem_finset (used xs ys))).2

theorem familyGenerator_minimal {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hzA : z ∈ activeSet family xs) (hzU : z ∉ used xs ys) :
    familyGenerator family t xs ys ≤ z := by
  classical
  simpa [familyGenerator] using Nat.find_min'
    ((activeSet_infinite family xs).exists_notMem_finset (used xs ys))
    ⟨hzA, hzU⟩

noncomputable def histories (gen : OnlineGenerator) (input : Stream) :
    (t : ℕ) → (Fin t → ℕ)
  | 0 => fun i => Fin.elim0 i
  | t + 1 => Fin.lastCases
      (gen t (fun i => input i) (histories gen input t))
      (histories gen input t)

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => histories gen input (t + 1) (Fin.last t)

theorem histories_castSucc (gen : OnlineGenerator) (input : Stream)
    {t : ℕ} (i : Fin t) :
    histories gen input (t + 1) i.castSucc = histories gen input t i := by
  simp [histories]

theorem histories_eq_trajectory (gen : OnlineGenerator) (input : Stream)
    {t : ℕ} (i : Fin t) : histories gen input t i = trajectory gen input i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [trajectory, histories]
      · rw [histories_castSucc, ih]
        rfl

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  change histories gen input (t + 1) (Fin.last t) =
    gen t (fun i => input i) (fun i => trajectory gen input i)
  rw [show histories gen input (t + 1) (Fin.last t) =
      gen t (fun i => input i) (histories gen input t) by simp [histories]]
  congr 1
  funext i
  exact histories_eq_trajectory gen input i

theorem prefixCore_eq_informationCore_of_agreement {m : ℕ}
    (family : Fin m → Language) (input : Stream) {t : ℕ}
    (hagree : ∀ j, (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j)) :
    prefixCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [prefixCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((hagree j).2 hj)
  · intro hz j hj
    exact hz j ((hagree j).1 hj)

theorem eventually_prefix_agreement {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hj : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hstream : GenLimit.Generic.StreamIn input (family j)
    · exact ⟨0, fun _ _ => ⟨fun _ => hstream, fun _ i => hstream ⟨i, rfl⟩⟩⟩
    · obtain ⟨z, ⟨s, rfl⟩, hnot⟩ := Set.not_subset.mp hstream
      refine ⟨s, ?_⟩
      intro t hst
      constructor
      · intro hall
        exact False.elim (hnot (hall ⟨s, Nat.lt_succ_of_le hst⟩))
      · intro hs
        exact False.elim (hstream hs)
  choose witness hwitness using hj
  refine ⟨Finset.univ.sup witness, ?_⟩
  intro t ht j
  exact hwitness j t (le_trans (Finset.le_sup (f := witness) (by simp)) ht)

theorem trajectory_fresh_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    trajectory (familyGenerator family) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  classical
  have h := familyGenerator_not_used family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (familyGenerator family) input i)
  rw [← trajectory_follows (familyGenerator family) input t] at h
  intro hsample
  apply h
  apply Finset.mem_union_left
  rw [GenLimit.Generic.mem_sample_iff] at hsample
  obtain ⟨i, hi, hit⟩ := hsample
  exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, by simp, hit⟩

theorem trajectory_output_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Function.Injective (trajectory (familyGenerator family) input) := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exfalso
    have h := familyGenerator_not_used family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (familyGenerator family) input i)
    rw [← trajectory_follows (familyGenerator family) input t] at h
    apply h
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨s, hlt⟩, by simp, hst⟩
  · exact heq
  · exfalso
    have h := familyGenerator_not_used family
      (fun i : Fin (s + 1) => input i)
      (fun i : Fin s => trajectory (familyGenerator family) input i)
    rw [← trajectory_follows (familyGenerator family) input s] at h
    apply h
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨t, hgt⟩, by simp, hst.symm⟩

theorem eventually_trajectory_mem_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      trajectory (familyGenerator family) input t ∈ informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_prefix_agreement family input
  refine ⟨T, ?_⟩
  intro t ht
  have heq := prefixCore_eq_informationCore_of_agreement family input (hT t ht)
  have hactive : activeSet family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
    rw [activeSet, if_pos]
    · exact heq
    · simpa [heq] using hcore
  have hmem := familyGenerator_mem_activeSet family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (familyGenerator family) input i)
  rw [← trajectory_follows (familyGenerator family) input t, hactive] at hmem
  exact hmem

end Stage3Case017Proof

namespace Stage3Case017Proof

open Stage3Case017

 theorem stable_activeSet {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hT : ∀ u, T ≤ u → ∀ j,
      (∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (ht : T ≤ t) :
    activeSet family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  have heq := prefixCore_eq_informationCore_of_agreement family input (hT t ht)
  rw [activeSet, if_pos]
  · exact heq
  · simpa [heq] using hcore

theorem core_subset_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (trajectory (familyGenerator family) input) := by
  classical
  obtain ⟨T, hT⟩ := eventually_prefix_agreement family input
  intro z hz
  by_contra hnot
  have hnotInput : ∀ s, input s ≠ z := by
    intro s hs
    apply hnot
    exact Set.mem_union_left _ ⟨s, hs⟩
  have hnotOutput : ∀ s, trajectory (familyGenerator family) input s ≠ z := by
    intro s hs
    apply hnot
    exact Set.mem_union_right _ ⟨s, hs⟩
  have hle : ∀ t, T ≤ t → trajectory (familyGenerator family) input t ≤ z := by
    intro t ht
    have hactive := stable_activeSet family input hT hcore ht
    have hzUsed : z ∉ used
        (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (familyGenerator family) input i) := by
      intro hused
      rcases Finset.mem_union.mp hused with hin | hout
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hin
        exact hnotInput i hi
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hout
        exact hnotOutput i hi
    have hmin := familyGenerator_minimal family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (familyGenerator family) input i)
      (z := z) (hactive.symm ▸ hz) hzUsed
    simpa only [← trajectory_follows (familyGenerator family) input t] using hmin
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨trajectory (familyGenerator family) input (T + i),
      Nat.lt_succ_of_le (hle (T + i) (Nat.le_add_right T i))⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hadd := trajectory_output_injective family input (congrArg Fin.val hij)
    exact Nat.add_left_cancel hadd
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

theorem core_covered_by_first {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (trajectory (familyGenerator family) input) ∪
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  intro z hz
  rcases core_subset_announced family input hcore hz with hin | hout
  · exact GenLimit.range_subset_first_announcements input
      (trajectory (familyGenerator family) input) hin
  · obtain ⟨t, ht⟩ := hout
    exact Set.mem_union_right _ ⟨t, ht, fun s hs hsin =>
      trajectory_fresh_input family input t
        (GenLimit.Generic.mem_sample_iff.mpr ⟨s, Nat.lt_succ_of_le hs, hsin.trans ht.symm⟩)⟩

theorem output_range_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range (trajectory (familyGenerator family) input) =
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl, fun s hs hsin => trajectory_fresh_input family input t
      (GenLimit.Generic.mem_sample_iff.mpr ⟨s, Nat.lt_succ_of_le hs, hsin⟩)⟩
  · rintro ⟨t, ht, -⟩
    exact ⟨t, ht⟩

noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

theorem firstInputTime_spec {input : Stream} {output : Stream} {z : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) :
    input (firstInputTime input z) = z := by
  classical
  obtain ⟨t, ht, -⟩ := hz
  simp only [firstInputTime]
  split
  · exact Nat.find_spec ‹∃ t, input t = z›
  · exact False.elim (‹¬ ∃ t, input t = z› ⟨t, ht⟩)

theorem firstInputTime_min {input : Stream} {output : Stream} {z t : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) (ht : input t = z) :
    firstInputTime input z ≤ t := by
  classical
  obtain ⟨w, hw, -⟩ := hz
  simp only [firstInputTime]
  split
  · exact Nat.find_min' ‹∃ q, input q = z› ht
  · exact False.elim (‹¬ ∃ q, input q = z› ⟨w, hw⟩)

noncomputable def earlyAttacker (input output : Stream) (T : ℕ) : Finset ℕ := by
  classical
  exact (GenLimit.Generic.sample input (T + 1)).filter
    (fun z => z ∈ GenLimit.AdversaryFirst input output)

noncomputable def predecessorPartner (input output : Stream) (z : ℕ) : ℕ :=
  output (firstInputTime input z - 1)

 theorem late_firstInputTime {input output : Stream} {T z : ℕ}
    (hzA : z ∈ GenLimit.AdversaryFirst input output)
    (hzLate : z ∉ earlyAttacker input output T) :
    T < firstInputTime input z := by
  by_contra hle
  apply hzLate
  classical
  simp only [earlyAttacker, Finset.mem_filter]
  refine ⟨?_, hzA⟩
  rw [GenLimit.Generic.mem_sample_iff]
  exact ⟨firstInputTime input z, Nat.lt_succ_of_le (Nat.le_of_not_gt hle),
    firstInputTime_spec hzA⟩

 theorem predecessor_lt {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinputInj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) {T z : ℕ}
    (hstable : ∀ t, T ≤ t →
      activeSet family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (hzCore : z ∈ informationCore family input)
    (hzA : z ∈ GenLimit.AdversaryFirst input
      (trajectory (familyGenerator family) input))
    (hzLate : z ∉ earlyAttacker input
      (trajectory (familyGenerator family) input) T) :
    predecessorPartner input (trajectory (familyGenerator family) input) z < z := by
  have htime := late_firstInputTime hzA hzLate
  have hpos : 0 < firstInputTime input z := lt_of_le_of_lt (Nat.zero_le T) htime
  let s := firstInputTime input z - 1
  have hsT : T ≤ s := by omega
  have hzNoInput : ∀ q, q ≤ s → input q ≠ z := by
    intro q hq hqz
    have hmin := firstInputTime_min hzA hqz
    omega
  have hzNoOutput : ∀ q, q < s →
      trajectory (familyGenerator family) input q ≠ z := by
    intro q hq
    have hzA' := hzA
    obtain ⟨w, hw, hbefore⟩ := hzA
    have hfirstLe := firstInputTime_min hzA' hw
    exact hbefore q (lt_of_lt_of_le hq (by omega))
  have hzUsed : z ∉ used
      (fun i : Fin (s + 1) => input i)
      (fun i : Fin s => trajectory (familyGenerator family) input i) := by
    intro hused
    rcases Finset.mem_union.mp hused with hin | hout
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hin
      exact hzNoInput i (Nat.le_of_lt_succ i.isLt) hi
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hout
      exact hzNoOutput i i.isLt hi
  have hmin := familyGenerator_minimal family
    (fun i : Fin (s + 1) => input i)
    (fun i : Fin s => trajectory (familyGenerator family) input i)
    (z := z) ((hstable s hsT).symm ▸ hzCore) hzUsed
  have hle : trajectory (familyGenerator family) input s ≤ z := by
    simpa only [← trajectory_follows (familyGenerator family) input s] using hmin
  have hne : trajectory (familyGenerator family) input s ≠ z := by
    intro heq
    have hzA' := hzA
    obtain ⟨w, hw, hbefore⟩ := hzA
    have hfirstLe := firstInputTime_min hzA' hw
    exact hbefore s (by omega) heq
  simpa [predecessorPartner, s] using lt_of_le_of_ne hle hne

theorem trajectory_mem_core_of_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hstable : ∀ u, T ≤ u →
      activeSet family (fun i : Fin (u + 1) => input i) =
        informationCore family input)
    (ht : T ≤ t) :
    trajectory (familyGenerator family) input t ∈
      informationCore family input := by
  have hmem := familyGenerator_mem_activeSet family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (familyGenerator family) input i)
  rw [← trajectory_follows (familyGenerator family) input t,
    hstable t ht] at hmem
  exact hmem

theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (hfamilyInfinite : ∀ j, (family j).Infinite)
    (input : Stream) (hinputInj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      activeSet family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (j : Fin m) (hstream : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input
          (trajectory (familyGenerator family) input) ∩ family j) (family j) := by
  let output := trajectory (familyGenerator family) input
  have hcoreTarget : informationCore family input ⊆ family j := by
    intro z hz
    exact hz j hstream
  let P : GenLimit.PatientScope.PartialEnumerationCertificate :=
    { target := family j
      enumerated := informationCore family input
      enumerated_subset_target := hcoreTarget
      attacker := GenLimit.AdversaryFirst input output ∩ informationCore family input
      defender := GenLimit.GeneratorFirst input output
      output := output
      output_range := by
        simpa [output] using output_range_generatorFirst family input
      output_injective := by
        simpa [output] using trajectory_output_injective family input
      validFrom := T
      eventual_target := by
        intro t ht
        exact hcoreTarget (trajectory_mem_core_of_stable family input hstable ht)
      enumerated_covered := by
        intro z hz
        rcases core_covered_by_first family input hcore hz with hzA | hzD
        · exact Set.mem_union_left _ ⟨hzA, hz⟩
        · exact Set.mem_union_right _ hzD
      attacker_subset_target := by
        intro z hz
        exact hcoreTarget hz.2
      ownership_disjoint := by
        exact (GenLimit.adversaryFirst_disjoint_generatorFirst input output).mono
          Set.inter_subset_left Set.Subset.rfl
      earlyAttacker := earlyAttacker input output T
      switchLoss := ∅
      switchLoss_subset := by simp
      partner := predecessorPartner input output
      partner_mem := by
        intro z hz
        change z ∈
          ((GenLimit.AdversaryFirst input output ∩ informationCore family input) ∩
              family j) \
            ((↑(earlyAttacker input output T) : Set ℕ) ∪ ∅) at hz
        rcases hz with ⟨⟨⟨hzA, hzCore⟩, -⟩, hzNotEarly⟩
        have hzLate : z ∉ earlyAttacker input output T := by
          intro hzEarly
          exact hzNotEarly (Set.mem_union_left _ hzEarly)
        have htime := late_firstInputTime hzA hzLate
        have hsT : T ≤ firstInputTime input z - 1 := by omega
        constructor
        · rw [← output_range_generatorFirst family input]
          exact ⟨firstInputTime input z - 1, rfl⟩
        · exact hcoreTarget
            (trajectory_mem_core_of_stable family input hstable hsT)
      partner_lt := by
        intro z hz
        change z ∈
          ((GenLimit.AdversaryFirst input output ∩ informationCore family input) ∩
              family j) \
            ((↑(earlyAttacker input output T) : Set ℕ) ∪ ∅) at hz
        rcases hz with ⟨⟨⟨hzA, hzCore⟩, -⟩, hzNotEarly⟩
        have hzLate : z ∉ earlyAttacker input output T := by
          intro hzEarly
          exact hzNotEarly (Set.mem_union_left _ hzEarly)
        exact predecessor_lt family input hinputInj hcore hstable hzCore hzA hzLate
      partner_injective := by
        intro x hx y hy hxy
        change x ∈
          ((GenLimit.AdversaryFirst input output ∩ informationCore family input) ∩
              family j) \
            ((↑(earlyAttacker input output T) : Set ℕ) ∪ ∅) at hx
        change y ∈
          ((GenLimit.AdversaryFirst input output ∩ informationCore family input) ∩
              family j) \
            ((↑(earlyAttacker input output T) : Set ℕ) ∪ ∅) at hy
        rcases hx with ⟨⟨⟨hxA, -⟩, -⟩, hxNotEarly⟩
        rcases hy with ⟨⟨⟨hyA, -⟩, -⟩, hyNotEarly⟩
        have hxLate : x ∉ earlyAttacker input output T := by
          intro hxEarly
          exact hxNotEarly (Set.mem_union_left _ hxEarly)
        have hyLate : y ∉ earlyAttacker input output T := by
          intro hyEarly
          exact hyNotEarly (Set.mem_union_left _ hyEarly)
        have htx := late_firstInputTime hxA hxLate
        have hty := late_firstInputTime hyA hyLate
        change output (firstInputTime input x - 1) =
          output (firstInputTime input y - 1) at hxy
        have hsub := trajectory_output_injective family input hxy
        have htime : firstInputTime input x = firstInputTime input y := by omega
        calc
          x = input (firstInputTime input x) := (firstInputTime_spec hxA).symm
          _ = input (firstInputTime input y) := by rw [htime]
          _ = y := firstInputTime_spec hyA
      switchBudget := fun _ => 0
      switch_prefix_le := by
        intro n
        change (GenLimit.PatientScope.prefixFinset ∅ n).card ≤ 0
        simp [GenLimit.PatientScope.prefixFinset] }
  have hhalf := P.theorem_3_17 (hfamilyInfinite j) (by
    intro n
    change (GenLimit.PatientScope.prefixFinset ∅ n).card ≤
      Nat.log2 (GenLimit.PatientScope.prefixCount (family j) n)
    simp [GenLimit.PatientScope.prefixFinset])
  simpa [P, GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity,
    output] using hhalf

theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hn]
      · apply div_le_div_of_nonneg_right
        · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
        · exact_mod_cast (Nat.zero_le
            (GenLimit.PatientScope.prefixCount K n))
  · exact isBoundedUnder_of
      ⟨0, fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  · apply isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      norm_num
    · have hnPos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnPos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

theorem core_difference_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hstream : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input
        (trajectory (familyGenerator family) input) ∩ family j := by
  intro z hz
  have hcoreTarget : informationCore family input ⊆ family j := by
    intro w hw
    exact hw j hstream
  constructor
  · rw [← output_range_generatorFirst family input]
    rcases core_subset_announced family input hcore hz.1 with hzInput | hzOutput
    · exact False.elim (hz.2 hzInput)
    · exact hzOutput
  · exact hcoreTarget hz.1

end Stage3Case017Proof

open Stage3Case017

 theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamilyInfinite
  refine ⟨Stage3Case017Proof.familyGenerator family, ?_⟩
  intro input hinputInj hpresentation hcore
  let output := Stage3Case017Proof.trajectory
    (Stage3Case017Proof.familyGenerator family) input
  obtain ⟨T, hT⟩ := Stage3Case017Proof.eventually_prefix_agreement family input
  have hstable : ∀ t, T ≤ t →
      Stage3Case017Proof.activeSet family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
    intro t ht
    exact Stage3Case017Proof.stable_activeSet family input hT hcore ht
  refine ⟨output, ?_, ?_⟩
  · simpa [output] using
      Stage3Case017Proof.trajectory_follows
        (Stage3Case017Proof.familyGenerator family) input
  · intro j hstream
    have hcoreTarget : informationCore family input ⊆ family j := by
      intro z hz
      exact hz j hstream
    constructor
    · refine ⟨T, ?_⟩
      intro t ht
      refine ⟨hcoreTarget
          (Stage3Case017Proof.trajectory_mem_core_of_stable family input hstable ht),
        (by
          intro hsample
          apply Stage3Case017Proof.trajectory_fresh_input family input t
          rw [GenLimit.Generic.mem_sample_iff]
          rw [GenLimit.mem_sample_iff] at hsample
          exact hsample), ?_⟩
      intro s hs hEq
      have hst := Stage3Case017Proof.trajectory_output_injective family input
        (by simpa [output] using hEq)
      omega
    · apply max_le
      · simpa [output] using
          Stage3Case017Proof.half_core_density family hfamilyInfinite input
            hinputInj hcore hstable j hstream
      · apply Stage3Case017Proof.relativeLowerDensity_mono
        · simpa [output] using
            Stage3Case017Proof.core_difference_subset_generatorFirst
              family input hcore j hstream
        · exact Set.inter_subset_right
