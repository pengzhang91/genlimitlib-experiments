import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def inputSample {t : ℕ} (xs : Fin (t + 1) → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs

noncomputable def outputSample {t : ℕ} (ys : Fin t → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample ys

def prefixCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : ∃ z, z ∈ prefixCore family xs ∧
        z ∉ inputSample xs ∧ z ∉ outputSample ys then
      Nat.find h
    else
      Nat.find (Finset.exists_nat_subset_range
        (inputSample xs ∪ outputSample ys))

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  WellFounded.fix Nat.lt_wfRel.wf fun t rec =>
    gen t (fun i => input i) (fun i => rec i i.isLt)

@[simp] theorem trajectory_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory, WellFounded.fix_eq]

@[simp] theorem mem_inputSample {t : ℕ} {xs : Fin (t + 1) → ℕ} {z : ℕ} :
    z ∈ inputSample xs ↔ ∃ i, xs i = z := by
  exact GenLimit.Generic.mem_sequenceSample_iff

@[simp] theorem mem_outputSample {t : ℕ} {ys : Fin t → ℕ} {z : ℕ} :
    z ∈ outputSample ys ↔ ∃ i, ys i = z := by
  exact GenLimit.Generic.mem_sequenceSample_iff

theorem greedy_not_input {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    greedyGenerator family t xs ys ∉ inputSample xs := by
  classical
  unfold greedyGenerator
  split_ifs with h
  · exact (Nat.find_spec h).2.1
  · intro hmem
    have hlt := Nat.find_spec (Finset.exists_nat_subset_range
      (inputSample xs ∪ outputSample ys))
      (Finset.mem_union_left _ hmem)
    exact (Nat.lt_irrefl _) (Finset.mem_range.mp hlt)

theorem greedy_not_output {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    greedyGenerator family t xs ys ∉ outputSample ys := by
  classical
  unfold greedyGenerator
  split_ifs with h
  · exact (Nat.find_spec h).2.2
  · intro hmem
    have hlt := Nat.find_spec (Finset.exists_nat_subset_range
      (inputSample xs ∪ outputSample ys))
      (Finset.mem_union_right _ hmem)
    exact (Nat.lt_irrefl _) (Finset.mem_range.mp hlt)

theorem greedy_mem_core_of_exists {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, z ∈ prefixCore family xs ∧
      z ∉ inputSample xs ∧ z ∉ outputSample ys) :
    greedyGenerator family t xs ys ∈ prefixCore family xs := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact (Nat.find_spec h).1

theorem greedy_le_of_available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hz : z ∈ prefixCore family xs)
    (hxi : z ∉ inputSample xs) (hyo : z ∉ outputSample ys) :
    greedyGenerator family t xs ys ≤ z := by
  classical
  let h : ∃ w, w ∈ prefixCore family xs ∧
      w ∉ inputSample xs ∧ w ∉ outputSample ys := ⟨z, hz, hxi, hyo⟩
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_min' h ⟨hz, hxi, hyo⟩

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory_eq gen input t

theorem greedy_trajectory_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (trajectory (greedyGenerator family) input) := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · exfalso
    have hnot := greedy_not_output family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (greedyGenerator family) input i)
    rw [← trajectory_eq (greedyGenerator family) input t] at hnot
    apply hnot
    rw [mem_outputSample]
    exact ⟨⟨s, hlt⟩, hst⟩
  · rfl
  · exfalso
    have hnot := greedy_not_output family
      (fun i : Fin (s + 1) => input i)
      (fun i : Fin s => trajectory (greedyGenerator family) input i)
    rw [← trajectory_eq (greedyGenerator family) input s] at hnot
    apply hnot
    rw [mem_outputSample]
    exact ⟨⟨t, hgt⟩, hst.symm⟩

theorem greedy_trajectory_avoids_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    trajectory (greedyGenerator family) input t ∉
      GenLimit.Generic.sample input (t + 1) := by
  have hnot := greedy_not_input family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (greedyGenerator family) input i)
  rw [← trajectory_eq (greedyGenerator family) input t] at hnot
  intro hsample
  rw [GenLimit.Generic.mem_sample_iff] at hsample
  obtain ⟨s, hst, hs⟩ := hsample
  apply hnot
  rw [mem_inputSample]
  exact ⟨⟨s, hst⟩, hs⟩

theorem exists_bad_time {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    ∃ t, input t ∉ family j := by
  by_contra hall
  apply h
  rintro _ ⟨t, rfl⟩
  exact Classical.not_not.mp (fun hbad => hall ⟨t, hbad⟩)

noncomputable def badWitness {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (exists_bad_time family input j h)

noncomputable def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  Finset.univ.sup (badWitness family input)

theorem badWitness_le_stabilization {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    badWitness family input j ≤ stabilizationTime family input := by
  classical
  exact Finset.le_sup (Finset.mem_univ j)

theorem prefixCore_eq_informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stabilizationTime family input ≤ t) :
    prefixCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  classical
  ext z
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact hj ⟨i, rfl⟩
  · intro hz j hjprefix
    apply hz j
    rintro _ ⟨q, rfl⟩
    by_contra hbad
    have hnot : ¬ GenLimit.Generic.StreamIn input (family j) := by
      intro hall
      exact hbad (hall ⟨q, rfl⟩)
    have hw : input (badWitness family input j) ∉ family j := by
      simp only [badWitness, dif_neg hnot]
      exact Nat.find_spec (exists_bad_time family input j hnot)
    have hle : badWitness family input j ≤ t :=
      le_trans (badWitness_le_stabilization family input j) ht
    exact hw (hjprefix ⟨badWitness family input j, Nat.lt_succ_iff.mpr hle⟩)

end Stage3Case017Proof

namespace Stage3Case017Proof

open Stage3Case017

variable {m : ℕ} (family : Fin m → Language) (input : Stream)

local notation "G" => greedyGenerator family
local notation "out" => trajectory G input
local notation "core" => informationCore family input
local notation "S" => stabilizationTime family input

theorem exists_available (hcore : (core).Infinite) {t : ℕ} (ht : S ≤ t) :
    ∃ z, z ∈ prefixCore family (fun i : Fin (t + 1) => input i) ∧
      z ∉ inputSample (fun i : Fin (t + 1) => input i) ∧
      z ∉ outputSample (fun i : Fin t => out i) := by
  classical
  obtain ⟨z, hzcore, hz⟩ := hcore.exists_not_mem_finset
    (inputSample (fun i : Fin (t + 1) => input i) ∪
      outputSample (fun i : Fin t => out i))
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [prefixCore_eq_informationCore family input ht]
    exact hzcore
  · intro hmem
    exact hz (Finset.mem_union_left _ hmem)
  · intro hmem
    exact hz (Finset.mem_union_right _ hmem)

theorem eventual_output_mem_core (hcore : (core).Infinite) {t : ℕ} (ht : S ≤ t) :
    out t ∈ core := by
  have havail := exists_available family input hcore ht
  rw [trajectory_eq]
  have hmem := greedy_mem_core_of_exists family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => out i) havail
  rw [prefixCore_eq_informationCore family input ht] at hmem
  exact hmem

theorem generatorFirst_eq_range :
    GenLimit.GeneratorFirst input out = Set.range out := by
  ext z
  constructor
  · rintro ⟨t, rfl, -⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t, rfl, ?_⟩
    intro s hst heq
    have havoid := greedy_trajectory_avoids_input family input t
    apply havoid
    rw [GenLimit.Generic.mem_sample_iff]
    exact ⟨s, Nat.lt_succ_iff.mpr hst, heq⟩

theorem output_le_of_core_not_announced (hcore : (core).Infinite)
    {z t : ℕ} (ht : S ≤ t) (hzcore : z ∈ core)
    (hzinput : z ∉ Set.range input) (hzoutput : z ∉ Set.range out) :
    out t ≤ z := by
  rw [trajectory_eq]
  apply greedy_le_of_available family
  · rw [prefixCore_eq_informationCore family input ht]
    exact hzcore
  · intro hmem
    rw [mem_inputSample] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact hzinput ⟨i, hi⟩
  · intro hmem
    rw [mem_outputSample] at hmem
    obtain ⟨i, hi⟩ := hmem
    exact hzoutput ⟨i, hi⟩

theorem core_subset_input_or_output (hcore : (core).Infinite) :
    core ⊆ Set.range input ∪ Set.range out := by
  intro z hzcore
  by_cases hzin : z ∈ Set.range input
  · exact Or.inl hzin
  · apply Or.inr
    by_contra hzout
    let f : Fin (z + 2) → Fin (z + 1) := fun k =>
      ⟨out (S + k), Nat.lt_succ_iff.mpr
        (output_le_of_core_not_announced family input hcore
          (Nat.le_add_right S k) hzcore hzin hzout)⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      have hout : out (S + (a : ℕ)) = out (S + (b : ℕ)) := by
        simpa only [f] using congrArg (fun q : Fin (z + 1) => (q : ℕ)) hab
      exact Nat.add_left_cancel ((greedy_trajectory_injective family input) hout)
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hcard
    omega

theorem core_covered_by_first (hcore : (core).Infinite) :
    core ⊆ GenLimit.AdversaryFirst input out ∪
      GenLimit.GeneratorFirst input out := by
  intro z hz
  rcases core_subset_input_or_output family input hcore hz with hzin | hzout
  · exact GenLimit.range_subset_first_announcements input out hzin
  · exact Or.inr <| by
      rw [generatorFirst_eq_range family input]
      exact hzout

theorem eventual_novel (hcore : (core).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input out (family j) := by
  refine ⟨S, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_⟩
  · exact (eventual_output_mem_core family input hcore ht) j hj
  · intro hsample
    have havoid := greedy_trajectory_avoids_input family input t
    apply havoid
    rw [GenLimit.Generic.mem_sample_iff]
    rw [GenLimit.mem_sample_iff] at hsample
    exact hsample
  · intro s hst heq
    exact (Nat.ne_of_lt hst) ((greedy_trajectory_injective family input) heq)

end Stage3Case017Proof

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

noncomputable def earlySet {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Finset ℕ :=
  (Finset.range (stabilizationTime family input + 1)).image input

noncomputable def predecessorPartner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (z : ℕ) : ℕ :=
  trajectory (greedyGenerator family) input (firstInput input z - 1)

theorem firstInput_spec {input : Stream} {z : ℕ} (h : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  obtain ⟨t, ht⟩ := h
  have hex : ∃ q, input q = z := ⟨t, ht⟩
  simp only [firstInput, dif_pos hex]
  exact Nat.find_spec hex

theorem firstInput_min {input : Stream} {z q : ℕ} (h : z ∈ Set.range input)
    (hq : input q = z) : firstInput input z ≤ q := by
  classical
  obtain ⟨t, ht⟩ := h
  have hex : ∃ r, input r = z := ⟨t, ht⟩
  simp only [firstInput, dif_pos hex]
  exact Nat.find_min' hex hq

theorem firstInput_eq_of_injective {input : Stream} (hinj : Function.Injective input)
    {z t : ℕ} (ht : input t = z) : firstInput input z = t := by
  apply hinj
  rw [firstInput_spec ⟨t, ht⟩, ht]

theorem firstInput_gt_stabilization_of_not_early {m : ℕ}
    (family : Fin m → Language) (input : Stream) {z : ℕ}
    (hzrange : z ∈ Set.range input) (hzearly : z ∉ earlySet family input) :
    stabilizationTime family input < firstInput input z := by
  by_contra hle
  apply hzearly
  unfold earlySet
  rw [Finset.mem_image]
  exact ⟨firstInput input z,
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hle)),
    firstInput_spec hzrange⟩

theorem partner_properties {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker
      (informationCore family input)
      (GenLimit.AdversaryFirst input (trajectory (greedyGenerator family) input))
      ∅ (earlySet family input)) :
    predecessorPartner family input z ∈
        GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
          informationCore family input ∧
      predecessorPartner family input z < z := by
  classical
  let out := trajectory (greedyGenerator family) input
  have hzatt : z ∈ GenLimit.AdversaryFirst input out := hz.1.1
  have hzcore : z ∈ informationCore family input := hz.1.2
  have hzearly : z ∉ earlySet family input := by
    intro hearly
    exact hz.2 (by simp [hearly])
  obtain ⟨t, htz, hnoout⟩ := hzatt
  have hp : firstInput input z = t := firstInput_eq_of_injective hinj htz
  have hzrange : z ∈ Set.range input := ⟨t, htz⟩
  have hSlt : stabilizationTime family input < firstInput input z :=
    firstInput_gt_stabilization_of_not_early family input hzrange hzearly
  have hpos : 0 < firstInput input z := lt_of_le_of_lt (Nat.zero_le _) hSlt
  have hS : stabilizationTime family input ≤ firstInput input z - 1 := by omega
  have hzinput : z ∉ inputSample
      (fun i : Fin ((firstInput input z - 1) + 1) => input i) := by
    intro hmem
    rw [mem_inputSample] at hmem
    obtain ⟨q, hq⟩ := hmem
    have hqle : q < firstInput input z := by omega
    exact (Nat.ne_of_lt hqle) (firstInput_eq_of_injective hinj hq).symm
  have hzoutput : z ∉ outputSample
      (fun i : Fin (firstInput input z - 1) => out i) := by
    intro hmem
    rw [mem_outputSample] at hmem
    obtain ⟨q, hq⟩ := hmem
    have hqt : q < t := by omega
    exact hnoout q hqt hq
  have hzprefix : z ∈ prefixCore family
      (fun i : Fin ((firstInput input z - 1) + 1) => input i) := by
    rw [prefixCore_eq_informationCore family input hS]
    exact hzcore
  have hle : predecessorPartner family input z ≤ z := by
    unfold predecessorPartner
    rw [trajectory_eq]
    exact greedy_le_of_available family _ _ hzprefix hzinput hzoutput
  have hne : predecessorPartner family input z ≠ z := by
    intro heq
    have hqt : firstInput input z - 1 < t := by omega
    exact hnoout _ hqt heq
  refine ⟨?_, lt_of_le_of_ne hle hne⟩
  constructor
  · rw [generatorFirst_eq_range family input]
    exact ⟨firstInput input z - 1, rfl⟩
  · exact eventual_output_mem_core family input hcore hS

theorem partner_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) :
    Set.InjOn (predecessorPartner family input)
      (GenLimit.PatientScope.ordinaryAttacker
        (informationCore family input)
        (GenLimit.AdversaryFirst input (trajectory (greedyGenerator family) input))
        ∅ (earlySet family input)) := by
  intro x hx y hy hxy
  have hxprop := partner_properties family input hinj hcore hx
  have hyprop := partner_properties family input hinj hcore hy
  have hxrange : x ∈ Set.range input := by
    obtain ⟨t, htx, -⟩ := hx.1.1
    exact ⟨t, htx⟩
  have hyrange : y ∈ Set.range input := by
    obtain ⟨t, hty, -⟩ := hy.1.1
    exact ⟨t, hty⟩
  have hxnot : x ∉ earlySet family input := by
    intro hearly
    exact hx.2 (by simp [hearly])
  have hynot : y ∉ earlySet family input := by
    intro hearly
    exact hy.2 (by simp [hearly])
  have hxgt := firstInput_gt_stabilization_of_not_early family input hxrange hxnot
  have hygt := firstInput_gt_stabilization_of_not_early family input hyrange hynot
  have hpred : firstInput input x - 1 = firstInput input y - 1 := by
    apply greedy_trajectory_injective family input
    simpa only [predecessorPartner] using hxy
  have hfirst : firstInput input x = firstInput input y := by omega
  calc
    x = input (firstInput input x) := (firstInput_spec hxrange).symm
    _ = input (firstInput input y) := by rw [hfirst]
    _ = y := firstInput_spec hyrange

end Stage3Case017Proof

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def densityCertificate {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) :
    GenLimit.PatientScope.PartialEnumerationCertificate where
  target := informationCore family input
  enumerated := informationCore family input
  enumerated_subset_target := Set.Subset.rfl
  attacker := GenLimit.AdversaryFirst input
    (trajectory (greedyGenerator family) input) ∩ informationCore family input
  defender := GenLimit.GeneratorFirst input
    (trajectory (greedyGenerator family) input)
  output := trajectory (greedyGenerator family) input
  output_range := (generatorFirst_eq_range family input).symm
  output_injective := greedy_trajectory_injective family input
  validFrom := stabilizationTime family input
  eventual_target := fun t ht => eventual_output_mem_core family input hcore ht
  enumerated_covered := by
    intro z hz
    rcases core_covered_by_first family input hcore hz with hza | hzg
    · exact Or.inl ⟨hza, hz⟩
    · exact Or.inr hzg
  attacker_subset_target := Set.inter_subset_right
  ownership_disjoint :=
    (GenLimit.adversaryFirst_disjoint_generatorFirst _ _).mono
      Set.inter_subset_left Set.Subset.rfl
  earlyAttacker := earlySet family input
  switchLoss := ∅
  switchLoss_subset := by simp
  partner := predecessorPartner family input
  partner_mem := by
    intro z hz
    have hz' : z ∈ GenLimit.PatientScope.ordinaryAttacker
        (informationCore family input)
        (GenLimit.AdversaryFirst input (trajectory (greedyGenerator family) input))
        ∅ (earlySet family input) := by
      simpa [GenLimit.PatientScope.ordinaryAttacker] using hz
    exact (partner_properties family input hinj hcore hz').1
  partner_lt := by
    intro z hz
    have hz' : z ∈ GenLimit.PatientScope.ordinaryAttacker
        (informationCore family input)
        (GenLimit.AdversaryFirst input (trajectory (greedyGenerator family) input))
        ∅ (earlySet family input) := by
      simpa [GenLimit.PatientScope.ordinaryAttacker] using hz
    exact (partner_properties family input hinj hcore hz').2
  partner_injective := by
    intro x hx y hy hxy
    apply partner_injective family input hinj hcore
    · simpa [GenLimit.PatientScope.ordinaryAttacker] using hx
    · simpa [GenLimit.PatientScope.ordinaryAttacker] using hy
    · exact hxy
  switchBudget := fun _ => 0
  switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j))
    (hK : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
          family j) (family j) := by
  let P := densityCertificate family input hinj hcore
  have hlog : ∀ n, GenLimit.PatientScope.prefixCount P.switchLoss n ≤
      Nat.log2 (P.targetCount n) := by
    intro n
    dsimp [P, densityCertificate]
    simp [GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]
  apply GenLimit.PatientScope.partialDensity_of_counting
    (GenLimit.PatientScope.prefixCount (family j))
    (GenLimit.PatientScope.prefixCount (informationCore family input))
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
        family j))
    P.earlyAttacker.card
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  · intro n
    apply GenLimit.PatientScope.prefixCount_mono
    intro z hz
    exact hz j hj
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have hcount := P.enumeratedCount_le_two_mul_defender hlog n
    have hdef : P.defenderCount n ≤
        GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
            family j) n := by
      apply GenLimit.PatientScope.prefixCount_mono
      intro z hz
      exact ⟨hz.1, hz.2 j hj⟩
    have hlogmono : Nat.log2 (P.targetCount n) ≤
        Nat.log2 (GenLimit.PatientScope.prefixCount (family j) n) := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      apply Nat.log_mono_right
      apply GenLimit.PatientScope.prefixCount_mono
      intro z hz
      exact hz j hj
    change GenLimit.PatientScope.prefixCount (informationCore family input) n ≤ _ at hcount ⊢
    exact le_trans hcount (by omega)

theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · exact isBoundedUnder_of_eventually_ge <| Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ)) ?_
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

theorem missing_core_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  intro z hz
  rw [generatorFirst_eq_range family input]
  rcases core_subset_input_or_output family input hcore hz.1 with hzin | hzout
  · exact False.elim (hz.2 hzin)
  · exact hzout

end Stage3Case017Proof
