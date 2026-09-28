import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.GameTrace
import GenLimit.Paper39_DenseGeneration.Abstract.TargetMain
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter

namespace Stage3Case017Proof

open Stage3Case017

def compatibleAt {m : ℕ} (family : Fin m → Language) (t : ℕ)
    (input : Fin (t + 1) → ℕ) (j : Fin m) : Prop :=
  ∀ i, input i ∈ family j

def approximateCore {m : ℕ} (family : Fin m → Language) (t : ℕ)
    (input : Fin (t + 1) → ℕ) : Language :=
  {x | ∀ j, compatibleAt family t input j → x ∈ family j}

def inputSeen (t : ℕ) (input : Fin (t + 1) → ℕ) : Finset ℕ :=
  Finset.univ.image input

def outputSeen (t : ℕ) (output : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image output

noncomputable def activeSet (S : Language) : Language :=
  by
    classical
    exact if _h : S.Infinite then S else Set.univ

theorem activeSet_infinite (S : Language) : (activeSet S).Infinite := by
  classical
  by_cases hS : S.Infinite
  · simpa [activeSet, hS] using hS
  · rw [activeSet, dif_neg hS]
    exact Set.infinite_univ

noncomputable def greedyGenerator {m : ℕ}
    (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t input output =>
    Nat.find ((activeSet_infinite (approximateCore family t input)).exists_notMem_finset
      (inputSeen t input ∪ outputSeen t output))

theorem greedyGenerator_spec {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    greedyGenerator family t input output ∈ activeSet (approximateCore family t input) ∧
      greedyGenerator family t input output ∉ inputSeen t input ∪ outputSeen t output := by
  classical
  simpa [greedyGenerator] using Nat.find_spec
    ((activeSet_infinite (approximateCore family t input)).exists_notMem_finset
      (inputSeen t input ∪ outputSeen t output))

theorem greedyGenerator_minimal {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) {x : ℕ}
    (hxSet : x ∈ activeSet (approximateCore family t input))
    (hxFresh : x ∉ inputSeen t input ∪ outputSeen t output) :
    greedyGenerator family t input output ≤ x := by
  classical
  simpa [greedyGenerator] using Nat.find_min'
    ((activeSet_infinite (approximateCore family t input)).exists_notMem_finset
      (inputSeen t input ∪ outputSeen t output)) ⟨hxSet, hxFresh⟩

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t => t

theorem trajectory_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory]

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory_eq gen input t

theorem greedy_fresh_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hst : s ≤ t) :
    input s ≠ trajectory (greedyGenerator family) input t := by
  classical
  intro heq
  have hnot := (greedyGenerator_spec family t (fun i => input i)
    (fun i => trajectory (greedyGenerator family) input i)).2
  apply hnot
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨⟨s, Nat.lt_succ_of_le hst⟩, Finset.mem_univ _, ?_⟩
  exact heq.trans (trajectory_eq (greedyGenerator family) input t)

theorem greedy_fresh_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hst : s < t) :
    trajectory (greedyGenerator family) input s ≠
      trajectory (greedyGenerator family) input t := by
  classical
  intro heq
  have hnot := (greedyGenerator_spec family t (fun i => input i)
    (fun i => trajectory (greedyGenerator family) input i)).2
  apply hnot
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨⟨s, hst⟩, Finset.mem_univ _, ?_⟩
  exact heq.trans (trajectory_eq (greedyGenerator family) input t)

theorem greedy_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Function.Injective (trajectory (greedyGenerator family) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact greedy_fresh_output family input t s hlt hst
  · exact greedy_fresh_output family input s t hgt hst.symm

theorem exists_bad_time_of_not_streamIn {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    ∃ t, input t ∉ family j := by
  obtain ⟨x, ⟨t, rfl⟩, hx⟩ := Set.not_subset.mp h
  exact ⟨t, hx⟩

noncomputable def rejectionTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ :=
  by
    classical
    exact if h : GenLimit.Generic.StreamIn input (family j) then 0
      else Nat.find (exists_bad_time_of_not_streamIn family input j h)

theorem compatibleAt_iff_of_rejectionTime_le {m : ℕ}
    (family : Fin m → Language) (input : Stream) (j : Fin m) {t : ℕ}
    (ht : rejectionTime family input j ≤ t) :
    compatibleAt family t (fun i => input i) j ↔
      GenLimit.Generic.StreamIn input (family j) := by
  classical
  by_cases hj : GenLimit.Generic.StreamIn input (family j)
  · exact ⟨fun _ => hj, fun _ i => hj ⟨i, rfl⟩⟩
  · have hw := Nat.find_spec (exists_bad_time_of_not_streamIn family input j hj)
    constructor
    · intro hcompat
      have htime : rejectionTime family input j =
          Nat.find (exists_bad_time_of_not_streamIn family input j hj) := by
        simp [rejectionTime, hj]
      have ht' : Nat.find (exists_bad_time_of_not_streamIn family input j hj) ≤ t := by
        rw [← htime]
        exact ht
      exact False.elim (hw (hcompat ⟨_, Nat.lt_succ_of_le ht'⟩))
    · exact fun h => False.elim (hj h)

noncomputable def stabilizationTime {m : ℕ}
    (family : Fin m → Language) (input : Stream) : ℕ :=
  Finset.univ.sup (rejectionTime family input)

theorem rejectionTime_le_stabilizationTime {m : ℕ}
    (family : Fin m → Language) (input : Stream) (j : Fin m) :
    rejectionTime family input j ≤ stabilizationTime family input := by
  classical
  exact Finset.le_sup (Finset.mem_univ j)

theorem approximateCore_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) {t : ℕ}
    (ht : stabilizationTime family input ≤ t) :
    approximateCore family t (fun i => input i) = informationCore family input := by
  ext x
  constructor
  · intro hx j hj
    apply hx j
    exact (compatibleAt_iff_of_rejectionTime_le family input j
      (le_trans (rejectionTime_le_stabilizationTime family input j) ht)).2 hj
  · intro hx j hj
    apply hx j
    exact (compatibleAt_iff_of_rejectionTime_le family input j
      (le_trans (rejectionTime_le_stabilizationTime family input j) ht)).1 hj

theorem greedy_eventual_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stabilizationTime family input ≤ t) :
    trajectory (greedyGenerator family) input t ∈ informationCore family input := by
  classical
  have hspec := (greedyGenerator_spec family t (fun i => input i)
    (fun i => trajectory (greedyGenerator family) input i)).1
  rw [approximateCore_eq_informationCore family input ht] at hspec
  rw [activeSet, dif_pos hcore] at hspec
  rw [trajectory_eq]
  exact hspec

theorem greedy_minimal_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t x : ℕ} (ht : stabilizationTime family input ≤ t)
    (hxCore : x ∈ informationCore family input)
    (hxInput : ∀ s, s ≤ t → input s ≠ x)
    (hxOutput : ∀ s, s < t → trajectory (greedyGenerator family) input s ≠ x) :
    trajectory (greedyGenerator family) input t ≤ x := by
  classical
  rw [trajectory_eq]
  apply greedyGenerator_minimal family
  · rw [approximateCore_eq_informationCore family input ht]
    rw [activeSet, dif_pos hcore]
    exact hxCore
  · rw [Finset.mem_union, not_or]
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, -, hi⟩
      exact hxInput i (Nat.le_of_lt_succ i.isLt) hi
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, -, hi⟩
      exact hxOutput i i.isLt hi

theorem omitted_core_mem_output_range {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {x : ℕ} (hxCore : x ∈ informationCore family input)
    (hxInput : x ∉ Set.range input) :
    x ∈ Set.range (trajectory (greedyGenerator family) input) := by
  classical
  by_contra hxOutput
  let T := stabilizationTime family input
  let tail : ℕ → ℕ := fun n => trajectory (greedyGenerator family) input (T + n)
  have htailInj : Function.Injective tail := by
    intro a b hab
    exact Nat.add_left_cancel
      (greedy_injective family input hab)
  have htailInfinite : (Set.range tail).Infinite :=
    Set.infinite_range_of_injective htailInj
  obtain ⟨y, ⟨n, rfl⟩, hy⟩ :=
    htailInfinite.exists_notMem_finset (Finset.range (x + 1))
  have hle : tail n ≤ x := by
    apply greedy_minimal_core family input hcore (t := T + n) (x := x)
    · exact Nat.le_add_right T n
    · exact hxCore
    · intro s hs hEq
      exact hxInput ⟨s, hEq⟩
    · intro s hs hEq
      exact hxOutput ⟨s, hEq⟩
  exact hy (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))

theorem core_covered_by_first_announcements {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (trajectory (greedyGenerator family) input) ∪
        GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  intro x hxCore
  by_cases hxInput : x ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input
      (trajectory (greedyGenerator family) input) hxInput
  · apply Set.mem_union_right
    obtain ⟨t, ht⟩ := omitted_core_mem_output_range family input hcore hxCore hxInput
    refine ⟨t, ht, ?_⟩
    intro s hs hEq
    exact hxInput ⟨s, hEq⟩

theorem omitted_core_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  rintro x ⟨hxCore, hxInput⟩
  obtain ⟨t, ht⟩ := omitted_core_mem_output_range family input hcore hxCore hxInput
  exact ⟨t, ht, fun s _ hEq => hxInput ⟨s, hEq⟩⟩

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
  · apply isBoundedUnder_of_eventually_ge
    exact Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact isCoboundedUnder_ge_of_le atTop (fun n => by
      show (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · have hle := GenLimit.PatientScope.prefixCount_mono hBK n
        have hBn : GenLimit.PatientScope.prefixCount B n = 0 := by omega
        simp [hn, hBn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n)

noncomputable def firstTime (input : Stream) (x : ℕ) : ℕ := by
  classical
  exact if h : x ∈ Set.range input then Nat.find h else 0

theorem firstTime_spec (input : Stream) {x : ℕ} (hx : x ∈ Set.range input) :
    input (firstTime input x) = x := by
  classical
  simp only [firstTime, dif_pos hx]
  exact Nat.find_spec hx

theorem firstTime_min (input : Stream) {x t : ℕ}
    (hx : x ∈ Set.range input) (ht : input t = x) :
    firstTime input x ≤ t := by
  classical
  simp only [firstTime, dif_pos hx]
  exact Nat.find_min' hx ht

def coreAttacker {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Language :=
  GenLimit.AdversaryFirst input (trajectory (greedyGenerator family) input) ∩
    informationCore family input

noncomputable def earlyAttacker {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Finset ℕ := by
  classical
  exact (GenLimit.sample input (stabilizationTime family input + 1)).filter
    (fun x => x ∈ coreAttacker family input)

noncomputable def greedyPartner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (x : ℕ) : ℕ :=
  trajectory (greedyGenerator family) input (firstTime input x - 1)

theorem ordinary_attacker_late {m : ℕ} (family : Fin m → Language)
    (input : Stream) (K : Language) {x : ℕ}
    (hx : x ∈ GenLimit.PatientScope.ordinaryAttacker K
      (coreAttacker family input)
      ∅ (earlyAttacker family input)) :
    stabilizationTime family input < firstTime input x := by
  classical
  have hxAttacker : x ∈ GenLimit.AdversaryFirst input
      (trajectory (greedyGenerator family) input) := hx.1.1.1
  obtain ⟨t, htx, -⟩ := hxAttacker
  have hxRange : x ∈ Set.range input := ⟨t, htx⟩
  have hxNotEarly : x ∉ earlyAttacker family input := by
    intro hearly
    exact hx.2 (Set.mem_union_left _ hearly)
  by_contra hnot
  have hle : firstTime input x ≤ stabilizationTime family input :=
    Nat.le_of_not_gt hnot
  apply hxNotEarly
  apply Finset.mem_filter.mpr
  refine ⟨?_, hx.1.1⟩
  rw [GenLimit.mem_sample_iff]
  exact ⟨firstTime input x, Nat.lt_succ_of_le hle, firstTime_spec input hxRange⟩

theorem greedyPartner_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hcoreK : informationCore family input ⊆ K) {x : ℕ}
    (hx : x ∈ GenLimit.PatientScope.ordinaryAttacker K
      (coreAttacker family input)
      ∅ (earlyAttacker family input)) :
    greedyPartner family input x ∈
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩ K := by
  classical
  have hxAttacker : x ∈ GenLimit.AdversaryFirst input
      (trajectory (greedyGenerator family) input) := hx.1.1.1
  obtain ⟨t, htx, hnoOutput⟩ := hxAttacker
  have hxRange : x ∈ Set.range input := ⟨t, htx⟩
  have hlate := ordinary_attacker_late family input K hx
  have hpred : stabilizationTime family input ≤ firstTime input x - 1 := by omega
  have hcoreMem : greedyPartner family input x ∈ informationCore family input := by
    exact greedy_eventual_core family input hcore hpred
  refine ⟨?_, hcoreK hcoreMem⟩
  refine ⟨firstTime input x - 1, rfl, ?_⟩
  intro s hs
  exact greedy_fresh_input family input (firstTime input x - 1) s hs

theorem greedyPartner_lt {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) {x : ℕ}
    (hx : x ∈ GenLimit.PatientScope.ordinaryAttacker K
      (coreAttacker family input)
      ∅ (earlyAttacker family input)) :
    greedyPartner family input x < x := by
  classical
  have hxAttacker : x ∈ GenLimit.AdversaryFirst input
      (trajectory (greedyGenerator family) input) := hx.1.1.1
  obtain ⟨t, htx, hnoOutput⟩ := hxAttacker
  have hxRange : x ∈ Set.range input := ⟨t, htx⟩
  have hfirstLe : firstTime input x ≤ t := firstTime_min input hxRange htx
  have hlate := ordinary_attacker_late family input K hx
  have hpred : stabilizationTime family input ≤ firstTime input x - 1 := by omega
  have hle : greedyPartner family input x ≤ x := by
    apply greedy_minimal_core family input hcore hpred hx.1.1.2
    · intro s hs hEq
      have hmin := firstTime_min input hxRange hEq
      omega
    · intro s hs hEq
      exact hnoOutput s (lt_of_lt_of_le (by omega) hfirstLe) hEq
  have hne : greedyPartner family input x ≠ x := by
    intro hEq
    exact hnoOutput (firstTime input x - 1)
      (lt_of_lt_of_le (by omega) hfirstLe) hEq
  omega

theorem greedyPartner_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (K : Language) :
    Set.InjOn (greedyPartner family input)
      (GenLimit.PatientScope.ordinaryAttacker K
        (coreAttacker family input)
        ∅ (earlyAttacker family input)) := by
  classical
  intro x hx y hy hxy
  have hxAttacker : x ∈ GenLimit.AdversaryFirst input
      (trajectory (greedyGenerator family) input) := hx.1.1.1
  have hyAttacker : y ∈ GenLimit.AdversaryFirst input
      (trajectory (greedyGenerator family) input) := hy.1.1.1
  obtain ⟨tx, htx, -⟩ := hxAttacker
  obtain ⟨ty, hty, -⟩ := hyAttacker
  have hxRange : x ∈ Set.range input := ⟨tx, htx⟩
  have hyRange : y ∈ Set.range input := ⟨ty, hty⟩
  have htimesPred : firstTime input x - 1 = firstTime input y - 1 :=
    greedy_injective family input hxy
  have hxLate := ordinary_attacker_late family input K hx
  have hyLate := ordinary_attacker_late family input K hy
  have htimes : firstTime input x = firstTime input y := by omega
  calc
    x = input (firstTime input x) := (firstTime_spec input hxRange).symm
    _ = input (firstTime input y) := by rw [htimes]
    _ = y := firstTime_spec input hyRange

noncomputable def partialCertificate {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    (K : Language) (hinputK : GenLimit.Generic.StreamIn input K)
    (hcoreK : informationCore family input ⊆ K) :
    GenLimit.PatientScope.PartialEnumerationCertificate := by
  classical
  let output := trajectory (greedyGenerator family) input
  let attacker := coreAttacker family input
  let defender := GenLimit.GeneratorFirst input output
  refine
    { target := K
      enumerated := informationCore family input
      enumerated_subset_target := hcoreK
      attacker := attacker
      defender := defender
      output := output
      output_range := ?_
      output_injective := greedy_injective family input
      validFrom := stabilizationTime family input
      eventual_target := ?_
      enumerated_covered := ?_
      attacker_subset_target := ?_
      ownership_disjoint := ?_
      earlyAttacker := earlyAttacker family input
      switchLoss := ∅
      switchLoss_subset := by simp
      partner := greedyPartner family input
      partner_mem := ?_
      partner_lt := ?_
      partner_injective := ?_
      switchBudget := fun _ => 0
      switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset] }
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl, greedy_fresh_input family input t⟩
    · rintro ⟨t, htx, -⟩
      exact ⟨t, htx⟩
  · intro t ht
    exact hcoreK (greedy_eventual_core family input hcore ht)
  · intro x hx
    rcases core_covered_by_first_announcements family input hcore hx with hxA | hxD
    · exact Set.mem_union_left _ ⟨hxA, hx⟩
    · exact Set.mem_union_right _ hxD
  · intro x hx
    exact hcoreK hx.2
  · rw [Set.disjoint_left]
    intro x hxA hxD
    exact Set.disjoint_left.mp
      (GenLimit.adversaryFirst_disjoint_generatorFirst input output)
      hxA.1 hxD
  · intro x hx
    simpa [attacker, defender] using
      (greedyPartner_mem family input hcore K hcoreK hx)
  · intro x hx
    simpa [attacker] using
      (greedyPartner_lt family input hcore K hx)
  · simpa [attacker] using greedyPartner_injective family input K

theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hinputK : GenLimit.Generic.StreamIn input K)
    (hcoreK : informationCore family input ⊆ K) (hK : K.Infinite) :
    (1 / 2 : ℝ) *
        GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) ∩ K) K := by
  let P := partialCertificate family input hcore K hinputK hcoreK
  have hlog : ∀ n, GenLimit.PatientScope.prefixCount P.switchLoss n ≤
      Nat.log2 (P.targetCount n) := by
    intro n
    simp [P, partialCertificate, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]
  have hhalf := P.theorem_3_17 hK hlog
  simpa [P, GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity,
    partialCertificate] using hhalf

theorem omitted_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hcoreK : informationCore family input ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) ∩ K) K := by
  apply relativeLowerDensity_mono
  · intro x hx
    exact ⟨omitted_core_subset_generatorFirst family input hcore hx,
      hcoreK hx.1⟩
  · exact Set.inter_subset_right

theorem density_max_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hinputK : GenLimit.Generic.StreamIn input K)
    (hcoreK : informationCore family input ⊆ K) (hK : K.Infinite) :
    max
        ((1 / 2 : ℝ) *
          GenLimit.PatientScope.relativeLowerDensity
            (informationCore family input) K)
        (GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) K) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) ∩ K) K := by
  apply max_le
  · exact half_core_density family input hcore K hinputK hcoreK hK
  · exact omitted_core_density family input hcore K hcoreK

theorem greedy_novel_generates {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hcoreK : informationCore family input ⊆ K) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (greedyGenerator family) input) K := by
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  refine ⟨hcoreK (greedy_eventual_core family input hcore ht), ?_, ?_⟩
  · intro hx
    rw [GenLimit.mem_sample_iff] at hx
    obtain ⟨s, hs, heq⟩ := hx
    exact greedy_fresh_input family input t s (Nat.le_of_lt_succ hs) heq
  · intro s hs
    exact greedy_fresh_output family input t s hs

end Stage3Case017Proof
