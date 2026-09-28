import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity
import GenLimit.Paper39_DenseGeneration.Partial.Trace

open Filter

namespace Case017Proof

open Stage3Case017

def PrefixCompatible {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) (j : Fin m) : Prop :=
  ∀ i, history i ∈ family j

def prefixCore {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) : Language :=
  {x | ∀ j, PrefixCompatible family history j → x ∈ family j}

noncomputable def activeSet {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) : Language := by
  classical
  exact if (prefixCore family history).Infinite then
    prefixCore family history
  else
    Set.univ

theorem activeSet_infinite {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) :
    (activeSet family history).Infinite := by
  classical
  simp only [activeSet]
  split
  · assumption
  · exact Set.infinite_univ

def Available {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) (x : ℕ) : Prop :=
  x ∈ activeSet family history ∧
    x ∉ GenLimit.Generic.sequenceSample history ∧
    x ∉ GenLimit.Generic.sequenceSample previous

theorem available_exists {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) :
    ∃ x, Available family history previous x := by
  classical
  obtain ⟨x, hx, hnot⟩ :=
    (activeSet_infinite family history).exists_notMem_finset
      (GenLimit.Generic.sequenceSample history ∪
        GenLimit.Generic.sequenceSample previous)
  simp only [Finset.mem_union, not_or] at hnot
  exact ⟨x, hx, hnot.1, hnot.2⟩

noncomputable def leastAvailable {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) : ℕ := by
  classical
  exact Nat.find (available_exists family history previous)

theorem leastAvailable_spec {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) :
    Available family history previous
      (leastAvailable family history previous) := by
  classical
  exact Nat.find_spec (available_exists family history previous)

theorem leastAvailable_minimal {m t : ℕ} (family : Fin m → Language)
    (history : Fin (t + 1) → ℕ) (previous : Fin t → ℕ) {x : ℕ}
    (hx : Available family history previous x) :
    leastAvailable family history previous ≤ x := by
  classical
  exact Nat.find_min' (available_exists family history previous) hx

noncomputable def generator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator :=
  fun _ history previous => leastAvailable family history previous

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream)
    (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
decreasing_by omega

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

theorem generator_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    Available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (generator family) input i)
      (trajectory (generator family) input t) := by
  rw [trajectory]
  exact leastAvailable_spec family _ _

theorem output_ne_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s ≤ t) :
    input s ≠ trajectory (generator family) input t := by
  intro heq
  have hnot := (generator_available family input t).2.1
  apply hnot
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  exact ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, heq⟩

theorem output_ne_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) {s t : ℕ} (hs : s < t) :
    trajectory (generator family) input s ≠
      trajectory (generator family) input t := by
  intro heq
  have hnot := (generator_available family input t).2.2
  apply hnot
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  exact ⟨⟨s, hs⟩, heq⟩

theorem output_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (trajectory (generator family) input) := by
  intro s t heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact output_ne_output family input hst heq
  · exact output_ne_output family input hts heq.symm

theorem exists_stabilization {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      PrefixCompatible family (fun i : Fin (t + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hexists : ∀ j : Fin m,
      ¬ GenLimit.Generic.StreamIn input (family j) →
        ∃ s, input s ∉ family j := by
    intro j hstream
    rw [GenLimit.Generic.StreamIn] at hstream
    obtain ⟨x, ⟨s, rfl⟩, hs⟩ := Set.not_subset.mp hstream
    exact ⟨s, hs⟩
  let threshold : Fin m → ℕ := fun j =>
    if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Classical.choose (hexists j h)
  refine ⟨∑ j, threshold j, ?_⟩
  intro t ht j
  have hjle : threshold j ≤ ∑ k, threshold k := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hjt : threshold j ≤ t := hjle.trans ht
  by_cases hstream : GenLimit.Generic.StreamIn input (family j)
  · constructor
    · exact fun _ => hstream
    · intro _ i
      exact hstream ⟨i, rfl⟩
  · have hbad : input (threshold j) ∉ family j := by
      simpa [threshold, hstream] using Classical.choose_spec (hexists j hstream)
    constructor
    · intro hprefix
      exact False.elim (hbad (hprefix ⟨threshold j, Nat.lt_succ_iff.mpr hjt⟩))
    · exact fun h => False.elim (hstream h)

theorem prefixCore_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) {t T : ℕ}
    (hstable : ∀ q, T ≤ q → ∀ j,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T ≤ t) :
    prefixCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext x
  simp only [prefixCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hx j hj
    exact hx j ((hstable t ht j).2 hj)
  · intro hx j hj
    exact hx j ((hstable t ht j).1 hj)

theorem activeSet_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) {t T : ℕ}
    (hstable : ∀ q, T ≤ q → ∀ j,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (ht : T ≤ t) :
    activeSet family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  classical
  rw [activeSet, prefixCore_eq_informationCore family input hstable ht]
  simp [hcore]

theorem output_mem_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hstable : ∀ q, T ≤ q → ∀ j,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (ht : T ≤ t) :
    trajectory (generator family) input t ∈ informationCore family input := by
  have hout := (generator_available family input t).1
  rwa [activeSet_eq_informationCore family input hstable hcore ht] at hout

theorem input_range_subset_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range input ⊆ informationCore family input := by
  rintro x ⟨t, rfl⟩ j hj
  exact hj ⟨t, rfl⟩

theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ q, T ≤ q → ∀ j,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (trajectory (generator family) input) := by
  classical
  intro x hx
  by_cases hin : x ∈ Set.range input
  · exact Set.mem_union_left _ hin
  · apply Set.mem_union_right
    by_contra hout
    have hle : ∀ q, T ≤ q → trajectory (generator family) input q ≤ x := by
      intro q hTq
      rw [trajectory]
      apply leastAvailable_minimal family
      refine ⟨?_, ?_, ?_⟩
      · rw [activeSet_eq_informationCore family input hstable hcore hTq]
        exact hx
      · intro hmem
        rw [GenLimit.Generic.mem_sequenceSample_iff] at hmem
        obtain ⟨i, hi⟩ := hmem
        exact hin ⟨i, hi⟩
      · intro hmem
        rw [GenLimit.Generic.mem_sequenceSample_iff] at hmem
        obtain ⟨i, hi⟩ := hmem
        exact hout ⟨i, hi⟩
    let f : Fin (x + 2) → Fin (x + 1) := fun i =>
      ⟨trajectory (generator family) input (T + i),
        Nat.lt_succ_iff.mpr (hle (T + i) (Nat.le_add_right T i))⟩
    have hf : Function.Injective f := by
      intro i k hik
      apply Fin.ext
      have houtEq : trajectory (generator family) input (T + i) =
          trajectory (generator family) input (T + k) := by
        exact congrArg Fin.val hik
      have htime := output_injective family input houtEq
      omega
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hcard
    omega

theorem relativeLowerDensity_mono {A B K : Language} (hAB : A ⊆ B)
    (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · exact isBoundedUnder_of ⟨0, fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  · have hratio_le_one : ∀ n,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
      intro n
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · have hBzero : GenLimit.PatientScope.prefixCount B n = 0 := by
          apply Nat.eq_zero_of_le_zero
          simpa [hzero] using GenLimit.PatientScope.prefixCount_mono hBK n
        simp [hzero, hBzero]
      · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
          exact_mod_cast Nat.pos_of_ne_zero hzero
        rw [div_le_one hpos]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
    exact isCoboundedUnder_ge_of_le atTop hratio_le_one

theorem generator_first_of_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    trajectory (generator family) input t ∈
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  exact ⟨t, rfl, fun s hs => output_ne_input family input t s hs⟩

theorem missing_core_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream) {T : ℕ}
    (hstable : ∀ q, T ≤ q → ∀ j,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  intro x hx
  obtain hxrange | hxrange := core_covered family input hstable hcore hx.1
  · exact False.elim (hx.2 hxrange)
  · obtain ⟨t, rfl⟩ := hxrange
    exact generator_first_of_output family input t

noncomputable def trace {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ)
    (hstable : ∀ q, T ≤ q → ∀ j,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    GenLimit.PartialEnumeration.PartialGameTrace where
  target := informationCore family input
  enumerated := Set.range input
  enumerated_subset_target := input_range_subset_core family input
  adversary := input
  generator := trajectory (generator family) input
  presents := rfl
  fresh_adversary := fun t s hst => output_ne_input family input t s hst
  fresh_generator := fun _ _ hst => output_ne_output family input hst
  validFrom := T
  eventual_target := fun _ ht => output_mem_core family input hstable hcore ht

theorem predecessor_comparison {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ q, T ≤ q → ∀ j,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    (trace family input T hstable hcore).HasPredecessorComparison ∅ := by
  intro t hTt hattacker hfresh _
  change T < t at hTt
  have hprev : T ≤ t - 1 := by omega
  obtain ⟨r, hr, hno⟩ := hattacker
  have htr : t ≤ r := by
    by_contra hnot
    apply hfresh
    rw [GenLimit.mem_sample_iff]
    exact ⟨r, Nat.lt_of_not_ge hnot, hr⟩
  have hxcore : input t ∈ informationCore family input :=
    input_range_subset_core family input ⟨t, rfl⟩
  have havail : Available family
      (fun i : Fin ((t - 1) + 1) => input i)
      (fun i : Fin (t - 1) => trajectory (generator family) input i)
      (input t) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [activeSet_eq_informationCore family input hstable hcore hprev]
      exact hxcore
    · intro hmem
      rw [GenLimit.Generic.mem_sequenceSample_iff] at hmem
      obtain ⟨i, hi⟩ := hmem
      apply hfresh
      rw [GenLimit.mem_sample_iff]
      exact ⟨i, by omega, hi⟩
    · intro hmem
      rw [GenLimit.Generic.mem_sequenceSample_iff] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact hno i (by omega) hi
  have hle : trajectory (generator family) input (t - 1) ≤ input t := by
    rw [trajectory]
    exact leastAvailable_minimal family _ _ havail
  have hne : trajectory (generator family) input (t - 1) ≠ input t := by
    exact hno (t - 1) (by omega)
  exact lt_of_le_of_ne hle hne

noncomputable def densityCertificate {m : ℕ}
    (family : Fin m → Language) (input : Stream) (j : Fin m) (T : ℕ)
    (hstable : ∀ q, T ≤ q → ∀ k,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) k ↔
        GenLimit.Generic.StreamIn input (family k))
    (hcore : (informationCore family input).Infinite)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.PartialEnumerationCertificate := by
  let G := trace family input T hstable hcore
  exact
    { target := family j
      enumerated := informationCore family input
      enumerated_subset_target := fun _ hx => hx j hj
      attacker := G.attacker
      defender := G.defender
      output := G.generator
      output_range := G.output_range
      output_injective := G.generator_injective
      validFrom := T
      eventual_target := fun t ht => (G.eventual_target t ht) j hj
      enumerated_covered := by
        intro x hx
        rcases core_covered family input hstable hcore hx with hin | hout
        · exact GenLimit.range_subset_first_announcements input G.generator hin
        · exact Set.mem_union_right _ (by rw [← G.output_range]; exact hout)
      attacker_subset_target := by
        rintro x ⟨t, rfl, -⟩
        exact hj ⟨t, rfl⟩
      ownership_disjoint := G.ownership_disjoint
      earlyAttacker := G.earlyAttacker
      switchLoss := ∅
      switchLoss_subset := by simp
      partner := G.predecessorPartner
      partner_mem := by
        intro x hx
        have hxcore : x ∈ informationCore family input := by
          obtain ⟨t, htx, -⟩ := hx.1.1
          exact input_range_subset_core family input ⟨t, htx⟩
        have hxG : x ∈ GenLimit.PatientScope.ordinaryAttacker
            G.target G.attacker (∅ : Set ℕ) G.earlyAttacker :=
          ⟨⟨hx.1.1, hxcore⟩, hx.2⟩
        have hp := G.predecessorPartner_mem hxG
        exact ⟨hp.1, hp.2 j hj⟩
      partner_lt := by
        intro x hx
        have hxcore : x ∈ informationCore family input := by
          obtain ⟨t, htx, -⟩ := hx.1.1
          exact input_range_subset_core family input ⟨t, htx⟩
        have hxG : x ∈ GenLimit.PatientScope.ordinaryAttacker
            G.target G.attacker (∅ : Set ℕ) G.earlyAttacker :=
          ⟨⟨hx.1.1, hxcore⟩, hx.2⟩
        exact G.predecessorPartner_lt
          (predecessor_comparison family input hstable hcore) hxG
      partner_injective := by
        intro x hx y hy hxy
        apply G.predecessorPartner_injective
        · have hxcore : x ∈ G.target := by
            obtain ⟨t, htx, -⟩ := hx.1.1
            exact input_range_subset_core family input ⟨t, htx⟩
          exact ⟨⟨hx.1.1, hxcore⟩, hx.2⟩
        · have hycore : y ∈ G.target := by
            obtain ⟨t, hty, -⟩ := hy.1.1
            exact input_range_subset_core family input ⟨t, hty⟩
          exact ⟨⟨hy.1.1, hycore⟩, hy.2⟩
        · exact hxy
      switchBudget := fun _ => 0
      switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset] }

end Case017Proof

namespace Case017Proof

open Stage3Case017

theorem density_bounds {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite) (input : Stream) (j : Fin m)
    {T : ℕ}
    (hstable : ∀ q, T ≤ q → ∀ k,
      PrefixCompatible family (fun i : Fin (q + 1) => input i) k ↔
        GenLimit.Generic.StreamIn input (family k))
    (hcore : (informationCore family input).Infinite)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) *
          GenLimit.PatientScope.relativeLowerDensity
            (informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input
            (trajectory (generator family) input) ∩ family j)
          (family j) := by
  apply max_le
  · let P := densityCertificate family input j T hstable hcore hj
    have hhalf :=
      GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17
        P (hfamily j) (by
          intro n
          simp [P, densityCertificate, GenLimit.PatientScope.prefixCount,
            GenLimit.PatientScope.prefixFinset])
    simpa only [P, densityCertificate,
      GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity,
      GenLimit.PartialEnumeration.PartialGameTrace.defender, trace] using hhalf
  · apply relativeLowerDensity_mono
    · intro x hx
      exact ⟨missing_core_subset_generatorFirst family input hstable hcore hx,
        hx.1 j hj⟩
    · exact Set.inter_subset_right

theorem succeeds {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite) :
    SucceedsFor family (generator family) := by
  intro input _ _ hcore
  obtain ⟨T, hstable⟩ := exists_stabilization family input
  refine ⟨trajectory (generator family) input,
    trajectory_follows (generator family) input, ?_⟩
  intro j hj
  constructor
  · refine ⟨T, ?_⟩
    intro t ht
    refine ⟨(output_mem_core family input hstable hcore ht) j hj, ?_, ?_⟩
    · intro hmem
      rw [GenLimit.mem_sample_iff] at hmem
      obtain ⟨s, hs, heq⟩ := hmem
      exact output_ne_input family input t s (by omega) heq
    · intro s hs
      exact output_ne_output family input hs
  · exact density_bounds family hfamily input j hstable hcore hj

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m _ family hfamily
  exact ⟨Case017Proof.generator family,
    Case017Proof.succeeds family hfamily⟩
