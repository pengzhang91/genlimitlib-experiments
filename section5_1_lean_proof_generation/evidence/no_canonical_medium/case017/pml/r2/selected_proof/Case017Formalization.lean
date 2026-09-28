import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Stage3Case017Proof

open Stage3Case017

abbrev Core {m : ℕ} (family : Fin m → Language) (input : Stream) :=
  informationCore family input

def PrefixCompatible {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (j : Fin m) : Prop :=
  ∀ i, input i ∈ family j

def visibleCore {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, PrefixCompatible family t input j → z ∈ family j}

def Available {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (prior : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ visibleCore family t input ∧
    (∀ i : Fin (t + 1), input i ≠ z) ∧
    (∀ i : Fin t, prior i ≠ z)

noncomputable def onlineRule {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t input prior =>
    if h : ∃ z, Available family t input prior z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream)
    (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

noncomputable def badTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (by
    simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using h)

noncomputable def stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  ∑ j : Fin m, badTime family input j

theorem badTime_le_stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    badTime family input j ≤ stableTime family input := by
  classical
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem prefixCompatible_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stableTime family input ≤ t)
    (j : Fin m) :
    PrefixCompatible family t (fun i => input i) j ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hp z hzrange
    obtain ⟨n, rfl⟩ := hzrange
    classical
    by_contra hn
    have hnot : ¬ GenLimit.Generic.StreamIn input (family j) := by
      intro hall
      exact hn (hall ⟨n, rfl⟩)
    have hfind : input (badTime family input j) ∉ family j := by
      simp only [badTime, dif_neg hnot]
      exact Nat.find_spec (by
        simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using hnot)
    have hle : badTime family input j ≤ t :=
      le_trans (badTime_le_stableTime family input j) ht
    exact hfind (hp ⟨badTime family input j, Nat.lt_succ_iff.mpr hle⟩)
  · intro hall i
    exact hall ⟨i, rfl⟩

theorem visibleCore_eq_core {m : ℕ}
    (family : Fin m → Language) (input : Stream) {t : ℕ}
    (ht : stableTime family input ≤ t) :
    visibleCore family t (fun i => input i) = Core family input := by
  ext z
  simp only [visibleCore, Core, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((prefixCompatible_iff family input ht j).2 hj)
  · intro hz j hj
    exact hz j ((prefixCompatible_iff family input ht j).1 hj)

theorem available_exists {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) (prior : Fin t → ℕ) :
    ∃ z, Available family t (fun i => input i) prior z := by
  classical
  let seen : Finset ℕ :=
    (Finset.univ.image fun i : Fin (t + 1) => input i) ∪
      (Finset.univ.image prior)
  obtain ⟨z, hzcore, hzseen⟩ := hcore.exists_notMem_finset seen
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [visibleCore_eq_core family input ht]
    exact hzcore
  · intro i hi
    apply hzseen
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  · intro i hi
    apply hzseen
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)

theorem onlineRule_spec {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (prior : Fin t → ℕ)
    (h : ∃ z, Available family t input prior z) :
    Available family t input prior
      (onlineRule family t input prior) := by
  classical
  simp only [onlineRule, dif_pos h]
  exact Nat.find_spec h

theorem onlineRule_minimal {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (prior : Fin t → ℕ)
    {z : ℕ} (hz : Available family t input prior z) :
    onlineRule family t input prior ≤ z := by
  classical
  let h : ∃ x, Available family t input prior x := ⟨z, hz⟩
  simp only [onlineRule, dif_pos h]
  exact Nat.find_min' h hz

noncomputable def output {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Stream := trajectory (onlineRule family) input

theorem output_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    Available family t (fun i => input i) (fun i => output family input i)
      (output family input t) := by
  rw [output, trajectory]
  apply onlineRule_spec
  exact available_exists family input hcore ht _

theorem output_minimal {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t z : ℕ}
    (hz : Available family t (fun i => input i) (fun i => output family input i) z) :
    output family input t ≤ z := by
  rw [output, trajectory]
  exact onlineRule_minimal family t _ _ hz

theorem output_tail_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite) :
    Function.Injective (fun n => output family input (stableTime family input + n)) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · have hs := output_spec family input hcore
      (show stableTime family input ≤ stableTime family input + b by omega)
    exact hs.2.2 ⟨stableTime family input + a, by omega⟩ hab
  · have hs := output_spec family input hcore
      (show stableTime family input ≤ stableTime family input + a by omega)
    exact hs.2.2 ⟨stableTime family input + b, by omega⟩ hab.symm

theorem tail_output_mem_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite) (n : ℕ) :
    output family input (stableTime family input + n) ∈ Core family input := by
  have ht : stableTime family input ≤ stableTime family input + n := by omega
  have hs := output_spec family input hcore ht
  have hs1 := hs.1
  rw [visibleCore_eq_core family input ht] at hs1
  exact hs1

theorem tail_output_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite) (n : ℕ) :
    output family input (stableTime family input + n) ∈
      GenLimit.GeneratorFirst input (output family input) := by
  let t := stableTime family input + n
  have ht : stableTime family input ≤ t := by omega
  have hs := output_spec family input hcore ht
  refine ⟨t, rfl, ?_⟩
  intro s hsle heq
  exact hs.2.1 ⟨s, Nat.lt_succ_iff.mpr hsle⟩ heq

theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite) :
    Core family input ⊆ Set.range input ∪ Set.range (output family input) := by
  intro z hz
  by_cases hin : z ∈ Set.range input
  · exact Set.mem_union_left _ hin
  by_cases hout : z ∈ Set.range (output family input)
  · exact Set.mem_union_right _ hout
  exfalso
  have havail : ∀ n, Available family (stableTime family input + n)
      (fun i => input i) (fun i => output family input i) z := by
    intro n
    refine ⟨?_, ?_, ?_⟩
    · rw [visibleCore_eq_core family input (by omega)]
      exact hz
    · intro i hi
      exact hin ⟨i, hi⟩
    · intro i hi
      exact hout ⟨i, hi⟩
  have hbound : ∀ n, output family input (stableTime family input + n) ≤ z :=
    fun n => output_minimal family input (havail n)
  have hfinite : Set.range (fun n => output family input
      (stableTime family input + n)) ⊆ Set.Iic z := by
    rintro _ ⟨n, rfl⟩
    exact hbound n
  exact (Set.infinite_range_of_injective (output_tail_injective family input hcore))
    ((Set.finite_Iic z).subset hfinite)

noncomputable def defender {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Set ℕ :=
  Set.range (fun n => output family input (stableTime family input + n))

noncomputable def attacker {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Set ℕ := Core family input \ defender family input

noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

theorem firstInputTime_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInputTime input z) = z := by
  classical
  simp only [firstInputTime, dif_pos hz]
  exact Nat.find_spec hz

theorem firstInputTime_min (input : Stream) {z t : ℕ}
    (hz : z ∈ Set.range input) (ht : input t = z) :
    firstInputTime input z ≤ t := by
  classical
  simp only [firstInputTime, dif_pos hz]
  exact Nat.find_min' hz ht

noncomputable def early {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Finset ℕ := by
  classical
  exact ((GenLimit.sample input (stableTime family input + 1)) ∪
    (GenLimit.sample (output family input) (stableTime family input))).filter
      (fun z => z ∈ attacker family input)

noncomputable def partner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (z : ℕ) : ℕ :=
  output family input (firstInputTime input z - 1)

theorem ordinary_in_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite)
    (K : Language) {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker K
      (attacker family input) ∅ (early family input)) : z ∈ Set.range input := by
  rcases core_covered family input hcore hz.1.1.1 with hin | hout
  · exact hin
  rcases hout with ⟨t, ht⟩
  by_cases htail : stableTime family input ≤ t
  · exfalso
    apply hz.1.1.2
    refine ⟨t - stableTime family input, ?_⟩
    simp only [defender]
    rw [← ht]
    congr
    omega
  · exfalso
    apply hz.2
    left
    classical
    change z ∈ (((GenLimit.sample input (stableTime family input + 1)) ∪
      (GenLimit.sample (output family input) (stableTime family input))).filter
        (fun x => x ∈ attacker family input))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union.mpr (Or.inr ?_), hz.1.1⟩
    rw [GenLimit.mem_sample_iff]
    exact ⟨t, Nat.lt_of_not_ge htail, ht⟩

theorem ordinary_time_gt {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite)
    (K : Language) {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker K
      (attacker family input) ∅ (early family input)) :
    stableTime family input < firstInputTime input z := by
  have hzin := ordinary_in_input family input hcore K hz
  by_contra hle
  apply hz.2
  left
  classical
  change z ∈ (((GenLimit.sample input (stableTime family input + 1)) ∪
    (GenLimit.sample (output family input) (stableTime family input))).filter
      (fun x => x ∈ attacker family input))
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_union.mpr (Or.inl ?_), hz.1.1⟩
  rw [GenLimit.mem_sample_iff]
  exact ⟨firstInputTime input z, by omega, firstInputTime_spec input hzin⟩

theorem partner_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite)
    (K : Language) (hsub : Core family input ⊆ K) {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker K
      (attacker family input) ∅ (early family input)) :
    partner family input z ∈ defender family input ∩ K := by
  have htime := ordinary_time_gt family input hcore K hz
  refine ⟨?_, ?_⟩
  · refine ⟨firstInputTime input z - 1 - stableTime family input, ?_⟩
    simp only [defender, partner]
    congr
    omega
  · apply hsub
    have ht : stableTime family input ≤ firstInputTime input z - 1 := by omega
    have hs := output_spec family input hcore ht
    have hs1 := hs.1
    rw [visibleCore_eq_core family input ht] at hs1
    exact hs1

theorem partner_lt {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite)
    (K : Language) {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker K
      (attacker family input) ∅ (early family input)) :
    partner family input z < z := by
  have hzatt : z ∈ attacker family input := hz.1.1
  have hzin := ordinary_in_input family input hcore K hz
  have htime := ordinary_time_gt family input hcore K hz
  let t := firstInputTime input z - 1
  have ht : stableTime family input ≤ t := by dsimp [t]; omega
  have havail : Available family t (fun i => input i) (fun i => output family input i) z := by
    refine ⟨?_, ?_, ?_⟩
    · rw [visibleCore_eq_core family input ht]
      exact hzatt.1
    · intro i hi
      have hmin := firstInputTime_min input hzin hi
      dsimp [t] at i
      omega
    · intro i hi
      by_cases histable : stableTime family input ≤ i
      · apply hzatt.2
        refine ⟨i - stableTime family input, ?_⟩
        change output family input
          (stableTime family input + (i - stableTime family input)) = z
        rw [Nat.add_sub_of_le histable]
        exact hi
      · apply hz.2
        left
        classical
        change z ∈ (((GenLimit.sample input (stableTime family input + 1)) ∪
          (GenLimit.sample (output family input) (stableTime family input))).filter
            (fun x => x ∈ attacker family input))
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_union.mpr (Or.inr ?_), hzatt⟩
        rw [GenLimit.mem_sample_iff]
        exact ⟨i, Nat.lt_of_not_ge histable, hi⟩
  have hle := output_minimal family input havail
  have hne : output family input t ≠ z := by
    intro heq
    apply hzatt.2
    refine ⟨t - stableTime family input, ?_⟩
    change output family input
      (stableTime family input + (t - stableTime family input)) = z
    rw [Nat.add_sub_of_le ht]
    exact heq
  change output family input t < z
  exact lt_of_le_of_ne hle hne

theorem partner_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite) (K : Language) :
    Set.InjOn (partner family input)
      (GenLimit.PatientScope.ordinaryAttacker K (attacker family input) ∅
        (early family input)) := by
  intro x hx y hy hxy
  have htx := ordinary_time_gt family input hcore K hx
  have hty := ordinary_time_gt family input hcore K hy
  have htailinj := output_tail_injective family input hcore
  have hindex : firstInputTime input x - 1 - stableTime family input =
      firstInputTime input y - 1 - stableTime family input := by
    apply htailinj
    have hxrepr : stableTime family input +
        (firstInputTime input x - 1 - stableTime family input) =
        firstInputTime input x - 1 := by omega
    have hyrepr : stableTime family input +
        (firstInputTime input y - 1 - stableTime family input) =
        firstInputTime input y - 1 := by omega
    change output family input
      (stableTime family input +
        (firstInputTime input x - 1 - stableTime family input)) =
      output family input
        (stableTime family input +
          (firstInputTime input y - 1 - stableTime family input))
    rw [hxrepr, hyrepr]
    simpa only [partner] using hxy
  have htimeeq : firstInputTime input x = firstInputTime input y := by omega
  have hxin := ordinary_in_input family input hcore K hx
  have hyin := ordinary_in_input family input hcore K hy
  calc
    x = input (firstInputTime input x) := (firstInputTime_spec input hxin).symm
    _ = input (firstInputTime input y) := by rw [htimeeq]
    _ = y := firstInputTime_spec input hyin

noncomputable def certificate {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite)
    (K : Language) (hsub : Core family input ⊆ K) :
    GenLimit.PatientScope.PartialEnumerationCertificate where
  target := K
  enumerated := Core family input
  enumerated_subset_target := hsub
  attacker := attacker family input
  defender := defender family input
  output := fun n => output family input (stableTime family input + n)
  output_range := rfl
  output_injective := output_tail_injective family input hcore
  validFrom := 0
  eventual_target := fun n _ => hsub (tail_output_mem_core family input hcore n)
  enumerated_covered := by
    intro z hz
    by_cases hd : z ∈ defender family input
    · exact Set.mem_union_right _ hd
    · exact Set.mem_union_left _ ⟨hz, hd⟩
  attacker_subset_target := fun _ hz => hsub hz.1
  ownership_disjoint := Set.disjoint_sdiff_left
  earlyAttacker := early family input
  switchLoss := ∅
  switchLoss_subset := by simp
  partner := partner family input
  partner_mem := fun _ hz => partner_mem family input hcore K hsub hz
  partner_lt := fun _ hz => partner_lt family input hcore K hz
  partner_injective := partner_injective family input hcore K
  switchBudget := fun _ => 0
  switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · apply Filter.Eventually.of_forall
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · have hle := GenLimit.PatientScope.prefixCount_mono hBK n
      have hBzero : GenLimit.PatientScope.prefixCount B n = 0 := by omega
      simp [hzero, hBzero]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      exact (div_le_div_iff_of_pos_right hpos).2 (by
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
  · exact Filter.isBoundedUnder_of ⟨0, fun n => div_nonneg
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  · exact Filter.isCoboundedUnder_ge_of_le (x := (1 : ℝ)) Filter.atTop (fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · have hle := GenLimit.PatientScope.prefixCount_mono hBK n
        have hBzero : GenLimit.PatientScope.prefixCount B n = 0 := by omega
        simp [hzero, hBzero]
      · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
          exact_mod_cast Nat.pos_of_ne_zero hzero
        rw [div_le_one hpos]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n)

theorem density_bounds {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Core family input).Infinite)
    (K : Language) (hK : K.Infinite) (hsub : Core family input ⊆ K) :
    max
        ((1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (Core family input) K)
        (GenLimit.PatientScope.relativeLowerDensity
          (Core family input \ Set.range input) K)
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input (output family input) ∩ K) K := by
  let P := certificate family input hcore K hsub
  have hhalf : (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
      (Core family input) K ≤ P.lowerDensity := by
    apply GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17 P hK
    intro n
    simp [P, certificate, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset,
      GenLimit.PatientScope.PartialEnumerationCertificate.targetCount]
  have hdef : defender family input ∩ K ⊆
      GenLimit.GeneratorFirst input (output family input) ∩ K := by
    rintro z ⟨⟨n, rfl⟩, hz⟩
    exact ⟨tail_output_generatorFirst family input hcore n, hz⟩
  have hhalf' : (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
      (Core family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (output family input) ∩ K) K := by
    exact le_trans hhalf (relativeLowerDensity_mono hdef Set.inter_subset_right)
  have hmissing : Core family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (output family input) ∩ K := by
    intro z hz
    rcases core_covered family input hcore hz.1 with hin | hout
    · exact False.elim (hz.2 hin)
    · rcases hout with ⟨n, hn⟩
      refine ⟨⟨n, hn, ?_⟩, hsub hz.1⟩
      intro s hsle hinput
      exact hz.2 ⟨s, hinput⟩
  exact max_le hhalf' (relativeLowerDensity_mono hmissing Set.inter_subset_right)

theorem succeeds {m : ℕ} (family : Fin m → Language)
    (hinfinite : ∀ j, (family j).Infinite) :
    SucceedsFor family (onlineRule family) := by
  intro input hinj hpresentation hcore
  refine ⟨output family input, trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨?_, ?_⟩
  · refine ⟨stableTime family input, ?_⟩
    intro t ht
    have hs := output_spec family input hcore ht
    refine ⟨?_, ?_, ?_⟩
    · have hmemcore : output family input t ∈ Core family input := by
        rw [← visibleCore_eq_core family input ht]
        exact hs.1
      exact hmemcore j hj
    · intro hsample
      rw [GenLimit.mem_sample_iff] at hsample
      obtain ⟨s, hslt, hseq⟩ := hsample
      exact hs.2.1 ⟨s, hslt⟩ hseq
    · intro s hslt heq
      exact hs.2.2 ⟨s, hslt⟩ heq
  · exact density_bounds family input hcore (family j) (hinfinite j)
      (fun z hz => hz j hj)

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  exact ⟨Stage3Case017Proof.onlineRule family,
    Stage3Case017Proof.succeeds family hinfinite⟩
