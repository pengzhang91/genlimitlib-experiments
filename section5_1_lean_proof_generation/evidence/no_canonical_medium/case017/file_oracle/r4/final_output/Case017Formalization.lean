import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def activeCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def leastOrZero (S : Set ℕ) : ℕ := by
  classical
  exact if h : S.Nonempty then sInf S else 0

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator :=
  fun t xs ys =>
    leastOrZero
      (activeCore family xs \ (Set.range xs ∪ Set.range ys))

noncomputable def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  Nat.strongRec
    (fun t previous =>
      gen t (fun i => input i) (fun i => previous i i.isLt)) t

theorem run_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    run gen input t =
      gen t (fun i => input i) (fun i => run gen input i) := by
  rw [run, Nat.strongRec_eq]
  congr

theorem follows_run (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  exact run_eq gen input t

theorem leastOrZero_mem {S : Set ℕ} (hS : S.Nonempty) :
    leastOrZero S ∈ S := by
  classical
  rw [leastOrZero, dif_pos hS]
  exact Nat.sInf_mem hS

theorem leastOrZero_le {S : Set ℕ} (hS : S.Nonempty) {z : ℕ} (hz : z ∈ S) :
    leastOrZero S ≤ z := by
  classical
  rw [leastOrZero, dif_pos hS]
  exact Nat.sInf_le hz

theorem exists_bad_time {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (hbad : ¬ GenLimit.Generic.StreamIn input (family j)) :
    ∃ n, input n ∉ family j := by
  rw [GenLimit.Generic.StreamIn] at hbad
  obtain ⟨z, ⟨n, rfl⟩, hz⟩ := Set.not_subset.mp hbad
  exact ⟨n, hz⟩

noncomputable def badTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (exists_bad_time family input j h)

theorem badTime_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (hbad : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (badTime family input j) ∉ family j := by
  classical
  rw [badTime, dif_neg hbad]
  exact Nat.find_spec (exists_bad_time family input j hbad)

noncomputable def stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  ∑ j, badTime family input j

theorem badTime_le_stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    badTime family input j ≤ stableTime family input := by
  classical
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem prefix_compatible_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stableTime family input ≤ t) (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hp
    by_contra hbad
    have hle := badTime_le_stableTime family input j
    have hlt : badTime family input j < t + 1 := by omega
    exact badTime_spec family input j hbad
      (hp ⟨badTime family input j, hlt⟩)
  · intro hs i
    exact hs ⟨i, rfl⟩

theorem activeCore_eq_informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stableTime family input ≤ t) :
    activeCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [activeCore, informationCore, Set.mem_setOf_eq]
  constructor <;> intro h j hj
  · exact h j ((prefix_compatible_iff family input ht j).2 hj)
  · exact h j ((prefix_compatible_iff family input ht j).1 hj)


theorem greedy_step {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    let output := run (greedyGenerator family) input
    output t ∈ informationCore family input ∧
      (∀ s, s ≤ t → input s ≠ output t) ∧
      (∀ s, s < t → output s ≠ output t) ∧
      ∀ z, z ∈ informationCore family input →
        (∀ s, s ≤ t → input s ≠ z) →
        (∀ s, s < t → output s ≠ z) → output t ≤ z := by
  classical
  let output := run (greedyGenerator family) input
  let S : Set ℕ :=
    activeCore family (fun i : Fin (t + 1) => input i) \ (Set.range (fun i : Fin (t + 1) => input i) ∪
        Set.range (fun i : Fin t => output i))
  have hforbidden :
      (Set.range (fun i : Fin (t + 1) => input i) ∪
        Set.range (fun i : Fin t => output i)).Finite :=
    (Set.finite_range (fun i : Fin (t + 1) => input i)).union
      (Set.finite_range (fun i : Fin t => output i))
  have hS : S.Nonempty := by
    by_contra hempty
    have hsub : informationCore family input ⊆
        Set.range (fun i : Fin (t + 1) => input i) ∪
          Set.range (fun i : Fin t => output i) := by
      intro z hz
      by_contra hznot
      apply hempty
      refine ⟨z, ?_, hznot⟩
      simpa [activeCore_eq_informationCore family input ht] using hz
    exact hcore (hforbidden.subset hsub)
  have hout : output t = leastOrZero S := by
    rw [show output t = run (greedyGenerator family) input t from rfl,
      run_eq]
    change leastOrZero
      (activeCore family (fun i : Fin (t + 1) => input i) \
        (Set.range (fun i : Fin (t + 1) => input i) ∪
          Set.range (fun i : Fin t => run (greedyGenerator family) input i))) =
      leastOrZero S
    rfl
  have houtS : output t ∈ S := by
    rw [hout]
    exact leastOrZero_mem hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← activeCore_eq_informationCore family input ht]
    exact houtS.1
  · intro s hst heq
    exact houtS.2 (Or.inl ⟨⟨s, by omega⟩, heq⟩)
  · intro s hst heq
    exact houtS.2 (Or.inr ⟨⟨s, hst⟩, heq⟩)
  · intro z hz hinput houtput
    have hzS : z ∈ S := by
      refine ⟨?_, ?_⟩
      · simpa [activeCore_eq_informationCore family input ht] using hz
      · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
        · exact hinput i (by omega) hi
        · exact houtput i i.isLt hi
    change output t ≤ z
    rw [hout]
    exact leastOrZero_le hS hzS


theorem output_tail_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    Set.InjOn (run (greedyGenerator family) input)
      {t | stableTime family input ≤ t} := by
  intro s hs t ht heq
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact False.elim ((greedy_step family input hcore ht).2.2.1 s hst heq)
  · rfl
  · exact False.elim ((greedy_step family input hcore hs).2.2.1 t hts heq.symm)

theorem core_eventually_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ informationCore family input) :
    ∃ t, input t = z ∨ run (greedyGenerator family) input t = z := by
  classical
  by_contra hnone
  push_neg at hnone
  let T := stableTime family input
  let output := run (greedyGenerator family) input
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨output (T + i), by
      have hleast := (greedy_step family input hcore
        (t := T + i) (by omega)).2.2.2 z hz
      have hinput : ∀ s ≤ T + i, input s ≠ z := by
        intro s hs
        exact hnone s |>.1
      have houtput : ∀ s < T + i, output s ≠ z := by
        intro s hs
        exact hnone s |>.2
      exact Nat.lt_succ_of_le (hleast hinput houtput)⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have htimes := output_tail_injective family input hcore
      (by simp [T]) (by simp [T]) (congrArg Fin.val hij)
    omega
  have hcard := Fintype.card_le_of_injective f hfinj
  simp at hcard



noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

theorem firstInput_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  rw [firstInput, dif_pos hz]
  exact Nat.find_spec hz

theorem firstInput_min (input : Stream) {z : ℕ} (hz : z ∈ Set.range input)
    {s : ℕ} (hs : input s = z) : firstInput input z ≤ s := by
  classical
  rw [firstInput, dif_pos hz]
  exact Nat.find_min' hz hs

theorem core_minus_input_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run (greedyGenerator family) input) := by
  intro z hz
  obtain ⟨t, hit | hout⟩ := core_eventually_announced family input hcore hz.1
  · exact False.elim (hz.2 ⟨t, hit⟩)
  · refine ⟨t, hout, ?_⟩
    intro s hst his
    exact hz.2 ⟨s, his⟩

theorem core_subset_target {m : ℕ} (family : Fin m → Language)
    (input : Stream) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

theorem late_partner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinput : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input
      (run (greedyGenerator family) input))
    (hlate : stableTime family input < firstInput input z) :
    let output := run (greedyGenerator family) input
    let p := firstInput input z - 1
    output p < z ∧
      output p ∈ informationCore family input ∧
      output p ∈ GenLimit.GeneratorFirst input output := by
  classical
  let output := run (greedyGenerator family) input
  let q := firstInput input z
  have hzrange : z ∈ Set.range input := by
    obtain ⟨t, hit | hout⟩ := core_eventually_announced family input hcore hzcore
    · exact ⟨t, hit⟩
    · by_contra hnrange
      apply hznot
      refine ⟨t, hout, ?_⟩
      intro s hst his
      exact hnrange ⟨s, his⟩
  have hqpos : 0 < q := by
    dsimp [q]
    omega
  have hpred : q - 1 + 1 = q := by omega
  have hstable : stableTime family input ≤ q - 1 := by omega
  have hstep := greedy_step family input hcore hstable
  have hz_prior_input : ∀ s, s ≤ q - 1 → input s ≠ z := by
    intro s hs his
    have hmin := firstInput_min input hzrange his
    omega
  have hz_prior_output : ∀ s, s < q - 1 → output s ≠ z := by
    intro s hs heq
    apply hznot
    refine ⟨s, heq, ?_⟩
    intro r hrs hir
    have hmin := firstInput_min input hzrange hir
    omega
  have hle : output (q - 1) ≤ z :=
    hstep.2.2.2 z hzcore hz_prior_input hz_prior_output
  have hne : output (q - 1) ≠ z := by
    intro heq
    apply hznot
    refine ⟨q - 1, heq, ?_⟩
    intro r hrs hir
    have hmin := firstInput_min input hzrange hir
    omega
  refine ⟨lt_of_le_of_ne hle hne, hstep.1, ?_⟩
  refine ⟨q - 1, rfl, ?_⟩
  intro r hrs
  exact hstep.2.1 r hrs



theorem core_not_generatorFirst_in_range {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input
      (run (greedyGenerator family) input)) :
    z ∈ Set.range input := by
  obtain ⟨t, hit | hout⟩ := core_eventually_announced family input hcore hzcore
  · exact ⟨t, hit⟩
  · by_contra hnrange
    apply hznot
    refine ⟨t, hout, ?_⟩
    intro s hst his
    exact hnrange ⟨s, his⟩

noncomputable def partner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (z : ℕ) : ℕ :=
  run (greedyGenerator family) input (firstInput input z - 1)

noncomputable def earlyValues {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Finset ℕ :=
  (Finset.range (stableTime family input + 1)).image input

theorem core_prefix_count_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinput : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (run (greedyGenerator family) input) ∩
          family j) n +
      (earlyValues family input).card := by
  classical
  let output := run (greedyGenerator family) input
  let G := GenLimit.GeneratorFirst input output
  let E := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let A := GenLimit.PatientScope.prefixFinset (informationCore family input \ G) n
  let D := GenLimit.PatientScope.prefixFinset (G ∩ family j) n
  let R := A.filter fun z => z ∉ earlyValues family input
  have hEsub : E ⊆ A ∪ D := by
    intro z hz
    have hz' := GenLimit.PatientScope.mem_prefixFinset.mp hz
    by_cases hzG : z ∈ G
    · exact Finset.mem_union_right _ <|
        GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨hz'.1, hzG, core_subset_target family input hj hz'.2⟩
    · exact Finset.mem_union_left _ <|
        GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hz'.1, hz'.2, hzG⟩
  have hAsub : A ⊆ R ∪ earlyValues family input := by
    intro z hz
    by_cases hearly : z ∈ earlyValues family input
    · exact Finset.mem_union_right _ hearly
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hearly⟩)
  have hRleD : R.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (partner family input)
    · intro z hz
      have hzR := Finset.mem_filter.mp hz
      have hzA := GenLimit.PatientScope.mem_prefixFinset.mp hzR.1
      have hzrange := core_not_generatorFirst_in_range family input hcore hzA.2.1 hzA.2.2
      have hlate : stableTime family input < firstInput input z := by
        by_contra hnot
        have hle : firstInput input z ≤ stableTime family input := Nat.le_of_not_gt hnot
        apply hzR.2
        rw [earlyValues, Finset.mem_image]
        exact ⟨firstInput input z, by simp; omega, firstInput_spec input hzrange⟩
      have hp := late_partner family input hinput hcore hzA.2.1 hzA.2.2 hlate
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      exact ⟨lt_trans hp.1 hzA.1, hp.2.2,
        core_subset_target family input hj hp.2.1⟩
    · intro x hx y hy hxy
      have hxR := Finset.mem_filter.mp hx
      have hyR := Finset.mem_filter.mp hy
      have hxA := GenLimit.PatientScope.mem_prefixFinset.mp hxR.1
      have hyA := GenLimit.PatientScope.mem_prefixFinset.mp hyR.1
      have hxrange := core_not_generatorFirst_in_range family input hcore hxA.2.1 hxA.2.2
      have hyrange := core_not_generatorFirst_in_range family input hcore hyA.2.1 hyA.2.2
      have hxlate : stableTime family input < firstInput input x := by
        by_contra hnot
        apply hxR.2
        rw [earlyValues, Finset.mem_image]
        exact ⟨firstInput input x, by simp; omega, firstInput_spec input hxrange⟩
      have hylate : stableTime family input < firstInput input y := by
        by_contra hnot
        apply hyR.2
        rw [earlyValues, Finset.mem_image]
        exact ⟨firstInput input y, by simp; omega, firstInput_spec input hyrange⟩
      have hpred := output_tail_injective family input hcore
        (show stableTime family input ≤ firstInput input x - 1 by omega)
        (show stableTime family input ≤ firstInput input y - 1 by omega) hxy
      have hfirst : firstInput input x = firstInput input y := by omega
      calc
        x = input (firstInput input x) := (firstInput_spec input hxrange).symm
        _ = input (firstInput input y) := congrArg input hfirst
        _ = y := firstInput_spec input hyrange
  calc
    GenLimit.PatientScope.prefixCount (informationCore family input) n = E.card := rfl
    _ ≤ (A ∪ D).card := Finset.card_le_card hEsub
    _ ≤ A.card + D.card := Finset.card_union_le _ _
    _ ≤ (R.card + (earlyValues family input).card) + D.card := by
      gcongr
      exact le_trans (Finset.card_le_card hAsub) (Finset.card_union_le _ _)
    _ ≤ (D.card + (earlyValues family input).card) + D.card := by omega
    _ = 2 * GenLimit.PatientScope.prefixCount (G ∩ family j) n +
        (earlyValues family input).card := by
      change (D.card + (earlyValues family input).card) + D.card =
        2 * D.card + (earlyValues family input).card
      omega



theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  let aRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let bRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hpoint : ∀ n, aRatio n ≤ bRatio n := by
    intro n
    dsimp [aRatio, bRatio]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
      (Nat.cast_nonneg _)
  have haNonneg : ∀ n, 0 ≤ aRatio n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbLeOne : ∀ n, bRatio n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [bRatio, hn]
    · dsimp [bRatio]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  unfold GenLimit.PatientScope.relativeLowerDensity
  exact liminf_le_liminf (Eventually.of_forall hpoint)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall haNonneg))
    (isCoboundedUnder_ge_of_le atTop hbLeOne)

theorem succeeds {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite) :
    SucceedsFor family (greedyGenerator family) := by
  intro input hinput hpresentation hcore
  let output := run (greedyGenerator family) input
  refine ⟨output, follows_run _ _, ?_⟩
  intro j hj
  have hcoreK : informationCore family input ⊆ family j :=
    core_subset_target family input hj
  constructor
  · refine ⟨stableTime family input, ?_⟩
    intro t ht
    have hstep := greedy_step family input hcore ht
    refine ⟨hcoreK hstep.1, ?_, hstep.2.2.1⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact hstep.2.1 s (by omega) heq
  · apply max_le
    · apply GenLimit.PatientScope.partialDensity_of_counting
        (GenLimit.PatientScope.prefixCount (family j))
        (GenLimit.PatientScope.prefixCount (informationCore family input))
        (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ family j))
        (earlyValues family input).card
      · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hfamily j)
      · intro n
        exact GenLimit.PatientScope.prefixCount_mono hcoreK n
      · intro n
        exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
      · intro n
        have hc := core_prefix_count_le family input hinput hcore hj n
        dsimp [output]
        exact le_trans hc (Nat.le_add_right _ _)
    · apply relativeLowerDensity_mono
      · intro z hz
        exact ⟨core_minus_input_subset_generatorFirst family input hcore hz,
          hcoreK hz.1⟩
      · exact Set.inter_subset_right



end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  exact ⟨Stage3Case017Proof.greedyGenerator family,
    Stage3Case017Proof.succeeds family hfamily⟩
