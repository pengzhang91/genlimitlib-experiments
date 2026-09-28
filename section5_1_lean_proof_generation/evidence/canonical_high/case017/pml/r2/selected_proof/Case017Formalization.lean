import Stage3Model
import GenLimit.Paper39_DenseGeneration.Partial.Trace
import GenLimit.Paper39_DenseGeneration.Abstract.TargetMain
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Case017

open GenLimit
open GenLimit.Generic
open GenLimit.PatientScope
open GenLimit.PartialEnumeration

abbrev Language := Stage3Case017.Language
abbrev Stream := Stage3Case017.Stream

noncomputable def prefixCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

noncomputable def leastFresh {t : ℕ} (C : Language) (hC : C.Infinite)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : ℕ := by
  classical
  exact Nat.find (hC.exists_notMem_finset (forbidden xs ys))

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    Stage3Case017.OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : (prefixCore family xs).Infinite then
      leastFresh (prefixCore family xs) h xs ys
    else
      leastFresh Set.univ Set.infinite_univ xs ys

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
decreasing_by exact i.isLt

@[simp] theorem trajectory_follows (gen : Stage3Case017.OnlineGenerator)
    (input : Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

private theorem leastFresh_spec {t : ℕ} (C : Language) (hC : C.Infinite)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    leastFresh C hC xs ys ∈ C ∧
      leastFresh C hC xs ys ∉ forbidden xs ys := by
  classical
  exact Nat.find_spec (hC.exists_notMem_finset (forbidden xs ys))

private theorem leastFresh_minimal {t : ℕ} (C : Language) (hC : C.Infinite)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hzC : z ∈ C) (hz : z ∉ forbidden xs ys) :
    leastFresh C hC xs ys ≤ z := by
  classical
  exact Nat.find_min' (hC.exists_notMem_finset (forbidden xs ys)) ⟨hzC, hz⟩

private theorem mem_forbidden_input {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (i : Fin (t + 1)) : xs i ∈ forbidden xs ys := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private theorem mem_forbidden_output {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (i : Fin t) : ys i ∈ forbidden xs ys := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private theorem greedy_fresh {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    greedyGenerator family t xs ys ∉ forbidden xs ys := by
  rw [greedyGenerator]
  split <;> exact (leastFresh_spec _ _ xs ys).2

private theorem greedy_mem_of_prefixCore_infinite {m t : ℕ}
    (family : Fin m → Language) (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (hcore : (prefixCore family xs).Infinite) :
    greedyGenerator family t xs ys ∈ prefixCore family xs := by
  rw [greedyGenerator, dif_pos hcore]
  exact (leastFresh_spec _ hcore xs ys).1

private theorem greedy_minimal_of_prefixCore_infinite {m t : ℕ}
    (family : Fin m → Language) (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (hcore : (prefixCore family xs).Infinite)
    {z : ℕ} (hzcore : z ∈ prefixCore family xs)
    (hzfresh : z ∉ forbidden xs ys) :
    greedyGenerator family t xs ys ≤ z := by
  rw [greedyGenerator, dif_pos hcore]
  exact leastFresh_minimal _ hcore xs ys hzcore hzfresh

private theorem output_fresh_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s ≤ t) :
    input s ≠ trajectory (greedyGenerator family) input t := by
  intro heq
  have hfresh := greedy_fresh family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (greedyGenerator family) input i)
  rw [← trajectory.eq_def (greedyGenerator family) input t] at hfresh
  apply hfresh
  rw [← heq]
  exact mem_forbidden_input _ _ ⟨s, Nat.lt_succ_iff.mpr hs⟩

private theorem output_fresh_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s < t) :
    trajectory (greedyGenerator family) input s ≠
      trajectory (greedyGenerator family) input t := by
  intro heq
  have hfresh := greedy_fresh family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (greedyGenerator family) input i)
  rw [← trajectory.eq_def (greedyGenerator family) input t] at hfresh
  apply hfresh
  rw [← heq]
  exact mem_forbidden_output _ _ ⟨s, hs⟩


private theorem input_mem_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) (t : ℕ) :
    input t ∈ Stage3Case017.informationCore family input := by
  intro j hj
  exact hj ⟨t, rfl⟩

private theorem prefixCore_stabilizes {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input := by
  have hj : ∀ j : Fin m, ∀ᶠ t : ℕ in Filter.atTop,
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hstream : GenLimit.Generic.StreamIn input (family j)
    · exact Filter.Eventually.of_forall fun _ =>
        ⟨fun _ => hstream, fun _ i => hstream ⟨i, rfl⟩⟩
    · rw [GenLimit.Generic.StreamIn, Set.not_subset] at hstream
      obtain ⟨x, ⟨s, hs⟩, hx⟩ := hstream
      subst x
      apply Filter.eventually_atTop.2
      refine ⟨s, fun t ht => ?_⟩
      constructor
      · intro hpref
        exact False.elim (hx (hpref ⟨s, by omega⟩))
      · intro hfalse
        exact False.elim (hx (hfalse ⟨s, rfl⟩))
  have hall : ∀ᶠ t : ℕ in Filter.atTop, ∀ j : Fin m,
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) :=
    Filter.eventually_all.2 hj
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hall
  refine ⟨T, fun t ht => ?_⟩
  ext z
  constructor
  · intro hz j hjstream
    exact hz j ((hT t ht j).2 hjstream)
  · intro hz j hjprefix
    exact hz j ((hT t ht j).1 hjprefix)

private theorem not_mem_forbidden_of_not_ranges {t : ℕ}
    (input output : Stream) {z : ℕ}
    (hzinput : z ∉ Set.range input) (hzoutput : z ∉ Set.range output) :
    z ∉ forbidden (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i) := by
  classical
  intro hz
  simp only [forbidden, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hz
  rcases hz with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact hzinput ⟨i, hi⟩
  · exact hzoutput ⟨i, hi⟩

private theorem output_mem_core_after {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input)
    {t : ℕ} (ht : T ≤ t) :
    trajectory (greedyGenerator family) input t ∈
      Stage3Case017.informationCore family input := by
  let xs : Fin (t + 1) → ℕ := fun i => input i
  let ys : Fin t → ℕ := fun i => trajectory (greedyGenerator family) input i
  have hprefix : (prefixCore family xs).Infinite := by
    rw [hstable t ht]
    exact hcore
  rw [trajectory.eq_def]
  have hmem := greedy_mem_of_prefixCore_infinite family xs ys hprefix
  rw [hstable t ht] at hmem
  exact hmem

private theorem output_le_core_of_unannounced {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input)
    {z t : ℕ} (hzcore : z ∈ Stage3Case017.informationCore family input)
    (hzinput : z ∉ Set.range input)
    (hzoutput : z ∉ Set.range (trajectory (greedyGenerator family) input))
    (ht : T ≤ t) :
    trajectory (greedyGenerator family) input t ≤ z := by
  let xs : Fin (t + 1) → ℕ := fun i => input i
  let ys : Fin t → ℕ := fun i => trajectory (greedyGenerator family) input i
  have hprefix : (prefixCore family xs).Infinite := by
    rw [hstable t ht]
    exact hcore
  have hzprefix : z ∈ prefixCore family xs := by
    rw [hstable t ht]
    exact hzcore
  have hzfresh : z ∉ forbidden xs ys :=
    not_mem_forbidden_of_not_ranges input _ hzinput hzoutput
  rw [trajectory.eq_def]
  exact greedy_minimal_of_prefixCore_infinite family xs ys hprefix hzprefix hzfresh

private theorem core_covered {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input) :
    Stage3Case017.informationCore family input ⊆
      Set.range input ∪ Set.range (trajectory (greedyGenerator family) input) := by
  intro z hzcore
  by_cases hzinput : z ∈ Set.range input
  · exact Or.inl hzinput
  · by_cases hzoutput : z ∈ Set.range (trajectory (greedyGenerator family) input)
    · exact Or.inr hzoutput
    · exfalso
      let f : Fin (z + 2) → Fin (z + 1) := fun i =>
        ⟨trajectory (greedyGenerator family) input (T + i), by
          have hle := output_le_core_of_unannounced family input hcore hstable
            hzcore hzinput hzoutput (show T ≤ T + i by omega)
          omega⟩
      have hf : Function.Injective f := by
        intro i j hij
        have hout : trajectory (greedyGenerator family) input (T + (i : ℕ)) =
            trajectory (greedyGenerator family) input (T + (j : ℕ)) :=
          congrArg Fin.val hij
        apply Fin.ext
        have ht : T + (i : ℕ) = T + (j : ℕ) := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hab | hba
          · exact output_fresh_output family input _ _ hab hout
          · exact output_fresh_output family input _ _ hba hout.symm
        omega
      have hcard := Fintype.card_le_of_injective f hf
      simp at hcard

private theorem has_predecessor_comparison {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hinputInjective : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (target : Language) (hinputTarget : Set.range input ⊆ target) {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input)
    (heventual : ∀ t, T ≤ t →
      trajectory (greedyGenerator family) input t ∈ target) :
    let output := trajectory (greedyGenerator family) input
    let G : GenLimit.PartialEnumeration.PartialGameTrace := {
      target := target
      enumerated := Set.range input
      enumerated_subset_target := hinputTarget
      adversary := input
      generator := output
      presents := rfl
      fresh_adversary := fun t s hst => output_fresh_input family input t s hst
      fresh_generator := fun t s hst => output_fresh_output family input t s hst
      validFrom := T
      eventual_target := heventual }
    G.HasPredecessorComparison ∅ := by
  dsimp
  intro t ht hattacker hnew _
  change T < t at ht
  change input t ∈ GenLimit.AdversaryFirst input
    (trajectory (greedyGenerator family) input) at hattacker
  change input t ∉ GenLimit.sample input t at hnew
  change trajectory (greedyGenerator family) input (t - 1) < input t
  have htPred : T ≤ t - 1 := by omega
  have hinputCore : input t ∈ Stage3Case017.informationCore family input :=
    input_mem_informationCore family input t
  have hprefix :
      (prefixCore family (fun i : Fin ((t - 1) + 1) => input i)).Infinite := by
    rw [hstable (t - 1) htPred]
    exact hcore
  have hattacker' : input t ∈ GenLimit.AdversaryFirst input
      (trajectory (greedyGenerator family) input) := hattacker
  obtain ⟨q, hqt, hnoOutput⟩ := hattacker'
  have hqt' : q = t := by
    apply hinputInjective
    exact hqt
  subst q
  have hfresh : input t ∉ forbidden
      (fun i : Fin ((t - 1) + 1) => input i)
      (fun i : Fin (t - 1) => trajectory (greedyGenerator family) input i) := by
    classical
    intro hmem
    simp only [forbidden, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨i, hi⟩ | ⟨i, hi⟩
    · apply hnew
      rw [GenLimit.mem_sample_iff]
      exact ⟨i, by omega, hi⟩
    · exact hnoOutput i (by omega) hi
  have hle : trajectory (greedyGenerator family) input (t - 1) ≤ input t := by
    rw [trajectory.eq_def]
    apply greedy_minimal_of_prefixCore_infinite family _ _ hprefix
    · rw [hstable (t - 1) htPred]
      exact hinputCore
    · exact hfresh
  exact lt_of_le_of_ne hle (hnoOutput (t - 1) (by omega))

private theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
      · exact Nat.cast_nonneg _
  · exact Filter.isBoundedUnder_of_eventually_ge <|
      Filter.Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply Filter.isCoboundedUnder_ge_of_le (x := (1 : ℝ)) Filter.atTop
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n

end Case017

open Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  refine ⟨greedyGenerator family, ?_⟩
  intro input hinjective _ hcore
  let output := trajectory (greedyGenerator family) input
  refine ⟨output, trajectory_follows _ _, ?_⟩
  obtain ⟨T, hstable⟩ := prefixCore_stabilizes family input
  intro j hj
  have hcoreTarget : Stage3Case017.informationCore family input ⊆ family j :=
    fun _ hz => hz j hj
  have hnovel : GenLimit.NovelGeneratesInLimit input output (family j) := by
    refine ⟨T, fun t ht => ⟨?_, ?_, ?_⟩⟩
    · exact hcoreTarget (output_mem_core_after family input hcore hstable ht)
    · intro hsample
      rw [GenLimit.mem_sample_iff] at hsample
      obtain ⟨s, hs, heq⟩ := hsample
      exact output_fresh_input family input t s (by omega) heq
    · exact fun s hs => output_fresh_output family input t s hs
  refine ⟨hnovel, ?_⟩
  let G : GenLimit.PartialEnumeration.PartialGameTrace := {
    target := family j
    enumerated := Set.range input
    enumerated_subset_target := hj
    adversary := input
    generator := output
    presents := rfl
    fresh_adversary := fun t s hst => output_fresh_input family input t s hst
    fresh_generator := fun t s hst => output_fresh_output family input t s hst
    validFrom := T
    eventual_target := fun t ht =>
      hcoreTarget (output_mem_core_after family input hcore hstable ht) }
  have hcompare : G.HasPredecessorComparison ∅ := by
    simpa [G, output] using
      has_predecessor_comparison family input hinjective hcore (family j) hj hstable
        (fun t ht => hcoreTarget
          (output_mem_core_after family input hcore hstable ht))
  let P : GenLimit.PatientScope.PartialEnumerationCertificate := {
    target := family j
    enumerated := Stage3Case017.informationCore family input
    enumerated_subset_target := hcoreTarget
    attacker := G.attacker
    defender := G.defender
    output := output
    output_range := G.output_range
    output_injective := G.generator_injective
    validFrom := T
    eventual_target := fun t ht =>
      hcoreTarget (output_mem_core_after family input hcore hstable ht)
    enumerated_covered := by
      intro z hz
      rcases core_covered family input hcore hstable hz with hzInput | hzOutput
      · exact GenLimit.range_subset_first_announcements input output hzInput
      · exact Set.mem_union_right _ <| by
          rw [← G.output_range]
          exact hzOutput
    attacker_subset_target := G.attacker_subset_target
    ownership_disjoint := G.ownership_disjoint
    earlyAttacker := G.earlyAttacker
    switchLoss := ∅
    switchLoss_subset := by simp
    partner := G.predecessorPartner
    partner_mem := fun _ hx => G.predecessorPartner_mem hx
    partner_lt := fun _ hx => G.predecessorPartner_lt hcompare hx
    partner_injective := G.predecessorPartner_injective
    switchBudget := fun _ => 0
    switch_prefix_le := by
      intro n
      simp [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset] }
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (Stage3Case017.informationCore family input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    have h := P.theorem_3_17 (hinfinite j) (by
      intro n
      simp [P, GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset])
    simpa [GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity,
      P, G] using h
  have hmissingSubset :
      Stage3Case017.informationCore family input \ Set.range input ⊆
        GenLimit.GeneratorFirst input output ∩ family j := by
    intro z hz
    refine ⟨?_, hcoreTarget hz.1⟩
    rcases core_covered family input hcore hstable hz.1 with hzInput | hzOutput
    · exact False.elim (hz.2 hzInput)
    · rcases hzOutput with ⟨t, rfl⟩
      exact ⟨t, rfl, fun s hs => output_fresh_input family input t s hs⟩
  have hmissing := relativeLowerDensity_mono hmissingSubset Set.inter_subset_right
  exact max_le hhalf hmissing
