import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Case017Proof

abbrev Language := Stage3Case017.Language
abbrev Stream := Stage3Case017.Stream
abbrev OnlineGenerator := Stage3Case017.OnlineGenerator

noncomputable def inputUsed {t : ℕ} (xs : Fin (t + 1) → ℕ) : Finset ℕ :=
  Finset.univ.image xs

noncomputable def outputUsed {t : ℕ} (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image ys

def available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Set ℕ :=
  {z | (∀ j, (∀ i, xs i ∈ family j) → z ∈ family j) ∧
    z ∉ inputUsed xs ∧ z ∉ outputUsed ys}

noncomputable def leastFresh {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : ℕ :=
  sInf (available family xs ys)

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) : OnlineGenerator :=
  fun _ xs ys => leastFresh family xs ys

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  Nat.lt_wfRel.wf.fix (fun t rec =>
    gen t (fun i => input i) (fun i => rec i.1 i.2))

theorem trajectory_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory, WellFounded.fix_eq]

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory_eq gen input t

private theorem eventually_stable_one {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    ∀ᶠ t in atTop,
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
  by_cases hj : GenLimit.Generic.StreamIn input (family j)
  · exact Eventually.of_forall fun _ =>
      ⟨fun _ => hj, fun _ i => hj ⟨i, rfl⟩⟩
  · have hbad := hj
    unfold GenLimit.Generic.StreamIn at hbad
    rw [Set.not_subset] at hbad
    obtain ⟨z, ⟨s, rfl⟩, hnot⟩ := hbad
    filter_upwards [eventually_ge_atTop s] with t ht
    constructor
    · intro h
      exact (hnot (h ⟨s, Nat.lt_succ_iff.mpr ht⟩)).elim
    · intro h
      exact (hj h).elim

theorem exists_stable_time {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
  have h : ∀ᶠ t in atTop, ∀ j,
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) :=
    Filter.eventually_all.mpr (eventually_stable_one family input)
  exact h.exists_forall_of_atTop

private theorem mem_inputUsed_iff {t : ℕ} (xs : Fin (t + 1) → ℕ) (z : ℕ) :
    z ∈ inputUsed xs ↔ ∃ i, xs i = z := by
  simp [inputUsed]

private theorem mem_outputUsed_iff {t : ℕ} (ys : Fin t → ℕ) (z : ℕ) :
    z ∈ outputUsed ys ↔ ∃ i, ys i = z := by
  simp [outputUsed]

theorem available_nonempty_after_stable {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T t : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (ht : T ≤ t) :
    (available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i)).Nonempty := by
  let used := inputUsed (fun i : Fin (t + 1) => input i) ∪
    outputUsed (fun i : Fin t => output i)
  obtain ⟨z, hzcore, hzused⟩ := hcore.exists_notMem_finset used
  refine ⟨z, ?_, ?_, ?_⟩
  · intro j hcons
    exact hzcore j ((hstable t ht j).mp hcons)
  · intro hz
    exact hzused (Finset.mem_union_left _ hz)
  · intro hz
    exact hzused (Finset.mem_union_right _ hz)

theorem output_available_after_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T t : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (ht : T ≤ t) :
    trajectory (familyGenerator family) input t ∈
      available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (familyGenerator family) input i) := by
  rw [trajectory_eq, familyGenerator, leastFresh]
  exact Nat.sInf_mem (available_nonempty_after_stable family input _ hcore hstable ht)

theorem output_le_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t z : ℕ}
    (hz : z ∈ available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (familyGenerator family) input i)) :
    trajectory (familyGenerator family) input t ≤ z := by
  rw [trajectory_eq, familyGenerator, leastFresh]
  exact Nat.sInf_le hz

theorem output_core_after_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T t : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (ht : T ≤ t) :
    trajectory (familyGenerator family) input t ∈
      Stage3Case017.informationCore family input := by
  intro j hj
  exact (output_available_after_stable family input hcore hstable ht).1 j
    ((hstable t ht j).mpr hj)

theorem output_not_input_through {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T t s : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (ht : T ≤ t) (hs : s ≤ t) :
    trajectory (familyGenerator family) input t ≠ input s := by
  intro heq
  have hav := (output_available_after_stable family input hcore hstable ht).2.1
  apply hav
  rw [mem_inputUsed_iff]
  exact ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, heq.symm⟩

theorem output_no_repeat {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T t s : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (ht : T ≤ t) (hs : s < t) :
    trajectory (familyGenerator family) input s ≠
      trajectory (familyGenerator family) input t := by
  intro heq
  have hav := (output_available_after_stable family input hcore hstable ht).2.2
  apply hav
  rw [mem_outputUsed_iff]
  exact ⟨⟨s, hs⟩, heq⟩

theorem novel_after_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (familyGenerator family) input) (family j) := by
  refine ⟨T, fun t ht => ?_⟩
  refine ⟨output_core_after_stable family input hcore hstable ht j hj, ?_, ?_⟩
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact output_not_input_through family input hcore hstable ht (Nat.lt_succ_iff.mp hs) heq.symm
  · intro s hs
    exact output_no_repeat family input hcore hstable ht hs


theorem core_unseen_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j))) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) := by
  intro z hz
  have hzrange : z ∈ Set.range (trajectory (familyGenerator family) input) := by
    by_contra hzout
    let tail : ℕ → ℕ := fun n => trajectory (familyGenerator family) input (T + n)
    have hinj : Function.Injective tail := by
      intro a b hab
      rcases lt_trichotomy a b with hablt | rfl | hbalt
      · exfalso
        exact output_no_repeat family input hcore hstable (show T ≤ T + b by omega)
          (show T + a < T + b by omega) hab
      · rfl
      · exfalso
        exact output_no_repeat family input hcore hstable (show T ≤ T + a by omega)
          (show T + b < T + a by omega) hab.symm
    have hrange : Set.range tail ⊆ Set.Iic z := by
      rintro y ⟨n, rfl⟩
      apply output_le_available family input
      refine ⟨?_, ?_, ?_⟩
      · intro j hcons
        exact hz.1 j ((hstable (T + n) (by omega) j).mp hcons)
      · intro hmem
        rw [mem_inputUsed_iff] at hmem
        obtain ⟨i, hi⟩ := hmem
        exact hz.2 ⟨i, hi⟩
      · intro hmem
        rw [mem_outputUsed_iff] at hmem
        obtain ⟨i, hi⟩ := hmem
        exact hzout ⟨i, hi⟩
    exact (Set.infinite_range_of_injective hinj) ((Set.finite_Iic z).subset hrange)
  obtain ⟨t, ht⟩ := hzrange
  refine ⟨t, ht, ?_⟩
  intro s hs heq
  exact hz.2 ⟨s, heq⟩

theorem core_unseen_generatorFirst_target {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j := by
  intro z hz
  exact ⟨core_unseen_generatorFirst family input hcore hstable hz, hz.1 j hj⟩

noncomputable def arrival (input : Stream) (z : ℕ) : ℕ :=
  sInf {t | input t = z}

theorem arrival_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (arrival input z) = z := by
  rw [arrival]
  change sInf {t | input t = z} ∈ {t | input t = z}
  apply Nat.sInf_mem
  obtain ⟨t, ht⟩ := hz
  exact ⟨t, ht⟩

theorem arrival_le (input : Stream) {z t : ℕ} (ht : input t = z) :
    arrival input z ≤ t := by
  exact Nat.sInf_le ht

noncomputable def latePartner (input output : Stream) (z : ℕ) : ℕ :=
  output (arrival input z - 1)

private theorem late_loser_facts {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    {z : ℕ}
    (hzcore : z ∈ Stage3Case017.informationCore family input)
    (hznotGF : z ∉ GenLimit.GeneratorFirst input
      (trajectory (familyGenerator family) input))
    (hzlate : z ∉ (GenLimit.sample input (T + 1) : Set ℕ)) :
    z ∈ Set.range input ∧ T < arrival input z ∧
      latePartner input (trajectory (familyGenerator family) input) z < z := by
  have hzrange : z ∈ Set.range input := by
    by_contra hznot
    exact hznotGF (core_unseen_generatorFirst family input hcore hstable ⟨hzcore, hznot⟩)
  have harrival : input (arrival input z) = z := arrival_spec input hzrange
  have hTarrival : T < arrival input z := by
    by_contra hnot
    apply hzlate
    simp only [GenLimit.sample, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨arrival input z, Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hnot), harrival⟩
  have hzavailable : z ∈ available family
      (fun i : Fin ((arrival input z - 1) + 1) => input i)
      (fun i : Fin (arrival input z - 1) =>
        trajectory (familyGenerator family) input i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hcons
      exact hzcore j ((hstable (arrival input z - 1) (by omega) j).mp hcons)
    · intro hmem
      rw [mem_inputUsed_iff] at hmem
      obtain ⟨i, hi⟩ := hmem
      have hi_lt : i.1 < arrival input z := by omega
      exact (Nat.not_lt_of_ge (arrival_le input hi)) hi_lt
    · intro hmem
      rw [mem_outputUsed_iff] at hmem
      obtain ⟨i, hi⟩ := hmem
      apply hznotGF
      refine ⟨i, hi, ?_⟩
      intro s hs heq
      have hs_lt : s < arrival input z := by omega
      exact hinj (heq.trans harrival.symm) |>.not_lt hs_lt
  have hle : latePartner input (trajectory (familyGenerator family) input) z ≤ z :=
    output_le_available family input hzavailable
  refine ⟨hzrange, hTarrival, lt_of_le_of_ne hle ?_⟩
  intro heq
  apply hznotGF
  refine ⟨arrival input z - 1, heq, ?_⟩
  intro s hs hsz
  have hs_lt : s < arrival input z := by omega
  exact hinj (hsz.trans harrival.symm) |>.not_lt hs_lt

theorem latePartner_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j))
    {z : ℕ}
    (hzcore : z ∈ Stage3Case017.informationCore family input)
    (hznotGF : z ∉ GenLimit.GeneratorFirst input
      (trajectory (familyGenerator family) input))
    (hzlate : z ∉ (GenLimit.sample input (T + 1) : Set ℕ)) :
    latePartner input (trajectory (familyGenerator family) input) z ∈
      GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j := by
  obtain ⟨hzrange, hTarrival, hpartner_lt⟩ :=
    late_loser_facts family input hinj hcore hstable hzcore hznotGF hzlate
  have harrival : input (arrival input z) = z := arrival_spec input hzrange
  have htime : T ≤ arrival input z - 1 := by omega
  refine ⟨?_, output_core_after_stable family input hcore hstable htime j hj⟩
  refine ⟨arrival input z - 1, rfl, ?_⟩
  intro s hs heq
  exact output_not_input_through family input hcore hstable htime hs heq.symm

theorem latePartner_lt {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    {z : ℕ}
    (hzcore : z ∈ Stage3Case017.informationCore family input)
    (hznotGF : z ∉ GenLimit.GeneratorFirst input
      (trajectory (familyGenerator family) input))
    (hzlate : z ∉ (GenLimit.sample input (T + 1) : Set ℕ)) :
    latePartner input (trajectory (familyGenerator family) input) z < z :=
  (late_loser_facts family input hinj hcore hstable hzcore hznotGF hzlate).2.2

theorem latePartner_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j))) :
    Set.InjOn (latePartner input (trajectory (familyGenerator family) input))
      (Stage3Case017.informationCore family input \
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∪
          (GenLimit.sample input (T + 1) : Set ℕ))) := by
  intro z₁ hz₁ z₂ hz₂ heq
  have hf₁ := late_loser_facts family input hinj hcore hstable hz₁.1
    (fun h => hz₁.2 (Or.inl h)) (fun h => hz₁.2 (Or.inr h))
  have hf₂ := late_loser_facts family input hinj hcore hstable hz₂.1
    (fun h => hz₂.2 (Or.inl h)) (fun h => hz₂.2 (Or.inr h))
  have htime : arrival input z₁ - 1 = arrival input z₂ - 1 := by
    rcases lt_trichotomy (arrival input z₁ - 1) (arrival input z₂ - 1) with hlt | he | hgt
    · exfalso
      exact output_no_repeat family input hcore hstable (show T ≤ arrival input z₂ - 1 by omega)
        hlt heq
    · exact he
    · exfalso
      exact output_no_repeat family input hcore hstable (show T ≤ arrival input z₁ - 1 by omega)
        hgt heq.symm
  have harrival : arrival input z₁ = arrival input z₂ := by omega
  calc
    z₁ = input (arrival input z₁) := (arrival_spec input hf₁.1).symm
    _ = input (arrival input z₂) := by rw [harrival]
    _ = z₂ := arrival_spec input hf₂.1


@[simp] theorem mem_prefixFinset (S : Set ℕ) (n z : ℕ) :
    z ∈ GenLimit.PatientScope.prefixFinset S n ↔ z < n ∧ z ∈ S := by
  classical
  simp [GenLimit.PatientScope.prefixFinset]

theorem late_prefix_count_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount
        (Stage3Case017.informationCore family input \
          (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∪
            (GenLimit.sample input (T + 1) : Set ℕ))) n ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j) n := by
  change (GenLimit.PatientScope.prefixFinset
      (Stage3Case017.informationCore family input \
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∪
          (GenLimit.sample input (T + 1) : Set ℕ))) n).card ≤
    (GenLimit.PatientScope.prefixFinset
      (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j) n).card
  apply Finset.card_le_card_of_injOn
    (latePartner input (trajectory (familyGenerator family) input))
  · intro z hz
    have hz' := (mem_prefixFinset
      (Stage3Case017.informationCore family input \
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∪
          (GenLimit.sample input (T + 1) : Set ℕ))) n z).mp hz
    apply (mem_prefixFinset
      (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j)
      n (latePartner input (trajectory (familyGenerator family) input) z)).mpr
    refine ⟨latePartner_lt family input hinj hcore hstable hz'.2.1
      (fun h => hz'.2.2 (Or.inl h)) (fun h => hz'.2.2 (Or.inr h)) |>.trans hz'.1, ?_⟩
    exact latePartner_mem family input hinj hcore hstable j hj hz'.2.1
      (fun h => hz'.2.2 (Or.inl h)) (fun h => hz'.2.2 (Or.inr h))
  · intro z₁ hz₁ z₂ hz₂ heq
    have hz₁' := (mem_prefixFinset
      (Stage3Case017.informationCore family input \
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∪
          (GenLimit.sample input (T + 1) : Set ℕ))) n z₁).mp hz₁
    have hz₂' := (mem_prefixFinset
      (Stage3Case017.informationCore family input \
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∪
          (GenLimit.sample input (T + 1) : Set ℕ))) n z₂).mp hz₂
    apply latePartner_injective family input hinj hcore hstable hz₁'.2 hz₂'.2 heq

theorem prefix_count_core_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n ≤
      (GenLimit.sample input (T + 1)).card +
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j) n := by
  let core := Stage3Case017.informationCore family input
  let gf := GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input)
  let early : Set ℕ := GenLimit.sample input (T + 1)
  let target := family j
  let late := core \ (gf ∪ early)
  let coreN := GenLimit.PatientScope.prefixFinset core n
  let earlyN := GenLimit.PatientScope.prefixFinset early n
  let defenderN := GenLimit.PatientScope.prefixFinset (gf ∩ target) n
  let lateN := GenLimit.PatientScope.prefixFinset late n
  have hsubset : coreN ⊆ (earlyN ∪ defenderN) ∪ lateN := by
    intro z hz
    have hz' : z < n ∧ z ∈ core := by
      simpa [coreN, GenLimit.PatientScope.prefixFinset] using hz
    by_cases hearly : z ∈ early
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simpa [earlyN, GenLimit.PatientScope.prefixFinset] using And.intro hz'.1 hearly
    · by_cases hgf : z ∈ gf
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        have htarget : z ∈ target := hz'.2 j hj
        simpa [defenderN, GenLimit.PatientScope.prefixFinset] using
          And.intro hz'.1 (And.intro hgf htarget)
      · apply Finset.mem_union_right
        have hzlate : z ∈ late := ⟨hz'.2, fun h => h.elim hgf hearly⟩
        simpa [lateN, GenLimit.PatientScope.prefixFinset] using And.intro hz'.1 hzlate
  have hearly : earlyN.card ≤ (GenLimit.sample input (T + 1)).card := by
    apply Finset.card_le_card
    intro z hz
    have hz' : z < n ∧ z ∈ early := by
      simpa [earlyN, GenLimit.PatientScope.prefixFinset] using hz
    exact hz'.2
  have hlate : lateN.card ≤ defenderN.card := by
    simpa [lateN, defenderN, late, core, gf, early, target,
      GenLimit.PatientScope.prefixCount] using
      late_prefix_count_le family input hinj hcore hstable j hj n
  have hcards : coreN.card ≤ earlyN.card + defenderN.card + lateN.card := by
    calc
      coreN.card ≤ ((earlyN ∪ defenderN) ∪ lateN).card := Finset.card_le_card hsubset
      _ ≤ (earlyN ∪ defenderN).card + lateN.card := Finset.card_union_le _ _
      _ ≤ (earlyN.card + defenderN.card) + lateN.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hfinal : coreN.card ≤ (GenLimit.sample input (T + 1)).card + 2 * defenderN.card := by
    omega
  simpa [coreN, defenderN, core, gf, target, GenLimit.PatientScope.prefixCount] using hfinal


theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  change (GenLimit.PatientScope.prefixFinset A n).card ≤
    (GenLimit.PatientScope.prefixFinset B n).card
  apply Finset.card_le_card
  intro z hz
  exact (mem_prefixFinset B n z).mpr
    ⟨((mem_prefixFinset A n z).mp hz).1, hAB ((mem_prefixFinset A n z).mp hz).2⟩

theorem density_ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

theorem density_ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero, Nat.eq_zero_of_le_zero (hzero ▸ prefixCount_mono hAK n)]
  · apply (div_le_one (by positivity : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n)).mpr
    exact_mod_cast prefixCount_mono hAK n

theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_mono hAB n)
        (by positivity)
  · exact isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun n => density_ratio_nonneg A K n)
  · exact isCoboundedUnder_ge_of_eventually_le atTop
      (Eventually.of_forall fun n => density_ratio_le_one hBK n)

theorem unseen_density_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j)
        (family j) := by
  apply relativeLowerDensity_mono
  · exact core_unseen_generatorFirst_target family input hcore hstable j hj
  · exact Set.inter_subset_right

theorem prefixCount_eq_indicator_sum (S : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount S n =
      ∑ k ∈ Finset.range n, S.indicator (fun _ => (1 : ℕ)) k := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Set.indicator_apply]

theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) Nat.zero_lt_one] at hK
  convert hK using 1
  funext n
  exact prefixCount_eq_indicator_sum K n

theorem half_core_density_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ u, T ≤ u → ∀ j,
      ((∀ i : Fin (u + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)))
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j))
    (hK : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j)
        (family j) := by
  let core := Stage3Case017.informationCore family input
  let defender := GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j
  let target := family j
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount core n : ℝ) /
      (GenLimit.PatientScope.prefixCount target n : ℝ)
  let d : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount defender n : ℝ) /
      (GenLimit.PatientScope.prefixCount target n : ℝ)
  let e : ℕ → ℝ := fun n =>
    ((GenLimit.sample input (T + 1)).card : ℝ) /
      (GenLimit.PatientScope.prefixCount target n : ℝ)
  change (1 / 2 : ℝ) * liminf a atTop ≤ liminf d atTop
  have ha_lower : IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop a :=
    isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun n => density_ratio_nonneg core target n)
  have hd_upper : IsCoboundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop d :=
    isCoboundedUnder_ge_of_eventually_le atTop
      (Eventually.of_forall fun n => density_ratio_le_one Set.inter_subset_right n)
  have hcount : Tendsto (GenLimit.PatientScope.prefixCount target) atTop atTop :=
    prefixCount_tendsto_atTop hK
  have hcast : Tendsto (fun n => (GenLimit.PatientScope.prefixCount target n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have he_zero : Tendsto e atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hcast
  have hpoint : ∀ n, a n ≤ e n + 2 * d n := by
    intro n
    have hnat := prefix_count_core_le family input hinj hcore hstable j hj n
    have hreal : (GenLimit.PatientScope.prefixCount core n : ℝ) ≤
        ((GenLimit.sample input (T + 1)).card : ℝ) +
          2 * (GenLimit.PatientScope.prefixCount defender n : ℝ) := by
      exact_mod_cast hnat
    dsimp [a, d, e, core, defender, target]
    calc
      (GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (family j) n : ℝ) ≤
        (((GenLimit.sample input (T + 1)).card : ℝ) +
            2 * (GenLimit.PatientScope.prefixCount
              (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j) n : ℝ)) /
          (GenLimit.PatientScope.prefixCount (family j) n : ℝ) :=
        div_le_div_of_nonneg_right hreal (by positivity)
      _ = ((GenLimit.sample input (T + 1)).card : ℝ) /
            (GenLimit.PatientScope.prefixCount (family j) n : ℝ) +
          2 * ((GenLimit.PatientScope.prefixCount
              (GenLimit.GeneratorFirst input (trajectory (familyGenerator family) input) ∩ family j) n : ℝ) /
            (GenLimit.PatientScope.prefixCount (family j) n : ℝ)) := by ring
  apply le_of_forall_lt
  intro c hc
  let c' : ℝ := (c + (1 / 2 : ℝ) * liminf a atTop) / 2
  have hcc' : c < c' := by
    dsimp [c']
    linarith
  have hc' : c' < (1 / 2 : ℝ) * liminf a atTop := by
    dsimp [c']
    linarith
  let b : ℝ := (2 * c' + liminf a atTop) / 2
  have hcb : 2 * c' < b := by
    dsimp [b]
    linarith
  have hba : b < liminf a atTop := by
    dsimp [b]
    linarith
  have ha_event : ∀ᶠ n in atTop, b < a n :=
    eventually_lt_of_lt_liminf hba ha_lower
  have he_event : ∀ᶠ n in atTop, e n < b - 2 * c' :=
    (tendsto_order.1 he_zero).2 _ (by linarith)
  have hc'lim : c' ≤ liminf d atTop := by
    apply le_liminf_of_le hd_upper
    filter_upwards [ha_event, he_event] with n han hen
    have := hpoint n
    linarith
  exact hcc'.trans_le hc'lim

end Case017Proof
