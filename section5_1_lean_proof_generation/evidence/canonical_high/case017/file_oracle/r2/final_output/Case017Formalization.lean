import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity
import Mathlib

open Filter
open scoped Topology

namespace Case017Formalization

open Stage3Case017

noncomputable def prefixCore {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def usedValues {t : ℕ}
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs ∪ GenLimit.Generic.sequenceSample ys

lemma exists_nat_not_mem (s : Finset ℕ) : ∃ z, z ∉ s := by
  refine ⟨s.sup id + 1, ?_⟩
  intro hz
  have hle : s.sup id + 1 ≤ s.sup id := by
    simpa using Finset.le_sup (f := id) hz
  omega

noncomputable def pickFresh (S : Set ℕ) (used : Finset ℕ) : ℕ := by
  classical
  exact if h : ∃ z, z ∈ S ∧ z ∉ used then Nat.find h
    else Classical.choose (exists_nat_not_mem used)

lemma pickFresh_not_mem (S : Set ℕ) (used : Finset ℕ) :
    pickFresh S used ∉ used := by
  classical
  unfold pickFresh
  split_ifs with h
  · exact (Nat.find_spec h).2
  · exact Classical.choose_spec (exists_nat_not_mem used)

lemma pickFresh_mem_of_exists (S : Set ℕ) (used : Finset ℕ)
    (h : ∃ z, z ∈ S ∧ z ∉ used) : pickFresh S used ∈ S := by
  classical
  simp only [pickFresh, dif_pos h]
  exact (Nat.find_spec h).1

lemma pickFresh_le_of_mem (S : Set ℕ) (used : Finset ℕ)
    {z : ℕ} (hzS : z ∈ S) (hzused : z ∉ used) :
    pickFresh S used ≤ z := by
  classical
  let h : ∃ w, w ∈ S ∧ w ∉ used := ⟨z, hzS, hzused⟩
  rw [pickFresh, dif_pos h]
  exact Nat.find_min' h ⟨hzS, hzused⟩

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator :=
  fun _ xs ys => pickFresh (prefixCore family xs) (usedValues xs ys)

noncomputable def run (gen : OnlineGenerator) (input : Stream) : Stream :=
  WellFounded.fix Nat.lt_wfRel.wf
    (fun t rec => gen t (fun i => input i) (fun i => rec i i.isLt))

lemma run_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    run gen input t =
      gen t (fun i => input i) (fun i => run gen input i) := by
  rw [run, WellFounded.fix_eq]

lemma run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  exact run_eq gen input t

lemma streamIn_iff (input : Stream) (L : Language) :
    GenLimit.Generic.StreamIn input L ↔ ∀ t, input t ∈ L := by
  constructor
  · intro h t
    exact h ⟨t, rfl⟩
  · rintro h _ ⟨t, rfl⟩
    exact h t

noncomputable def badTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Nat.find ((not_forall.mp ((streamIn_iff input (family j)).not.mp h)))

lemma badTime_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (badTime family input j) ∉ family j := by
  classical
  rw [badTime, dif_neg h]
  exact Nat.find_spec
    ((not_forall.mp ((streamIn_iff input (family j)).not.mp h)))

noncomputable def stabilizationTime {m : ℕ}
    (family : Fin m → Language) (input : Stream) : ℕ :=
  Finset.univ.sup (badTime family input)

lemma badTime_le_stabilizationTime {m : ℕ}
    (family : Fin m → Language) (input : Stream) (j : Fin m) :
    badTime family input j ≤ stabilizationTime family input := by
  exact Finset.le_sup (f := badTime family input) (Finset.mem_univ j)

lemma prefix_compatible_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stabilizationTime family input ≤ t)
    (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hprefix
    by_contra hbad
    have hle : badTime family input j ≤ t :=
      le_trans (badTime_le_stabilizationTime family input j) ht
    exact badTime_spec family input j hbad
      (hprefix ⟨badTime family input j, Nat.lt_succ_of_le hle⟩)
  · intro hstream i
    exact (streamIn_iff input (family j)).mp hstream i

lemma prefixCore_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) {t : ℕ}
    (ht : stabilizationTime family input ≤ t) :
    prefixCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [prefixCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((prefix_compatible_iff family input ht j).mpr hj)
  · intro hz j hj
    exact hz j ((prefix_compatible_iff family input ht j).mp hj)

lemma informationCore_subset {m : ℕ} {family : Fin m → Language}
    {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj


lemma run_not_input_up_to {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hst : s ≤ t) :
    run (familyGenerator family) input t ≠ input s := by
  intro heq
  have hnot := pickFresh_not_mem
    (prefixCore family (fun i : Fin (t + 1) => input i))
    (usedValues (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (familyGenerator family) input i))
  have hcurrent : run (familyGenerator family) input t =
      pickFresh (prefixCore family (fun i : Fin (t + 1) => input i))
        (usedValues (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => run (familyGenerator family) input i)) := by
    rw [run_eq, familyGenerator]
  apply hnot
  apply Finset.mem_union_left
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  exact ⟨⟨s, Nat.lt_succ_of_le hst⟩, heq.symm.trans hcurrent⟩

lemma run_ne_previous {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hst : s < t) :
    run (familyGenerator family) input s ≠
      run (familyGenerator family) input t := by
  intro heq
  have hnot := pickFresh_not_mem
    (prefixCore family (fun i : Fin (t + 1) => input i))
    (usedValues (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (familyGenerator family) input i))
  have hcurrent : run (familyGenerator family) input t =
      pickFresh (prefixCore family (fun i : Fin (t + 1) => input i))
        (usedValues (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => run (familyGenerator family) input i)) := by
    rw [run_eq, familyGenerator]
  apply hnot
  apply Finset.mem_union_right
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  exact ⟨⟨s, hst⟩, heq.trans hcurrent⟩

lemma run_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (run (familyGenerator family) input) := by
  intro s t hst
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact False.elim ((run_ne_previous family input t s hlt) hst)
  · exact heq
  · exact False.elim ((run_ne_previous family input s t hgt) hst.symm)

lemma run_range_subset_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range (run (familyGenerator family) input) ⊆
      GenLimit.GeneratorFirst input (run (familyGenerator family) input) := by
  rintro z ⟨t, rfl⟩
  exact ⟨t, rfl, fun s hst => (run_not_input_up_to family input t s hst).symm⟩

lemma exists_core_not_used {m : ℕ} {family : Fin m → Language}
    {input : Stream} (hcore : (informationCore family input).Infinite)
    (used : Finset ℕ) :
    ∃ z, z ∈ informationCore family input ∧ z ∉ used := by
  by_contra h
  push_neg at h
  have hsubset : informationCore family input ⊆ (used : Set ℕ) := by
    intro z hz
    exact h z hz
  exact hcore (used.finite_toSet.subset hsubset)

lemma run_mem_core_of_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stabilizationTime family input ≤ t) :
    run (familyGenerator family) input t ∈ informationCore family input := by
  let used := usedValues (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (familyGenerator family) input i)
  have hex : ∃ z, z ∈ informationCore family input ∧ z ∉ used :=
    exists_core_not_used hcore used
  rw [run_eq, familyGenerator, prefixCore_eq_informationCore family input ht]
  exact pickFresh_mem_of_exists _ _ hex

lemma run_le_available_of_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t z : ℕ} (ht : stabilizationTime family input ≤ t)
    (hzcore : z ∈ informationCore family input)
    (hzinput : ∀ s, s ≤ t → input s ≠ z)
    (hzoutput : ∀ s, s < t → run (familyGenerator family) input s ≠ z) :
    run (familyGenerator family) input t ≤ z := by
  rw [run_eq, familyGenerator, prefixCore_eq_informationCore family input ht]
  apply pickFresh_le_of_mem _ _ hzcore
  intro hzused
  rcases Finset.mem_union.mp hzused with hxin | hyout
  · rw [GenLimit.Generic.mem_sequenceSample_iff] at hxin
    obtain ⟨i, hi⟩ := hxin
    exact hzinput i (Nat.le_of_lt_succ i.isLt) hi
  · rw [GenLimit.Generic.mem_sequenceSample_iff] at hyout
    obtain ⟨i, hi⟩ := hyout
    exact hzoutput i i.isLt hi

lemma core_eventually_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (run (familyGenerator family) input) := by
  intro z hzcore
  by_contra hz
  rw [Set.mem_union, not_or] at hz
  let T := stabilizationTime family input
  let output := run (familyGenerator family) input
  have hzinput : ∀ s, input s ≠ z := by
    intro s hs
    exact hz.1 ⟨s, hs⟩
  have hzoutput : ∀ s, output s ≠ z := by
    intro s hs
    exact hz.2 ⟨s, hs⟩
  let f : Fin (z + 2) → Fin (z + 1) := fun k =>
    ⟨output (T + k), by
      have hle : output (T + k) ≤ z := by
        apply run_le_available_of_stable family input
        · exact Nat.le_add_right T k
        · exact hzcore
        · intro s _
          exact hzinput s
        · intro s _
          exact hzoutput s
      omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hout : output (T + a) = output (T + b) := by
      exact congrArg Fin.val hab
    have htime : T + (a : ℕ) = T + (b : ℕ) :=
      run_injective family input hout
    exact Fin.ext (Nat.add_left_cancel htime)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

lemma novel_generates {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (run (familyGenerator family) input) (family j) := by
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  refine ⟨informationCore_subset hj (run_mem_core_of_stable family input hcore ht), ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hst, hs⟩ := hsample
    exact run_not_input_up_to family input t s (Nat.le_of_lt_succ hst) hs.symm
  · intro s hst
    exact run_ne_previous family input t s hst

lemma unpresented_core_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run (familyGenerator family) input) := by
  intro z hz
  rcases core_eventually_announced family input hcore hz.1 with hzin | hzout
  · exact False.elim (hz.2 hzin)
  · exact run_range_subset_generatorFirst family input hzout


noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

lemma firstInputTime_spec {input : Stream} {z : ℕ}
    (hz : z ∈ Set.range input) : input (firstInputTime input z) = z := by
  classical
  rw [firstInputTime, dif_pos hz]
  exact Nat.find_spec hz

lemma firstInputTime_eq {input : Stream} (hinj : Function.Injective input)
    {z t : ℕ} (ht : input t = z) : firstInputTime input z = t := by
  apply hinj
  rw [firstInputTime_spec ⟨t, ht⟩, ht]

lemma firstInputTime_injective_on_range {input : Stream}
    (hinj : Function.Injective input) :
    Set.InjOn (firstInputTime input) (Set.range input) := by
  intro x hx y hy hxy
  have := congrArg input hxy
  simpa [firstInputTime_spec hx, firstInputTime_spec hy] using this

lemma adversaryFirst_at_firstInputTime {input output : Stream}
    (hinj : Function.Injective input) {z : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) :
    input (firstInputTime input z) = z ∧
      ∀ s, s < firstInputTime input z → output s ≠ z := by
  obtain ⟨t, ht, hbefore⟩ := hz
  have htime : firstInputTime input z = t := firstInputTime_eq hinj ht
  exact ⟨firstInputTime_spec ⟨t, ht⟩, by simpa [htime] using hbefore⟩

noncomputable def tracePartner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (z : ℕ) : ℕ :=
  run (familyGenerator family) input (firstInputTime input z)

lemma tracePartner_injective_on_adversaryFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hinj : Function.Injective input) :
    Set.InjOn (tracePartner family input)
      (GenLimit.AdversaryFirst input (run (familyGenerator family) input)) := by
  intro x hx y hy hxy
  have htime : firstInputTime input x = firstInputTime input y :=
    run_injective family input hxy
  exact firstInputTime_injective_on_range hinj
    ⟨_, (adversaryFirst_at_firstInputTime hinj hx).1⟩
    ⟨_, (adversaryFirst_at_firstInputTime hinj hy).1⟩ htime

lemma terminal_attacker_unique {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) {n : ℕ} :
    Set.Subsingleton
      {z | z ∈ GenLimit.AdversaryFirst input (run (familyGenerator family) input) ∧
        z ∈ informationCore family input ∧ z < n ∧
        stabilizationTime family input ≤ firstInputTime input z ∧
        n ≤ tracePartner family input z}
      := by
  intro x hx y hy
  rcases lt_trichotomy (firstInputTime input x) (firstInputTime input y) with hlt | heq | hgt
  · have hyfirst := adversaryFirst_at_firstInputTime hinj hy.1
    have hxpartner : tracePartner family input x ≤ y := by
      change run (familyGenerator family) input (firstInputTime input x) ≤ y
      apply run_le_available_of_stable family input hx.2.2.2.1 hy.2.1
      · intro s hs hsy
        have hs_eq : s = firstInputTime input y := by
          apply hinj
          rw [hsy, hyfirst.1]
        omega
      · intro s hs
        exact hyfirst.2 s (lt_trans hs hlt)
    exact False.elim ((Nat.not_lt_of_ge hx.2.2.2.2)
      (lt_of_le_of_lt hxpartner hy.2.2.1))
  · exact firstInputTime_injective_on_range hinj
      ⟨_, (adversaryFirst_at_firstInputTime hinj hx.1).1⟩
      ⟨_, (adversaryFirst_at_firstInputTime hinj hy.1).1⟩ heq
  · have hxfirst := adversaryFirst_at_firstInputTime hinj hx.1
    have hypartner : tracePartner family input y ≤ x := by
      change run (familyGenerator family) input (firstInputTime input y) ≤ x
      apply run_le_available_of_stable family input hy.2.2.2.1 hx.2.1
      · intro s hs hsx
        have hs_eq : s = firstInputTime input x := by
          apply hinj
          rw [hsx, hxfirst.1]
        omega
      · intro s hs
        exact hxfirst.2 s (lt_trans hs hgt)
    exact False.elim ((Nat.not_lt_of_ge hy.2.2.2.2)
      (lt_of_le_of_lt hypartner hx.2.2.1))

lemma core_prefix_count_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
          informationCore family input) n +
        stabilizationTime family input + 1 := by
  classical
  let I := informationCore family input
  let output := run (familyGenerator family) input
  let T := stabilizationTime family input
  let P := GenLimit.PatientScope.prefixFinset I n
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ I) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ I) n
  have hcover : P ⊆ A ∪ D := by
    intro z hz
    have hzP := GenLimit.PatientScope.mem_prefixFinset.mp hz
    have hzann : z ∈ Set.range input ∪ Set.range output := by
      exact core_eventually_announced family input hcore hzP.2
    have hzowner : z ∈ GenLimit.AdversaryFirst input output ∪
        GenLimit.GeneratorFirst input output := by
      rcases hzann with hzin | hzout
      · exact GenLimit.range_subset_first_announcements input output hzin
      · exact Set.mem_union_right _ (run_range_subset_generatorFirst family input hzout)
    rcases hzowner with hzA | hzD
    · apply Finset.mem_union_left
      exact GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hzP.1, hzA, hzP.2⟩
    · apply Finset.mem_union_right
      exact GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hzP.1, hzD, hzP.2⟩
  have hPcard : P.card ≤ A.card + D.card := by
    exact le_trans (Finset.card_le_card hcover) (Finset.card_union_le A D)
  let early := A.filter (fun z => firstInputTime input z < T)
  let late := A.filter (fun z => T ≤ firstInputTime input z)
  have hAcover : A ⊆ early ∪ late := by
    intro z hz
    by_cases hearly : firstInputTime input z < T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hearly⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hz, Nat.le_of_not_gt hearly⟩)
  have hearly : early.card ≤ T := by
    rw [← Finset.card_range T]
    apply Finset.card_le_card_of_injOn (firstInputTime input)
    · intro z hz
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2
    · intro x hx y hy hxy
      apply firstInputTime_injective_on_range hinj
      · have hxA := GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hx).1
        exact ⟨_, (adversaryFirst_at_firstInputTime hinj hxA.2.1).1⟩
      · have hyA := GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hy).1
        exact ⟨_, (adversaryFirst_at_firstInputTime hinj hyA.2.1).1⟩
      · exact hxy
  let good := late.filter (fun z => tracePartner family input z < n)
  let bad := late.filter (fun z => n ≤ tracePartner family input z)
  have hlatecover : late ⊆ good ∪ bad := by
    intro z hz
    by_cases hgood : tracePartner family input z < n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hgood⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hz, Nat.le_of_not_gt hgood⟩)
  have hgood : good.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (tracePartner family input)
    · intro z hz
      have hzgood := Finset.mem_filter.mp hz
      have hzlate := Finset.mem_filter.mp hzgood.1
      have hzA := GenLimit.PatientScope.mem_prefixFinset.mp hzlate.1
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      refine ⟨hzgood.2, ?_, run_mem_core_of_stable family input hcore hzlate.2⟩
      exact run_range_subset_generatorFirst family input
        ⟨firstInputTime input z, rfl⟩
    · intro x hx y hy hxy
      apply tracePartner_injective_on_adversaryFirst family input hinj
      · exact (GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).2.1
      · exact (GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).2.1
      · exact hxy
  have hbad : bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply terminal_attacker_unique family input hinj hcore
    · have hxlate := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
      have hxA := GenLimit.PatientScope.mem_prefixFinset.mp hxlate.1
      exact ⟨hxA.2.1, hxA.2.2, hxA.1,
        hxlate.2, (Finset.mem_filter.mp hx).2⟩
    · have hylate := Finset.mem_filter.mp (Finset.mem_filter.mp hy).1
      have hyA := GenLimit.PatientScope.mem_prefixFinset.mp hylate.1
      exact ⟨hyA.2.1, hyA.2.2, hyA.1,
        hylate.2, (Finset.mem_filter.mp hy).2⟩
  have hAcard : A.card ≤ T + D.card + 1 := by
    calc
      A.card ≤ early.card + late.card :=
        le_trans (Finset.card_le_card hAcover) (Finset.card_union_le early late)
      _ ≤ T + (good.card + bad.card) := by
        gcongr
        exact le_trans (Finset.card_le_card hlatecover)
          (Finset.card_union_le good bad)
      _ ≤ T + (D.card + 1) := by omega
      _ = T + D.card + 1 := by omega
  change P.card ≤ 2 * D.card + T + 1
  omega

lemma relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      gcongr
      exact GenLimit.PatientScope.prefixCount_mono hAB n
  · apply isBoundedUnder_of_eventually_ge
    exact Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ)) ?_
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · have hnB : GenLimit.PatientScope.prefixCount B n = 0 := by
        have := GenLimit.PatientScope.prefixCount_mono hBK n
        omega
      simp [hn, hnB]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n


lemma half_core_density {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) *
        GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
          family j) (family j) := by
  apply GenLimit.PatientScope.partialDensity_of_counting
    (fun n => GenLimit.PatientScope.prefixCount (family j) n)
    (fun n => GenLimit.PatientScope.prefixCount
      (informationCore family input) n)
    (fun n => GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
        family j) n)
    (stabilizationTime family input + 1)
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hfamily j)
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono (informationCore_subset hj) n
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have hcount := core_prefix_count_le family input hinj hcore n
    have hmono := GenLimit.PatientScope.prefixCount_mono
      (show GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
          informationCore family input ⊆
        GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
          family j by
        intro z hz
        exact ⟨hz.1, informationCore_subset hj hz.2⟩) n
    omega

lemma unpresented_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
          family j) (family j) := by
  apply relativeLowerDensity_mono
  · intro z hz
    exact ⟨unpresented_core_subset_generatorFirst family input hcore hz,
      informationCore_subset hj hz.1⟩
  · exact Set.inter_subset_right

end Case017Formalization

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Case017Formalization.familyGenerator family, ?_⟩
  intro input hinj hpresentation hcore
  refine ⟨Case017Formalization.run
    (Case017Formalization.familyGenerator family) input,
    Case017Formalization.run_follows _ _, ?_⟩
  intro j hj
  refine ⟨Case017Formalization.novel_generates family input hcore j hj, ?_⟩
  apply max_le
  · exact Case017Formalization.half_core_density
      family hfamily input hinj hcore j hj
  · exact Case017Formalization.unpresented_core_density
      family input hcore j hj
