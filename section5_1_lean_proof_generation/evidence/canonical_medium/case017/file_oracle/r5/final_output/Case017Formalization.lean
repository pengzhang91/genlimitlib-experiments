import Stage3Model
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Stage3Case017

noncomputable def prefixSet {t : ℕ} (xs : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs

noncomputable def currentCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin t → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  prefixSet xs ∪ prefixSet ys

noncomputable def leastFresh (S : Set ℕ) (F : Finset ℕ) : ℕ :=
  sInf {z | z ∈ S ∧ z ∉ F}

lemma exists_not_mem_finset (F : Finset ℕ) : ∃ z, z ∉ F := by
  exact Finset.exists_not_mem F

lemma exists_mem_diff_of_infinite {S : Set ℕ} (hS : S.Infinite) (F : Finset ℕ) :
    ∃ z, z ∈ S ∧ z ∉ F := by
  exact hS.exists_not_mem_finset F

lemma leastFresh_mem {S : Set ℕ} {F : Finset ℕ}
    (h : ∃ z, z ∈ S ∧ z ∉ F) :
    leastFresh S F ∈ S ∧ leastFresh S F ∉ F := by
  unfold leastFresh
  exact Nat.sInf_mem h

lemma leastFresh_le {S : Set ℕ} {F : Finset ℕ} {z : ℕ}
    (hzS : z ∈ S) (hzF : z ∉ F) : leastFresh S F ≤ z := by
  exact Nat.sInf_le ⟨hzS, hzF⟩


lemma mem_prefixSet_iff {t : ℕ} {xs : Fin t → ℕ} {z : ℕ} :
    z ∈ prefixSet xs ↔ ∃ i, xs i = z := by
  classical
  simp [prefixSet]

lemma input_mem_forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (i : Fin (t + 1)) : xs i ∈ forbidden xs ys := by
  classical
  simp [forbidden, mem_prefixSet_iff]

lemma output_mem_forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) (i : Fin t) : ys i ∈ forbidden xs ys := by
  classical
  simp [forbidden, mem_prefixSet_iff]

lemma eventually_prefix_compatible {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
  classical
  have hlocal : ∀ j : Fin m, ∃ q, ∀ t, q ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hj : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, fun t _ => ⟨fun _ => hj, ?_⟩⟩
      intro _ i
      exact hj ⟨i, rfl⟩
    · rw [GenLimit.Generic.StreamIn] at hj
      obtain ⟨z, ⟨q, hq⟩, hz⟩ := Set.not_subset.mp hj
      subst z
      refine ⟨q, fun t hqt => ⟨?_, fun h => False.elim (hj h)⟩⟩
      intro hp
      exfalso
      exact hz (hp ⟨q, Nat.lt_succ_of_le hqt⟩)
  let q : Fin m → ℕ := fun j => Classical.choose (hlocal j)
  refine ⟨Finset.univ.sup q, ?_⟩
  intro t hT j
  exact Classical.choose_spec (hlocal j) t
    (le_trans (Finset.le_sup (f := q) (Finset.mem_univ j)) hT)

lemma currentCore_eventually_eq {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      currentCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_prefix_compatible family input
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor <;> intro hz j hj
  · exact hz j ((hT t ht j).2 hj)
  · exact hz j ((hT t ht j).1 hj)

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t xs ys =>
    let F := forbidden xs ys
    let C := currentCore family xs
    if h : ∃ z, z ∈ C ∧ z ∉ F then leastFresh C F else leastFresh Set.univ F

lemma familyGenerator_fresh {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    familyGenerator family t xs ys ∉ forbidden xs ys := by
  classical
  unfold familyGenerator
  dsimp only
  split_ifs with h
  · exact (leastFresh_mem h).2
  · exact (leastFresh_mem (by
      obtain ⟨z, hz⟩ := exists_not_mem_finset (forbidden xs ys)
      exact ⟨z, Set.mem_univ z, hz⟩)).2

lemma familyGenerator_mem_of_core_infinite {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (currentCore family xs).Infinite) :
    familyGenerator family t xs ys ∈ currentCore family xs := by
  classical
  unfold familyGenerator
  dsimp only
  split_ifs with h
  · exact (leastFresh_mem h).1
  · exfalso
    exact h (exists_mem_diff_of_infinite hC (forbidden xs ys))

lemma familyGenerator_le_of_mem {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hzC : z ∈ currentCore family xs) (hzF : z ∉ forbidden xs ys) :
    familyGenerator family t xs ys ≤ z := by
  classical
  unfold familyGenerator
  dsimp only
  rw [dif_pos ⟨z, hzC, hzF⟩]
  exact leastFresh_le hzC hzF

noncomputable def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t
decreasing_by omega

lemma run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  rw [run]



lemma run_fresh_forbidden {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    run (familyGenerator family) input t ∉
      forbidden (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => run (familyGenerator family) input i) := by
  rw [run]
  exact familyGenerator_fresh family t _ _

lemma run_ne_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) {s t : ℕ} (hst : s ≤ t) :
    input s ≠ run (familyGenerator family) input t := by
  intro h
  have hf := run_fresh_forbidden family input t
  apply hf
  have hm := input_mem_forbidden
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (familyGenerator family) input i)
    ⟨s, Nat.lt_succ_of_le hst⟩
  simpa [h] using hm

lemma run_ne_previous {m : ℕ} (family : Fin m → Language)
    (input : Stream) {s t : ℕ} (hst : s < t) :
    run (familyGenerator family) input s ≠
      run (familyGenerator family) input t := by
  intro h
  have hf := run_fresh_forbidden family input t
  apply hf
  have hm := output_mem_forbidden
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (familyGenerator family) input i)
    ⟨s, hst⟩
  simpa [h] using hm

lemma run_injective {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Function.Injective (run (familyGenerator family) input) := by
  intro s t h
  by_contra hst
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · exact run_ne_previous family input hlt h
  · exact run_ne_previous family input hgt h.symm

lemma not_mem_forbidden_of_not_ranges {m t : ℕ} (family : Fin m → Language)
    (input : Stream) {z : ℕ}
    (hin : z ∉ Set.range input)
    (hout : z ∉ Set.range (run (familyGenerator family) input)) :
    z ∉ forbidden (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run (familyGenerator family) input i) := by
  classical
  intro hz
  rw [forbidden, Finset.mem_union] at hz
  rcases hz with hz | hz
  · rw [mem_prefixSet_iff] at hz
    obtain ⟨i, hi⟩ := hz
    exact hin ⟨i, hi⟩
  · rw [mem_prefixSet_iff] at hz
    obtain ⟨i, hi⟩ := hz
    exact hout ⟨i, hi⟩

lemma run_mem_core_from {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      run (familyGenerator family) input t ∈ informationCore family input := by
  obtain ⟨T, hT⟩ := currentCore_eventually_eq family input
  refine ⟨T, ?_⟩
  intro t ht
  have hc : (currentCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hT t ht]
    exact hI
  have hm := familyGenerator_mem_of_core_infinite family t
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (familyGenerator family) input i) hc
  have hr := run_follows (familyGenerator family) input t
  rw [hr]
  exact (hT t ht ▸ hm)

lemma core_subset_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (run (familyGenerator family) input) := by
  obtain ⟨T, hT⟩ := currentCore_eventually_eq family input
  intro z hz
  by_contra hnot
  rw [Set.mem_union, not_or] at hnot
  have hbound : ∀ n, run (familyGenerator family) input (T + n) ≤ z := by
    intro n
    have hzC : z ∈ currentCore family
        (fun i : Fin (T + n + 1) => input i) := by
      rw [hT (T + n) (Nat.le_add_right T n)]
      exact hz
    have hzF := not_mem_forbidden_of_not_ranges
      (t := T + n) family input hnot.1 hnot.2
    have hle := familyGenerator_le_of_mem family (T + n)
      (fun i : Fin (T + n + 1) => input i)
      (fun i : Fin (T + n) => run (familyGenerator family) input i) hzC hzF
    rw [run]
    exact hle
  have hinj : Function.Injective
      (fun n => run (familyGenerator family) input (T + n)) := by
    exact (run_injective family input).comp (fun _ _ h => Nat.add_left_cancel h)
  have hirange := Set.infinite_range_of_injective hinj
  exact hirange ((Set.finite_Iic z).subset (by
    rintro y ⟨n, rfl⟩
    exact hbound n))



noncomputable def inputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

lemma inputTime_spec {input : Stream} {z : ℕ} (hz : z ∈ Set.range input) :
    input (inputTime input z) = z := by
  unfold inputTime
  rw [dif_pos hz]
  exact Nat.find_spec hz

lemma inputTime_min {input : Stream} {z : ℕ} (hz : z ∈ Set.range input)
    {t : ℕ} (ht : input t = z) : inputTime input z ≤ t := by
  unfold inputTime
  rw [dif_pos hz]
  exact Nat.find_min' hz ht

lemma inputTime_injective_on_range {input : Stream} (hinj : Function.Injective input) :
    Set.InjOn (inputTime input) (Set.range input) := by
  intro x hx y hy hxy
  calc
    x = input (inputTime input x) := (inputTime_spec hx).symm
    _ = input (inputTime input y) := congrArg input hxy
    _ = y := inputTime_spec hy

lemma output_range_eq_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range (run (familyGenerator family) input) =
      GenLimit.GeneratorFirst input (run (familyGenerator family) input) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, rfl, ?_⟩
    intro s hst
    exact run_ne_input family input hst
  · rintro ⟨t, ht, -⟩
    exact ⟨t, ht⟩

lemma novel_for_compatible {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (run (familyGenerator family) input)
      (family j) := by
  obtain ⟨T, hT⟩ := run_mem_core_from family input hI
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨(hT t ht) j hj, ?_, ?_⟩
  · intro hs
    rw [GenLimit.mem_sample_iff] at hs
    obtain ⟨s, hst, hs⟩ := hs
    exact run_ne_input family input (Nat.le_of_lt_succ hst) hs
  · intro s hst
    exact run_ne_previous family input hst

lemma core_subset_first_announcements {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (run (familyGenerator family) input) ∪
        GenLimit.GeneratorFirst input (run (familyGenerator family) input) := by
  intro z hz
  have ha := core_subset_announced family input hI hz
  rcases ha with hin | hout
  · exact GenLimit.range_subset_first_announcements input
      (run (familyGenerator family) input) hin
  · by_cases hin : z ∈ Set.range input
    · exact GenLimit.range_subset_first_announcements input
        (run (familyGenerator family) input) hin
    · right
      obtain ⟨t, ht⟩ := hout
      refine ⟨t, ht, ?_⟩
      intro q hqt hq
      exact hin ⟨q, hq⟩

lemma unpresented_core_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hI : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run (familyGenerator family) input) := by
  intro z hz
  have ha := core_subset_announced family input hI hz.1
  rcases ha with hin | hout
  · exact False.elim (hz.2 hin)
  · obtain ⟨t, ht⟩ := hout
    refine ⟨t, ht, ?_⟩
    intro q hqt hq
    exact hz.2 ⟨q, hq⟩


lemma adversaryFirst_at_inputTime {input output : Stream}
    (hinj : Function.Injective input) {z : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) :
    input (inputTime input z) = z ∧
      ∀ s, s < inputTime input z → output s ≠ z := by
  obtain ⟨t, ht, hno⟩ := hz
  have hrange : z ∈ Set.range input := ⟨t, ht⟩
  have hspec := inputTime_spec hrange
  have heq : inputTime input z = t := hinj (hspec.trans ht.symm)
  subst t
  exact ⟨hspec, hno⟩

lemma late_attacker_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hI : (informationCore family input).Infinite)
    (T : ℕ)
    (hcore : ∀ t, T ≤ t →
      currentCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (n : ℕ) :
    let A := GenLimit.PatientScope.prefixFinset
      (GenLimit.AdversaryFirst input (run (familyGenerator family) input) ∩
        informationCore family input) n
    let L := A.filter (fun z => T ≤ inputTime input z)
    let D := GenLimit.PatientScope.prefixFinset
      (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
        informationCore family input) n
    L.card ≤ D.card + 1 := by
  classical
  dsimp only
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input (run (familyGenerator family) input) ∩
      informationCore family input) n
  let L := A.filter (fun z => T ≤ inputTime input z)
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
      informationCore family input) n
  change L.card ≤ D.card + 1
  by_cases hL : L.Nonempty
  · obtain ⟨e, heL, hemax⟩ := Finset.exists_max_image L (inputTime input) hL
    have herange : e ∈ Set.range input := by
      have heA : e ∈ A := (Finset.mem_filter.mp heL).1
      exact ⟨inputTime input e,
        (adversaryFirst_at_inputTime hinj
          (GenLimit.PatientScope.mem_prefixFinset.mp heA).2.1).1⟩
    have hmaps : Set.MapsTo
        (fun z => run (familyGenerator family) input (inputTime input z))
        (↑(L.erase e) : Set ℕ) (↑D : Set ℕ) := by
      intro x hx
      have hxL : x ∈ L := Finset.mem_of_mem_erase hx
      have hxA : x ∈ A := (Finset.mem_filter.mp hxL).1
      have hxdata := GenLimit.PatientScope.mem_prefixFinset.mp hxA
      have hxadv : x ∈ GenLimit.AdversaryFirst input
          (run (familyGenerator family) input) := hxdata.2.1
      have hxI : x ∈ informationCore family input := hxdata.2.2
      have hxlate : T ≤ inputTime input x := (Finset.mem_filter.mp hxL).2
      have hxrange : x ∈ Set.range input := by
        exact ⟨inputTime input x, (adversaryFirst_at_inputTime hinj hxadv).1⟩
      have hxe : x ≠ e := by
        simpa using (Finset.ne_of_mem_erase hx)
      have hlt : inputTime input x < inputTime input e := by
        have hle := hemax x hxL
        exact lt_of_le_of_ne hle (fun h => hxe
          ((inputTime_injective_on_range hinj) hxrange herange h))
      have heA : e ∈ A := (Finset.mem_filter.mp heL).1
      have hedata := GenLimit.PatientScope.mem_prefixFinset.mp heA
      have headv : e ∈ GenLimit.AdversaryFirst input
          (run (familyGenerator family) input) := hedata.2.1
      have heI : e ∈ informationCore family input := hedata.2.2
      have heFresh : e ∉ forbidden
          (fun i : Fin (inputTime input x + 1) => input i)
          (fun i : Fin (inputTime input x) =>
            run (familyGenerator family) input i) := by
        classical
        intro heF
        rw [forbidden, Finset.mem_union] at heF
        rcases heF with heF | heF
        · rw [mem_prefixSet_iff] at heF
          obtain ⟨q, hq⟩ := heF
          have hqtime : inputTime input e = q := hinj
            ((inputTime_spec herange).trans hq.symm)
          have hqle : (q : ℕ) ≤ inputTime input x := Nat.lt_succ_iff.mp q.isLt
          exact (Nat.not_lt_of_ge hqle) (by simpa [hqtime] using hlt)
        · rw [mem_prefixSet_iff] at heF
          obtain ⟨q, hq⟩ := heF
          exact (adversaryFirst_at_inputTime hinj headv).2 q
            (lt_trans q.isLt hlt) hq
      have hout_le : run (familyGenerator family) input (inputTime input x) ≤ e := by
        rw [run]
        apply familyGenerator_le_of_mem
        · rw [hcore (inputTime input x) hxlate]
          exact heI
        · exact heFresh
      have houtI : run (familyGenerator family) input (inputTime input x) ∈
          informationCore family input := by
        have hc : (currentCore family
            (fun i : Fin (inputTime input x + 1) => input i)).Infinite := by
          rw [hcore (inputTime input x) hxlate]
          exact hI
        have hm := familyGenerator_mem_of_core_infinite family (inputTime input x)
          (fun i : Fin (inputTime input x + 1) => input i)
          (fun i : Fin (inputTime input x) =>
            run (familyGenerator family) input i) hc
        rw [← hcore (inputTime input x) hxlate]
        rw [run]
        exact hm
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      refine ⟨lt_of_le_of_lt hout_le hedata.1, ?_, houtI⟩
      rw [← output_range_eq_generatorFirst family input]
      exact ⟨inputTime input x, rfl⟩
    have hinjMap : Set.InjOn
        (fun z => run (familyGenerator family) input (inputTime input z))
        (↑(L.erase e) : Set ℕ) := by
      intro x hx y hy hxy
      apply (inputTime_injective_on_range hinj)
      · have hxA : x ∈ A := (Finset.mem_filter.mp
          (Finset.mem_of_mem_erase hx)).1
        exact ⟨inputTime input x,
          (adversaryFirst_at_inputTime hinj
            (GenLimit.PatientScope.mem_prefixFinset.mp hxA).2.1).1⟩
      · have hyA : y ∈ A := (Finset.mem_filter.mp
          (Finset.mem_of_mem_erase hy)).1
        exact ⟨inputTime input y,
          (adversaryFirst_at_inputTime hinj
            (GenLimit.PatientScope.mem_prefixFinset.mp hyA).2.1).1⟩
      · exact (run_injective family input) hxy
    have hcard := Finset.card_le_card_of_injOn _ hmaps hinjMap
    have herase := Finset.card_erase_add_one heL
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hL]
    simp


lemma core_count_le_twice_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hinj : Function.Injective input)
    (hI : (informationCore family input).Infinite) :
    ∃ C, ∀ n,
      GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
            informationCore family input) n + C := by
  classical
  obtain ⟨T, hcore⟩ := currentCore_eventually_eq family input
  refine ⟨T + 1, ?_⟩
  intro n
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input (run (familyGenerator family) input) ∩
      informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
      informationCore family input) n
  let L := A.filter (fun z => T ≤ inputTime input z)
  let E := A.filter (fun z => ¬ T ≤ inputTime input z)
  have hEcard : E.card ≤ T := by
    have htemp : E.card ≤ (Finset.range T).card := by
      apply Finset.card_le_card_of_injOn (inputTime input)
      · intro z hz
        have hzE : z ∈ E := hz
        have hzlt : inputTime input z < T := Nat.lt_of_not_ge
          (Finset.mem_filter.mp hzE).2
        exact Finset.mem_range.mpr hzlt
      · intro x hx y hy hxy
        apply (inputTime_injective_on_range hinj)
        · have hxA : x ∈ A := (Finset.mem_filter.mp (show x ∈ E from hx)).1
          exact ⟨inputTime input x,
            (adversaryFirst_at_inputTime hinj
              (GenLimit.PatientScope.mem_prefixFinset.mp hxA).2.1).1⟩
        · have hyA : y ∈ A := (Finset.mem_filter.mp (show y ∈ E from hy)).1
          exact ⟨inputTime input y,
            (adversaryFirst_at_inputTime hinj
              (GenLimit.PatientScope.mem_prefixFinset.mp hyA).2.1).1⟩
        · exact hxy
    simpa using htemp
  have hLcard : L.card ≤ D.card + 1 := by
    exact late_attacker_card_le family input hinj hI T hcore n
  have hsplit : L.card + E.card = A.card := by
    simpa [L, E, Nat.not_le] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := A) (fun z => T ≤ inputTime input z))
  have hpartition :
      GenLimit.PatientScope.prefixCount (informationCore family input) n =
        A.card + D.card := by
    let P := GenLimit.PatientScope.prefixFinset (informationCore family input) n
    have hdis : Disjoint A D := by
      rw [Finset.disjoint_left]
      intro z hzA hzD
      have ha := (GenLimit.PatientScope.mem_prefixFinset.mp hzA).2.1
      have hd := (GenLimit.PatientScope.mem_prefixFinset.mp hzD).2.1
      exact Set.disjoint_left.1
        (GenLimit.adversaryFirst_disjoint_generatorFirst input
          (run (familyGenerator family) input)) ha hd
    have hunion : P = A ∪ D := by
      ext z
      simp only [GenLimit.PatientScope.mem_prefixFinset, Finset.mem_union, P, A, D]
      constructor
      · intro hz
        rcases core_subset_first_announcements family input hI hz.2 with ha | hd
        · exact Or.inl ⟨hz.1, ha, hz.2⟩
        · exact Or.inr ⟨hz.1, hd, hz.2⟩
      · rintro (⟨hzn, -, hzI⟩ | ⟨hzn, -, hzI⟩)
        · exact ⟨hzn, hzI⟩
        · exact ⟨hzn, hzI⟩
    unfold GenLimit.PatientScope.prefixCount
    change P.card = A.card + D.card
    rw [hunion, Finset.card_union_of_disjoint hdis]
  change GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
    2 * D.card + (T + 1)
  rw [hpartition]
  omega


lemma half_relative_density_of_counting {I D K : Set ℕ}
    (hK : K.Infinite) (hIK : I ⊆ K) (hDK : D ⊆ K)
    (C : ℕ) (hcount : ∀ n,
      GenLimit.PatientScope.prefixCount I n ≤
        2 * GenLimit.PatientScope.prefixCount D n + C) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity I K ≤
      GenLimit.PatientScope.relativeLowerDensity D K := by
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount I n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let d : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    (C : ℝ) / (2 * (GenLimit.PatientScope.prefixCount K n : ℝ))
  have hN := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have hNR : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hden : Tendsto
      (fun n => 2 * (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    hNR.const_mul_atTop (by norm_num)
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using tendsto_const_nhds.div_atTop hden
  have hneg : Tendsto (fun n => -e n) atTop (𝓝 0) := by
    simpa using he.neg
  have ha0 : ∀ n, 0 ≤ a n := fun n => by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have ha1 : ∀ n, a n ≤ 1 := fun n => by
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [a, hn]
    · have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      change (GenLimit.PatientScope.prefixCount I n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one hp]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hIK n
  have hd1 : ∀ n, d n ≤ 1 := fun n => by
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [d, hn]
    · have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      change (GenLimit.PatientScope.prefixCount D n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1
      rw [div_le_one hp]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hDK n
  have hd0 : ∀ n, 0 ≤ d n := fun n => by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hscale :
      (1 / 2 : ℝ) * liminf a atTop =
        liminf (fun n => (1 / 2 : ℝ) * a n) atTop := by
    have hm : Monotone (fun x : ℝ => (1 / 2 : ℝ) * x) :=
      monotone_id.const_mul (by norm_num)
    exact hm.map_liminf_of_continuousAt a
      (continuousAt_const.mul continuousAt_id)
      (isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop ha1)
      (isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
        (Filter.Eventually.of_forall ha0))
  have hadd : liminf (fun n => (1 / 2 : ℝ) * a n) atTop ≤
      liminf (fun n => (1 / 2 : ℝ) * a n - e n) atTop := by
    have h := le_liminf_add
      (f := atTop)
      (u := fun n => (1 / 2 : ℝ) * a n)
      (v := fun n => -e n)
      (isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
        (Filter.Eventually.of_forall fun n => mul_nonneg (by norm_num) (ha0 n)))
      (isBoundedUnder_of_eventually_le (a := (1 / 2 : ℝ))
        (Filter.Eventually.of_forall fun n => by
          nlinarith [ha1 n]))
      hneg.isBoundedUnder_ge
      hneg.isBoundedUnder_le.isCoboundedUnder_ge
    simpa [sub_eq_add_neg, hneg.liminf_eq] using h
  have hcompare : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * a n - e n ≤ d n := by
    filter_upwards [hN.eventually (eventually_gt_atTop 0)] with n hn
    have hp : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hcR :
        (GenLimit.PatientScope.prefixCount I n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + C := by
      exact_mod_cast hcount n
    dsimp [a, d, e]
    field_simp [hp.ne']
    nlinarith
  have hgbound : IsBoundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop
      (fun n => (1 / 2 : ℝ) * a n - e n) := by
    apply isBoundedUnder_of_eventually_ge (a := (-(C : ℝ) / 2))
    exact Filter.Eventually.of_forall fun n => by
      have henonneg : 0 ≤ e n := div_nonneg (Nat.cast_nonneg _) (by positivity)
      have hele : e n ≤ (C : ℝ) / 2 := by
        by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
        · simp [e, hn]; positivity
        · have hOne : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          dsimp [e]
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 *
            GenLimit.PatientScope.prefixCount K n)]
          nlinarith
      nlinarith [ha0 n]
  have hdcobound : IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≥ x2) atTop d :=
    isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop hd1
  have hlim : liminf (fun n => (1 / 2 : ℝ) * a n - e n) atTop ≤
      liminf d atTop :=
    liminf_le_liminf hcompare hgbound hdcobound
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) * liminf a atTop ≤ liminf d atTop
  rw [hscale]
  exact le_trans hadd (le_trans hlim (le_refl _))

lemma relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · apply isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
    exact Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop (fun n => ?_)
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hn]
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n


lemma half_density_bound {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hinj : Function.Injective input)
    (hI : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
          family j) (family j) := by
  obtain ⟨C, hC⟩ := core_count_le_twice_generatorFirst family input hinj hI
  apply half_relative_density_of_counting
    (I := informationCore family input)
    (D := GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
      family j)
    (K := family j)
    (hfamily j) (fun z hz => hz j hj) Set.inter_subset_right C
  intro n
  calc
    GenLimit.PatientScope.prefixCount (informationCore family input) n
        ≤ 2 * GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
              informationCore family input) n + C := hC n
    _ ≤ 2 * GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
              family j) n + C := by
      gcongr
      have hsub :
          GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
              informationCore family input ⊆
            GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
              family j :=
        fun z hz => ⟨hz.1, hz.2 j hj⟩
      exact GenLimit.PatientScope.prefixCount_mono hsub n

lemma unpresented_density_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hI : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩
          family j) (family j) := by
  apply relativeLowerDensity_mono
  · intro z hz
    exact ⟨unpresented_core_subset_generatorFirst family input hI hz,
      hz.1 j hj⟩
  · exact Set.inter_subset_right


end Stage3Case017

open Stage3Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨familyGenerator family, ?_⟩
  intro input hinj hexists hI
  refine ⟨run (familyGenerator family) input,
    run_follows (familyGenerator family) input, ?_⟩
  intro j hj
  refine ⟨novel_for_compatible family input hI hj, ?_⟩
  apply max_le
  · exact half_density_bound family hfamily input hinj hI hj
  · exact unpresented_density_bound family input hI hj
