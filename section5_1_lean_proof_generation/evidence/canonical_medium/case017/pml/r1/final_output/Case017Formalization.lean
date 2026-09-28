import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def inputSeen {t : ℕ} (input : Fin (t + 1) → ℕ) : Finset ℕ :=
  Finset.univ.image input

noncomputable def outputSeen {t : ℕ} (output : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image output

def currentCore {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, input i ∈ family j) → z ∈ family j}

noncomputable def activeSet {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) : Language := by
  classical
  exact if (currentCore family input).Infinite then currentCore family input else Set.univ

theorem activeSet_infinite {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) : (activeSet family input).Infinite := by
  classical
  simp only [activeSet]
  split
  · assumption
  · exact Set.infinite_univ

noncomputable def onlineGen {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun _ input output =>
    Nat.find ((activeSet_infinite family input).exists_notMem_finset
      (inputSeen input ∪ outputSeen output))

theorem onlineGen_spec {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    onlineGen family t input output ∈ activeSet family input ∧
      onlineGen family t input output ∉ inputSeen input ∪ outputSeen output := by
  classical
  simpa [onlineGen] using Nat.find_spec ((activeSet_infinite family input).exists_notMem_finset
    (inputSeen input ∪ outputSeen output))

theorem onlineGen_minimal {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) {z : ℕ}
    (hz : z ∈ activeSet family input)
    (hfresh : z ∉ inputSeen input ∪ outputSeen output) :
    onlineGen family t input output ≤ z := by
  classical
  simpa [onlineGen] using Nat.find_min' ((activeSet_infinite family input).exists_notMem_finset
    (inputSeen input ∪ outputSeen output)) ⟨hz, hfresh⟩

@[simp] theorem mem_inputSeen {t : ℕ} {input : Fin (t + 1) → ℕ} {z : ℕ} :
    z ∈ inputSeen input ↔ ∃ i : Fin (t + 1), input i = z := by
  classical
  simp [inputSeen]

@[simp] theorem mem_outputSeen {t : ℕ} {output : Fin t → ℕ} {z : ℕ} :
    z ∈ outputSeen output ↔ ∃ i : Fin t, output i = z := by
  classical
  simp [outputSeen]

noncomputable def outputHistory (family : Fin m → Language) (input : Stream) :
    (t : ℕ) → Fin t → ℕ
  | 0 => Fin.elim0
  | t + 1 => Fin.lastCases
      (onlineGen family t (fun i => input i) (outputHistory family input t))
      (outputHistory family input t)

noncomputable def trajectory (family : Fin m → Language) (input : Stream) : Stream :=
  fun t => outputHistory family input (t + 1) (Fin.last t)

theorem outputHistory_eq_trajectory (family : Fin m → Language) (input : Stream)
    {t : ℕ} (i : Fin t) : outputHistory family input t i = trajectory family input i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simp only [outputHistory, Fin.lastCases_castSucc]
        exact ih j

theorem follows_trajectory (family : Fin m → Language) (input : Stream) :
    Follows (onlineGen family) input (trajectory family input) := by
  intro t
  rw [trajectory]
  simp only [outputHistory, Fin.lastCases_last]
  congr 1
  funext i
  exact outputHistory_eq_trajectory family input i


def compatible (input : Stream) (L : Language) : Prop :=
  GenLimit.Generic.StreamIn input L

noncomputable def badTime (input : Stream) (L : Language) : ℕ := by
  classical
  exact if h : compatible input L then 0 else
    Classical.choose (show ∃ t, input t ∉ L by
      simpa [compatible, GenLimit.Generic.StreamIn, Set.subset_def,
        Set.range_subset_iff] using h)

theorem badTime_not_mem (input : Stream) (L : Language)
    (h : ¬ compatible input L) : input (badTime input L) ∉ L := by
  classical
  simp only [badTime, dif_neg h]
  exact Classical.choose_spec (show ∃ t, input t ∉ L by
    simpa [compatible, GenLimit.Generic.StreamIn, Set.subset_def,
      Set.range_subset_iff] using h)

noncomputable def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  Finset.univ.sup fun j => badTime input (family j)

theorem badTime_le_stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    badTime input (family j) ≤ stabilizationTime family input := by
  classical
  exact Finset.le_sup (f := fun k => badTime input (family k)) (Finset.mem_univ j)

theorem prefix_compatible_iff {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t) (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔ compatible input (family j) := by
  constructor
  · intro hp
    by_contra hbad
    have hle : badTime input (family j) ≤ t :=
      (badTime_le_stabilizationTime family input j).trans ht
    exact badTime_not_mem input (family j) hbad
      (hp ⟨badTime input (family j), Nat.lt_succ_of_le hle⟩)
  · intro hc i
    exact hc ⟨i, rfl⟩

theorem currentCore_eq_informationCore {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor <;> intro hz j hj
  · exact hz j ((prefix_compatible_iff family input ht j).2 hj)
  · exact hz j ((prefix_compatible_iff family input ht j).1 hj)

theorem activeSet_eq_informationCore {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (ht : stabilizationTime family input ≤ t) :
    activeSet family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  classical
  rw [activeSet, currentCore_eq_informationCore family input ht, if_pos hcore]

theorem trajectory_fresh_input (family : Fin m → Language) (input : Stream)
    (t s : ℕ) (hs : s ≤ t) : input s ≠ trajectory family input t := by
  intro heq
  have hspec := onlineGen_spec family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory family input i)
  rw [← follows_trajectory family input t] at hspec
  exact hspec.2 (Finset.mem_union_left _ (mem_inputSeen.mpr
    ⟨⟨s, Nat.lt_succ_of_le hs⟩, heq⟩))

theorem trajectory_ne_of_lt (family : Fin m → Language) (input : Stream)
    {s t : ℕ} (hst : s < t) : trajectory family input s ≠ trajectory family input t := by
  intro heq
  have hspec := onlineGen_spec family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory family input i)
  rw [← follows_trajectory family input t] at hspec
  exact hspec.2 (Finset.mem_union_right _ (mem_outputSeen.mpr
    ⟨⟨s, hst⟩, heq⟩))

theorem trajectory_mem_core (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) {t : ℕ}
    (ht : stabilizationTime family input ≤ t) :
    trajectory family input t ∈ informationCore family input := by
  have hspec := onlineGen_spec family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory family input i)
  rw [← follows_trajectory family input t,
    activeSet_eq_informationCore family input hcore ht] at hspec
  exact hspec.1

theorem informationCore_subset_target (family : Fin m → Language)
    (input : Stream) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

theorem trajectory_novel (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (trajectory family input) (family j) := by
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  refine ⟨informationCore_subset_target family input hj
      (trajectory_mem_core family input hcore ht), ?_, ?_⟩
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact trajectory_fresh_input family input t s (Nat.le_of_lt_succ hs) heq
  · intro s hs
    exact trajectory_ne_of_lt family input hs


theorem missing_core_eventually_output (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input) (hzinput : z ∉ Set.range input) :
    z ∈ Set.range (trajectory family input) := by
  by_contra hzoutput
  let T := stabilizationTime family input
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨trajectory family input (T + i), by
      have hzFreshInput : z ∉ inputSeen (fun k : Fin (T + i + 1) => input k) := by
        intro h
        obtain ⟨k, hk⟩ := mem_inputSeen.mp h
        exact hzinput ⟨k, hk⟩
      have hzFreshOutput : z ∉ outputSeen
          (fun k : Fin (T + i) => trajectory family input k) := by
        intro h
        obtain ⟨k, hk⟩ := mem_outputSeen.mp h
        exact hzoutput ⟨k, hk⟩
      have hmin := onlineGen_minimal family
        (fun k : Fin (T + i + 1) => input k)
        (fun k : Fin (T + i) => trajectory family input k)
        (z := z)
        (by rw [activeSet_eq_informationCore family input hcore (Nat.le_add_right T i)]
            exact hzcore)
        (by simp only [Finset.mem_union, hzFreshInput, hzFreshOutput, or_false,
              not_false_eq_true])
      rw [← follows_trajectory family input (T + i)] at hmin
      exact Nat.lt_succ_of_le hmin⟩
  have hf : Function.Injective f := by
    intro i k hik
    apply Fin.ext
    by_contra hne
    have hlt : (i : ℕ) < k ∨ (k : ℕ) < i := lt_or_gt_of_ne hne
    cases hlt with
    | inl hlt =>
        exact trajectory_ne_of_lt family input (Nat.add_lt_add_left hlt T)
          (congrArg Fin.val hik)
    | inr hlt =>
        exact trajectory_ne_of_lt family input (Nat.add_lt_add_left hlt T)
          (congrArg Fin.val hik).symm
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard

theorem missing_core_generatorFirst (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory family input) := by
  intro z hz
  obtain ⟨t, ht⟩ := missing_core_eventually_output family input hcore hz.1 hz.2
  refine ⟨t, ht, ?_⟩
  intro s hs heq
  exact hz.2 ⟨s, heq⟩


theorem informationCore_first_covered (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (trajectory family input) ∪
        GenLimit.GeneratorFirst input (trajectory family input) := by
  intro z hz
  by_cases hr : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input (trajectory family input) hr
  · exact Set.mem_union_right _ (missing_core_generatorFirst family input hcore ⟨hz, hr⟩)

noncomputable def inputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

theorem inputTime_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (inputTime input z) = z := by
  classical
  simp only [inputTime, dif_pos hz]
  exact Nat.find_spec hz

theorem inputTime_min (input : Stream) {z : ℕ} (hz : z ∈ Set.range input)
    {t : ℕ} (ht : input t = z) : inputTime input z ≤ t := by
  classical
  simp only [inputTime, dif_pos hz]
  exact Nat.find_min' hz ht

theorem adversaryFirst_range {input output : Stream} {z : ℕ}
    (hz : z ∈ GenLimit.AdversaryFirst input output) : z ∈ Set.range input := by
  obtain ⟨t, ht, -⟩ := hz
  exact ⟨t, ht⟩

noncomputable def attackerPrefix (core : Language) (input output : Stream) (n : ℕ) :
    Finset ℕ :=
  GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ core) n

noncomputable def defenderPrefix (core : Language) (input output : Stream) (n : ℕ) :
    Finset ℕ :=
  GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ core) n

noncomputable def earlyAttacker (core : Language) (input output : Stream)
    (T n : ℕ) : Finset ℕ :=
  (attackerPrefix core input output n).filter fun z => inputTime input z ≤ T

noncomputable def lateAttacker (core : Language) (input output : Stream)
    (T n : ℕ) : Finset ℕ :=
  (attackerPrefix core input output n).filter fun z => T < inputTime input z

noncomputable def goodAttacker (core : Language) (input output : Stream)
    (T n : ℕ) : Finset ℕ :=
  (lateAttacker core input output T n).filter fun z => output (inputTime input z) < n

noncomputable def badAttacker (core : Language) (input output : Stream)
    (T n : ℕ) : Finset ℕ :=
  (lateAttacker core input output T n).filter fun z => n ≤ output (inputTime input z)

theorem attackerPrefix_split (core : Language) (input output : Stream) (T n : ℕ) :
    (attackerPrefix core input output n).card =
      (earlyAttacker core input output T n).card +
        (lateAttacker core input output T n).card := by
  classical
  let A := attackerPrefix core input output n
  let p : ℕ → Prop := fun z => inputTime input z ≤ T
  have hlate : lateAttacker core input output T n = A.filter fun z => ¬p z := by
    ext z
    simp [lateAttacker, A, p]
  have hearly : earlyAttacker core input output T n = A.filter p := by
    rfl
  rw [hearly, hlate]
  have hu := Finset.filter_union_filter_neg_eq p A
  have hd : Disjoint (A.filter p) (A.filter fun z => ¬p z) := by
    exact Finset.disjoint_filter_filter_neg A A p
  rw [← Finset.card_union_of_disjoint hd, hu]

theorem lateAttacker_split (core : Language) (input output : Stream) (T n : ℕ) :
    (lateAttacker core input output T n).card =
      (goodAttacker core input output T n).card +
        (badAttacker core input output T n).card := by
  classical
  let A := lateAttacker core input output T n
  let p : ℕ → Prop := fun z => output (inputTime input z) < n
  have hbad : badAttacker core input output T n = A.filter fun z => ¬p z := by
    ext z
    simp [badAttacker, A, p]
  have hgood : goodAttacker core input output T n = A.filter p := by
    rfl
  rw [hgood, hbad]
  have hu := Finset.filter_union_filter_neg_eq p A
  have hd : Disjoint (A.filter p) (A.filter fun z => ¬p z) := by
    exact Finset.disjoint_filter_filter_neg A A p
  rw [← Finset.card_union_of_disjoint hd, hu]


theorem earlyAttacker_card_le (core : Language) (input output : Stream)
    (T n : ℕ) : (earlyAttacker core input output T n).card ≤ T + 1 := by
  classical
  let f : ℕ → ℕ := fun z => inputTime input z
  have hcard : (earlyAttacker core input output T n).card ≤
      (Finset.range (T + 1)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hz).2)
    · intro x hx y hy hxy
      have hxA := (Finset.mem_filter.mp hx).1
      have hyA := (Finset.mem_filter.mp hy).1
      have hxrange := adversaryFirst_range
        (GenLimit.PatientScope.mem_prefixFinset.mp hxA).2.1
      have hyrange := adversaryFirst_range
        (GenLimit.PatientScope.mem_prefixFinset.mp hyA).2.1
      dsimp [f] at hxy
      calc
        x = input (inputTime input x) := (inputTime_spec input hxrange).symm
        _ = input (inputTime input y) := by rw [hxy]
        _ = y := inputTime_spec input hyrange
  simpa using hcard

theorem goodAttacker_card_le_defender (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    (goodAttacker (informationCore family input) input (trajectory family input)
      (stabilizationTime family input) n).card ≤
      (defenderPrefix (informationCore family input) input
        (trajectory family input) n).card := by
  classical
  let T := stabilizationTime family input
  let G := goodAttacker (informationCore family input) input
    (trajectory family input) T n
  let D := defenderPrefix (informationCore family input) input
    (trajectory family input) n
  let f : ℕ → ℕ := fun z => trajectory family input (inputTime input z)
  apply Finset.card_le_card_of_injOn f
  · intro z hz
    have hzGood := Finset.mem_filter.mp hz
    have hzLate := Finset.mem_filter.mp hzGood.1
    have hzAtt := GenLimit.PatientScope.mem_prefixFinset.mp hzLate.1
    have ht : T ≤ inputTime input z := Nat.le_of_lt hzLate.2
    have hmemCore := trajectory_mem_core family input hcore ht
    have hgen : f z ∈ GenLimit.GeneratorFirst input (trajectory family input) := by
      refine ⟨inputTime input z, rfl, ?_⟩
      intro s hs
      exact trajectory_fresh_input family input (inputTime input z) s hs
    exact GenLimit.PatientScope.mem_prefixFinset.mpr
      ⟨hzGood.2, hgen, hmemCore⟩
  · intro x hx y hy hxy
    have hxLate := (Finset.mem_filter.mp hx).1
    have hyLate := (Finset.mem_filter.mp hy).1
    have hxAtt := GenLimit.PatientScope.mem_prefixFinset.mp
      (Finset.mem_filter.mp hxLate).1
    have hyAtt := GenLimit.PatientScope.mem_prefixFinset.mp
      (Finset.mem_filter.mp hyLate).1
    have hxrange := adversaryFirst_range hxAtt.2.1
    have hyrange := adversaryFirst_range hyAtt.2.1
    have htime : inputTime input x = inputTime input y := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact trajectory_ne_of_lt family input hlt hxy
      · exact trajectory_ne_of_lt family input hlt hxy.symm
    calc
      x = input (inputTime input x) := (inputTime_spec input hxrange).symm
      _ = input (inputTime input y) := by rw [htime]
      _ = y := inputTime_spec input hyrange

theorem badAttacker_card_le_one (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    (badAttacker (informationCore family input) input (trajectory family input)
      (stabilizationTime family input) n).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxBad := Finset.mem_filter.mp hx
  have hyBad := Finset.mem_filter.mp hy
  have hxLate := Finset.mem_filter.mp hxBad.1
  have hyLate := Finset.mem_filter.mp hyBad.1
  have hxPrefix := GenLimit.PatientScope.mem_prefixFinset.mp hxLate.1
  have hyPrefix := GenLimit.PatientScope.mem_prefixFinset.mp hyLate.1
  have hxrange := adversaryFirst_range hxPrefix.2.1
  have hyrange := adversaryFirst_range hyPrefix.2.1
  by_contra hxy
  rcases lt_or_gt_of_ne (show inputTime input x ≠ inputTime input y by
    intro heq
    apply hxy
    calc
      x = input (inputTime input x) := (inputTime_spec input hxrange).symm
      _ = input (inputTime input y) := by rw [heq]
      _ = y := inputTime_spec input hyrange) with hlt | hlt
  · have hyInputFresh : y ∉ inputSeen
        (fun k : Fin (inputTime input x + 1) => input k) := by
      intro hymem
      obtain ⟨k, hk⟩ := mem_inputSeen.mp hymem
      have hmin := inputTime_min input hyrange hk
      omega
    have hyOutputFresh : y ∉ outputSeen
        (fun k : Fin (inputTime input x) => trajectory family input k) := by
      intro hymem
      obtain ⟨k, hk⟩ := mem_outputSeen.mp hymem
      obtain ⟨ty, hty, hno⟩ := hyPrefix.2.1
      have hity : inputTime input y ≤ ty := inputTime_min input hyrange hty
      exact hno k (by omega) hk
    have hmin := onlineGen_minimal family
      (fun k : Fin (inputTime input x + 1) => input k)
      (fun k : Fin (inputTime input x) => trajectory family input k)
      (z := y)
      (by rw [activeSet_eq_informationCore family input hcore
          (Nat.le_of_lt hxLate.2)]
          exact hyPrefix.2.2)
      (by simp only [Finset.mem_union, hyInputFresh, hyOutputFresh, or_false,
          not_false_eq_true])
    rw [← follows_trajectory family input (inputTime input x)] at hmin
    omega
  · have hxInputFresh : x ∉ inputSeen
        (fun k : Fin (inputTime input y + 1) => input k) := by
      intro hxmem
      obtain ⟨k, hk⟩ := mem_inputSeen.mp hxmem
      have hmin := inputTime_min input hxrange hk
      omega
    have hxOutputFresh : x ∉ outputSeen
        (fun k : Fin (inputTime input y) => trajectory family input k) := by
      intro hxmem
      obtain ⟨k, hk⟩ := mem_outputSeen.mp hxmem
      obtain ⟨tx, htx, hno⟩ := hxPrefix.2.1
      have hitx : inputTime input x ≤ tx := inputTime_min input hxrange htx
      exact hno k (by omega) hk
    have hmin := onlineGen_minimal family
      (fun k : Fin (inputTime input y + 1) => input k)
      (fun k : Fin (inputTime input y) => trajectory family input k)
      (z := x)
      (by rw [activeSet_eq_informationCore family input hcore
          (Nat.le_of_lt hyLate.2)]
          exact hxPrefix.2.2)
      (by simp only [Finset.mem_union, hxInputFresh, hxOutputFresh, or_false,
          not_false_eq_true])
    rw [← follows_trajectory family input (inputTime input y)] at hmin
    omega


theorem core_prefix_counting (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * (defenderPrefix (informationCore family input) input
        (trajectory family input) n).card + stabilizationTime family input + 2 := by
  classical
  let core := informationCore family input
  let output := trajectory family input
  let T := stabilizationTime family input
  let E := GenLimit.PatientScope.prefixFinset core n
  let A := attackerPrefix core input output n
  let D := defenderPrefix core input output n
  have hcover : E ⊆ A ∪ D := by
    intro z hz
    have hzE := GenLimit.PatientScope.mem_prefixFinset.mp hz
    rcases informationCore_first_covered family input hcore hzE.2 with hzA | hzD
    · exact Finset.mem_union_left _ (GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hzE.1, hzA, hzE.2⟩)
    · exact Finset.mem_union_right _ (GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hzE.1, hzD, hzE.2⟩)
  have hEA : E.card ≤ A.card + D.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le A D)
  have hsplitA := attackerPrefix_split core input output T n
  have hsplitLate := lateAttacker_split core input output T n
  have hearly := earlyAttacker_card_le core input output T n
  have hgood := goodAttacker_card_le_defender family input hcore n
  have hbad := badAttacker_card_le_one family input hcore n
  change E.card ≤ 2 * D.card + T + 2
  change A.card = _ at hsplitA
  change (lateAttacker core input output T n).card = _ at hsplitLate
  change (earlyAttacker core input output T n).card ≤ T + 1 at hearly
  change (goodAttacker core input output T n).card ≤ D.card at hgood
  change (badAttacker core input output T n).card ≤ 1 at hbad
  omega

theorem half_core_density (family : Fin m → Language) (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) (family j) := by
  apply GenLimit.PatientScope.partialDensity_of_counting
    (GenLimit.PatientScope.prefixCount (family j))
    (GenLimit.PatientScope.prefixCount (informationCore family input))
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j))
    (stabilizationTime family input + 2)
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hfamily j)
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono
      (informationCore_subset_target family input hj) n
  · intro n
    exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · intro n
    have hcount := core_prefix_counting family input hcore n
    have hmono :
        (defenderPrefix (informationCore family input) input
          (trajectory family input) n).card ≤
        GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n := by
      apply Finset.card_le_card
      intro z hz
      have hz' := GenLimit.PatientScope.mem_prefixFinset.mp hz
      exact GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hz'.1, hz'.2.1, informationCore_subset_target family input hj hz'.2.2⟩
    omega

open Filter

theorem relativeLowerDensity_mono {A B K : Language} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      gcongr
      exact GenLimit.PatientScope.prefixCount_mono hAB n
  · exact isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hratio : ∀ n : ℕ,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
      intro n
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · have hle := GenLimit.PatientScope.prefixCount_mono hBK n
        have hzero : GenLimit.PatientScope.prefixCount B n = 0 := by omega
        simp [hn, hzero]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
    exact isCoboundedUnder_ge_of_le atTop hratio


theorem missing_core_density (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) (family j) := by
  apply relativeLowerDensity_mono
  · intro z hz
    exact ⟨missing_core_generatorFirst family input hcore hz,
      informationCore_subset_target family input hj hz.1⟩
  · exact Set.inter_subset_right

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.onlineGen family, ?_⟩
  intro input hinjective hexists hcore
  refine ⟨Stage3Case017Proof.trajectory family input,
    Stage3Case017Proof.follows_trajectory family input, ?_⟩
  intro j hj
  refine ⟨Stage3Case017Proof.trajectory_novel family input hcore j hj, ?_⟩
  apply max_le
  · exact Stage3Case017Proof.half_core_density family hfamily input hcore j hj
  · exact Stage3Case017Proof.missing_core_density family input hcore j hj
