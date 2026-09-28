import Stage3Model

open Filter
open scoped Topology

namespace Case017Proof

open Stage3Case017

noncomputable def finiteValues {n : ℕ} (xs : Fin n → ℕ) : Finset ℕ :=
  Finset.univ.image xs

def versionCore {m n : ℕ} (family : Fin m → Language)
    (xs : Fin n → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def leastFresh (S : Set ℕ) (hS : S.Infinite)
    (used : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (hS.exists_notMem_finset used)

theorem leastFresh_mem (S : Set ℕ) (hS : S.Infinite) (used : Finset ℕ) :
    leastFresh S hS used ∈ S := by
  classical
  exact (Nat.find_spec (hS.exists_notMem_finset used)).1

theorem leastFresh_not_mem (S : Set ℕ) (hS : S.Infinite) (used : Finset ℕ) :
    leastFresh S hS used ∉ used := by
  classical
  exact (Nat.find_spec (hS.exists_notMem_finset used)).2

theorem leastFresh_le (S : Set ℕ) (hS : S.Infinite) (used : Finset ℕ)
    {z : ℕ} (hzS : z ∈ S) (hz : z ∉ used) :
    leastFresh S hS used ≤ z := by
  classical
  exact Nat.find_min' (hS.exists_notMem_finset used) ⟨hzS, hz⟩

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun _ xs ys =>
    let used := finiteValues xs ∪ finiteValues ys
    if h : (versionCore family xs).Infinite then
      leastFresh (versionCore family xs) h used
    else
      leastFresh Set.univ Set.infinite_univ used

noncomputable def history (gen : OnlineGenerator) (input : Stream) :
    (t : ℕ) → Fin t → ℕ
  | 0 => Fin.elim0
  | t + 1 => Fin.lastCases
      (gen t (fun i => input i) (history gen input t))
      (history gen input t)

noncomputable def run (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => history gen input (t + 1) (Fin.last t)

theorem history_castSucc (gen : OnlineGenerator) (input : Stream)
    {t : ℕ} (i : Fin t) :
    history gen input (t + 1) i.castSucc = history gen input t i := by
  simp [history]

theorem history_eq_run (gen : OnlineGenerator) (input : Stream) :
    ∀ {t : ℕ} (i : Fin t), history gen input t i = run gen input i := by
  intro t
  induction t with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ t ih =>
      intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rfl
      · simpa [history_castSucc] using ih k

theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  change history gen input (t + 1) (Fin.last t) = _
  rw [show history gen input (t + 1) (Fin.last t) =
      gen t (fun i => input i) (history gen input t) by simp [history]]
  congr 1
  funext i
  exact history_eq_run gen input i


theorem mem_finiteValues {n : ℕ} (xs : Fin n → ℕ) (z : ℕ) :
    z ∈ finiteValues xs ↔ ∃ i, xs i = z := by
  classical
  simp [finiteValues]

theorem familyGenerator_core {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hcore : (versionCore family xs).Infinite) :
    familyGenerator family t xs ys ∈ versionCore family xs := by
  classical
  simp [familyGenerator, hcore, leastFresh_mem]

theorem familyGenerator_not_input {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    ∀ i, xs i ≠ familyGenerator family t xs ys := by
  classical
  intro i hi
  by_cases hcore : (versionCore family xs).Infinite
  · have hnot := leastFresh_not_mem (versionCore family xs) hcore
      (finiteValues xs ∪ finiteValues ys)
    apply hnot
    apply Finset.mem_union_left
    exact (mem_finiteValues xs _).2 ⟨i, by simpa [familyGenerator, hcore] using hi⟩
  · have hnot := leastFresh_not_mem Set.univ Set.infinite_univ
      (finiteValues xs ∪ finiteValues ys)
    apply hnot
    apply Finset.mem_union_left
    exact (mem_finiteValues xs _).2 ⟨i, by simpa [familyGenerator, hcore] using hi⟩

theorem familyGenerator_not_output {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    ∀ i, ys i ≠ familyGenerator family t xs ys := by
  classical
  intro i hi
  by_cases hcore : (versionCore family xs).Infinite
  · have hnot := leastFresh_not_mem (versionCore family xs) hcore
      (finiteValues xs ∪ finiteValues ys)
    apply hnot
    apply Finset.mem_union_right
    exact (mem_finiteValues ys _).2 ⟨i, by simpa [familyGenerator, hcore] using hi⟩
  · have hnot := leastFresh_not_mem Set.univ Set.infinite_univ
      (finiteValues xs ∪ finiteValues ys)
    apply hnot
    apply Finset.mem_union_right
    exact (mem_finiteValues ys _).2 ⟨i, by simpa [familyGenerator, hcore] using hi⟩

theorem familyGenerator_le {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hcore : (versionCore family xs).Infinite) {z : ℕ}
    (hzcore : z ∈ versionCore family xs)
    (hzx : ∀ i, xs i ≠ z) (hzy : ∀ i, ys i ≠ z) :
    familyGenerator family t xs ys ≤ z := by
  classical
  simp only [familyGenerator, dif_pos hcore]
  apply leastFresh_le (versionCore family xs) hcore
  · exact hzcore
  · simp only [Finset.mem_union, mem_finiteValues, not_or, not_exists]
    exact ⟨fun i => hzx i, fun i => hzy i⟩

theorem not_streamIn_exists {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    ∃ t, input t ∉ family j := by
  rw [GenLimit.Generic.StreamIn, Set.range_subset_iff] at h
  exact Classical.not_forall.mp h

noncomputable def exclusionTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  by_cases h : GenLimit.Generic.StreamIn input (family j)
  · exact 0
  · exact Classical.choose (not_streamIn_exists family input j h)

theorem exclusionTime_bad {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (exclusionTime family input j) ∉ family j := by
  classical
  simp only [exclusionTime, dif_neg h]
  exact Classical.choose_spec (not_streamIn_exists family input j h)

noncomputable def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  Finset.univ.sup (exclusionTime family input)

theorem prefix_compatible_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stabilizationTime family input ≤ t)
    (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  classical
  constructor
  · intro hprefix
    by_contra hstream
    let q := exclusionTime family input j
    have hq : q ≤ t :=
      (Finset.le_sup (s := Finset.univ) (f := exclusionTime family input)
        (Finset.mem_univ j)).trans ht
    have hbad := exclusionTime_bad family input j hstream
    exact hbad (hprefix ⟨q, Nat.lt_succ_of_le hq⟩)
  · intro hstream i
    exact hstream ⟨i, rfl⟩

theorem versionCore_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stabilizationTime family input ≤ t) :
    versionCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [versionCore, informationCore, Set.mem_setOf_eq]
  constructor <;> intro hz j hj
  · exact hz j ((prefix_compatible_iff family input ht j).2 hj)
  · exact hz j ((prefix_compatible_iff family input ht j).1 hj)


theorem run_not_current_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    ∀ s, s ≤ t → input s ≠ run (familyGenerator family) input t := by
  intro s hs
  rw [run_follows (familyGenerator family) input t]
  exact familyGenerator_not_input family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (familyGenerator family) input i)
    ⟨s, Nat.lt_succ_of_le hs⟩

theorem run_not_previous {m : ℕ} (family : Fin m → Language)
    (input : Stream) {s t : ℕ} (hst : s < t) :
    run (familyGenerator family) input s ≠
      run (familyGenerator family) input t := by
  rw [run_follows (familyGenerator family) input t]
  have h := familyGenerator_not_output family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (familyGenerator family) input i) ⟨s, hst⟩
  exact h

theorem run_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (run (familyGenerator family) input) := by
  intro s t heq
  rcases lt_trichotomy s t with h | h | h
  · exact (run_not_previous family input h heq).elim
  · exact h
  · exact (run_not_previous family input h heq.symm).elim

theorem run_mem_core_after {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stabilizationTime family input ≤ t) :
    run (familyGenerator family) input t ∈ informationCore family input := by
  rw [run_follows (familyGenerator family) input t]
  have hstable := versionCore_stable family input ht
  have hinf : (versionCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    simpa [hstable] using hcore
  have hmem := familyGenerator_core family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (familyGenerator family) input i) hinf
  simpa [hstable] using hmem

theorem run_le_available_after {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t z : ℕ} (ht : stabilizationTime family input ≤ t)
    (hz : z ∈ informationCore family input)
    (hzx : ∀ s, s ≤ t → input s ≠ z)
    (hzy : ∀ s, s < t → run (familyGenerator family) input s ≠ z) :
    run (familyGenerator family) input t ≤ z := by
  rw [run_follows (familyGenerator family) input t]
  have hstable := versionCore_stable family input ht
  have hinf : (versionCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    simpa [hstable] using hcore
  apply familyGenerator_le family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (familyGenerator family) input i) hinf
  · simpa [hstable] using hz
  · intro i
    exact hzx i (Nat.le_of_lt_succ i.isLt)
  · intro i
    exact hzy i i.isLt

theorem run_novel_after {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (run (familyGenerator family) input)
      (family j) := by
  refine ⟨stabilizationTime family input, fun t ht => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (run_mem_core_after family input hcore ht) j hj
  · intro hmem
    classical
    rw [GenLimit.sample] at hmem
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hmem
    exact run_not_current_input family input t s
      (Nat.le_of_lt_succ (Finset.mem_range.mp hs)) heq
  · intro s hs
    exact run_not_previous family input hs

theorem core_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (run (familyGenerator family) input) := by
  intro z hz
  by_contra hnot
  simp only [Set.mem_union, Set.mem_range, not_or, not_exists] at hnot
  let T := stabilizationTime family input
  let f : Fin (z + 2) → Fin (z + 1) := fun k =>
    ⟨run (familyGenerator family) input (T + k), by
      have hle := run_le_available_after family input hcore
        (show T ≤ T + k by omega) hz
        (fun s hs heq => hnot.1 s heq)
        (fun s hs heq => hnot.2 s heq)
      omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hout : run (familyGenerator family) input (T + a) =
        run (familyGenerator family) input (T + b) := by
      exact Fin.ext_iff.mp hab
    have htime := run_injective family input hout
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard



theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run (familyGenerator family) input) := by
  intro z hz
  have hcovered := core_covered family input hcore hz.1
  rcases hcovered with hin | hout
  · exact (hz.2 hin).elim
  · obtain ⟨t, ht⟩ := hout
    refine ⟨t, ht, ?_⟩
    intro s hs heq
    exact hz.2 ⟨s, heq⟩

theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

theorem relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B)
    (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · filter_upwards [] with n
    gcongr
    exact prefixCount_mono hAB n
  · apply Filter.isBoundedUnder_of_eventually_ge
    filter_upwards [] with n
    exact div_nonneg (by positivity) (by positivity)
  · apply Filter.IsBoundedUnder.isCoboundedUnder_ge
    apply Filter.isBoundedUnder_of_eventually_le
    filter_upwards [] with n
    apply div_le_one_of_le₀
    · exact_mod_cast prefixCount_mono hBK n
    · positivity



theorem run_mem_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    run (familyGenerator family) input t ∈
      GenLimit.GeneratorFirst input (run (familyGenerator family) input) := by
  exact ⟨t, rfl, run_not_current_input family input t⟩

noncomputable def firstInputTime (input : Stream) (z : ℕ)
    (hz : z ∈ Set.range input) : ℕ :=
  Nat.find hz

theorem firstInputTime_spec (input : Stream) (z : ℕ)
    (hz : z ∈ Set.range input) :
    input (firstInputTime input z hz) = z :=
  Nat.find_spec hz

theorem firstInputTime_min (input : Stream) (z : ℕ)
    (hz : z ∈ Set.range input) {s : ℕ}
    (hs : s < firstInputTime input z hz) : input s ≠ z :=
  Nat.find_min hz hs

theorem core_not_generatorFirst_in_range {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input (run (familyGenerator family) input)) :
    z ∈ Set.range input := by
  by_contra hzrange
  exact hznot (core_diff_range_subset_generatorFirst family input hcore ⟨hzcore, hzrange⟩)

theorem paired_output_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {x w : ℕ}
    (hxcore : x ∈ informationCore family input)
    (hwcore : w ∈ informationCore family input)
    (hxnot : x ∉ GenLimit.GeneratorFirst input (run (familyGenerator family) input))
    (hwnot : w ∉ GenLimit.GeneratorFirst input (run (familyGenerator family) input))
    (hT : stabilizationTime family input ≤
      firstInputTime input x (core_not_generatorFirst_in_range family input hcore hxcore hxnot))
    (htime : firstInputTime input x
        (core_not_generatorFirst_in_range family input hcore hxcore hxnot) <
      firstInputTime input w
        (core_not_generatorFirst_in_range family input hcore hwcore hwnot)) :
    let tx := firstInputTime input x
      (core_not_generatorFirst_in_range family input hcore hxcore hxnot)
    run (familyGenerator family) input tx ∈ informationCore family input ∧
      run (familyGenerator family) input tx ∈
        GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∧
      run (familyGenerator family) input tx ≤ w := by
  let hxrange := core_not_generatorFirst_in_range family input hcore hxcore hxnot
  let hwrange := core_not_generatorFirst_in_range family input hcore hwcore hwnot
  let tx := firstInputTime input x hxrange
  let tw := firstInputTime input w hwrange
  have hw_input : ∀ s, s ≤ tx → input s ≠ w := by
    intro s hs
    exact firstInputTime_min input w hwrange (lt_of_le_of_lt hs htime)
  have hw_output : ∀ s, s < tx → run (familyGenerator family) input s ≠ w := by
    intro s hs heq
    exact hwnot ⟨s, heq, fun r hr => hw_input r (hr.trans hs.le)⟩
  exact ⟨run_mem_core_after family input hcore hT,
    run_mem_generatorFirst family input tx,
    run_le_available_after family input hcore hT hwcore hw_input hw_output⟩

theorem prefix_half_count {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hIK : informationCore family input ⊆ K) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩ K) n +
        stabilizationTime family input + 1 := by
  classical
  let I := informationCore family input
  let G := GenLimit.GeneratorFirst input (run (familyGenerator family) input)
  let U := GenLimit.PatientScope.prefixFinset I n
  let D := U.filter (fun z => z ∈ G)
  let A := U.filter (fun z => z ∉ G)
  have hpartition : D.card + A.card = U.card := by
    simpa [D, A] using Finset.filter_card_add_filter_neg_card_eq_card
      (s := U) (fun z => z ∈ G)
  have hA_range : ∀ z ∈ A, z ∈ Set.range input := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzU := hz'.1
    have hzU' : z < n ∧ z ∈ I := by
      have h := Finset.mem_filter.mp hzU
      exact ⟨Finset.mem_range.mp h.1, h.2⟩
    exact core_not_generatorFirst_in_range family input hcore hzU'.2 hz'.2
  let time : ℕ → ℕ := fun z =>
    if hz : z ∈ A then firstInputTime input z (hA_range z hz) else 0
  have htime_spec : ∀ z, z ∈ A → input (time z) = z := by
    intro z hz
    simp only [time, dif_pos hz]
    exact firstInputTime_spec input z (hA_range z hz)
  have htime_inj : Set.InjOn time (↑A : Set ℕ) := by
    intro x hx y hy hxy
    rw [← htime_spec x hx, ← htime_spec y hy, hxy]
  let T := stabilizationTime family input
  let early := A.filter (fun z => time z < T)
  let late := A.filter (fun z => T ≤ time z)
  have hsplit : early.card + late.card = A.card := by
    simpa [early, late, Nat.not_lt] using
      Finset.filter_card_add_filter_neg_card_eq_card (s := A) (fun z => time z < T)
  have hearly : early.card ≤ T := by
    have hle : early.card ≤ (Finset.range T).card := by
      apply Finset.card_le_card_of_injOn time
      · intro z hz
        have hz' : z ∈ early := hz
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hz').2
      · exact htime_inj.mono (by
          intro z hz
          have hz' : z ∈ early := hz
          exact (Finset.mem_filter.mp hz').1)
    simpa using hle
  have hDprefix : D.card ≤ GenLimit.PatientScope.prefixCount (G ∩ K) n := by
    apply Finset.card_le_card
    intro z hz
    simp only [D, U, GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range] at hz ⊢
    exact ⟨hz.1.1, hz.2, hIK hz.1.2⟩
  have hlate : late.card ≤ D.card + 1 := by
    by_cases hempty : late.Nonempty
    · obtain ⟨w, hwlate, hwmax⟩ := Finset.exists_max_image late time hempty
      have herase : (late.erase w).card ≤ D.card := by
        apply Finset.card_le_card_of_injOn (fun z => run (familyGenerator family) input (time z))
        · intro x hx
          have hxlate : x ∈ late := (Finset.mem_erase.mp hx).2
          have hxne : x ≠ w := (Finset.mem_erase.mp hx).1
          have hxA : x ∈ A := (Finset.mem_filter.mp hxlate).1
          have hwA : w ∈ A := (Finset.mem_filter.mp hwlate).1
          have hxtime_le := hwmax x hxlate
          have hxtime_ne : time x ≠ time w := fun h => hxne (htime_inj hxA hwA h)
          have hxtime : time x < time w := lt_of_le_of_ne hxtime_le hxtime_ne
          have hxU : x ∈ U := (Finset.mem_filter.mp hxA).1
          have hwU : w ∈ U := (Finset.mem_filter.mp hwA).1
          have hxnot : x ∉ G := (Finset.mem_filter.mp hxA).2
          have hwnot : w ∉ G := (Finset.mem_filter.mp hwA).2
          have hxU' : x < n ∧ x ∈ I := by
            simpa [U, GenLimit.PatientScope.prefixFinset] using hxU
          have hwU' : w < n ∧ w ∈ I := by
            simpa [U, GenLimit.PatientScope.prefixFinset] using hwU
          have hxcore : x ∈ I := hxU'.2
          have hwcore : w ∈ I := hwU'.2
          have hstable : T ≤ time x := (Finset.mem_filter.mp hxlate).2
          have hstable' : stabilizationTime family input ≤
              firstInputTime input x
                (core_not_generatorFirst_in_range family input hcore hxcore hxnot) := by
            simpa [T, time, hxA] using hstable
          have hxtime' :
              firstInputTime input x
                  (core_not_generatorFirst_in_range family input hcore hxcore hxnot) <
                firstInputTime input w
                  (core_not_generatorFirst_in_range family input hcore hwcore hwnot) := by
            simpa [time, hxA, hwA] using hxtime
          have hpair := paired_output_mem family input hcore hxcore hwcore hxnot hwnot
            hstable' hxtime'
          have hwn : w < n := hwU'.1
          have hpair' :
              run (familyGenerator family) input (time x) ∈ I ∧
              run (familyGenerator family) input (time x) ∈ G ∧
              run (familyGenerator family) input (time x) ≤ w := by
            simpa [time, hxA, I, G] using hpair
          show run (familyGenerator family) input (time x) ∈ D
          rw [Finset.mem_filter]
          constructor
          · simp only [U, GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
              Finset.mem_range]
            exact ⟨lt_of_le_of_lt hpair'.2.2 hwn, hpair'.1⟩
          · exact hpair'.2.1
        · intro x hx y hy hxy
          apply htime_inj
          · exact (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).1
          · exact (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).1
          exact run_injective family input hxy
      have hwmem : w ∈ late := hwlate
      have hcard := Finset.card_erase_add_one hwmem
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty] at hempty
      simp [hempty]
  change U.card ≤ 2 * GenLimit.PatientScope.prefixCount (G ∩ K) n + T + 1
  omega



theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  rw [tendsto_atTop]
  intro r
  obtain ⟨s, hsK, hscard⟩ := hK.exists_subset_card_eq r
  filter_upwards [eventually_ge_atTop (s.sup id + 1)] with n hn
  rw [← hscard]
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨lt_of_le_of_lt (Finset.le_sup (f := id) hz) (by omega), hsK hz⟩

theorem fixed_div_prefixCount_tendsto_zero {K : Set ℕ} (hK : K.Infinite)
    (c : ℝ) :
    Tendsto (fun n => c / (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop (nhds 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_natCast_atTop_atTop.comp (prefixCount_tendsto_atTop hK)

theorem ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) :=
  div_nonneg (by positivity) (by positivity)

theorem ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast prefixCount_mono hAK n
  · positivity

theorem half_relativeLowerDensity {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hK : K.Infinite) (hIK : informationCore family input ⊆ K) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩ K) K := by
  let I := informationCore family input
  let D := GenLimit.GeneratorFirst input (run (familyGenerator family) input) ∩ K
  let fI : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount I n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let fD : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let c : ℝ := stabilizationTime family input + 1
  have hIK' : I ⊆ K := by simpa [I] using hIK
  have hDK : D ⊆ K := by
    intro z hz
    exact hz.2
  have hpoint : ∀ n, (1 / 2 : ℝ) * fI n ≤ fD n +
      c / (GenLimit.PatientScope.prefixCount K n : ℝ) := by
    intro n
    have hcount : GenLimit.PatientScope.prefixCount I n ≤
        2 * GenLimit.PatientScope.prefixCount D n +
          stabilizationTime family input + 1 := by
      simpa [I, D] using prefix_half_count family input hcore K hIK n
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · have hi : GenLimit.PatientScope.prefixCount I n = 0 := by
        have := prefixCount_mono hIK' n
        omega
      have hd : GenLimit.PatientScope.prefixCount D n = 0 := by
        have := prefixCount_mono hDK n
        omega
      simp [fI, fD, c, hk, hi, hd]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      calc
        (1 / 2 : ℝ) * fI n =
            ((1 / 2 : ℝ) * GenLimit.PatientScope.prefixCount I n) /
              GenLimit.PatientScope.prefixCount K n := by simp [fI]; ring
        _ ≤ ((GenLimit.PatientScope.prefixCount D n : ℝ) + c) /
              GenLimit.PatientScope.prefixCount K n := by
            apply (div_le_div_iff_of_pos_right hkpos).2
            dsimp [c]
            have hcast : (GenLimit.PatientScope.prefixCount I n : ℝ) ≤
                2 * GenLimit.PatientScope.prefixCount D n +
                  stabilizationTime family input + 1 := by
              exact_mod_cast hcount
            nlinarith
        _ = fD n + c / GenLimit.PatientScope.prefixCount K n := by
            simp [fD, add_div]
  have hIbelow : IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop fI := by
    apply Filter.isBoundedUnder_of_eventually_ge
    filter_upwards [] with n
    exact ratio_nonneg I K n
  have hDbelow : IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop fD := by
    apply Filter.isBoundedUnder_of_eventually_ge
    filter_upwards [] with n
    exact ratio_nonneg D K n
  have hDabove : IsCoboundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop fD := by
    apply Filter.IsBoundedUnder.isCoboundedUnder_ge
    apply Filter.isBoundedUnder_of_eventually_le
    filter_upwards [] with n
    apply ratio_le_one
    intro z hz
    exact hz.2
  have herr : Tendsto
      (fun n => c / (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop (nhds 0) :=
    fixed_div_prefixCount_tendsto_zero hK c
  change (1 / 2 : ℝ) * liminf fI atTop ≤ liminf fD atTop
  rw [Filter.le_liminf_iff hDabove hDbelow]
  intro b hb
  let δ := (1 / 2 : ℝ) * liminf fI atTop - b
  have hδ : 0 < δ := sub_pos.mpr hb
  have hIlow : ∀ᶠ n in atTop, liminf fI atTop - δ < fI n :=
    Filter.eventually_lt_of_lt_liminf (sub_lt_self _ hδ) hIbelow
  have herrsmall : ∀ᶠ n in atTop,
      c / (GenLimit.PatientScope.prefixCount K n : ℝ) < δ / 2 :=
    herr.eventually_lt_const (half_pos hδ)
  filter_upwards [hIlow, herrsmall] with n hnI hnerr
  have hp := hpoint n
  dsimp [δ] at hδ hnI hnerr
  nlinarith


end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  refine ⟨Case017Proof.familyGenerator family, ?_⟩
  intro input hinjective hcompatible hcore
  let output := Case017Proof.run (Case017Proof.familyGenerator family) input
  refine ⟨output, Case017Proof.run_follows _ _, ?_⟩
  intro j hj
  refine ⟨Case017Proof.run_novel_after family input hcore j hj, ?_⟩
  apply max_le
  · exact Case017Proof.half_relativeLowerDensity family input hcore
      (family j) (hinfinite j) (fun z hz => hz j hj)
  · apply Case017Proof.relativeLowerDensity_mono
    · intro z hz
      exact ⟨Case017Proof.core_diff_range_subset_generatorFirst family input hcore hz,
        hz.1 j hj⟩
    · intro z hz
      exact hz.2
