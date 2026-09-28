import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set

namespace Stage3Case017Proof

open Stage3Case017

def prefixCore {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, input i ∈ family j) → z ∈ family j}

def Available {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ prefixCore family input ∧
    (∀ i, z ≠ input i) ∧
    ∀ i, z ≠ output i

noncomputable def leastAvailable {m t : ℕ} (family : Fin m → Language)
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : ℕ := by
  classical
  exact if h : ∃ z, Available family input output z then Nat.find h else 0

theorem leastAvailable_spec {m t : ℕ} {family : Fin m → Language}
    {input : Fin (t + 1) → ℕ} {output : Fin t → ℕ}
    (h : ∃ z, Available family input output z) :
    Available family input output (leastAvailable family input output) := by
  classical
  rw [leastAvailable, dif_pos h]
  exact Nat.find_spec h

theorem leastAvailable_min {m t : ℕ} {family : Fin m → Language}
    {input : Fin (t + 1) → ℕ} {output : Fin t → ℕ}
    (h : ∃ z, Available family input output z)
    {z : ℕ} (hz : Available family input output z) :
    leastAvailable family input output ≤ z := by
  classical
  rw [leastAvailable, dif_pos h]
  exact Nat.find_min' h hz

noncomputable def familyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator :=
  fun _ input output => leastAvailable family input output

noncomputable def run {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) : ℕ :=
  familyGenerator family t (fun i => input i) (fun i => run family input i)
termination_by t
decreasing_by exact i.isLt

theorem run_follows {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Follows (familyGenerator family) input (run family input) := by
  intro t
  rw [run]


theorem streamIn_iff_forall {input : Stream} {L : Language} :
    GenLimit.Generic.StreamIn input L ↔ ∀ n, input n ∈ L := by
  constructor
  · intro h n
    exact h ⟨n, rfl⟩
  · rintro h _ ⟨n, rfl⟩
    exact h n

 theorem prefix_membership_eventually_iff {input : Stream} {L : Language} :
    ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ L) ↔
        GenLimit.Generic.StreamIn input L) := by
  classical
  by_cases h : GenLimit.Generic.StreamIn input L
  · refine ⟨0, fun t _ => ⟨fun _ => h, ?_⟩⟩
    intro _ i
    exact (streamIn_iff_forall.mp h) i
  · rw [streamIn_iff_forall] at h
    push_neg at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    intro t hnt
    constructor
    · intro hp
      exact False.elim (hn (hp ⟨n, Nat.lt_succ_of_le hnt⟩))
    · intro hs
      exact False.elim (hn ((streamIn_iff_forall.mp hs) n))

 theorem prefixCore_eventually_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  have hj : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    exact prefix_membership_eventually_iff
  let bound : Fin m → ℕ := fun j => Classical.choose (hj j)
  let T := ∑ j : Fin m, bound j
  refine ⟨T, ?_⟩
  intro t hT
  have hbound : ∀ j : Fin m, bound j ≤ t := by
    intro j
    have hjT : bound j ≤ T := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact le_trans hjT hT
  ext z
  simp only [prefixCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hjstream
    apply hz j
    have heq := Classical.choose_spec (hj j) t (hbound j)
    exact heq.mpr hjstream
  · intro hz j hjprefix
    apply hz j
    have heq := Classical.choose_spec (hj j) t (hbound j)
    exact heq.mp hjprefix


theorem available_of_infinite {m t : ℕ} {family : Fin m → Language}
    {input : Fin (t + 1) → ℕ} {output : Fin t → ℕ}
    (hcore : (prefixCore family input).Infinite) :
    ∃ z, Available family input output z := by
  classical
  let forbidden : Finset ℕ :=
    Finset.univ.image input ∪ Finset.univ.image output
  obtain ⟨z, hzcore, hznot⟩ := hcore.exists_notMem_finset forbidden
  refine ⟨z, hzcore, ?_, ?_⟩
  · intro i hzi
    apply hznot
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hzi.symm⟩
  · intro i hzi
    apply hznot
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hzi.symm⟩

 theorem run_eventually_core_fresh {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      run family input t ∈ informationCore family input ∧
      run family input t ∉ GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t → run family input s ≠ run family input t := by
  classical
  obtain ⟨T, hstable⟩ := prefixCore_eventually_eq_informationCore family input
  refine ⟨T, ?_⟩
  intro t ht
  have hcoreEq := hstable t ht
  have hprefixInfinite :
      (prefixCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hcoreEq]
    exact hcore
  have havail : ∃ z, Available family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run family input i) z :=
    available_of_infinite hprefixInfinite
  have hspec := leastAvailable_spec havail
  have hout : run family input t = leastAvailable family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run family input i) := by
    rw [run, familyGenerator]
  rw [hout] at *
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcoreEq]
    exact hspec.1
  · intro hsample
    rw [GenLimit.Generic.mem_sample_iff] at hsample
    obtain ⟨s, hst, hs⟩ := hsample
    exact hspec.2.1 ⟨s, hst⟩ hs.symm
  · intro s hst hs
    exact hspec.2.2 ⟨s, hst⟩ hs.symm


theorem informationCore_subset_announced {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (run family input) := by
  classical
  intro z hz
  by_contra hnot
  have hzInput : z ∉ Set.range input := by
    intro h
    exact hnot (Set.mem_union_left _ h)
  have hzOutput : z ∉ Set.range (run family input) := by
    intro h
    exact hnot (Set.mem_union_right _ h)
  obtain ⟨T, hstable⟩ := prefixCore_eventually_eq_informationCore family input
  obtain ⟨Tf, hfresh⟩ := run_eventually_core_fresh family input hcore
  let B := max T Tf
  have hle (q : ℕ) : run family input (B + q) ≤ z := by
    let t := B + q
    have htT : T ≤ t := by exact le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)
    have hEq := hstable t htT
    have havailZ : Available family
        (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => run family input i) z := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hEq]
        exact hz
      · intro i hzi
        exact hzInput ⟨i, hzi.symm⟩
      · intro i hzi
        exact hzOutput ⟨i, hzi.symm⟩
    have hex : ∃ w, Available family
        (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => run family input i) w := ⟨z, havailZ⟩
    have hmin := leastAvailable_min hex havailZ
    have hout : run family input t = leastAvailable family
        (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => run family input i) := by
      rw [run, familyGenerator]
    simpa [t, hout] using hmin
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨run family input (B + i), Nat.lt_succ_of_le (hle i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hijval
    have hneTime : B + (i : ℕ) ≠ B + (j : ℕ) := by
      intro heq
      apply hijval
      omega
    rcases lt_or_gt_of_ne hneTime with hijt | hjit
    · have htime : Tf ≤ B + (j : ℕ) := by
        exact le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)
      have hneq := (hfresh (B + (j : ℕ)) htime).2.2
        (B + (i : ℕ)) hijt
      exact hneq (congrArg Fin.val hij)
    · have htime : Tf ≤ B + (i : ℕ) := by
        exact le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)
      have hneq := (hfresh (B + (i : ℕ)) htime).2.2
        (B + (j : ℕ)) hjit
      exact hneq (congrArg Fin.val hij).symm
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega


theorem output_range_subset_first_announcements
    (input output : Stream) :
    Set.range output ⊆
      GenLimit.AdversaryFirst input output ∪
        GenLimit.GeneratorFirst input output := by
  classical
  intro z hz
  let t := Nat.find hz
  have hout : output t = z := Nat.find_spec hz
  by_cases hin : ∃ s, s ≤ t ∧ input s = z
  · obtain ⟨s, hst, hs⟩ := hin
    refine Set.mem_union_left _ ⟨s, hs, ?_⟩
    intro q hqs hq
    have hqt : q < t := lt_of_lt_of_le hqs hst
    exact (Nat.not_lt_of_ge (Nat.find_min' hz hq)) hqt
  · refine Set.mem_union_right _ ⟨t, hout, ?_⟩
    intro s hst hs
    exact hin ⟨s, hst, hs⟩

 theorem informationCore_subset_first_announcements {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (run family input) ∪
        GenLimit.GeneratorFirst input (run family input) := by
  intro z hz
  rcases informationCore_subset_announced family input hcore hz with hzIn | hzOut
  · exact GenLimit.range_subset_first_announcements input (run family input) hzIn
  · exact output_range_subset_first_announcements input (run family input) hzOut

 theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (run family input) := by
  intro z hz
  rcases informationCore_subset_first_announcements family input hcore hz.1 with hzA | hzG
  · obtain ⟨t, ht, -⟩ := hzA
    exact False.elim (hz.2 ⟨t, ht⟩)
  · exact hzG

 theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  let aRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let bRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hab : ∀ n, aRatio n ≤ bRatio n := by
    intro n
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
      (Nat.cast_nonneg _)
  have haBound : Filter.atTop.IsBoundedUnder (· ≥ ·) aRatio :=
    Filter.isBoundedUnder_of_eventually_ge <|
      Filter.Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbLeOne : ∀ n, bRatio n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [bRatio, hn]
    · dsimp [bRatio]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  have hbCobound : Filter.atTop.IsCoboundedUnder (· ≥ ·) bRatio :=
    Filter.isCoboundedUnder_ge_of_le Filter.atTop hbLeOne
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hab) haBound hbCobound


noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

theorem firstInputTime_spec {input : Stream} {z : ℕ}
    (hz : z ∈ Set.range input) : input (firstInputTime input z) = z := by
  classical
  rw [firstInputTime, dif_pos hz]
  exact Nat.find_spec hz

 theorem firstInputTime_min {input : Stream} {z : ℕ}
    (hz : z ∈ Set.range input) {t : ℕ} (ht : input t = z) :
    firstInputTime input z ≤ t := by
  classical
  rw [firstInputTime, dif_pos hz]
  exact Nat.find_min' hz ht

 theorem run_tail_injective {m : ℕ} {family : Fin m → Language}
    {input : Stream} {T : ℕ}
    (hfresh : ∀ t, T ≤ t →
      run family input t ∈ informationCore family input ∧
      run family input t ∉ GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t → run family input s ≠ run family input t) :
    Set.InjOn (run family input) {t | T ≤ t} := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with habt | hbat
  · exact (hfresh b hb).2.2 a habt hab
  · exact (hfresh a ha).2.2 b hbat hab.symm


theorem late_output_mem_generatorFirst {m : ℕ} {family : Fin m → Language}
    {input : Stream} {T t : ℕ}
    (hfresh : ∀ q, T ≤ q →
      run family input q ∈ informationCore family input ∧
      run family input q ∉ GenLimit.Generic.sample input (q + 1) ∧
      ∀ s, s < q → run family input s ≠ run family input q)
    (ht : T ≤ t) :
    run family input t ∈
      GenLimit.GeneratorFirst input (run family input) ∩
        informationCore family input := by
  refine ⟨?_, (hfresh t ht).1⟩
  refine ⟨t, rfl, ?_⟩
  intro s hst hs
  apply (hfresh t ht).2.1
  rw [GenLimit.Generic.mem_sample_iff]
  exact ⟨s, Nat.lt_succ_of_le hst, hs⟩

 theorem adversaryFirst_before_firstInput {input output : Stream}
    (hinj : Function.Injective input) {z : ℕ}
    (hzA : z ∈ GenLimit.AdversaryFirst input output) :
    ∀ s, s < firstInputTime input z → output s ≠ z := by
  obtain ⟨t, ht, hbefore⟩ := hzA
  have hzRange : z ∈ Set.range input := ⟨t, ht⟩
  have heq : t = firstInputTime input z := by
    apply hinj
    rw [ht, firstInputTime_spec hzRange]
  simpa [← heq] using hbefore


theorem core_prefix_counting {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) :
    ∃ c, ∀ n,
      GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (run family input) ∩
            informationCore family input) n + c := by
  classical
  let I := informationCore family input
  let output := run family input
  obtain ⟨Ts, hstable0⟩ := prefixCore_eventually_eq_informationCore family input
  obtain ⟨Tf, hfresh0⟩ := run_eventually_core_fresh family input hcore
  let T := max Ts Tf
  have hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) = I := by
    intro t ht
    exact hstable0 t (le_trans (Nat.le_max_left _ _) ht)
  have hfresh : ∀ t, T ≤ t →
      output t ∈ I ∧
      output t ∉ GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t → output s ≠ output t := by
    intro t ht
    exact hfresh0 t (le_trans (Nat.le_max_right _ _) ht)
  refine ⟨T + 1, ?_⟩
  intro n
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ I) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ I) n
  have hpartition : GenLimit.PatientScope.prefixCount I n = A.card + D.card := by
    have hdis : Disjoint A D := by
      rw [Finset.disjoint_left]
      intro z hzA hzD
      have hzA' := (GenLimit.PatientScope.mem_prefixFinset.mp hzA).2.1
      have hzD' := (GenLimit.PatientScope.mem_prefixFinset.mp hzD).2.1
      exact Set.disjoint_left.1
        (GenLimit.adversaryFirst_disjoint_generatorFirst input output) hzA' hzD'
    have hunion : GenLimit.PatientScope.prefixFinset I n = A ∪ D := by
      ext z
      simp only [GenLimit.PatientScope.mem_prefixFinset, Finset.mem_union, A, D]
      constructor
      · intro hz
        rcases informationCore_subset_first_announcements family input hcore hz.2 with hzA | hzD
        · exact Or.inl ⟨hz.1, hzA, hz.2⟩
        · exact Or.inr ⟨hz.1, hzD, hz.2⟩
      · rintro (⟨hzn, -, hzI⟩ | ⟨hzn, -, hzI⟩)
        · exact ⟨hzn, hzI⟩
        · exact ⟨hzn, hzI⟩
    unfold GenLimit.PatientScope.prefixCount
    rw [hunion, Finset.card_union_of_disjoint hdis]
  have hbad_order : ∀ x y : ↥A,
      firstInputTime input x < firstInputTime input y →
      T ≤ firstInputTime input x →
      n ≤ output (firstInputTime input x) → False := by
    intro x y hxyTime hxLate hxLarge
    have hyMem := GenLimit.PatientScope.mem_prefixFinset.mp y.property
    have hyRange : (y : ℕ) ∈ Set.range input := by
      obtain ⟨q, hq, -⟩ := hyMem.2.1
      exact ⟨q, hq⟩
    have hyAvailable : Available family
        (fun i : Fin (firstInputTime input x + 1) => input i)
        (fun i : Fin (firstInputTime input x) => output i) y := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hstable (firstInputTime input x) hxLate]
        exact hyMem.2.2
      · intro i hyi
        have hmin := firstInputTime_min hyRange hyi.symm
        omega
      · intro i hyi
        exact adversaryFirst_before_firstInput hinj hyMem.2.1 i
          (lt_trans i.isLt hxyTime) hyi.symm
    have hex : ∃ z, Available family
        (fun i : Fin (firstInputTime input x + 1) => input i)
        (fun i : Fin (firstInputTime input x) => output i) z :=
      ⟨y, hyAvailable⟩
    have hle := leastAvailable_min hex hyAvailable
    have hout : output (firstInputTime input x) = leastAvailable family
        (fun i : Fin (firstInputTime input x + 1) => input i)
        (fun i : Fin (firstInputTime input x) => output i) := by
      dsimp [output]
      rw [run, familyGenerator]
    have houtLe : output (firstInputTime input x) ≤ (y : ℕ) := by
      simpa [hout] using hle
    have hylt : (y : ℕ) < n := hyMem.1
    omega
  have hbad_unique : ∀ x y : ↥A,
      T ≤ firstInputTime input x →
      T ≤ firstInputTime input y →
      n ≤ output (firstInputTime input x) →
      n ≤ output (firstInputTime input y) → x = y := by
    intro x y hxLate hyLate hxLarge hyLarge
    by_contra hxy
    have htimeNe : firstInputTime input x ≠ firstInputTime input y := by
      intro heq
      apply hxy
      apply Subtype.ext
      have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp x.property).2.1
      have hyA := (GenLimit.PatientScope.mem_prefixFinset.mp y.property).2.1
      obtain ⟨tx, htx, -⟩ := hxA
      obtain ⟨ty, hty, -⟩ := hyA
      have hxRange : (x : ℕ) ∈ Set.range input := ⟨tx, htx⟩
      have hyRange : (y : ℕ) ∈ Set.range input := ⟨ty, hty⟩
      rw [← firstInputTime_spec hxRange, ← firstInputTime_spec hyRange, heq]
    rcases lt_or_gt_of_ne htimeNe with hxyTime | hyxTime
    · exact hbad_order x y hxyTime hxLate hxLarge
    · exact hbad_order y x hyxTime hyLate hyLarge
  let g : ↥A → Fin T ⊕ (↥D ⊕ Unit) := fun x =>
    if hearly : firstInputTime input x < T then
      Sum.inl ⟨firstInputTime input x, hearly⟩
    else if hsmall : output (firstInputTime input x) < n then
      Sum.inr (Sum.inl ⟨output (firstInputTime input x), by
        apply GenLimit.PatientScope.mem_prefixFinset.mpr
        refine ⟨hsmall, ?_⟩
        exact late_output_mem_generatorFirst hfresh (Nat.le_of_not_gt hearly)⟩)
    else
      Sum.inr (Sum.inr ())
  have hg : Function.Injective g := by
    intro x y hxy
    by_cases hxEarly : firstInputTime input x < T
    · by_cases hyEarly : firstInputTime input y < T
      · have htime : firstInputTime input x = firstInputTime input y := by
          simpa [g, hxEarly, hyEarly] using hxy
        apply Subtype.ext
        have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp x.property).2.1
        have hyA := (GenLimit.PatientScope.mem_prefixFinset.mp y.property).2.1
        obtain ⟨tx, htx, -⟩ := hxA
        obtain ⟨ty, hty, -⟩ := hyA
        have hxRange : (x : ℕ) ∈ Set.range input := ⟨tx, htx⟩
        have hyRange : (y : ℕ) ∈ Set.range input := ⟨ty, hty⟩
        rw [← firstInputTime_spec hxRange, ← firstInputTime_spec hyRange, htime]
      · by_cases hySmall : output (firstInputTime input y) < n <;>
          simp [g, hxEarly, hyEarly, hySmall] at hxy
    · by_cases hyEarly : firstInputTime input y < T
      · by_cases hxSmall : output (firstInputTime input x) < n <;>
          simp [g, hxEarly, hyEarly, hxSmall] at hxy
      · by_cases hxSmall : output (firstInputTime input x) < n
        · by_cases hySmall : output (firstInputTime input y) < n
          · have houtEq : output (firstInputTime input x) =
                output (firstInputTime input y) := by
              simpa [g, hxEarly, hyEarly, hxSmall, hySmall] using hxy
            have htime := run_tail_injective hfresh
              (Nat.le_of_not_gt hxEarly) (Nat.le_of_not_gt hyEarly) houtEq
            apply Subtype.ext
            have hxA := (GenLimit.PatientScope.mem_prefixFinset.mp x.property).2.1
            have hyA := (GenLimit.PatientScope.mem_prefixFinset.mp y.property).2.1
            obtain ⟨tx, htx, -⟩ := hxA
            obtain ⟨ty, hty, -⟩ := hyA
            have hxRange : (x : ℕ) ∈ Set.range input := ⟨tx, htx⟩
            have hyRange : (y : ℕ) ∈ Set.range input := ⟨ty, hty⟩
            rw [← firstInputTime_spec hxRange, ← firstInputTime_spec hyRange, htime]
          · simp [g, hxEarly, hyEarly, hxSmall, hySmall] at hxy
        · by_cases hySmall : output (firstInputTime input y) < n
          · simp [g, hxEarly, hyEarly, hxSmall, hySmall] at hxy
          · exact hbad_unique x y (Nat.le_of_not_gt hxEarly)
              (Nat.le_of_not_gt hyEarly) (Nat.le_of_not_gt hxSmall)
              (Nat.le_of_not_gt hySmall)
  have hcard := Fintype.card_le_of_injective g hg
  have hAcard : A.card ≤ T + (D.card + 1) := by
    simpa using hcard
  have hDcard : GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (run family input) ∩
        informationCore family input) n = D.card := rfl
  rw [hpartition, hDcard]
  omega


theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {K : Language} (hK : K.Infinite)
    (hIK : informationCore family input ⊆ K) :
    (1 / 2 : ℝ) *
        GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (run family input) ∩ K) K := by
  obtain ⟨c, hcountCore⟩ := core_prefix_counting family input hinj hcore
  let N : ℕ → ℕ := GenLimit.PatientScope.prefixCount K
  let E : ℕ → ℕ := GenLimit.PatientScope.prefixCount (informationCore family input)
  let D : ℕ → ℕ := GenLimit.PatientScope.prefixCount
    (GenLimit.GeneratorFirst input (run family input) ∩ K)
  have hDI :
      GenLimit.GeneratorFirst input (run family input) ∩
          informationCore family input ⊆
        GenLimit.GeneratorFirst input (run family input) ∩ K := by
    intro z hz
    exact ⟨hz.1, hIK hz.2⟩
  have hresult := GenLimit.PatientScope.partialDensity_of_counting N E D c
    (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
    (fun n => GenLimit.PatientScope.prefixCount_mono hIK n)
    (fun n => GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n)
    (fun n => by
      calc
        E n ≤ 2 * GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input (run family input) ∩
              informationCore family input) n + c := hcountCore n
        _ ≤ 2 * D n + c := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left 2
              (GenLimit.PatientScope.prefixCount_mono hDI n)) c
        _ ≤ 2 * D n + c + Nat.log2 (N n) := Nat.le_add_right _ _)
  simpa [N, E, D, GenLimit.PatientScope.relativeLowerDensity] using hresult

 theorem target_density_bounds {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hK : (family j).Infinite)
    (hstream : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) *
          GenLimit.PatientScope.relativeLowerDensity
            (informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input (run family input) ∩ family j)
          (family j) := by
  have hIK : informationCore family input ⊆ family j := by
    intro z hz
    exact hz j hstream
  apply max_le
  · exact half_core_density family input hinj hcore hK hIK
  · apply relativeLowerDensity_mono
    · intro z hz
      exact ⟨core_diff_range_subset_generatorFirst family input hcore hz,
        hIK hz.1⟩
    · exact Set.inter_subset_right

end Stage3Case017Proof
