import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Case017Proof

open Stage3Case017

noncomputable def currentScope {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def historySet {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

theorem scopeFreshExists {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : (currentScope family xs).Infinite) :
    ∃ n, n ∈ currentScope family xs ∧ n ∉ historySet xs ys :=
  h.exists_not_mem_finset (historySet xs ys)

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  intro t xs ys
  exact if h : (currentScope family xs).Infinite then
    Nat.find (scopeFreshExists family xs ys h)
  else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  WellFounded.fix Nat.lt_wfRel.wf fun t rec =>
    gen t (fun i => input i) (fun i => rec i i.isLt)

@[simp] theorem trajectory_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory, WellFounded.fix_eq]

 theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory_eq gen input t

theorem badWitness {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    ∃ n, input n ∉ family j := by
  rw [GenLimit.Generic.StreamIn, Set.range_subset_iff] at h
  push_neg at h
  exact h

noncomputable def badTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (badWitness family input j h)

noncomputable def stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  ∑ j, (badTime family input j + 1)

 theorem badTime_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (hj : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (badTime family input j) ∉ family j := by
  classical
  rw [badTime, dif_neg hj]
  exact Nat.find_spec (badWitness family input j hj)

 theorem badTime_lt_stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (j : Fin m) :
    badTime family input j < stableTime family input := by
  rw [stableTime]
  have hjmem : j ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ j
  have hle : badTime family input j + 1 ≤
      ∑ k : Fin m, (badTime family input k + 1) := by
    simpa using Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin m)))
      (f := fun k => badTime family input k + 1)
      (fun _ _ => Nat.zero_le _) hjmem
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hle

 theorem compatible_of_prefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) {t : ℕ}
    (ht : stableTime family input ≤ t) (j : Fin m)
    (hj : ∀ i : Fin (t + 1), input i ∈ family j) :
    GenLimit.Generic.StreamIn input (family j) := by
  by_contra hnot
  have hlt := badTime_lt_stableTime family input hm j
  have hb := badTime_spec family input j hnot
  have hi : badTime family input j < t + 1 := by omega
  exact hb (hj ⟨badTime family input j, hi⟩)

 theorem currentScope_eq_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) {t : ℕ}
    (ht : stableTime family input ≤ t) :
    currentScope family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact hj ⟨i, rfl⟩
  · intro hz j hj
    exact hz j (compatible_of_prefix family input hm ht j hj)

 theorem greedy_mem_fresh {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hinf : (currentScope family xs).Infinite) :
    greedyGenerator family t xs ys ∈ currentScope family xs ∧
      greedyGenerator family t xs ys ∉ historySet xs ys := by
  classical
  rw [greedyGenerator, dif_pos hinf]
  exact Nat.find_spec (scopeFreshExists family xs ys hinf)


theorem trajectory_step {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    let output := trajectory (greedyGenerator family) input
    output t ∈ informationCore family input ∧
      (∀ s, s ≤ t → input s ≠ output t) ∧
      (∀ s, s < t → output s ≠ output t) := by
  classical
  let output := trajectory (greedyGenerator family) input
  have hscope := currentScope_eq_core family input hm ht
  have hinf : (currentScope family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hscope]
    exact hcore
  have hpick := greedy_mem_fresh family
    (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i) hinf
  have hout : output t = greedyGenerator family t
      (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i) := by
    exact trajectory_eq (greedyGenerator family) input t
  rw [← hout] at hpick
  rw [hscope] at hpick
  refine ⟨hpick.1, ?_, ?_⟩
  · intro s hs heq
    apply hpick.2
    rw [historySet, Finset.mem_union]
    left
    rw [Finset.mem_image]
    exact ⟨⟨s, by omega⟩, Finset.mem_univ _, heq⟩
  · intro s hs heq
    apply hpick.2
    rw [historySet, Finset.mem_union]
    right
    rw [Finset.mem_image]
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, heq⟩

theorem eventually_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (greedyGenerator family) input) (family j) := by
  refine ⟨stableTime family input, ?_⟩
  intro t ht
  have hs := trajectory_step family input hm hcore ht
  refine ⟨?_, ?_, hs.2.2⟩
  · exact hs.1 j hj
  · intro hmem
    rw [GenLimit.sample, Finset.mem_image] at hmem
    obtain ⟨s, hslt, heq⟩ := hmem
    exact hs.2.1 s (Nat.le_of_lt_succ (by simpa only [Finset.mem_range] using hslt)) heq


theorem trajectory_le_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    {t z : ℕ} (ht : stableTime family input ≤ t)
    (hzcore : z ∈ informationCore family input)
    (hzinput : ∀ s, s ≤ t → input s ≠ z)
    (hzoutput : ∀ s, s < t → trajectory (greedyGenerator family) input s ≠ z) :
    trajectory (greedyGenerator family) input t ≤ z := by
  classical
  have hscope := currentScope_eq_core family input hm ht
  have hinf : (currentScope family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hscope]
    exact hcore
  rw [trajectory_eq, greedyGenerator, dif_pos hinf]
  apply Nat.find_min' (scopeFreshExists family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => trajectory (greedyGenerator family) input i) hinf)
  refine ⟨?_, ?_⟩
  · rwa [hscope]
  · rw [historySet, Finset.mem_union, not_or]
    constructor
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨s, -, heq⟩ := hmem
      exact hzinput s (Nat.le_of_lt_succ s.isLt) heq
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨s, -, heq⟩ := hmem
      exact hzoutput s s.isLt heq

theorem missing_core_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hzmissing : z ∉ Set.range input) :
    ∃ t, trajectory (greedyGenerator family) input t = z := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
      classical
      have lower_ready : ∀ w < z, w ∈ informationCore family input →
          ∃ r, (input r = w ∨ trajectory (greedyGenerator family) input r = w) := by
        intro w hw hwcore
        by_cases hwrange : w ∈ Set.range input
        · obtain ⟨r, hr⟩ := hwrange
          exact ⟨r, Or.inl hr⟩
        · obtain ⟨r, hr⟩ := ih w hw hwcore hwrange
          exact ⟨r, Or.inr hr⟩
      let readyTime : ℕ → ℕ := fun w =>
        if hw : w < z ∧ w ∈ informationCore family input then
          Classical.choose (lower_ready w hw.1 hw.2) + 1
        else 0
      let t := stableTime family input + ∑ w ∈ Finset.range z, readyTime w
      have ht : stableTime family input ≤ t := by
        simp [t]
      by_cases hprior : ∃ s < t, trajectory (greedyGenerator family) input s = z
      · obtain ⟨s, hs, hsz⟩ := hprior
        exact ⟨s, hsz⟩
      · have hzinput : ∀ s, s ≤ t → input s ≠ z := by
          intro s hs heq
          exact hzmissing ⟨s, heq⟩
        have houtle := trajectory_le_available family input hm hcore ht hzcore
          hzinput (by simpa only [not_exists, not_and] using hprior)
        have houtcore := (trajectory_step family input hm hcore ht).1
        have hnotlt : ¬ trajectory (greedyGenerator family) input t < z := by
          intro houtlt
          have hwready := lower_ready _ houtlt houtcore
          have hwcond : trajectory (greedyGenerator family) input t < z ∧
              trajectory (greedyGenerator family) input t ∈ informationCore family input :=
            ⟨houtlt, houtcore⟩
          have hmem : trajectory (greedyGenerator family) input t ∈ Finset.range z := by
            exact Finset.mem_range.mpr houtlt
          have hterm : readyTime (trajectory (greedyGenerator family) input t) ≤
              ∑ w ∈ Finset.range z, readyTime w := by
            exact Finset.single_le_sum (s := Finset.range z)
              (f := readyTime) (fun _ _ => Nat.zero_le _) hmem
          have hchosen := Classical.choose_spec hwready
          have hreadydef : readyTime (trajectory (greedyGenerator family) input t) =
              Classical.choose hwready + 1 := by
            simp only [readyTime, dif_pos hwcond]
          have hrlt : Classical.choose hwready < t := by
            dsimp [t]
            rw [hreadydef] at hterm
            omega
          rcases hchosen with hinput | houtput
          · exact (trajectory_step family input hm hcore ht).2.1
              (Classical.choose hwready) (Nat.le_of_lt hrlt) hinput
          · exact (trajectory_step family input hm hcore ht).2.2
              (Classical.choose hwready) hrlt houtput
        exact ⟨t, Nat.le_antisymm houtle (Nat.le_of_not_gt hnotlt)⟩

end Case017Proof

namespace Case017Proof

open Stage3Case017

theorem missing_core_subset_first {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  intro z hz
  obtain ⟨t, ht⟩ := missing_core_announced family input hm hcore hz.1 hz.2
  refine ⟨t, ht, ?_⟩
  intro s hs heq
  exact hz.2 ⟨s, heq⟩

theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

theorem relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply Filter.liminf_le_liminf
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_mono hAB n
    · positivity
  · apply Filter.isBoundedUnder_of
    refine ⟨0, ?_⟩
    intro n
    positivity
  · apply Filter.isCoboundedUnder_ge_of_eventually_le atTop (x := (1 : ℝ))
    filter_upwards [] with n
    apply div_le_one_of_le₀
    · exact_mod_cast prefixCount_mono hBK n
    · positivity

theorem missing_density_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩ family j)
        (family j) := by
  apply relativeLowerDensity_mono
  · intro z hz
    exact ⟨missing_core_subset_first family input hm hcore hz, hz.1 j hj⟩
  · exact Set.inter_subset_right


noncomputable def arrival (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

theorem arrival_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (arrival input z) = z := by
  classical
  rw [arrival, dif_pos hz]
  exact Nat.find_spec hz

theorem arrival_min (input : Stream) {z s : ℕ} (hz : z ∈ Set.range input)
    (hs : s < arrival input z) : input s ≠ z := by
  classical
  rw [arrival, dif_pos hz] at hs
  exact Nat.find_min hz hs

theorem arrival_injective (input : Stream) (hinj : Function.Injective input) :
    Set.InjOn (arrival input) (Set.range input) := by
  intro x hx y hy heq
  have h := congrArg input heq
  rwa [arrival_spec input hx, arrival_spec input hy] at h

theorem core_not_first_range {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input
      (trajectory (greedyGenerator family) input)) :
    z ∈ Set.range input := by
  by_contra hzrange
  exact hznot (missing_core_subset_first family input hm hcore ⟨hzcore, hzrange⟩)

theorem output_at_arrival_first {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hzrange : z ∈ Set.range input)
    (ht : stableTime family input ≤ arrival input z) :
    trajectory (greedyGenerator family) input (arrival input z) ∈
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  have hs := trajectory_step family input hm hcore ht
  refine ⟨arrival input z, rfl, ?_⟩
  exact hs.2.1

theorem output_arrival_lt_of_later {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    {z w n : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hzrange : z ∈ Set.range input)
    (hznot : z ∉ GenLimit.GeneratorFirst input
      (trajectory (greedyGenerator family) input))
    (hwcore : w ∈ informationCore family input)
    (hwrange : w ∈ Set.range input)
    (hwnot : w ∉ GenLimit.GeneratorFirst input
      (trajectory (greedyGenerator family) input))
    (ht : stableTime family input ≤ arrival input z)
    (harr : arrival input z < arrival input w)
    (hwn : w < n) :
    trajectory (greedyGenerator family) input (arrival input z) < n := by
  have hinput : ∀ s, s ≤ arrival input z → input s ≠ w := by
    intro s hs
    apply arrival_min input hwrange
    omega
  have houtput : ∀ s, s < arrival input z →
      trajectory (greedyGenerator family) input s ≠ w := by
    intro s hs heq
    apply hwnot
    refine ⟨s, heq, ?_⟩
    intro r hr hir
    exact arrival_min input hwrange (by omega) hir
  have hle := trajectory_le_available family input hm hcore ht hwcore hinput houtput
  exact lt_of_le_of_lt hle hwn

theorem output_arrival_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hm : 0 < m) (hcore : (informationCore family input).Infinite)
    {S : Set ℕ}
    (hSrange : S ⊆ Set.range input)
    (hSlate : ∀ z ∈ S, stableTime family input ≤ arrival input z) :
    Set.InjOn (fun z => trajectory (greedyGenerator family) input (arrival input z)) S := by
  intro x hx y hy heq
  by_contra hxy
  have harrne : arrival input x ≠ arrival input y := by
    intro harr
    exact hxy (arrival_injective input hinj (hSrange hx) (hSrange hy) harr)
  rcases lt_or_gt_of_ne harrne with hlt | hgt
  · exact (trajectory_step family input hm hcore (hSlate y hy)).2.2
      (arrival input x) hlt heq
  · exact (trajectory_step family input hm hcore (hSlate x hx)).2.2
      (arrival input y) hgt heq.symm

theorem prefix_half_count {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) (hm : 0 < m)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩ family j) n
        + stableTime family input + 1 := by
  classical
  let D := GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩ family j
  let C := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let DF := GenLimit.PatientScope.prefixFinset D n
  let B := C \ DF
  let E := B.filter (fun z => arrival input z < stableTime family input)
  let L := B.filter (fun z => stableTime family input ≤ arrival input z)
  have hBsplit : B = E ∪ L := by
    ext z
    simp only [E, L, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hz
      by_cases hlt : arrival input z < stableTime family input
      · exact Or.inl ⟨hz, hlt⟩
      · exact Or.inr ⟨hz, Nat.le_of_not_gt hlt⟩
    · rintro (hz | hz) <;> exact hz.1
  have memE : ∀ {z}, z ∈ E ↔ z ∈ C ∧ z ∉ DF ∧ arrival input z < stableTime family input := by
    intro z
    simp only [E, B, Finset.mem_filter, Finset.mem_sdiff, and_assoc]
  have memL : ∀ {z}, z ∈ L ↔ z ∈ C ∧ z ∉ DF ∧ stableTime family input ≤ arrival input z := by
    intro z
    simp only [L, B, Finset.mem_filter, Finset.mem_sdiff, and_assoc]
  have memC : ∀ {z}, z ∈ C ↔ z < n ∧ z ∈ informationCore family input := by
    intro z
    simp only [C, GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
  have memDF : ∀ {z}, z ∈ DF ↔ z < n ∧ z ∈ D := by
    intro z
    simp only [DF, GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
  have hEcard : E.card ≤ stableTime family input := by
    rw [← Finset.card_range (stableTime family input)]
    apply Finset.card_le_card_of_injOn (arrival input)
      (s := E) (t := Finset.range (stableTime family input))
    · intro z hz
      exact Finset.mem_range.mpr (memE.mp hz).2.2
    · intro x hx y hy heq
      have hxE := memE.mp hx
      have hyE := memE.mp hy
      have hxC := memC.mp hxE.1
      have hyC := memC.mp hyE.1
      apply arrival_injective input hinj
      · apply core_not_first_range family input hm hcore hxC.2
        intro hxfirst
        exact hxE.2.1 (memDF.mpr ⟨hxC.1, hxfirst, hxC.2 j hj⟩)
      · apply core_not_first_range family input hm hcore hyC.2
        intro hyfirst
        exact hyE.2.1 (memDF.mpr ⟨hyC.1, hyfirst, hyC.2 j hj⟩)
      · exact heq
  by_cases hLempty : L = ∅
  · have hBcard : B.card ≤ stableTime family input := by
      rw [hBsplit, hLempty, Finset.union_empty]
      exact hEcard
    have hCsplit : B.card + (C ∩ DF).card = C.card := by
      exact Finset.card_sdiff_add_card_inter C DF
    have hintercard : (C ∩ DF).card ≤ DF.card := Finset.card_le_card (Finset.inter_subset_right)
    dsimp [GenLimit.PatientScope.prefixCount]
    change C.card ≤ 2 * DF.card + stableTime family input + 1
    omega
  · have hLnonempty : L.Nonempty := Finset.nonempty_iff_ne_empty.mpr hLempty
    obtain ⟨last, hlastmem, hlastmax⟩ := Finset.exists_max_image L (arrival input) hLnonempty
    let L' := L.erase last
    have hlastL := memL.mp hlastmem
    have hlastC := memC.mp hlastL.1
    have hL'card : L'.card + 1 = L.card := by
      exact Finset.card_erase_add_one hlastmem
    have hmap : Set.MapsTo
        (fun z => trajectory (greedyGenerator family) input (arrival input z))
        (↑L' : Set ℕ) (↑DF : Set ℕ) := by
      intro z hz
      have hzL : z ∈ L := (Finset.mem_erase.mp hz).2
      have hzLm := memL.mp hzL
      have hzC := memC.mp hzLm.1
      have hzcore : z ∈ informationCore family input := hzC.2
      have hznotD := hzLm.2.1
      have hznot : z ∉ GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) := by
        intro hzfirst
        exact hznotD (by
          exact memDF.mpr ⟨hzC.1, hzfirst, hzcore j hj⟩)
      have hzrange := core_not_first_range family input hm hcore hzcore hznot
      have hlastcore : last ∈ informationCore family input := hlastC.2
      have hlastnot : last ∉ GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) := by
        intro hfirst
        exact hlastL.2.1 (by
          exact memDF.mpr ⟨hlastC.1, hfirst, hlastcore j hj⟩)
      have hlastrange := core_not_first_range family input hm hcore hlastcore hlastnot
      have harrle : arrival input z ≤ arrival input last := by
        exact hlastmax z hzL
      have harrlt : arrival input z < arrival input last := lt_of_le_of_ne harrle (by
        intro heq
        have hzlast := arrival_injective input hinj hzrange hlastrange heq
        exact (Finset.mem_erase.mp hz).1 hzlast)
      have houtfirst := output_at_arrival_first family input hm hcore hzcore hzrange hzLm.2.2
      have houtlt := output_arrival_lt_of_later family input hm hcore hzcore hzrange hznot
        hlastcore hlastrange hlastnot hzLm.2.2 harrlt hlastC.1
      exact memDF.mpr ⟨houtlt, houtfirst, (trajectory_step family input hm hcore hzLm.2.2).1 j hj⟩
    have hinjmap : Set.InjOn
        (fun z => trajectory (greedyGenerator family) input (arrival input z))
        (↑L' : Set ℕ) := by
      apply output_arrival_injective family input hinj hm hcore
      · intro z hz
        have hzL := (Finset.mem_erase.mp hz).2
        have hzLm := memL.mp hzL
        have hzC := memC.mp hzLm.1
        apply core_not_first_range family input hm hcore hzC.2
        intro hfirst
        exact hzLm.2.1 (memDF.mpr ⟨hzC.1, hfirst, hzC.2 j hj⟩)
      · intro z hz
        exact (memL.mp (Finset.mem_erase.mp hz).2).2.2
    have hL'cardle : L'.card ≤ DF.card :=
      Finset.card_le_card_of_injOn _ hmap hinjmap
    have hBcard : B.card ≤ DF.card + stableTime family input + 1 := by
      rw [hBsplit]
      calc
        (E ∪ L).card ≤ E.card + L.card := Finset.card_union_le E L
        _ ≤ stableTime family input + (L'.card + 1) := by omega
        _ ≤ stableTime family input + (DF.card + 1) := by omega
        _ = DF.card + stableTime family input + 1 := by omega
    have hCsplit : B.card + (C ∩ DF).card = C.card := by
      exact Finset.card_sdiff_add_card_inter C DF
    have hintercard : (C ∩ DF).card ≤ DF.card := Finset.card_le_card (Finset.inter_subset_right)
    dsimp [GenLimit.PatientScope.prefixCount]
    change C.card ≤ 2 * DF.card + stableTime family input + 1
    omega

theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => GenLimit.PatientScope.prefixCount K n) atTop atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) (r := 1) (by omega)] at hK
  convert hK using 1
  funext n
  classical
  simp only [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Finset.card_eq_sum_ones, Set.indicator, Pi.one_apply]
  rw [Finset.sum_filter]

theorem half_density_bound {m : ℕ} (family : Fin m → Language)
    (hfamily : ∀ j, (family j).Infinite)
    (input : Stream) (hinj : Function.Injective input) (hm : 0 < m)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩ family j)
        (family j) := by
  let A : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (informationCore family input) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  let D : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩ family j) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  let E : ℕ → ℝ := fun n =>
    ((stableTime family input + 1 : ℕ) : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  have hKtendNat := prefixCount_tendsto_atTop (hfamily j)
  have hKtend : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount (family j) n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKtendNat
  have hEtend : Tendsto E atTop (𝓝 0) := by
    exact hKtend.const_div_atTop _
  have hA0 : ∀ᶠ n in atTop, 0 ≤ A n := Filter.Eventually.of_forall (by
    intro n; dsimp [A]; positivity)
  have hD0 : ∀ᶠ n in atTop, 0 ≤ D n := Filter.Eventually.of_forall (by
    intro n; dsimp [D]; positivity)
  have hE0 : ∀ᶠ n in atTop, 0 ≤ E n := Filter.Eventually.of_forall (by
    intro n; dsimp [E]; positivity)
  have hA1 : ∀ᶠ n in atTop, A n ≤ 1 := Filter.Eventually.of_forall (by
    intro n
    dsimp [A]
    apply div_le_one_of_le₀
    · exact_mod_cast prefixCount_mono
        (show informationCore family input ⊆ family j from fun z hz => hz j hj) n
    · positivity)
  have hD1 : ∀ᶠ n in atTop, D n ≤ 1 := Filter.Eventually.of_forall (by
    intro n
    dsimp [D]
    apply div_le_one_of_le₀
    · exact_mod_cast prefixCount_mono Set.inter_subset_right n
    · positivity)
  have hE1 : ∀ᶠ n in atTop, E n ≤ 1 :=
    (hEtend.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))).mono
      (fun _ hn => le_of_lt hn)
  have hpoint : ∀ᶠ n in atTop, (1 / 2 : ℝ) * A n ≤ D n + E n := by
    have hkpos : ∀ᶠ n in atTop,
        0 < (GenLimit.PatientScope.prefixCount (family j) n : ℝ) :=
      (hKtend.eventually (eventually_gt_atTop 0))
    filter_upwards [hkpos] with n hn
    have hc := prefix_half_count family input hinj hm hcore j hj n
    have hcr : (GenLimit.PatientScope.prefixCount (informationCore family input) n : ℝ) ≤
        2 * (GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩ family j) n : ℝ)
          + ((stableTime family input + 1 : ℕ) : ℝ) := by
      exact_mod_cast hc
    dsimp [A, D, E]
    rw [div_add_div_same, ← mul_div_assoc, div_le_div_iff_of_pos_right hn]
    nlinarith
  have hmul : (1 / 2 : ℝ) * liminf A atTop ≤
      liminf (fun n => (1 / 2 : ℝ) * A n) atTop := by
    have hmulRaw := le_liminf_mul
      (f := atTop) (u := fun _ : ℕ => (1 / 2 : ℝ)) (v := A)
      (Filter.Eventually.of_forall (fun _ => by norm_num))
      (Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall (fun _ => le_rfl)))
      hA0 (Filter.isCoboundedUnder_ge_of_eventually_le atTop hA1)
    simpa [Filter.liminf_const] using hmulRaw
  have hleft0 : ∀ᶠ n in atTop, 0 ≤ (1 / 2 : ℝ) * A n := by
    filter_upwards [hA0] with n hn
    positivity
  have hright2 : ∀ᶠ n in atTop, D n + E n ≤ (2 : ℝ) := by
    filter_upwards [hD1, hE1] with n hd he
    linarith
  have hmono : liminf (fun n => (1 / 2 : ℝ) * A n) atTop ≤
      liminf (fun n => D n + E n) atTop := by
    exact Filter.liminf_le_liminf hpoint
      (Filter.isBoundedUnder_of_eventually_ge hleft0)
      (Filter.isCoboundedUnder_ge_of_eventually_le atTop hright2)
  have hadd : liminf (fun n => D n + E n) atTop ≤ liminf D atTop := by
    rw [show (fun n => D n + E n) = E + D by funext n; simp [add_comm]]
    calc
      liminf (E + D) atTop ≤ limsup E atTop + liminf D atTop := by
        apply liminf_add_le
        · exact Filter.isBoundedUnder_of_eventually_ge hE0
        · exact Filter.isBoundedUnder_of_eventually_le hE1
        · exact Filter.isBoundedUnder_of_eventually_ge hD0
        · exact Filter.isCoboundedUnder_ge_of_eventually_le atTop hD1
      _ = liminf D atTop := by rw [hEtend.limsup_eq]; simp
  change (1 / 2 : ℝ) * liminf A atTop ≤ liminf D atTop
  exact hmul.trans (hmono.trans hadd)
end Case017Proof

open Stage3Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  let gen := Case017Proof.greedyGenerator family
  refine ⟨gen, ?_⟩
  intro input hinj hexists hcore
  let output := Case017Proof.trajectory gen input
  refine ⟨output, Case017Proof.trajectory_follows gen input, ?_⟩
  intro j hj
  refine ⟨?_, ?_⟩
  · exact Case017Proof.eventually_novel family input hm hcore j hj
  apply max_le
  · exact Case017Proof.half_density_bound family hfamily input hinj hm hcore j hj
  · exact Case017Proof.missing_density_bound family input hm hcore j hj
