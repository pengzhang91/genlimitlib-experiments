import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

noncomputable section

open Stage3Case017

def prefixCompatible {m t : ℕ} (family : Fin m → Language)
    (xs : Fin t → ℕ) (j : Fin m) : Prop :=
  ∀ i, xs i ∈ family j

def active {m t : ℕ} (family : Fin m → Language)
    (xs : Fin t → ℕ) (z : ℕ) : Prop :=
  ∀ j, prefixCompatible family xs j → z ∈ family j

def blocked {s t : ℕ} (xs : Fin s → ℕ) (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

def available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  active family xs z ∧ z ∉ blocked xs ys

 theorem exists_unblocked {s t : ℕ} (xs : Fin s → ℕ) (ys : Fin t → ℕ) :
    ∃ z, z ∉ blocked xs ys := by
  obtain ⟨z, -, hz⟩ := Set.infinite_univ.exists_not_mem_finset (blocked xs ys)
  exact ⟨z, hz⟩

def greedyGenerator {m : ℕ} (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : ∃ z, available family xs ys z then Nat.find h
    else Nat.find (exists_unblocked xs ys)

theorem greedy_not_blocked {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    greedyGenerator family t xs ys ∉ blocked xs ys := by
  classical
  rw [greedyGenerator]
  split
  next h => exact (Nat.find_spec h).2
  next h => exact Nat.find_spec (exists_unblocked xs ys)

theorem greedy_spec {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, available family xs ys z) :
    available family xs ys (greedyGenerator family t xs ys) := by
  classical
  rw [greedyGenerator, dif_pos h]
  exact Nat.find_spec h

theorem greedy_le {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, available family xs ys z) {z : ℕ}
    (hz : available family xs ys z) :
    greedyGenerator family t xs ys ≤ z := by
  classical
  rw [greedyGenerator, dif_pos h]
  exact Nat.find_min' h hz

def run {m : ℕ} (family : Fin m → Language) (input : Stream) : Stream :=
  fun t => (Nat.strongRec (motive := fun _ => ℕ)
    (fun n rec => greedyGenerator family n (fun i => input i) (fun i => rec i i.isLt)) t)

theorem run_eq {m : ℕ} (family : Fin m → Language) (input : Stream) (t : ℕ) :
    run family input t = greedyGenerator family t (fun i => input i)
      (fun i => run family input i) := by
  exact Nat.strongRec_eq
    (fun n rec => greedyGenerator family n (fun i => input i)
      (fun i => rec i i.isLt)) t

theorem run_follows {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Follows (greedyGenerator family) input (run family input) := by
  intro t
  exact run_eq family input t

theorem run_avoids {m : ℕ} (family : Fin m → Language) (input : Stream)
    (t : ℕ) :
    (∀ s, s ≤ t → input s ≠ run family input t) ∧
      (∀ s, s < t → run family input s ≠ run family input t) := by
  have h := greedy_not_blocked family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run family input i)
  rw [← run_eq family input t] at h
  constructor
  · intro s hs heq
    apply h
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨⟨s, Nat.lt_succ_iff.mpr hs⟩, Finset.mem_univ _, heq⟩
  · intro s hs heq
    apply h
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨⟨s, hs⟩, Finset.mem_univ _, heq⟩

theorem run_injective {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Function.Injective (run family input) := by
  intro s t heq
  rcases lt_trichotomy s t with hst | hst | hst
  · exact False.elim ((run_avoids family input t).2 s hst heq)
  · exact hst
  · exact False.elim ((run_avoids family input s).2 t hst heq.symm)

theorem eventually_prefixCompatible {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      prefixCompatible family (fun i : Fin (t + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hEach : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      (prefixCompatible family (fun i : Fin (t + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hj : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, fun t _ => ⟨fun _ => hj, ?_⟩⟩
      intro _ i
      exact hj ⟨i, rfl⟩
    · rw [GenLimit.Generic.StreamIn] at hj
      obtain ⟨x, ⟨s, rfl⟩, hs⟩ := Set.not_subset.mp hj
      refine ⟨s, fun t hst => ⟨?_, fun h => False.elim (hj h)⟩⟩
      intro hprefix
      exact False.elim (hs (hprefix ⟨s, lt_of_le_of_lt hst (Nat.lt_succ_self t)⟩))
  choose cutoff hcutoff using hEach
  obtain ⟨T, hT⟩ := Finset.exists_le (Finset.univ.image cutoff)
  refine ⟨T, ?_⟩
  intro t ht j
  apply hcutoff j t
  exact le_trans (hT _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)) ht


theorem active_iff_informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (ht : T ≤ t) (z : ℕ) :
    active family (fun i : Fin (t + 1) => input i) z ↔
      z ∈ informationCore family input := by
  constructor
  · intro hz j hj
    exact hz j ((hstable t ht j).mpr hj)
  · intro hz j hj
    exact hz j ((hstable t ht j).mp hj)

theorem exists_available_of_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (ht : T ≤ t) :
    ∃ z, available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run family input i) z := by
  obtain ⟨z, hzcore, hzblock⟩ :=
    hcore.exists_not_mem_finset
      (blocked (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => run family input i))
  exact ⟨z, (active_iff_informationCore family input hstable ht z).2 hzcore,
    hzblock⟩

theorem run_mem_core_of_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (ht : T ≤ t) :
    run family input t ∈ informationCore family input := by
  have hex := exists_available_of_stable family input hstable hcore ht
  have hspec := greedy_spec family (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run family input i) hex
  rw [← run_eq family input t] at hspec
  exact (active_iff_informationCore family input hstable ht _).1 hspec.1

theorem run_le_of_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t z : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (ht : T ≤ t)
    (hzcore : z ∈ informationCore family input)
    (hzinput : ∀ s, s ≤ t → input s ≠ z)
    (hzoutput : ∀ s, s < t → run family input s ≠ z) :
    run family input t ≤ z := by
  have hex := exists_available_of_stable family input hstable hcore ht
  have hzblock : z ∉ blocked (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run family input i) := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
      exact hzinput i (Nat.le_of_lt_succ i.isLt) hi
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
      exact hzoutput i i.isLt hi
  have hzavail : available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => run family input i) z :=
    ⟨(active_iff_informationCore family input hstable ht z).2 hzcore, hzblock⟩
  rw [run_eq family input t]
  exact greedy_le family _ _ hex hzavail

def tail {m : ℕ} (family : Fin m → Language) (input : Stream) (T : ℕ) : Stream :=
  fun n => run family input (T + n)

theorem tail_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ) : Function.Injective (tail family input T) := by
  intro s t h
  have := run_injective family input h
  omega

theorem tail_mem_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    tail family input T n ∈ informationCore family input := by
  exact run_mem_core_of_stable family input hstable hcore (Nat.le_add_right T n)

theorem core_diff_range_subset_run {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      Set.range (run family input) := by
  intro z hz
  by_contra hzrun
  have hzinput : ∀ s, input s ≠ z := by
    intro s hs
    exact hz.2 ⟨s, hs⟩
  have hzout : ∀ n, run family input n ≠ z := by
    intro n hn
    exact hzrun ⟨n, hn⟩
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨run family input (T + i), by
      have hle : run family input (T + i) ≤ z := by
        apply run_le_of_available family input hstable hcore (Nat.le_add_right T i) hz.1
        · intro s _
          exact hzinput s
        · intro s _
          exact hzout s
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hrun : run family input (T + i) = run family input (T + j) :=
      congrArg Fin.val hij
    have hadd : T + (i : ℕ) = T + (j : ℕ) := run_injective family input hrun
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega


def earlyInputs (input : Stream) (T : ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : Fin (T + 1) => input i)

def firstTime (input : Stream) (x : ℕ) : ℕ := by
  classical
  exact if h : x ∈ Set.range input then Nat.find h else 0

theorem firstTime_spec (input : Stream) {x : ℕ} (hx : x ∈ Set.range input) :
    input (firstTime input x) = x := by
  classical
  rw [firstTime, dif_pos hx]
  exact Nat.find_spec hx

theorem firstTime_min (input : Stream) {x : ℕ} (hx : x ∈ Set.range input)
    {s : ℕ} (hs : input s = x) : firstTime input x ≤ s := by
  classical
  rw [firstTime, dif_pos hx]
  exact Nat.find_min' hx hs

def traceAttacker {m : ℕ} (family : Fin m → Language) (input : Stream) : Set ℕ :=
  informationCore family input \ Set.range (run family input)

def traceDefender {m : ℕ} (family : Fin m → Language) (input : Stream) : Set ℕ :=
  Set.range (run family input)

def predecessorPartner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (x : ℕ) : ℕ :=
  run family input (firstTime input x - 1)

theorem core_subset_compatible {m : ℕ} (family : Fin m → Language)
    (input : Stream) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro x hx
  exact hx j hj

theorem attacker_mem_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) {x : ℕ}
    (hx : x ∈ traceAttacker family input) : x ∈ Set.range input := by
  by_contra hxinput
  exact hx.2 (core_diff_range_subset_run family input hstable hcore
    ⟨hx.1, hxinput⟩)

theorem firstTime_gt_of_not_early {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) {x : ℕ}
    (hxatt : x ∈ traceAttacker family input)
    (hxearly : x ∉ earlyInputs input T) : T < firstTime input x := by
  have hxrange := attacker_mem_input family input hstable hcore hxatt
  by_contra hnot
  have hle : firstTime input x ≤ T := Nat.le_of_not_gt hnot
  apply hxearly
  apply Finset.mem_image.mpr
  exact ⟨⟨firstTime input x, Nat.lt_succ_iff.mpr hle⟩, Finset.mem_univ _,
    firstTime_spec input hxrange⟩

theorem predecessor_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) {x : ℕ}
    (hxatt : x ∈ traceAttacker family input)
    (hxearly : x ∉ earlyInputs input T) :
    predecessorPartner family input x ∈
      traceDefender family input ∩ family j := by
  have hgt := firstTime_gt_of_not_early family input hstable hcore hxatt hxearly
  have hTpred : T ≤ firstTime input x - 1 := by omega
  constructor
  · exact ⟨firstTime input x - 1, rfl⟩
  · exact core_subset_compatible family input hj
      (run_mem_core_of_stable family input hstable hcore hTpred)

theorem predecessor_lt {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) {x : ℕ}
    (hxatt : x ∈ traceAttacker family input)
    (hxearly : x ∉ earlyInputs input T) :
    predecessorPartner family input x < x := by
  have hxrange := attacker_mem_input family input hstable hcore hxatt
  have hgt := firstTime_gt_of_not_early family input hstable hcore hxatt hxearly
  have hTpred : T ≤ firstTime input x - 1 := by omega
  have hle : predecessorPartner family input x ≤ x := by
    apply run_le_of_available family input hstable hcore hTpred hxatt.1
    · intro s hs hseq
      have hmin := firstTime_min input hxrange hseq
      omega
    · intro s _ hsout
      exact hxatt.2 ⟨s, hsout⟩
  exact lt_of_le_of_ne hle (fun heq => hxatt.2
    ⟨firstTime input x - 1, heq⟩)

theorem predecessor_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j))
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    Set.InjOn (predecessorPartner family input)
      (GenLimit.PatientScope.ordinaryAttacker
        (family j) (traceAttacker family input) ∅
        (earlyInputs input T)) := by
  intro x hx y hy hxy
  simp [GenLimit.PatientScope.ordinaryAttacker] at hx hy
  have hxrange := attacker_mem_input family input hstable hcore hx.1.1
  have hyrange := attacker_mem_input family input hstable hcore hy.1.1
  have hxgt := firstTime_gt_of_not_early family input hstable hcore hx.1.1 hx.2
  have hygt := firstTime_gt_of_not_early family input hstable hcore hy.1.1 hy.2
  have hpred : firstTime input x - 1 = firstTime input y - 1 :=
    run_injective family input hxy
  have htime : firstTime input x = firstTime input y := by omega
  calc
    x = input (firstTime input x) := (firstTime_spec input hxrange).symm
    _ = input (firstTime input y) := by rw [htime]
    _ = y := firstTime_spec input hyrange

theorem half_density_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j))
    (hK : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (traceDefender family input ∩ family j) (family j) := by
  let P : GenLimit.PatientScope.PartialEnumerationCertificate :=
    { target := family j
      enumerated := informationCore family input
      enumerated_subset_target := core_subset_compatible family input hj
      attacker := traceAttacker family input
      defender := traceDefender family input
      output := run family input
      output_range := rfl
      output_injective := run_injective family input
      validFrom := T
      eventual_target := fun t ht => core_subset_compatible family input hj
        (run_mem_core_of_stable family input hstable hcore ht)
      enumerated_covered := by
        intro x hx
        by_cases hr : x ∈ Set.range (run family input)
        · exact Or.inr hr
        · exact Or.inl ⟨hx, hr⟩
      attacker_subset_target := fun _ hx =>
        core_subset_compatible family input hj hx.1
      ownership_disjoint := by
        rw [Set.disjoint_left]
        exact fun _ hxA hxD => hxA.2 hxD
      earlyAttacker := earlyInputs input T
      switchLoss := ∅
      switchLoss_subset := by simp
      partner := predecessorPartner family input
      partner_mem := by
        intro x hx
        simp [GenLimit.PatientScope.ordinaryAttacker] at hx
        exact predecessor_mem family input hstable hcore hj hx.1.1 hx.2
      partner_lt := by
        intro x hx
        simp [GenLimit.PatientScope.ordinaryAttacker] at hx
        exact predecessor_lt family input hstable hcore hx.1.1 hx.2
      partner_injective := predecessor_injective family input hj hstable hcore
      switchBudget := fun _ => 0
      switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset] }
  have h := P.theorem_3_17 hK (by
    intro n
    change GenLimit.PatientScope.prefixCount (∅ : Set ℕ) n ≤ _
    simp [GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset])
  exact h


theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  let ar : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let br : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have har0 : ∀ n, 0 ≤ ar n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbr1 : ∀ n, br n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [br, hn]
    · dsimp [br]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  have hpoint : ∀ n, ar n ≤ br n := by
    intro n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
    · exact_mod_cast Nat.zero_le (GenLimit.PatientScope.prefixCount K n)
  exact liminf_le_liminf (Eventually.of_forall hpoint)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall har0))
    (isCoboundedUnder_ge_of_le atTop hbr1)

theorem range_run_subset_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range (run family input) ⊆ GenLimit.GeneratorFirst input (run family input) := by
  rintro x ⟨t, rfl⟩
  exact ⟨t, rfl, (run_avoids family input t).1⟩

theorem novel_generates {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (run family input) (family j) := by
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨core_subset_compatible family input hj
    (run_mem_core_of_stable family input hstable hcore ht), ?_, ?_⟩
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    exact (run_avoids family input t).1 s (Nat.le_of_lt_succ hs) heq
  · exact (run_avoids family input t).2

theorem density_bounds {m : ℕ} (family : Fin m → Language)
    (hInfinite : ∀ j, (family j).Infinite) (input : Stream) {T : ℕ}
    (hstable : ∀ u, T ≤ u → ∀ j,
      prefixCompatible family (fun i : Fin (u + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input (run family input) ∩ family j)
          (family j) := by
  apply max_le
  · refine (half_density_bound family input hstable hcore hj (hInfinite j)).trans ?_
    apply relativeLowerDensity_mono
    · intro x hx
      exact ⟨range_run_subset_generatorFirst family input hx.1, hx.2⟩
    · exact Set.inter_subset_right
  · apply relativeLowerDensity_mono
    · intro x hx
      have hrun := core_diff_range_subset_run family input hstable hcore hx
      exact ⟨range_run_subset_generatorFirst family input hrun,
        core_subset_compatible family input hj hx.1⟩
    · exact Set.inter_subset_right


end

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hInfinite
  refine ⟨Stage3Case017Proof.greedyGenerator family, ?_⟩
  intro input hInjective hPartial hcore
  obtain ⟨T, hstable⟩ :=
    Stage3Case017Proof.eventually_prefixCompatible family input
  refine ⟨Stage3Case017Proof.run family input,
    Stage3Case017Proof.run_follows family input, ?_⟩
  intro j hj
  exact ⟨Stage3Case017Proof.novel_generates family input hstable hcore hj,
    Stage3Case017Proof.density_bounds family hInfinite input hstable hcore hj⟩
