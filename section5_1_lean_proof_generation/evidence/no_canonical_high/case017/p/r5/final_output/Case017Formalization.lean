import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Case017Proof

open Stage3Case017

def ConsistentAt {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) (j : Fin m) : Prop :=
  ∀ s, s ≤ t → input s ∈ family j

def ApproxCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) : Language :=
  {z | ∀ j, ConsistentAt family input t j → z ∈ family j}

def Available {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  (∀ j, (∀ s : Fin (t + 1), xs s ∈ family j) → z ∈ family j) ∧
    (∀ s, xs s ≠ z) ∧ ∀ s, ys s ≠ z

noncomputable def greedyGenerator {m : ℕ}
    (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t xs ys => if h : ∃ z, Available family t xs ys z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t => t

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

theorem finite_stabilization {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      (ConsistentAt family input t j ↔
        GenLimit.Generic.StreamIn input (family j)) := by
  classical
  have hj : ∀ j : Fin m, ∃ T : ℕ, ∀ t, T ≤ t →
      (ConsistentAt family input t j ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hstream : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, ?_⟩
      intro t
      intro ht
      constructor
      · intro h
        exact hstream
      · intro h s hs
        exact h ⟨s, rfl⟩
    · have hstream' : ∃ s, input s ∉ family j := by
        simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using hstream
      obtain ⟨s, hnot⟩ := hstream'
      refine ⟨s, ?_⟩
      intro t
      intro hst
      constructor
      · intro h
        exact False.elim (hnot (h s hst))
      · intro h
        exact False.elim (hstream h)
  choose bound hbound using hj
  let T := ∑ j : Fin m, bound j
  refine ⟨T, ?_⟩
  intro t hT j
  exact hbound j t (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)) hT)

theorem approxCore_eq_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream) {T t : ℕ}
    (hstab : ∀ t, T ≤ t → ∀ j,
      (ConsistentAt family input t j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (ht : T ≤ t) :
    ApproxCore family input t = informationCore family input := by
  ext z
  simp only [ApproxCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((hstab t ht j).2 hj)
  · intro hz j hj
    exact hz j ((hstab t ht j).1 hj)


theorem available_exists {m : ℕ} (family : Fin m → Language)
    (input output : Stream) {T t : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (ht : T ≤ t) (hinf : (informationCore family input).Infinite) :
    ∃ z, Available family t (fun i => input i) (fun i => output i) z := by
  classical
  let used : Finset ℕ :=
    (Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
      (Finset.univ.image (fun i : Fin t => output i))
  obtain ⟨z, hzcore, hzused⟩ := hinf.exists_not_mem_finset used
  refine ⟨z, ?_, ?_, ?_⟩
  · intro j hj
    exact hzcore j ((hstab t ht j).1 (by
      intro s hs
      exact hj ⟨s, Nat.lt_succ_iff.mpr hs⟩))
  · intro s hEq
    apply hzused
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hEq⟩
  · intro s hEq
    apply hzused
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hEq⟩

theorem greedyGenerator_spec {m : ℕ} (family : Fin m → Language)
    {t : ℕ} {xs : Fin (t + 1) → ℕ} {ys : Fin t → ℕ}
    (h : ∃ z, Available family t xs ys z) :
    Available family t xs ys (greedyGenerator family t xs ys) := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_spec h

theorem greedyGenerator_le {m : ℕ} (family : Fin m → Language)
    {t : ℕ} {xs : Fin (t + 1) → ℕ} {ys : Fin t → ℕ} {z : ℕ}
    (hz : Available family t xs ys z) :
    greedyGenerator family t xs ys ≤ z := by
  classical
  let h : ∃ z, Available family t xs ys z := ⟨z, hz⟩
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_min' h hz

theorem trajectory_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) (ht : T ≤ t) :
    Available family t (fun i => input i)
      (fun i => trajectory (greedyGenerator family) input i)
      (trajectory (greedyGenerator family) input t) := by
  rw [trajectory]
  exact greedyGenerator_spec family
    (available_exists family input (trajectory (greedyGenerator family) input)
      hstab ht hinf)



theorem trajectory_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (greedyGenerator family) input) (family j) := by
  refine ⟨T, ?_⟩
  intro t ht
  have hspec := trajectory_spec family input hstab hinf ht
  refine ⟨hspec.1 j ?_, ?_, ?_⟩
  · intro s
    exact hj ⟨s, rfl⟩
  · intro hmem
    rw [GenLimit.sample] at hmem
    obtain ⟨s, hs, hEq⟩ := Finset.mem_image.mp hmem
    exact hspec.2.1 ⟨s, Finset.mem_range.mp hs⟩ hEq
  · intro s hst hEq
    exact hspec.2.2 ⟨s, hst⟩ hEq

theorem tail_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) :
    Function.Injective
      (fun n => trajectory (greedyGenerator family) input (T + n)) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · have hspec := trajectory_spec family input hstab hinf (show T ≤ T + b by omega)
    exact hspec.2.2 ⟨T + a, by omega⟩ hab
  · have hspec := trajectory_spec family input hstab hinf (show T ≤ T + a by omega)
    exact hspec.2.2 ⟨T + b, by omega⟩ hab.symm

theorem unseen_core_eventually_output {m : ℕ}
    (family : Fin m → Language) (input : Stream) {T : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hzinput : z ∉ Set.range input) :
    z ∈ Set.range (trajectory (greedyGenerator family) input) := by
  classical
  by_contra hzoutput
  have hle : ∀ n,
      trajectory (greedyGenerator family) input (T + n) ≤ z := by
    intro n
    rw [trajectory]
    apply greedyGenerator_le family
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      exact hzcore j ((hstab (T + n) (by omega) j).1 (by
        intro s hs
        exact hj ⟨s, Nat.lt_succ_iff.mpr hs⟩))
    · intro s hEq
      exact hzinput ⟨s, hEq⟩
    · intro s hEq
      exact hzoutput ⟨s, hEq⟩
  have hrange_inf :
      (Set.range (fun n => trajectory (greedyGenerator family) input (T + n))).Infinite :=
    Set.infinite_range_of_injective (tail_injective family input hstab hinf)
  have hrange_sub :
      Set.range (fun n => trajectory (greedyGenerator family) input (T + n)) ⊆
        Set.Iic z := by
    rintro _ ⟨n, rfl⟩
    exact hle n
  exact hrange_inf ((Set.finite_Iic z).subset hrange_sub)

theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream) {T : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
        family j := by
  intro z hz
  obtain ⟨t, ht⟩ := unseen_core_eventually_output family input hstab hinf hz.1 hz.2
  refine ⟨?_, hz.1 j hj⟩
  refine ⟨t, ht, ?_⟩
  intro s hs hEq
  exact hz.2 ⟨s, hEq⟩




noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

theorem firstInput_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  obtain ⟨t, ht⟩ := hz
  let h : ∃ t, input t = z := ⟨t, ht⟩
  simp only [firstInput, dif_pos h]
  exact Nat.find_spec h

theorem firstInput_min (input : Stream) {z t : ℕ} (ht : input t = z) :
    firstInput input z ≤ t := by
  classical
  let h : ∃ s, input s = z := ⟨t, ht⟩
  simp only [firstInput, dif_pos h]
  exact Nat.find_min' h ht

noncomputable def partner (input output : Stream) (z : ℕ) : ℕ :=
  output (firstInput input z - 1)

theorem trajectory_injective_from {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T s t : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite)
    (hs : T ≤ s) (ht : T ≤ t)
    (heq : trajectory (greedyGenerator family) input s =
      trajectory (greedyGenerator family) input t) : s = t := by
  have htail := tail_injective family input hstab hinf
  have hsub : s - T = t - T := by
    apply htail
    simpa [Nat.add_sub_of_le hs, Nat.add_sub_of_le ht] using heq
  omega

theorem partner_of_late_loser {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hznotD : z ∉ GenLimit.GeneratorFirst input
      (trajectory (greedyGenerator family) input) ∩ family j)
    (hzlate : z ∉ (Finset.range (T + 1)).image input) :
    partner input (trajectory (greedyGenerator family) input) z ∈
        GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) ∩ family j ∧
      partner input (trajectory (greedyGenerator family) input) z ≤ z ∧
      T < firstInput input z := by
  classical
  have hzrange : z ∈ Set.range input := by
    by_contra hzinput
    exact hznotD (core_diff_range_subset_generatorFirst family input hstab hinf hj
      ⟨hzcore, hzinput⟩)
  let t := firstInput input z
  have htval : input t = z := firstInput_spec input hzrange
  have hTt : T < t := by
    by_contra hnot
    have htmem : t ∈ Finset.range (T + 1) := Finset.mem_range.mpr (by omega)
    exact hzlate (Finset.mem_image.mpr ⟨t, htmem, htval⟩)
  have hinput_before : ∀ s, s < t → input s ≠ z := by
    intro s hs hEq
    have := firstInput_min input hEq
    change t ≤ s at this
    omega
  have houtput_before : ∀ s, s < t →
      trajectory (greedyGenerator family) input s ≠ z := by
    intro s hs hEq
    apply hznotD
    refine ⟨⟨s, hEq, ?_⟩, hzcore j hj⟩
    intro u hu
    exact hinput_before u (lt_of_le_of_lt hu hs)
  have hzavail : Available family (t - 1)
      (fun i => input i)
      (fun i => trajectory (greedyGenerator family) input i) z := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact hzcore k ((hstab (t - 1) (by omega) k).1 (by
        intro s hs
        exact hk ⟨s, Nat.lt_succ_iff.mpr hs⟩))
    · intro s hEq
      exact hinput_before s (by omega) hEq
    · intro s hEq
      exact houtput_before s (by omega) hEq
  have hle : partner input (trajectory (greedyGenerator family) input) z ≤ z := by
    rw [partner, trajectory]
    exact greedyGenerator_le family hzavail
  have hspec := trajectory_spec family input hstab hinf (show T ≤ t - 1 by omega)
  refine ⟨?_, hle, hTt⟩
  refine ⟨⟨t - 1, rfl, ?_⟩, ?_⟩
  · intro s hs
    exact hspec.2.1 ⟨s, by omega⟩
  · exact hspec.1 j (by
      intro s
      exact hj ⟨s, rfl⟩)

theorem partner_injective_on_late_losers {m : ℕ}
    (family : Fin m → Language) (input : Stream) {T : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    Set.InjOn (partner input (trajectory (greedyGenerator family) input))
      {z | z ∈ informationCore family input ∧
        z ∉ GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) ∩ family j ∧
        z ∉ (Finset.range (T + 1)).image input} := by
  intro a ha b hb hab
  have haP := partner_of_late_loser family input hstab hinf hj ha.1 ha.2.1 ha.2.2
  have hbP := partner_of_late_loser family input hstab hinf hj hb.1 hb.2.1 hb.2.2
  have htime : firstInput input a - 1 = firstInput input b - 1 :=
    trajectory_injective_from family input hstab hinf (by omega) (by omega) hab
  have harange : a ∈ Set.range input := by
    by_contra h
    exact ha.2.1 (core_diff_range_subset_generatorFirst family input hstab hinf hj ⟨ha.1, h⟩)
  have hbrange : b ∈ Set.range input := by
    by_contra h
    exact hb.2.1 (core_diff_range_subset_generatorFirst family input hstab hinf hj ⟨hb.1, h⟩)
  have haT : T < firstInput input a := by omega
  have hbT : T < firstInput input b := by omega
  have ht : firstInput input a = firstInput input b := by omega
  calc
    a = input (firstInput input a) := (firstInput_spec input harange).symm
    _ = input (firstInput input b) := by rw [ht]
    _ = b := firstInput_spec input hbrange



theorem core_prefix_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) ∩ family j) n +
      ((Finset.range (T + 1)).image input).card := by
  classical
  let core := informationCore family input
  let D := GenLimit.GeneratorFirst input
    (trajectory (greedyGenerator family) input) ∩ family j
  let early := (Finset.range (T + 1)).image input
  let C := GenLimit.PatientScope.prefixFinset core n
  let DF := GenLimit.PatientScope.prefixFinset D n
  let A := C \ (DF ∪ early)
  have hmaps : Set.MapsTo
      (partner input (trajectory (greedyGenerator family) input))
      (A : Set ℕ) (DF : Set ℕ) := by
    intro z hz
    have hz' : z ∈ C ∧ z ∉ DF ∧ z ∉ early := by
      simpa [A] using hz
    have hzC : z < n ∧ z ∈ core := by
      simpa [C, GenLimit.PatientScope.prefixFinset] using hz'.1
    have hznotD : z ∉ D := by
      intro hzD
      apply hz'.2.1
      simp [DF, GenLimit.PatientScope.prefixFinset, hzC.1, hzD]
    have hP := partner_of_late_loser family input hstab hinf hj
      (show z ∈ informationCore family input from hzC.2) hznotD hz'.2.2
    have hlt : partner input (trajectory (greedyGenerator family) input) z < n :=
      lt_of_le_of_lt hP.2.1 hzC.1
    simpa [DF, GenLimit.PatientScope.prefixFinset, hlt, D] using hP.1
  have hinj : Set.InjOn
      (partner input (trajectory (greedyGenerator family) input)) (A : Set ℕ) := by
    apply (partner_injective_on_late_losers family input hstab hinf hj).mono
    intro z hz
    have hz' : z ∈ C ∧ z ∉ DF ∧ z ∉ early := by
      simpa [A] using hz
    have hzC : z < n ∧ z ∈ core := by
      simpa [C, GenLimit.PatientScope.prefixFinset] using hz'.1
    refine ⟨hzC.2, ?_, hz'.2.2⟩
    intro hzD
    apply hz'.2.1
    have hzDinD : z ∈ D := by simpa [D] using hzD
    simp [DF, GenLimit.PatientScope.prefixFinset, hzC.1, hzDinD]
  have hcardA : A.card ≤ DF.card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hsubset : C ⊆ (DF ∪ early) ∪ A := by
    intro z hz
    by_cases hDF : z ∈ DF
    · simp [hDF]
    by_cases hearly : z ∈ early
    · simp [hearly]
    · simp [A, hz, hDF, hearly]
  have hcardC : C.card ≤ 2 * DF.card + early.card := by
    calc
      C.card ≤ ((DF ∪ early) ∪ A).card := Finset.card_le_card hsubset
      _ ≤ (DF ∪ early).card + A.card := Finset.card_union_le _ _
      _ ≤ (DF.card + early.card) + A.card :=
        Nat.add_le_add_right (Finset.card_union_le DF early) A.card
      _ ≤ 2 * DF.card + early.card := by omega
  simpa [GenLimit.PatientScope.prefixCount, C, DF, core, D, early] using hcardC


theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

theorem ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

theorem ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  have hcount := prefixCount_mono hAK n
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · have ha : GenLimit.PatientScope.prefixCount A n = 0 := by omega
    simp [hzero, ha]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast hcount

theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · filter_upwards [] with n
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast prefixCount_mono hAB n) (by positivity)
  · exact isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (ratio_nonneg A K))
  · exact isCoboundedUnder_ge_of_le atTop (ratio_le_one hBK)

theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨s, hsK, hscard⟩ := hK.exists_subset_card_eq b
  obtain ⟨M, hM⟩ := s.bddAbove
  refine ⟨M + 1, ?_⟩
  intro n hn
  rw [← hscard]
  apply Finset.card_le_card
  intro z hzs
  simp only [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
  exact ⟨(hM hzs).trans_lt (Nat.lt_of_succ_le hn), hsK hzs⟩

theorem const_div_prefixCount_tendsto_zero (K : Set ℕ) (hK : K.Infinite)
    (c : ℕ) :
    Tendsto (fun n => (c : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_natCast_atTop_atTop.comp (prefixCount_tendsto_atTop hK)



theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstab : ∀ u, T ≤ u → ∀ j,
      (ConsistentAt family input u j ↔
        GenLimit.Generic.StreamIn input (family j)))
    (hinf : (informationCore family input).Infinite) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j))
    (hKinf : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input
          (trajectory (greedyGenerator family) input) ∩ family j) (family j) := by
  classical
  let core := informationCore family input
  let D := GenLimit.GeneratorFirst input
    (trajectory (greedyGenerator family) input) ∩ family j
  let c := ((Finset.range (T + 1)).image input).card
  let coreRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount core n : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  let dRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  let err : ℕ → ℝ := fun n =>
    ((c : ℝ) / 2) /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
  have hcoreK : core ⊆ family j := by
    intro z hz
    exact hz j hj
  have hDK : D ⊆ family j := by
    intro z hz
    exact hz.2
  have hcore_nonneg : ∀ n, 0 ≤ coreRatio n := by
    intro n
    exact ratio_nonneg core (family j) n
  have hcore_one : ∀ n, coreRatio n ≤ 1 := ratio_le_one hcoreK
  have hd_nonneg : ∀ n, 0 ≤ dRatio n := by
    intro n
    exact ratio_nonneg D (family j) n
  have hd_one : ∀ n, dRatio n ≤ 1 := ratio_le_one hDK
  have herr_nonneg : ∀ n, 0 ≤ err n := by
    intro n
    dsimp [err]
    positivity
  have herr_le : ∀ n, err n ≤ (c : ℝ) := by
    intro n
    dsimp [err]
    by_cases hk : GenLimit.PatientScope.prefixCount (family j) n = 0
    · simp [hk]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount (family j) n := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hden : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount (family j) n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hc : (0 : ℝ) ≤ c := by positivity
      calc
        ((c : ℝ) / 2) / (GenLimit.PatientScope.prefixCount (family j) n : ℝ)
            ≤ (c : ℝ) / 2 := (div_le_iff₀ hkpos).2 (by nlinarith)
        _ ≤ (c : ℝ) := by nlinarith
  have herr_tendsto : Tendsto err atTop (𝓝 0) := by
    have h := (const_div_prefixCount_tendsto_zero (family j) hKinf c).const_mul (1 / 2 : ℝ)
    simpa [err, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hpoint : ∀ n, (1 / 2 : ℝ) * coreRatio n ≤ err n + dRatio n := by
    intro n
    have hcount := core_prefix_bound family input hstab hinf hj n
    by_cases hk : GenLimit.PatientScope.prefixCount (family j) n = 0
    · have hc0 : GenLimit.PatientScope.prefixCount core n = 0 := by
        have := prefixCount_mono hcoreK n
        omega
      have hd0 : GenLimit.PatientScope.prefixCount D n = 0 := by
        have := prefixCount_mono hDK n
        omega
      simp [coreRatio, dRatio, err, hk, hc0, hd0]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount (family j) n := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hcast : (GenLimit.PatientScope.prefixCount core n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + c := by
        exact_mod_cast hcount
      have hdiv := div_le_div_of_nonneg_right hcast hkpos.le
      dsimp [coreRatio, dRatio, err]
      rw [add_div, add_comm] at hdiv
      calc
        (1 / 2 : ℝ) *
            ((GenLimit.PatientScope.prefixCount core n : ℝ) /
              (GenLimit.PatientScope.prefixCount (family j) n : ℝ))
            ≤ (1 / 2 : ℝ) *
              (((c : ℝ) / (GenLimit.PatientScope.prefixCount (family j) n : ℝ)) +
                2 * (GenLimit.PatientScope.prefixCount D n : ℝ) /
                  (GenLimit.PatientScope.prefixCount (family j) n : ℝ)) :=
              mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = ((c : ℝ) / 2) /
              (GenLimit.PatientScope.prefixCount (family j) n : ℝ) +
            (GenLimit.PatientScope.prefixCount D n : ℝ) /
              (GenLimit.PatientScope.prefixCount (family j) n : ℝ) := by ring
  have hscale : (1 / 2 : ℝ) * liminf coreRatio atTop =
      liminf (fun n => (1 / 2 : ℝ) * coreRatio n) atTop := by
    have hmono : Monotone (fun x : ℝ => (1 / 2 : ℝ) * x) := by
      intro a b hab
      exact mul_le_mul_of_nonneg_left hab (by norm_num)
    have hmap := hmono.map_liminf_of_continuousAt coreRatio
      (continuous_mul_left (1 / 2 : ℝ)).continuousAt
      (isCoboundedUnder_ge_of_le atTop hcore_one)
      (isBoundedUnder_of_eventually_ge
        (Filter.Eventually.of_forall hcore_nonneg))
    simpa [Function.comp_def] using hmap
  have hlim_mono :
      liminf (fun n => (1 / 2 : ℝ) * coreRatio n) atTop ≤
        liminf (fun n => err n + dRatio n) atTop := by
    apply liminf_le_liminf
    · exact Filter.Eventually.of_forall hpoint
    · exact isBoundedUnder_of_eventually_ge
        (Filter.Eventually.of_forall (fun n => mul_nonneg (by norm_num) (hcore_nonneg n)))
    · exact isCoboundedUnder_ge_of_le atTop (fun n => by
        have := add_le_add (herr_le n) (hd_one n)
        exact this)
  have hadd : liminf (fun n => err n + dRatio n) atTop ≤ liminf dRatio atTop := by
    have h := liminf_add_le
      (isBoundedUnder_of_eventually_ge
        (Filter.Eventually.of_forall herr_nonneg))
      (isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall herr_le))
      (isBoundedUnder_of_eventually_ge
        (Filter.Eventually.of_forall hd_nonneg))
      (isCoboundedUnder_ge_of_le atTop hd_one)
    rw [herr_tendsto.limsup_eq] at h
    simpa only [Pi.add_apply, zero_add] using h
  change (1 / 2 : ℝ) * liminf coreRatio atTop ≤ liminf dRatio atTop
  rw [hscale]
  exact hlim_mono.trans hadd


end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamilyInfinite
  refine ⟨Case017Proof.greedyGenerator family, ?_⟩
  intro input hinputInjective hpartial hcoreInfinite
  obtain ⟨T, hstab⟩ := Case017Proof.finite_stabilization family input
  let output := Case017Proof.trajectory (Case017Proof.greedyGenerator family) input
  refine ⟨output, Case017Proof.trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨Case017Proof.trajectory_novel family input hstab hcoreInfinite hj, ?_⟩
  apply max_le
  · exact Case017Proof.half_core_density family input hstab hcoreInfinite hj
      (hfamilyInfinite j)
  · apply Case017Proof.relativeLowerDensity_mono
    · exact Case017Proof.core_diff_range_subset_generatorFirst
        family input hstab hcoreInfinite hj
    · intro z hz
      exact hz.2
