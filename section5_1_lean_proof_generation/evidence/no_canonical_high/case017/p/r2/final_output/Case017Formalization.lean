import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option maxHeartbeats 800000

open Set

namespace Case017Proof

open Stage3Case017

def Available {m : ℕ} (family : Fin m → Language) (t : ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  (∀ j, (∀ i, xs i ∈ family j) → z ∈ family j) ∧
  (∀ i, xs i ≠ z) ∧ (∀ i, ys i ≠ z)

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : ∃ z, Available family t xs ys z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t
decreasing_by exact i.isLt

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

theorem greedy_available {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, Available family t xs ys z) :
    Available family t xs ys (greedyGenerator family t xs ys) := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_spec h

theorem greedy_le {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, Available family t xs ys z) {z : ℕ}
    (hz : Available family t xs ys z) :
    greedyGenerator family t xs ys ≤ z := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_min' h hz

def Active {m : ℕ} (family : Fin m → Language) (input : Stream)
    (t : ℕ) (j : Fin m) : Prop :=
  ∀ i : Fin (t + 1), input i ∈ family j

theorem eventually_active_iff_compatible {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      Active family input t j ↔ GenLimit.Generic.StreamIn input (family j) := by
  classical
  have one : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      (Active family input t j ↔ GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hj : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, fun t _ => ⟨fun _ => hj, fun _ i => ?_⟩⟩
      exact hj ⟨i, rfl⟩
    · rw [GenLimit.Generic.StreamIn, Set.not_subset] at hj
      obtain ⟨z, ⟨n, heq⟩, hn⟩ := hj
      refine ⟨n, fun t hnt => ⟨?_, ?_⟩⟩
      intro ha
      exact (hn (heq ▸ ha ⟨n, Nat.lt_succ_of_le hnt⟩)).elim
      intro hs
      exact (hn (hs ⟨n, heq⟩)).elim
  choose bound hbound using one
  refine ⟨Finset.univ.sup bound, fun t ht j => hbound j t ?_⟩
  exact (Finset.le_sup (Finset.mem_univ j)).trans ht

theorem available_of_stable {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (t T : ℕ) (hT : T ≤ t)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    ∃ z, Available family t (fun i => input i) (fun i => output i) z := by
  classical
  let used : Finset ℕ :=
    (Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
      (Finset.univ.image (fun i : Fin t => output i))
  obtain ⟨z, hzcore, hzused⟩ := hcore.exists_not_mem_finset used
  refine ⟨z, ?_, ?_, ?_⟩
  · intro j hj
    exact hzcore j ((hstable t hT j).mp hj)
  · intro i hi
    apply hzused
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  · intro i hi
    apply hzused
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)

theorem trajectory_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t T : ℕ) (hT : T ≤ t)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    Available family t (fun i => input i)
      (fun i => trajectory (greedyGenerator family) input i)
      (trajectory (greedyGenerator family) input t) := by
  rw [trajectory]
  apply greedy_available
  exact available_of_stable family input _ t T hT hstable hcore

theorem tail_output_in_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t T : ℕ) (hT : T ≤ t)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    trajectory (greedyGenerator family) input t ∈ informationCore family input := by
  intro j hj
  exact (trajectory_available family input t T hT hstable hcore).1 j
    ((hstable t hT j).mpr hj)

theorem core_not_presented_eventually_output {m : ℕ}
    (family : Fin m → Language) (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hzinput : z ∉ Set.range input) :
    ∃ t, trajectory (greedyGenerator family) input t = z := by
  classical
  by_contra hzout
  push_neg at hzout
  let out := trajectory (greedyGenerator family) input
  have zavail : ∀ t, T ≤ t →
      Available family t (fun i => input i) (fun i => out i) z := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      exact hzcore j ((hstable t ht j).mp hj)
    · intro i hi
      exact hzinput ⟨i, hi⟩
    · intro i hi
      exact hzout i hi
  have out_le : ∀ t, T ≤ t → out t ≤ z := by
    intro t ht
    change trajectory (greedyGenerator family) input t ≤ z
    rw [trajectory]
    apply greedy_le
    · exact ⟨z, zavail t ht⟩
    · exact zavail t ht
  have out_ne : ∀ {s t}, T ≤ t → s < t → out s ≠ out t := by
    intro s t ht hst
    exact (trajectory_available family input t T ht hstable hcore).2.2
      ⟨s, hst⟩
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨out (T + i), Nat.lt_succ_of_le (out_le _ (Nat.le_add_right T i))⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · exact out_ne (Nat.le_add_right T j) (Nat.add_lt_add_left hijlt T)
        (Fin.ext_iff.mp hij)
    · exact out_ne (Nat.le_add_right T i) (Nat.add_lt_add_left hjilt T)
        (Fin.ext_iff.mp hij).symm
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

theorem firstInput_spec (input : Stream) {z : ℕ} (h : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  rw [Set.mem_range] at h
  simp only [firstInput, dif_pos h]
  exact Nat.find_spec h

theorem firstInput_min (input : Stream) {z : ℕ} (h : z ∈ Set.range input)
    {t : ℕ} (ht : input t = z) : firstInput input z ≤ t := by
  classical
  rw [Set.mem_range] at h
  simp only [firstInput, dif_pos h]
  exact Nat.find_min' h ht

theorem core_not_generatorFirst_is_presented {m : ℕ}
    (family : Fin m → Language) (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hzD : z ∉ GenLimit.GeneratorFirst input
      (trajectory (greedyGenerator family) input)) :
    z ∈ Set.range input := by
  by_contra hzinput
  obtain ⟨t, ht⟩ := core_not_presented_eventually_output family input T
    hstable hcore hzcore hzinput
  apply hzD
  refine ⟨t, ht, ?_⟩
  intro s hs his
  exact hzinput ⟨s, his⟩

theorem no_output_before_first_input_of_not_generatorFirst
    (input output : Stream) {z : ℕ}
    (hzrange : z ∈ Set.range input)
    (hzD : z ∉ GenLimit.GeneratorFirst input output) {s : ℕ}
    (hs : s < firstInput input z) : output s ≠ z := by
  intro hout
  apply hzD
  refine ⟨s, hout, ?_⟩
  intro u hu hin
  have hmin := firstInput_min input hzrange hin
  omega

theorem tail_output_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream) (T t : ℕ) (ht : T ≤ t)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    trajectory (greedyGenerator family) input t ∈
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hs
  exact (trajectory_available family input t T ht hstable hcore).2.1
    ⟨s, Nat.lt_succ_iff.mpr hs⟩

noncomputable def LosingCorePrefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact (GenLimit.PatientScope.prefixFinset (informationCore family input) n).filter
    (fun z => z ∉ GenLimit.GeneratorFirst input
      (trajectory (greedyGenerator family) input))

theorem mem_prefixFinset_iff (S : Set ℕ) (n z : ℕ) :
    z ∈ GenLimit.PatientScope.prefixFinset S n ↔ z < n ∧ z ∈ S := by
  classical
  simp [GenLimit.PatientScope.prefixFinset]

noncomputable def WinningCorePrefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact (GenLimit.PatientScope.prefixFinset (informationCore family input) n).filter
    (fun z => z ∈ GenLimit.GeneratorFirst input
      (trajectory (greedyGenerator family) input))

noncomputable def EarlyLosses {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T n : ℕ) : Finset ℕ := by
  classical
  exact (LosingCorePrefix family input n).filter (fun z => firstInput input z < T)

noncomputable def GoodLosses {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T n : ℕ) : Finset ℕ := by
  classical
  let out := trajectory (greedyGenerator family) input
  exact (LosingCorePrefix family input n).filter
    (fun z => T ≤ firstInput input z ∧ out (firstInput input z) < n)

noncomputable def BadLosses {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T n : ℕ) : Finset ℕ := by
  classical
  let out := trajectory (greedyGenerator family) input
  exact (LosingCorePrefix family input n).filter
    (fun z => T ≤ firstInput input z ∧ n ≤ out (firstInput input z))

theorem losingCorePrefix_covered {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T n : ℕ) :
    LosingCorePrefix family input n ⊆
      EarlyLosses family input T n ∪ GoodLosses family input T n ∪
        BadLosses family input T n := by
  classical
  intro z hz
  by_cases hearly : firstInput input z < T
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hz, hearly⟩))
  · by_cases hgood : trajectory (greedyGenerator family) input
        (firstInput input z) < n
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hz, Nat.le_of_not_gt hearly, hgood⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hz, Nat.le_of_not_gt hearly,
          Nat.le_of_not_gt hgood⟩)

theorem earlyLosses_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T n : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    (EarlyLosses family input T n).card ≤ T := by
  classical
  have hcard := Finset.card_le_card_of_injOn (s := EarlyLosses family input T n)
    (t := Finset.range T) (firstInput input) (by
      intro z hz
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2) (by
      intro a ha b hb hab
      have haL := (Finset.mem_filter.mp ha).1
      have hbL := (Finset.mem_filter.mp hb).1
      have har := core_not_generatorFirst_is_presented family input T hstable hcore
        (mem_prefixFinset_iff _ _ _ |>.mp (Finset.mem_filter.mp haL).1).2
        (Finset.mem_filter.mp haL).2
      have hbr := core_not_generatorFirst_is_presented family input T hstable hcore
        (mem_prefixFinset_iff _ _ _ |>.mp (Finset.mem_filter.mp hbL).1).2
        (Finset.mem_filter.mp hbL).2
      calc
        a = input (firstInput input a) := (firstInput_spec input har).symm
        _ = input (firstInput input b) := by rw [hab]
        _ = b := firstInput_spec input hbr)
  simpa using hcard
  /-
  · intro z hz
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2
  · intro a ha b hb hab
    have haL := (Finset.mem_filter.mp ha).1
    have hbL := (Finset.mem_filter.mp hb).1
    have har := core_not_generatorFirst_is_presented family input T hstable hcore
      (Finset.mem_filter.mp haL).1.1 (Finset.mem_filter.mp haL).2
    have hbr := core_not_generatorFirst_is_presented family input T hstable hcore
      (Finset.mem_filter.mp hbL).1.1 (Finset.mem_filter.mp hbL).2
    calc
      a = input (firstInput input a) := (firstInput_spec input har).symm
      _ = input (firstInput input b) := by rw [hab]
      _ = b := firstInput_spec input hbr
  -/

theorem goodLosses_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T n : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    (GoodLosses family input T n).card ≤ (WinningCorePrefix family input n).card := by
  classical
  let out := trajectory (greedyGenerator family) input
  apply Finset.card_le_card_of_injOn (fun z => out (firstInput input z))
  · intro z hz
    have hzG := Finset.mem_filter.mp hz
    have hzL := hzG.1
    have htime := hzG.2.1
    have hlt := hzG.2.2
    apply Finset.mem_filter.mpr
    refine ⟨?_, tail_output_generatorFirst family input T _ htime hstable hcore⟩
    rw [GenLimit.PatientScope.prefixFinset]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, tail_output_in_core family input _ T htime hstable hcore⟩
  · intro a ha b hb hab
    have haL := (Finset.mem_filter.mp ha).1
    have hbL := (Finset.mem_filter.mp hb).1
    have har := core_not_generatorFirst_is_presented family input T hstable hcore
      (mem_prefixFinset_iff _ _ _ |>.mp (Finset.mem_filter.mp haL).1).2
      (Finset.mem_filter.mp haL).2
    have hbr := core_not_generatorFirst_is_presented family input T hstable hcore
      (mem_prefixFinset_iff _ _ _ |>.mp (Finset.mem_filter.mp hbL).1).2
      (Finset.mem_filter.mp hbL).2
    have hat := (Finset.mem_filter.mp ha).2.1
    have hbt := (Finset.mem_filter.mp hb).2.1
    by_contra habz
    have htimes : firstInput input a ≠ firstInput input b := by
      intro heq
      apply habz
      calc
        a = input (firstInput input a) := (firstInput_spec input har).symm
        _ = input (firstInput input b) := by rw [heq]
        _ = b := firstInput_spec input hbr
    rcases lt_or_gt_of_ne htimes with hlt | hgt
    · exact (trajectory_available family input (firstInput input b) T hbt hstable hcore).2.2
        ⟨firstInput input a, hlt⟩ hab
    · exact (trajectory_available family input (firstInput input a) T hat hstable hcore).2.2
        ⟨firstInput input b, hgt⟩ hab.symm

theorem badLosses_card_le_one {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T n : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    (BadLosses family input T n).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  have haF := Finset.mem_filter.mp ha
  have hbF := Finset.mem_filter.mp hb
  have haL := Finset.mem_filter.mp haF.1
  have hbL := Finset.mem_filter.mp hbF.1
  have haP := (mem_prefixFinset_iff _ _ _).mp haL.1
  have hbP := (mem_prefixFinset_iff _ _ _).mp hbL.1
  have har := core_not_generatorFirst_is_presented family input T hstable hcore
    haP.2 haL.2
  have hbr := core_not_generatorFirst_is_presented family input T hstable hcore
    hbP.2 hbL.2
  let out := trajectory (greedyGenerator family) input
  by_contra hab
  have htne : firstInput input a ≠ firstInput input b := by
    intro heq
    apply hab
    calc
      a = input (firstInput input a) := (firstInput_spec input har).symm
      _ = input (firstInput input b) := by rw [heq]
      _ = b := firstInput_spec input hbr
  rcases lt_or_gt_of_ne htne with hlt | hgt
  · have hbavail : Available family (firstInput input a)
        (fun i => input i) (fun i => out i) b := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        exact hbP.2 j ((hstable _ haF.2.1 j).mp hj)
      · intro i hi
        have hmin := firstInput_min input hbr hi
        omega
      · intro i hi
        exact no_output_before_first_input_of_not_generatorFirst input out hbr hbL.2
          (lt_trans i.isLt hlt) hi
    have houtle : out (firstInput input a) ≤ b := by
      change trajectory (greedyGenerator family) input (firstInput input a) ≤ b
      rw [trajectory]
      apply greedy_le
      · exact ⟨b, hbavail⟩
      · exact hbavail
    dsimp only [out] at houtle
    omega
  · have haavail : Available family (firstInput input b)
        (fun i => input i) (fun i => out i) a := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        exact haP.2 j ((hstable _ hbF.2.1 j).mp hj)
      · intro i hi
        have hmin := firstInput_min input har hi
        omega
      · intro i hi
        exact no_output_before_first_input_of_not_generatorFirst input out har haL.2
          (lt_trans i.isLt hgt) hi
    have houtle : out (firstInput input b) ≤ a := by
      change trajectory (greedyGenerator family) input (firstInput input b) ≤ a
      rw [trajectory]
      apply greedy_le
      · exact ⟨a, haavail⟩
      · exact haavail
    dsimp only [out] at houtle
    omega

theorem losingCorePrefix_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T n : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    (LosingCorePrefix family input n).card ≤
      (WinningCorePrefix family input n).card + T + 1 := by
  classical
  have hcover := Finset.card_le_card
    (losingCorePrefix_covered family input T n)
  have hunion₁ := Finset.card_union_le
    (EarlyLosses family input T n ∪ GoodLosses family input T n)
    (BadLosses family input T n)
  have hunion₂ := Finset.card_union_le
    (EarlyLosses family input T n) (GoodLosses family input T n)
  have hearly := earlyLosses_card_le family input T n hstable hcore
  have hgood := goodLosses_card_le family input T n hstable hcore
  have hbad := badLosses_card_le_one family input T n hstable hcore
  omega

theorem corePrefix_card_le_twice_winning {m : ℕ}
    (family : Fin m → Language) (input : Stream) (T n : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * (WinningCorePrefix family input n).card + T + 1 := by
  classical
  have hpart0 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := GenLimit.PatientScope.prefixFinset (informationCore family input) n)
    (fun z => z ∈ GenLimit.GeneratorFirst input
      (trajectory (greedyGenerator family) input))
  have hpart : (WinningCorePrefix family input n).card +
      (LosingCorePrefix family input n).card =
      GenLimit.PatientScope.prefixCount (informationCore family input) n := by
    simpa [GenLimit.PatientScope.prefixCount, WinningCorePrefix,
      LosingCorePrefix] using hpart0
  have hloss := losingCorePrefix_card_le family input T n hstable hcore
  omega

theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro z hz
  rw [mem_prefixFinset_iff] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

theorem prefixCount_monotone (A : Set ℕ) :
    Monotone (GenLimit.PatientScope.prefixCount A) := by
  intro a b hab
  classical
  apply Finset.card_le_card
  intro z hz
  rw [mem_prefixFinset_iff] at hz ⊢
  exact ⟨lt_of_lt_of_le hz.1 hab, hz.2⟩

theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Filter.Tendsto (GenLimit.PatientScope.prefixCount K)
      Filter.atTop Filter.atTop := by
  apply (prefixCount_monotone K).tendsto_atTop_atTop
  intro q
  obtain ⟨s, hsK, hscard⟩ := hK.exists_subset_card_eq q
  let n := s.sup id + 1
  refine ⟨n, ?_⟩
  rw [GenLimit.PatientScope.prefixCount]
  have hsub : s ⊆ GenLimit.PatientScope.prefixFinset K n := by
    intro z hz
    rw [mem_prefixFinset_iff]
    refine ⟨Nat.lt_succ_of_le ?_, hsK hz⟩
    exact Finset.le_sup (f := id) hz
  rw [← hscard]
  exact Finset.card_le_card hsub

theorem natCast_div_le_one (a b : ℕ) (h : a ≤ b) :
    (a : ℝ) / (b : ℝ) ≤ 1 := by
  by_cases hb : b = 0
  · have ha : a = 0 := Nat.eq_zero_of_le_zero (hb ▸ h)
    simp [ha, hb]
  · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb))).mpr
    exact Nat.cast_le.mpr h

theorem relativeLowerDensity_mono_left {A B K : Set ℕ} (hAB : A ⊆ B)
    (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
    (hu := Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _))))
    (hv := Filter.IsCoboundedUnder.of_frequently_le
      (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => by
        exact natCast_div_le_one _ _ (prefixCount_mono hBK n)))))
  exact Filter.Eventually.of_forall (fun n =>
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (prefixCount_mono hAB n))
      (Nat.cast_nonneg _))

theorem half_relativeLowerDensity_of_count {A D K : Set ℕ}
    (hK : K.Infinite) (hAK : A ⊆ K) (hDK : D ⊆ K) (c : ℕ)
    (hcount : ∀ n, GenLimit.PatientScope.prefixCount A n ≤
      2 * GenLimit.PatientScope.prefixCount D n + c) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity D K := by
  let den : ℕ → ℝ := fun n => GenLimit.PatientScope.prefixCount K n
  let ar : ℕ → ℝ := fun n => GenLimit.PatientScope.prefixCount A n / den n
  let dr : ℕ → ℝ := fun n => GenLimit.PatientScope.prefixCount D n / den n
  let err : ℕ → ℝ := fun n => ((c : ℝ) / 2) / den n
  let halfA : ℕ → ℝ := fun n => (1 / 2 : ℝ) * ar n
  have hden : Filter.Tendsto den Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (prefixCount_tendsto_atTop hK)
  have hdenpos : ∀ᶠ n in Filter.atTop, 0 < den n := by
    filter_upwards [Filter.tendsto_atTop.1 hden 1] with n hn
    exact lt_of_lt_of_le zero_lt_one hn
  have herr : Filter.Tendsto err Filter.atTop (nhds 0) := by
    exact hden.const_div_atTop ((c : ℝ) / 2)
  have har_nonneg : ∀ n, 0 ≤ ar n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hdr_nonneg : ∀ n, 0 ≤ dr n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have har_le : ∀ n, ar n ≤ 1 := fun n => by
    exact natCast_div_le_one _ _ (prefixCount_mono hAK n)
  have hdr_le : ∀ n, dr n ≤ 1 := fun n => by
    exact natCast_div_le_one _ _ (prefixCount_mono hDK n)
  have herr_nonneg : ∀ n, 0 ≤ err n := fun n => by
    exact div_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num))
      (Nat.cast_nonneg _)
  have herr_le : ∀ n, err n ≤ (c : ℝ) / 2 := fun n => by
    by_cases hz : den n = 0
    · simp [err, hz]
      positivity
    · apply (div_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hz))).mpr
      have hdenone : 1 ≤ den n := by
        dsimp [den] at hz ⊢
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hz))
      nlinarith [show (0 : ℝ) ≤ (c : ℝ) by positivity]
  have hpoint : ∀ᶠ n in Filter.atTop, halfA n ≤ err n + dr n := by
    filter_upwards [hdenpos] with n hn
    dsimp [halfA, ar, err, dr]
    have hc : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
        2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + c := by
      exact_mod_cast hcount n
    calc
      (1 / 2 : ℝ) *
          ((GenLimit.PatientScope.prefixCount A n : ℝ) / den n) =
          ((GenLimit.PatientScope.prefixCount A n : ℝ) / 2) / den n := by ring
      _ ≤ ((GenLimit.PatientScope.prefixCount D n : ℝ) + (c : ℝ) / 2) /
          den n := (div_le_div_iff_of_pos_right hn).mpr (by linarith)
      _ = (c : ℝ) / 2 / den n +
          (GenLimit.PatientScope.prefixCount D n : ℝ) / den n := by ring
  unfold GenLimit.PatientScope.relativeLowerDensity
  have hhalf : (1 / 2 : ℝ) * Filter.liminf ar Filter.atTop ≤
      Filter.liminf halfA Filter.atTop := by
    have hm := le_liminf_mul (f := Filter.atTop)
      (u := fun _ : ℕ => (1 / 2 : ℝ)) (v := ar)
      (Filter.Eventually.of_forall (fun _ => by norm_num))
      (Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall (fun _ => le_rfl)))
      (Filter.Eventually.of_forall har_nonneg)
      (Filter.IsCoboundedUnder.of_frequently_le
        (Filter.Eventually.frequently (Filter.Eventually.of_forall har_le)))
    simpa [halfA, Filter.liminf_const] using hm
  rw [show (fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)) = ar by rfl]
  rw [show (fun n => (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)) = dr by rfl]
  have hsum_le : ∀ n, err n + dr n ≤ (c : ℝ) / 2 + 1 := fun n =>
    add_le_add (herr_le n) (hdr_le n)
  have hmono := Filter.liminf_le_liminf hpoint
    (hu := Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (fun n => mul_nonneg (by norm_num) (har_nonneg n))))
    (hv := Filter.IsCoboundedUnder.of_frequently_le
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hsum_le)))
  have hadd := liminf_add_le (f := Filter.atTop) (u := err) (v := dr)
    (Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall herr_nonneg))
    (Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall herr_le))
    (Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall hdr_nonneg))
    (Filter.IsCoboundedUnder.of_frequently_le
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hdr_le)))
  rw [herr.limsup_eq, zero_add] at hadd
  exact hhalf.trans (hmono.trans hadd)

theorem winningCorePrefix_card_le_target {m : ℕ}
    (family : Fin m → Language) (input : Stream) (n : ℕ) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    (WinningCorePrefix family input n).card ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
          family j) n := by
  classical
  rw [GenLimit.PatientScope.prefixCount]
  apply Finset.card_le_card
  intro z hz
  have hzW := Finset.mem_filter.mp hz
  have hzP := (mem_prefixFinset_iff _ _ _).mp hzW.1
  rw [mem_prefixFinset_iff]
  exact ⟨hzP.1, hzW.2, hzP.2 j hj⟩

theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j))
    (hjinf : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
          family j) (family j) := by
  apply half_relativeLowerDensity_of_count hjinf (c := T + 1)
  · intro z hz
    exact hz j hj
  · exact Set.inter_subset_right
  · intro n
    have hmain := corePrefix_card_le_twice_winning family input T n hstable hcore
    have hwin := winningCorePrefix_card_le_target family input n j hj
    omega

theorem unpresented_core_subset_generatorFirst_target {m : ℕ}
    (family : Fin m → Language) (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
        family j := by
  intro z hz
  obtain ⟨t, ht⟩ := core_not_presented_eventually_output family input T hstable
    hcore hz.1 hz.2
  refine ⟨⟨t, ht, ?_⟩, hz.1 j hj⟩
  intro s hs hin
  exact hz.2 ⟨s, hin⟩

theorem unpresented_core_density {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
          family j) (family j) := by
  apply relativeLowerDensity_mono_left
    (unpresented_core_subset_generatorFirst_target family input T hstable hcore j hj)
  exact Set.inter_subset_right

theorem greedy_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u → ∀ j,
      Active family input u j ↔ GenLimit.Generic.StreamIn input (family j))
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (greedyGenerator family) input) (family j) := by
  refine ⟨T, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · exact (tail_output_in_core family input t T ht hstable hcore) j hj
  · intro hmem
    rw [GenLimit.sample, Finset.mem_image] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    exact (trajectory_available family input t T ht hstable hcore).2.1
      ⟨s, by simpa using hs⟩ heq
  · intro s hs
    exact (trajectory_available family input t T ht hstable hcore).2.2 ⟨s, hs⟩

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Case017Proof.greedyGenerator family, ?_⟩
  intro input hinjective hpartial hcore
  obtain ⟨T, hstable⟩ := Case017Proof.eventually_active_iff_compatible family input
  let output := Case017Proof.trajectory (Case017Proof.greedyGenerator family) input
  refine ⟨output, ?_, ?_⟩
  · simpa [output] using Case017Proof.trajectory_follows
      (Case017Proof.greedyGenerator family) input
  · intro j hj
    constructor
    · simpa [output] using Case017Proof.greedy_novel family input T hstable hcore j hj
    · apply max_le
      · simpa [output] using Case017Proof.half_core_density family input T hstable
          hcore j hj (hfamily j)
      · simpa [output] using Case017Proof.unpresented_core_density family input T
          hstable hcore j hj
