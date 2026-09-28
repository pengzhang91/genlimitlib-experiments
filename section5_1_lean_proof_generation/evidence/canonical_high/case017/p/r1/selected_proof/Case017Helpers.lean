import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Stage3Case017

noncomputable section

def usedAt {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image xs ∪ Finset.univ.image ys

def currentCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

def leastAvailable (S : Set ℕ) (used : Finset ℕ) : ℕ := by
  classical
  exact if h : ∃ z, z ∈ S ∧ z ∉ used then Nat.find h
    else Nat.find (Finset.exists_notMem used)

lemma leastAvailable_mem {S : Set ℕ} {used : Finset ℕ}
    (h : ∃ z, z ∈ S ∧ z ∉ used) :
    leastAvailable S used ∈ S := by
  classical
  rw [leastAvailable, dif_pos h]
  exact (Nat.find_spec h).1

lemma leastAvailable_not_mem {S : Set ℕ} {used : Finset ℕ} :
    leastAvailable S used ∉ used := by
  classical
  by_cases h : ∃ z, z ∈ S ∧ z ∉ used
  · rw [leastAvailable, dif_pos h]
    exact (Nat.find_spec h).2
  · rw [leastAvailable, dif_neg h]
    exact Nat.find_spec (Finset.exists_notMem used)

lemma leastAvailable_le {S : Set ℕ} {used : Finset ℕ} {z : ℕ}
    (hzS : z ∈ S) (hzu : z ∉ used) :
    leastAvailable S used ≤ z := by
  classical
  let h : ∃ w, w ∈ S ∧ w ∉ used := ⟨z, hzS, hzu⟩
  rw [leastAvailable, dif_pos h]
  exact Nat.find_min' h ⟨hzS, hzu⟩

def greedyGenerator {m : ℕ} (family : Fin m → Language) : OnlineGenerator :=
  fun _ xs ys => leastAvailable (currentCore family xs) (usedAt xs ys)

def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

lemma trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

lemma usedAt_input {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (i : Fin (t + 1)) : xs i ∈ usedAt xs ys := by
  simp [usedAt]

lemma usedAt_output {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (i : Fin t) : ys i ∈ usedAt xs ys := by
  simp [usedAt]

lemma trajectory_fresh_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t s : ℕ) (hs : s ≤ t) :
    trajectory (greedyGenerator family) input t ≠ input s := by
  intro hEq
  have hmem : input s ∈ usedAt (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (greedyGenerator family) input i) :=
    usedAt_input _ _ ⟨s, Nat.lt_succ_of_le hs⟩
  have hnot := leastAvailable_not_mem
    (S := currentCore family (fun i : Fin (t + 1) => input i))
    (used := usedAt (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (greedyGenerator family) input i))
  rw [trajectory, greedyGenerator] at hEq
  exact hnot (hEq ▸ hmem)

lemma trajectory_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (trajectory (greedyGenerator family) input) := by
  intro s t hEq
  rcases lt_trichotomy s t with hst | hst | hts
  · have hmem : trajectory (greedyGenerator family) input s ∈
      usedAt (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (greedyGenerator family) input i) :=
      usedAt_output _ _ ⟨s, hst⟩
    have hnot := leastAvailable_not_mem
      (S := currentCore family (fun i : Fin (t + 1) => input i))
      (used := usedAt (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (greedyGenerator family) input i))
    have heq : trajectory (greedyGenerator family) input t =
        leastAvailable (currentCore family (fun i : Fin (t + 1) => input i))
          (usedAt (fun i : Fin (t + 1) => input i)
            (fun i : Fin t => trajectory (greedyGenerator family) input i)) := by
      exact trajectory_follows (greedyGenerator family) input t
    have houtnot : trajectory (greedyGenerator family) input t ∉
        usedAt (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => trajectory (greedyGenerator family) input i) := by
      intro hm
      exact hnot (heq ▸ hm)
    exact (houtnot (hEq ▸ hmem)).elim
  · exact hst
  · have hmem : trajectory (greedyGenerator family) input t ∈
      usedAt (fun i : Fin (s + 1) => input i)
        (fun i : Fin s => trajectory (greedyGenerator family) input i) :=
      usedAt_output _ _ ⟨t, hts⟩
    have hnot := leastAvailable_not_mem
      (S := currentCore family (fun i : Fin (s + 1) => input i))
      (used := usedAt (fun i : Fin (s + 1) => input i)
        (fun i : Fin s => trajectory (greedyGenerator family) input i))
    have heq : trajectory (greedyGenerator family) input s =
        leastAvailable (currentCore family (fun i : Fin (s + 1) => input i))
          (usedAt (fun i : Fin (s + 1) => input i)
            (fun i : Fin s => trajectory (greedyGenerator family) input i)) := by
      exact trajectory_follows (greedyGenerator family) input s
    have houtnot : trajectory (greedyGenerator family) input s ∉
        usedAt (fun i : Fin (s + 1) => input i)
          (fun i : Fin s => trajectory (greedyGenerator family) input i) := by
      intro hm
      exact hnot (heq ▸ hm)
    exact (houtnot (hEq.symm ▸ hmem)).elim



lemma exists_bad_of_not_streamIn {input : Stream} {L : Language}
    (h : ¬ GenLimit.Generic.StreamIn input L) :
    ∃ t, input t ∉ L := by
  simp only [GenLimit.Generic.StreamIn, Set.range_subset_iff] at h
  push_neg at h
  exact h

def badTime {m : ℕ} (family : Fin m → Language) (input : Stream)
    (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Nat.find (exists_bad_of_not_streamIn h)

def stableTime {m : ℕ} (family : Fin m → Language) (input : Stream) : ℕ :=
  ∑ j, badTime family input j

lemma badTime_spec {m : ℕ} (family : Fin m → Language) (input : Stream)
    (j : Fin m) (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (badTime family input j) ∉ family j := by
  classical
  rw [badTime, dif_neg h]
  exact Nat.find_spec (exists_bad_of_not_streamIn h)

lemma badTime_le_stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    badTime family input j ≤ stableTime family input := by
  classical
  rw [stableTime]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

lemma prefix_compatible_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stableTime family input ≤ t) (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hp
    by_contra hj
    have hle : badTime family input j ≤ t :=
      (badTime_le_stableTime family input j).trans ht
    exact badTime_spec family input j hj
      (hp ⟨badTime family input j, Nat.lt_succ_of_le hle⟩)
  · intro hj i
    exact hj ⟨i, rfl⟩

lemma currentCore_eq_informationCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (ht : stableTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  apply forall_congr'
  intro j
  rw [prefix_compatible_iff family input ht j]

lemma core_available {m : ℕ} (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) {t : ℕ}
    (ht : stableTime family input ≤ t) :
    ∃ z, z ∈ currentCore family (fun i : Fin (t + 1) => input i) ∧
      z ∉ usedAt (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (greedyGenerator family) input i) := by
  rw [currentCore_eq_informationCore family input ht]
  exact hcore.exists_notMem_finset _

lemma trajectory_mem_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    trajectory (greedyGenerator family) input t ∈ informationCore family input := by
  have havail := core_available family input hcore ht
  have hmem := leastAvailable_mem havail
  have heq : trajectory (greedyGenerator family) input t =
      leastAvailable (currentCore family (fun i : Fin (t + 1) => input i))
        (usedAt (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => trajectory (greedyGenerator family) input i)) :=
    trajectory_follows (greedyGenerator family) input t
  rw [heq]
  rw [← currentCore_eq_informationCore family input ht]
  exact hmem

lemma informationCore_subset {m : ℕ} {family : Fin m → Language}
    {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hj

lemma greedy_novel {m : ℕ} (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (greedyGenerator family) input) (family j) := by
  refine ⟨stableTime family input, ?_⟩
  intro t ht
  refine ⟨informationCore_subset hj (trajectory_mem_core family input hcore ht), ?_, ?_⟩
  · simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro s hs hEq
    exact trajectory_fresh_input family input t s (Nat.le_of_lt_succ hs) hEq.symm
  · intro s hs
    exact (trajectory_injective family input).ne (Nat.ne_of_lt hs)

lemma output_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    trajectory (greedyGenerator family) input t ∈
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hs
  exact (trajectory_fresh_input family input t s hs).symm

lemma output_le_of_unannounced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {t z : ℕ} (ht : stableTime family input ≤ t)
    (hzcore : z ∈ informationCore family input)
    (hzin : ∀ s, s ≤ t → input s ≠ z)
    (hzout : ∀ s, s < t → trajectory (greedyGenerator family) input s ≠ z) :
    trajectory (greedyGenerator family) input t ≤ z := by
  have hzcur : z ∈ currentCore family (fun i : Fin (t + 1) => input i) := by
    rw [currentCore_eq_informationCore family input ht]
    exact hzcore
  have hzused : z ∉ usedAt (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (greedyGenerator family) input i) := by
    simp only [usedAt, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      not_or, not_exists]
    constructor
    · intro i hEq
      exact hzin i (Nat.le_of_lt_succ i.isLt) hEq
    · intro i hEq
      exact hzout i i.isLt hEq
  have hle := leastAvailable_le hzcur hzused
  have heq : trajectory (greedyGenerator family) input t =
      leastAvailable (currentCore family (fun i : Fin (t + 1) => input i))
        (usedAt (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => trajectory (greedyGenerator family) input i)) :=
    trajectory_follows (greedyGenerator family) input t
  rwa [heq]

lemma core_eventually_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ informationCore family input) :
    z ∈ Set.range input ∪ Set.range (trajectory (greedyGenerator family) input) := by
  by_contra hnot
  simp only [Set.mem_union, Set.mem_range, not_or, not_exists] at hnot
  let T := stableTime family input
  let f : ℕ → ℕ := fun k => trajectory (greedyGenerator family) input (T + k)
  have hf_inj : Function.Injective f := by
    intro a b hab
    have := trajectory_injective family input hab
    omega
  have hf_le : ∀ k, f k ≤ z := by
    intro k
    apply output_le_of_unannounced family input hcore (Nat.le_add_right T k) hz
    · intro s _
      exact hnot.1 s
    · intro s _
      exact hnot.2 s
  let image := (Finset.range (z + 2)).image f
  have hcard : image.card = z + 2 := by
    simp [image, Finset.card_image_of_injective _ hf_inj]
  have hsub : image ⊆ Finset.range (z + 1) := by
    intro y hy
    simp only [image, Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hf_le k))
  have := Finset.card_le_card hsub
  simp [hcard] at this

lemma core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) := by
  intro z hz
  have hann := core_eventually_announced family input hcore hz.1
  rcases hann with hzin | hzout
  · exact (hz.2 hzin).elim
  · obtain ⟨t, ht⟩ := hzout
    rw [← ht]
    exact output_generatorFirst family input t


def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

lemma firstInput_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  obtain ⟨t, ht⟩ := hz
  let h : ∃ s, input s = z := ⟨t, ht⟩
  rw [firstInput, dif_pos h]
  exact Nat.find_spec h

lemma firstInput_le (input : Stream) {z t : ℕ} (ht : input t = z) :
    firstInput input z ≤ t := by
  classical
  rw [firstInput, dif_pos ⟨t, ht⟩]
  exact Nat.find_min' ⟨t, ht⟩ ht

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

lemma relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply Filter.liminf_le_liminf
  · filter_upwards [] with n
    exact div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (prefixCount_mono hAB n)) (Nat.cast_nonneg _)
  · refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [] with n
    show (0 : ℝ) ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine ⟨1, ?_⟩
    intro a ha
    rw [Filter.eventually_map] at ha
    obtain ⟨n, hn⟩ := ha.exists
    have hden : (0 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := Nat.cast_nonneg _
    have hnum : (GenLimit.PatientScope.prefixCount B n : ℝ) ≤
        GenLimit.PatientScope.prefixCount K n := Nat.cast_le.mpr (prefixCount_mono hBK n)
    by_cases hzero : (GenLimit.PatientScope.prefixCount K n : ℝ) = 0
    · simp [hzero] at hn
      linarith
    · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := lt_of_le_of_ne hden (Ne.symm hzero)
      have hratio : (GenLimit.PatientScope.prefixCount B n : ℝ) /
          GenLimit.PatientScope.prefixCount K n ≤ 1 := (div_le_one hpos).2 hnum
      linarith


lemma core_prefix_count_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input) ∩
          informationCore family input) n +
        stableTime family input + 1 := by
  classical
  let I := informationCore family input
  let D := GenLimit.GeneratorFirst input (trajectory (greedyGenerator family) input)
  let P := GenLimit.PatientScope.prefixFinset I n
  let G := P.filter (fun z => z ∈ D)
  let A := P.filter (fun z => z ∉ D)
  let T := stableTime family input
  have hP : P.card = G.card + A.card := by
    dsimp [G, A]
    simpa only [Classical.not_not] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := P) (p := fun z => z ∈ D)).symm
  have hG : G.card = GenLimit.PatientScope.prefixCount (D ∩ I) n := by
    apply congrArg Finset.card
    ext z
    simp only [G, P, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range,
      Set.mem_inter_iff]
    tauto
  have hPcount : P.card = GenLimit.PatientScope.prefixCount I n := rfl
  let early := A.filter (fun z => firstInput input z < T)
  let late := A.filter (fun z => T ≤ firstInput input z)
  have hA_split : A.card = early.card + late.card := by
    dsimp [early, late]
    simpa only [not_lt] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := A) (p := fun z => firstInput input z < T)).symm
  have hA_range : ∀ z ∈ A, z ∈ Set.range input := by
    intro z hzA
    have hzP : z ∈ P := (Finset.mem_filter.mp hzA).1
    have hzI : z ∈ I := by
      change z ∈ GenLimit.PatientScope.prefixFinset I n at hzP
      exact (Finset.mem_filter.mp hzP).2
    have hznotD : z ∉ D := (Finset.mem_filter.mp hzA).2
    have hann := core_eventually_announced family input hcore hzI
    rcases hann with hzin | hzout
    · exact hzin
    · obtain ⟨t, rfl⟩ := hzout
      exact (hznotD (output_generatorFirst family input t)).elim
  have hearly : early.card ≤ T := by
    have hcard : early.card ≤ (Finset.range T).card := by
      apply Finset.card_le_card_of_injOn (s := early) (t := Finset.range T) (firstInput input)
      · intro z hz
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hz).2
      · intro x hx y hy hxy
        have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
        have hyA : y ∈ A := (Finset.mem_filter.mp hy).1
        calc
          x = input (firstInput input x) := (firstInput_spec input (hA_range x hxA)).symm
          _ = input (firstInput input y) := by rw [hxy]
          _ = y := firstInput_spec input (hA_range y hyA)
    simpa using hcard
  by_cases hlate : late.Nonempty
  · let times := late.image (firstInput input)
    have htimes : times.Nonempty := hlate.image _
    let lastTime := times.max' htimes
    have hlastTime : lastTime ∈ times := Finset.max'_mem times htimes
    obtain ⟨last, hlastLate, hlastEq⟩ := Finset.mem_image.mp hlastTime
    let ordinary := late.erase last
    have hordinary : ordinary.card + 1 = late.card := by
      exact Finset.card_erase_add_one hlastLate
    have hordinary_le : ordinary.card ≤ G.card := by
      apply Finset.card_le_card_of_injOn
        (fun z => trajectory (greedyGenerator family) input (firstInput input z))
      · intro z hzOrd
        have hzLate : z ∈ late := (Finset.mem_erase.mp hzOrd).2
        have hzA : z ∈ A := (Finset.mem_filter.mp hzLate).1
        have hzP : z ∈ P := (Finset.mem_filter.mp hzA).1
        have hzI : z ∈ I := by
          change z ∈ GenLimit.PatientScope.prefixFinset I n at hzP
          exact (Finset.mem_filter.mp hzP).2
        have hzT : T ≤ firstInput input z := (Finset.mem_filter.mp hzLate).2
        have hlastA : last ∈ A := (Finset.mem_filter.mp hlastLate).1
        have hlastP : last ∈ P := (Finset.mem_filter.mp hlastA).1
        have hlastI : last ∈ I := by
          change last ∈ GenLimit.PatientScope.prefixFinset I n at hlastP
          exact (Finset.mem_filter.mp hlastP).2
        have hlastRange := hA_range last hlastA
        have hzRange := hA_range z hzA
        have hzle : firstInput input z ≤ lastTime := by
          apply Finset.le_max' times (firstInput input z)
          exact Finset.mem_image.mpr ⟨z, hzLate, rfl⟩
        have hzneq : firstInput input z ≠ lastTime := by
          intro heq
          have hzlast : z = last := by
            calc
              z = input (firstInput input z) := (firstInput_spec input hzRange).symm
              _ = input (firstInput input last) := by rw [heq, ← hlastEq]
              _ = last := firstInput_spec input hlastRange
          exact (Finset.mem_erase.mp hzOrd).1 hzlast
        have hzlt : firstInput input z < firstInput input last := by
          rw [hlastEq]
          exact lt_of_le_of_ne hzle hzneq
        have hlastNotInput : ∀ s, s ≤ firstInput input z → input s ≠ last := by
          intro s hs hEq
          have := firstInput_le input hEq
          omega
        have hlastNotOutput : ∀ s, s < firstInput input z →
            trajectory (greedyGenerator family) input s ≠ last := by
          intro s _ hEq
          have hlastD : last ∈ D := by
            rw [← hEq]
            exact output_generatorFirst family input s
          exact (Finset.mem_filter.mp hlastA).2 hlastD
        have houtLe : trajectory (greedyGenerator family) input (firstInput input z) ≤ last :=
          output_le_of_unannounced family input hcore hzT hlastI hlastNotInput hlastNotOutput
        apply Finset.mem_filter.mpr
        constructor
        · show trajectory (greedyGenerator family) input (firstInput input z) ∈ P
          simp only [P, GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
            Finset.mem_range]
          have hlastLt : last < n := by
            exact Finset.mem_range.mp (Finset.mem_filter.mp hlastP).1
          exact ⟨lt_of_le_of_lt houtLe hlastLt,
            trajectory_mem_core family input hcore hzT⟩
        · exact output_generatorFirst family input (firstInput input z)
      · intro x hx y hy hxy
        have htime := trajectory_injective family input hxy
        have hxLate : x ∈ late := (Finset.mem_erase.mp hx).2
        have hyLate : y ∈ late := (Finset.mem_erase.mp hy).2
        have hxA : x ∈ A := (Finset.mem_filter.mp hxLate).1
        have hyA : y ∈ A := (Finset.mem_filter.mp hyLate).1
        calc
          x = input (firstInput input x) := (firstInput_spec input (hA_range x hxA)).symm
          _ = input (firstInput input y) := by rw [htime]
          _ = y := firstInput_spec input (hA_range y hyA)
    change GenLimit.PatientScope.prefixCount I n ≤
      2 * GenLimit.PatientScope.prefixCount (D ∩ I) n + T + 1
    rw [← hPcount, ← hG, hP, hA_split]
    omega
  · have hlate0 : late.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hlate)
    change GenLimit.PatientScope.prefixCount I n ≤
      2 * GenLimit.PatientScope.prefixCount (D ∩ I) n + T + 1
    rw [← hPcount, ← hG, hP, hA_split, hlate0]
    omega

end

end Stage3Case017
