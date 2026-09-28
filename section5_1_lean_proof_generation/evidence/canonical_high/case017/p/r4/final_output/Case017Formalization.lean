import Stage3Model
import Mathlib

open Filter
open scoped Topology

namespace Case017Proof

open Stage3Case017

noncomputable def historyCore {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

noncomputable def blocked {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs ∪ GenLimit.Generic.sequenceSample ys

noncomputable def leastFresh (S : Set ℕ) (B : Finset ℕ) : ℕ := by
  classical
  by_cases hS : S.Infinite
  · exact Nat.find (hS.exists_notMem_finset B)
  · exact Nat.find (Set.infinite_univ.exists_notMem_finset B)

lemma leastFresh_not_mem (S : Set ℕ) (B : Finset ℕ) :
    leastFresh S B ∉ B := by
  classical
  unfold leastFresh
  split <;> rename_i hS
  · exact (Nat.find_spec (hS.exists_notMem_finset B)).2
  · exact (Nat.find_spec (Set.infinite_univ.exists_notMem_finset B)).2

lemma leastFresh_mem {S : Set ℕ} (hS : S.Infinite) (B : Finset ℕ) :
    leastFresh S B ∈ S := by
  classical
  unfold leastFresh
  rw [dif_pos hS]
  exact (Nat.find_spec (hS.exists_notMem_finset B)).1

lemma leastFresh_le {S : Set ℕ} (hS : S.Infinite) (B : Finset ℕ)
    {z : ℕ} (hzS : z ∈ S) (hzB : z ∉ B) :
    leastFresh S B ≤ z := by
  classical
  unfold leastFresh
  rw [dif_pos hS]
  exact Nat.find_min' (hS.exists_notMem_finset B) ⟨hzS, hzB⟩

noncomputable def generator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator :=
  fun _ xs ys => leastFresh (historyCore family xs) (blocked xs ys)

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream)
    (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

lemma trajectory_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    trajectory gen input t =
      gen t (fun i => input i) (fun i => trajectory gen input i) := by
  rw [trajectory]

lemma follows_trajectory (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  exact trajectory_eq gen input t

lemma mem_sequenceSample_iff {α : Type*} [DecidableEq α] {t : ℕ}
    {xs : Fin t → α} {x : α} :
    x ∈ GenLimit.Generic.sequenceSample xs ↔ ∃ i, xs i = x := by
  classical
  simp [GenLimit.Generic.sequenceSample]

lemma generator_fresh {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    trajectory (generator family) input t ∉
        GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t →
        trajectory (generator family) input s ≠
          trajectory (generator family) input t := by
  classical
  have hnot := leastFresh_not_mem
    (historyCore family (fun i : Fin (t + 1) => input i))
    (blocked (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (generator family) input i))
  have hout : trajectory (generator family) input t =
      leastFresh (historyCore family (fun i : Fin (t + 1) => input i))
        (blocked (fun i : Fin (t + 1) => input i)
          (fun i : Fin t => trajectory (generator family) input i)) := by
    rw [trajectory_eq, generator]
  constructor
  · intro hmem
    have hsamp : trajectory (generator family) input t ∈
        GenLimit.Generic.sequenceSample (fun i : Fin (t + 1) => input i) := by
      rw [mem_sequenceSample_iff]
      simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range] at hmem
      obtain ⟨a, ha, heq⟩ := hmem
      exact ⟨⟨a, ha⟩, heq⟩
    rw [hout] at hsamp
    exact hnot (Finset.mem_union_left _ hsamp)
  · intro s hst heq
    have hs : trajectory (generator family) input s ∈
        GenLimit.Generic.sequenceSample
          (fun i : Fin t => trajectory (generator family) input i) := by
      rw [mem_sequenceSample_iff]
      exact ⟨⟨s, hst⟩, rfl⟩
    rw [heq, hout] at hs
    exact hnot (Finset.mem_union_right _ hs)

lemma trajectory_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Function.Injective (trajectory (generator family) input) := by
  intro a b hab
  rcases lt_trichotomy a b with hablt | habEq | hbalt
  · exact False.elim ((generator_fresh family input b).2 a hablt hab)
  · exact habEq
  · exact False.elim ((generator_fresh family input a).2 b hbalt hab.symm)

lemma trajectory_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range (trajectory (generator family) input) ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  rintro z ⟨t, rfl⟩
  refine ⟨t, rfl, ?_⟩
  intro s hst heq
  exact (generator_fresh family input t).1 (by
    simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range]
    exact ⟨s, Nat.lt_succ_of_le hst, heq⟩)

lemma exists_stable_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      historyCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  have h_each : ∀ j : Fin m, ∃ T : ℕ, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hj : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, ?_⟩
      intro t _
      constructor
      · intro _
        exact hj
      · intro _ i
        exact hj ⟨i, rfl⟩
    · obtain ⟨z, ⟨s, rfl⟩, hs⟩ := Set.not_subset.mp hj
      refine ⟨s, ?_⟩
      intro t hst
      constructor
      · intro hall
        exact False.elim (hs (hall ⟨s, Nat.lt_succ_of_le hst⟩))
      · intro hstream
        exact False.elim (hj hstream)
  choose times htimes using h_each
  refine ⟨∑ j, times j, ?_⟩
  intro t hsum
  apply Set.ext
  intro z
  simp only [historyCore, informationCore, Set.mem_setOf_eq]
  apply forall_congr'
  intro j
  have hjle : times j ≤ ∑ k, times k := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [htimes j t (hjle.trans hsum)]

lemma stable_output_mem {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    (ht : T ≤ t) :
    trajectory (generator family) input t ∈ informationCore family input := by
  rw [trajectory_eq, generator]
  have hhist : (historyCore family
      (fun i : Fin (t + 1) => input i)).Infinite := by
    simpa [hstable t ht] using hcore
  have hmem := leastFresh_mem hhist
    (blocked (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (generator family) input i))
  simpa [hstable t ht] using hmem

lemma stable_output_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t z : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    (ht : T ≤ t) (hz : z ∈ informationCore family input)
    (hinput : ∀ s, s ≤ t → input s ≠ z)
    (houtput : ∀ s, s < t → trajectory (generator family) input s ≠ z) :
    trajectory (generator family) input t ≤ z := by
  rw [trajectory_eq, generator]
  apply leastFresh_le
  · simpa [hstable t ht] using hcore
  · simpa [hstable t ht] using hz
  · intro hblocked
    rcases Finset.mem_union.mp hblocked with hin | hout
    · rw [mem_sequenceSample_iff] at hin
      obtain ⟨i, hi⟩ := hin
      exact hinput i (Nat.le_of_lt_succ i.isLt) hi
    · rw [mem_sequenceSample_iff] at hout
      obtain ⟨i, hi⟩ := hout
      exact houtput i i.isLt hi

lemma core_point_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T z : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    (hz : z ∈ informationCore family input) :
    z ∈ Set.range input ∪ Set.range (trajectory (generator family) input) := by
  classical
  by_contra hnot
  have hnotInput : ∀ s, input s ≠ z := by
    intro s hs
    exact hnot (Or.inl ⟨s, hs⟩)
  have hnotOutput : ∀ s, trajectory (generator family) input s ≠ z := by
    intro s hs
    exact hnot (Or.inr ⟨s, hs⟩)
  have hle : ∀ k : Fin (z + 2),
      trajectory (generator family) input (T + k) ≤ z := by
    intro k
    apply stable_output_le family input hstable hcore (Nat.le_add_right T k) hz
    · intro s _
      exact hnotInput s
    · intro s _
      exact hnotOutput s
  let image : Finset ℕ := Finset.univ.image
    (fun k : Fin (z + 2) => trajectory (generator family) input (T + k))
  have himage_subset : image ⊆ Finset.range (z + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, _, rfl⟩ := hy
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hle k))
  have hinj : Function.Injective
      (fun k : Fin (z + 2) => trajectory (generator family) input (T + k)) := by
    intro a b hab
    have := trajectory_injective family input hab
    exact Fin.ext (Nat.add_left_cancel this)
  have hcard : image.card = z + 2 := by
    rw [show image = Finset.univ.image
      (fun k : Fin (z + 2) => trajectory (generator family) input (T + k)) by rfl]
    rw [Finset.card_image_iff.mpr hinj.injOn, Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_card himage_subset
  simp [hcard] at this


noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  by_cases hz : z ∈ Set.range input
  · exact Nat.find hz
  · exact 0

lemma firstInput_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  unfold firstInput
  rw [dif_pos hz]
  exact Nat.find_spec hz

lemma firstInput_min (input : Stream) {z : ℕ} (hz : z ∈ Set.range input)
    {t : ℕ} (ht : input t = z) :
    firstInput input z ≤ t := by
  classical
  unfold firstInput
  rw [dif_pos hz]
  exact Nat.find_min' hz ht

lemma firstInput_injective_on (input : Stream) (hinj : Function.Injective input)
    {x y : ℕ} (hx : x ∈ Set.range input) (hy : y ∈ Set.range input)
    (hxy : firstInput input x = firstInput input y) : x = y := by
  rw [← firstInput_spec input hx, ← firstInput_spec input hy, hxy]

lemma not_generatorFirst_input_range {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T z : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input
      (trajectory (generator family) input)) :
    z ∈ Set.range input := by
  rcases core_point_announced family input hstable hcore hzcore with hin | hout
  · exact hin
  · exact False.elim (hznot (trajectory_generatorFirst family input hout))

noncomputable def coreWinners (I : Set ℕ) (input output : Stream)
    (n : ℕ) : Finset ℕ := by
  classical
  exact (GenLimit.PatientScope.prefixFinset I n).filter
    (fun z => z ∈ GenLimit.GeneratorFirst input output)

noncomputable def coreLosers (I : Set ℕ) (input output : Stream)
    (n : ℕ) : Finset ℕ := by
  classical
  exact (GenLimit.PatientScope.prefixFinset I n).filter
    (fun z => z ∉ GenLimit.GeneratorFirst input output)

noncomputable def earlyLosers (I : Set ℕ) (input output : Stream)
    (T n : ℕ) : Finset ℕ :=
  (coreLosers I input output n).filter (fun z => firstInput input z < T)

noncomputable def lateLosers (I : Set ℕ) (input output : Stream)
    (T n : ℕ) : Finset ℕ :=
  (coreLosers I input output n).filter (fun z => T ≤ firstInput input z)

lemma prefix_winners_losers_card (I : Set ℕ) (input output : Stream)
    (n : ℕ) :
    (GenLimit.PatientScope.prefixFinset I n).card =
      (coreWinners I input output n).card +
        (coreLosers I input output n).card := by
  classical
  rw [coreWinners, coreLosers]
  exact (Finset.filter_card_add_filter_neg_card_eq_card
    (s := GenLimit.PatientScope.prefixFinset I n)
    (fun z => z ∈ GenLimit.GeneratorFirst input output)).symm

lemma losers_early_late_card (I : Set ℕ) (input output : Stream)
    (T n : ℕ) :
    (coreLosers I input output n).card =
      (earlyLosers I input output T n).card +
        (lateLosers I input output T n).card := by
  classical
  rw [earlyLosers, lateLosers]
  have := Finset.filter_card_add_filter_neg_card_eq_card
    (s := coreLosers I input output n)
    (fun z => firstInput input z < T)
  simpa [Nat.not_lt] using this.symm

lemma earlyLosers_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    (earlyLosers (informationCore family input) input
      (trajectory (generator family) input) T n).card ≤ T := by
  classical
  let E := earlyLosers (informationCore family input) input
    (trajectory (generator family) input) T n
  let image := E.image (firstInput input)
  change E.card ≤ T
  have hsub : image ⊆ Finset.range T := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨z, hzE, rfl⟩ := hq
    exact Finset.mem_range.mpr (by
      simpa [E, earlyLosers] using (Finset.mem_filter.mp hzE).2)
  have hinput : ∀ z ∈ E, z ∈ Set.range input := by
    intro z hzE
    have hzL : z ∈ coreLosers (informationCore family input) input
        (trajectory (generator family) input) n := by
      exact (Finset.mem_filter.mp (show z ∈ E by exact hzE)).1
    rw [coreLosers] at hzL
    have hzP := (Finset.mem_filter.mp hzL).1
    have hzcore : z ∈ informationCore family input := by
      simpa [GenLimit.PatientScope.prefixFinset] using
        (Finset.mem_filter.mp hzP).2
    exact not_generatorFirst_input_range family input hstable hcore hzcore
      (Finset.mem_filter.mp hzL).2
  have himage : image.card = E.card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy hxy
    exact firstInput_injective_on input hinj (hinput x hx) (hinput y hy) hxy
  calc
    E.card = image.card := himage.symm
    _ ≤ (Finset.range T).card := Finset.card_le_card hsub
    _ = T := Finset.card_range T

lemma lateLosers_card_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    (lateLosers (informationCore family input) input
      (trajectory (generator family) input) T n).card ≤
      (coreWinners (informationCore family input) input
        (trajectory (generator family) input) n).card + 1 := by
  classical
  let A := lateLosers (informationCore family input) input
    (trajectory (generator family) input) T n
  let W := coreWinners (informationCore family input) input
    (trajectory (generator family) input) n
  change A.card ≤ W.card + 1
  by_cases hA : A.Nonempty
  · obtain ⟨x₀, hx₀A, hx₀max⟩ := Finset.exists_max_image A (firstInput input) hA
    let R := A.erase x₀
    let partner : ℕ → ℕ := fun x =>
      trajectory (generator family) input (firstInput input x)
    have hA_input : ∀ z ∈ A, z ∈ Set.range input := by
      intro z hzA
      have hzL : z ∈ coreLosers (informationCore family input) input
          (trajectory (generator family) input) n :=
        (Finset.mem_filter.mp (show z ∈ A by exact hzA)).1
      rw [coreLosers] at hzL
      have hzP := (Finset.mem_filter.mp hzL).1
      have hzcore : z ∈ informationCore family input := by
        simpa [GenLimit.PatientScope.prefixFinset] using
          (Finset.mem_filter.mp hzP).2
      exact not_generatorFirst_input_range family input hstable hcore hzcore
        (Finset.mem_filter.mp hzL).2
    have hpartner : ∀ z ∈ R, partner z ∈ W := by
      intro z hzR
      have hzA : z ∈ A := (Finset.mem_erase.mp hzR).2
      have hzne : z ≠ x₀ := (Finset.mem_erase.mp hzR).1
      have hztime_le := hx₀max z hzA
      have htimes_ne : firstInput input z ≠ firstInput input x₀ := by
        intro heq
        exact hzne (firstInput_injective_on input hinj
          (hA_input z hzA) (hA_input x₀ hx₀A) heq)
      have htime_lt : firstInput input z < firstInput input x₀ :=
        lt_of_le_of_ne hztime_le htimes_ne
      have hzlate : T ≤ firstInput input z := by
        simpa [A, lateLosers] using (Finset.mem_filter.mp hzA).2
      have hx₀L : x₀ ∈ coreLosers (informationCore family input) input
          (trajectory (generator family) input) n :=
        (Finset.mem_filter.mp (show x₀ ∈ A by exact hx₀A)).1
      rw [coreLosers] at hx₀L
      have hx₀P := (Finset.mem_filter.mp hx₀L).1
      have hx₀core : x₀ ∈ informationCore family input := by
        simpa [GenLimit.PatientScope.prefixFinset] using
          (Finset.mem_filter.mp hx₀P).2
      have hx₀lt : x₀ < n := by
        simpa [GenLimit.PatientScope.prefixFinset] using
          (Finset.mem_filter.mp hx₀P).1
      have hx₀notGF := (Finset.mem_filter.mp hx₀L).2
      have hx₀input_prefix : ∀ s, s ≤ firstInput input z → input s ≠ x₀ := by
        intro s hs hval
        have hmin := firstInput_min input (hA_input x₀ hx₀A) hval
        omega
      have hx₀output_prefix : ∀ s, s < firstInput input z →
          trajectory (generator family) input s ≠ x₀ := by
        intro s _ hs
        exact hx₀notGF (trajectory_generatorFirst family input ⟨s, hs⟩)
      have hle : partner z ≤ x₀ := by
        exact stable_output_le family input hstable hcore hzlate hx₀core
          hx₀input_prefix hx₀output_prefix
      have hmemI : partner z ∈ informationCore family input :=
        stable_output_mem family input hstable hcore hzlate
      have hmemGF : partner z ∈ GenLimit.GeneratorFirst input
          (trajectory (generator family) input) :=
        trajectory_generatorFirst family input ⟨firstInput input z, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
          Finset.mem_range]
        exact ⟨Nat.lt_of_le_of_lt hle hx₀lt, hmemI⟩
      · exact hmemGF
    have hpartner_inj : Set.InjOn partner (↑R : Set ℕ) := by
      intro x hx y hy hxy
      have htime := trajectory_injective family input hxy
      exact firstInput_injective_on input hinj
        (hA_input x (Finset.mem_of_mem_erase (show x ∈ R by exact hx)))
        (hA_input y (Finset.mem_of_mem_erase (show y ∈ R by exact hy))) htime
    have himage : (R.image partner).card = R.card :=
      Finset.card_image_iff.mpr hpartner_inj
    have himage_sub : R.image partner ⊆ W := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨z, hzR, rfl⟩ := hy
      exact hpartner z hzR
    have hRcard : R.card + 1 = A.card := by
      simpa [R, hx₀A] using (Finset.card_erase_add_one hx₀A)
    have hRle : R.card ≤ W.card := by
      rw [← himage]
      exact Finset.card_le_card himage_sub
    omega
  · have hzero : A.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hA)
    omega

lemma core_prefix_half_count {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩
          informationCore family input) n + T + 1 := by
  classical
  let I := informationCore family input
  let output := trajectory (generator family) input
  change GenLimit.PatientScope.prefixCount I n ≤
    2 * GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input output ∩ I) n + T + 1
  have hp := prefix_winners_losers_card I input output n
  have hl := losers_early_late_card I input output T n
  have he : (earlyLosers I input output T n).card ≤ T := by
    simpa [I, output] using
      (earlyLosers_card_le family input hinj hstable hcore n)
  have ha : (lateLosers I input output T n).card ≤
      (coreWinners I input output n).card + 1 := by
    simpa [I, output] using
      (lateLosers_card_le family input hinj hstable hcore n)
  have hw : (coreWinners I input output n).card =
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ I) n := by
    simp only [coreWinners, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]
    congr 1
    ext z
    simp [and_left_comm, and_assoc, and_comm]
  simp only [GenLimit.PatientScope.prefixCount] at ⊢ hw
  rw [hp, hl, hw]
  omega


lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

lemma ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

lemma ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
  · have hle := prefixCount_mono hAK n
    have ha : GenLimit.PatientScope.prefixCount A n = 0 := by
      omega
    simp [hk, ha]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono hAK n

lemma relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall (fun n =>
      div_le_div_of_nonneg_right
        (by exact_mod_cast prefixCount_mono hAB n)
        (by positivity))
  · exact isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (ratio_nonneg A K))
  · exact isCoboundedUnder_ge_of_eventually_le atTop
      (Filter.Eventually.of_forall (ratio_le_one hBK))

lemma tendsto_prefixCount_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨s, hsK, hscard⟩ := hK.exists_subset_card_eq b
  let N := (∑ x ∈ s, x) + 1
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsub : s ⊆ GenLimit.PatientScope.prefixFinset K n := by
    intro x hx
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · have hxsum : x ≤ ∑ y ∈ s, y := by
        exact Finset.single_le_sum (s := s) (f := fun y : ℕ => y)
          (fun _ _ => Nat.zero_le _) hx
      omega
    · exact hsK hx
  have hcard := Finset.card_le_card hsub
  simpa [GenLimit.PatientScope.prefixCount, hscard] using hcard

lemma half_density_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    {K : Set ℕ} (hIK : informationCore family input ⊆ K)
    (hK : K.Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K) K := by
  let I := informationCore family input
  let output := trajectory (generator family) input
  let D := GenLimit.GeneratorFirst input output ∩ K
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount I n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let d : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    (((T + 1 : ℕ) : ℝ) / 2) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hID : GenLimit.GeneratorFirst input output ∩ I ⊆ D := by
    intro z hz
    exact ⟨hz.1, hIK hz.2⟩
  have hpoint : ∀ n, (1 / 2 : ℝ) * a n ≤ d n + e n := by
    intro n
    have hnat : GenLimit.PatientScope.prefixCount I n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ I) n + T + 1 := by
      simpa [I, output] using
        (core_prefix_half_count family input hinj hstable hcore n)
    have hwin := prefixCount_mono hID n
    have hcountNat : GenLimit.PatientScope.prefixCount I n ≤
        2 * GenLimit.PatientScope.prefixCount D n + T + 1 := by
      omega
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · have hi : GenLimit.PatientScope.prefixCount I n = 0 := by
        have hle := prefixCount_mono hIK n
        rw [hk] at hle
        exact Nat.eq_zero_of_le_zero hle
      simp [a, d, e, hk, hi]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hreal : (GenLimit.PatientScope.prefixCount I n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + (T + 1 : ℕ) := by
        exact_mod_cast hcountNat
      have hinv : 0 ≤ (GenLimit.PatientScope.prefixCount K n : ℝ)⁻¹ := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right hreal hinv
      dsimp [a, d, e]
      calc
        (1 / 2 : ℝ) *
            ((GenLimit.PatientScope.prefixCount I n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ)) =
            ((GenLimit.PatientScope.prefixCount I n : ℝ) *
              (GenLimit.PatientScope.prefixCount K n : ℝ)⁻¹) / 2 := by ring
        _ ≤ ((2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + (T + 1 : ℕ)) *
              (GenLimit.PatientScope.prefixCount K n : ℝ)⁻¹) / 2 := by
            linarith
        _ = (GenLimit.PatientScope.prefixCount D n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) +
            (((T + 1 : ℕ) : ℝ) / 2) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by ring
  have ha0 : ∀ᶠ n in atTop, 0 ≤ a n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [a]
      exact ratio_nonneg I K n)
  have ha1 : ∀ᶠ n in atTop, a n ≤ 1 :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [a]
      exact ratio_le_one hIK n)
  have hDsub : D ⊆ K := fun _ hz => hz.2
  have hd0 : ∀ᶠ n in atTop, 0 ≤ d n :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [d]
      exact ratio_nonneg D K n)
  have hd1 : ∀ᶠ n in atTop, d n ≤ 1 :=
    Filter.Eventually.of_forall (fun n => by
      dsimp [d]
      exact ratio_le_one hDsub n)
  have he0 : ∀ᶠ n in atTop, 0 ≤ e n := by
    exact Filter.Eventually.of_forall (fun n => by
      dsimp [e]
      positivity)
  have heC : ∀ᶠ n in atTop, e n ≤ (((T + 1 : ℕ) : ℝ) / 2) := by
    apply Filter.Eventually.of_forall
    intro n
    dsimp [e]
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hk]
      positivity
    · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hk)).2
      have hC : 0 ≤ (((T + 1 : ℕ) : ℝ) / 2) := by positivity
      have hkone : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      nlinarith
  have he_tendsto : Tendsto e atTop (𝓝 0) := by
    have hcount := tendsto_prefixCount_atTop hK
    have hbase := tendsto_const_div_atTop_nhds_zero_nat
      (((T + 1 : ℕ) : ℝ) / 2)
    simpa [e] using hbase.comp hcount
  have hscale : (1 / 2 : ℝ) * liminf a atTop ≤
      liminf (fun n => (1 / 2 : ℝ) * a n) atTop := by
    have h := le_liminf_mul (f := atTop)
      (u := fun _ : ℕ => (1 / 2 : ℝ)) (v := a)
      (Filter.Eventually.of_forall (fun _ => by norm_num))
      (isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall (fun _ => le_rfl)))
      ha0
      (isCoboundedUnder_ge_of_eventually_le atTop ha1)
    simpa using h
  have hmono : liminf (fun n => (1 / 2 : ℝ) * a n) atTop ≤
      liminf (fun n => e n + d n) atTop := by
    apply Filter.liminf_le_liminf
    · exact Filter.Eventually.of_forall (fun n => by
        simpa [add_comm] using hpoint n)
    · apply isBoundedUnder_of_eventually_ge
      filter_upwards [ha0] with n hn
      positivity
    · apply isCoboundedUnder_ge_of_eventually_le atTop
        (x := (((T + 1 : ℕ) : ℝ) / 2) + 1)
      filter_upwards [heC, hd1] with n hen hdn
      nlinarith
  have hadd : liminf (fun n => e n + d n) atTop ≤ liminf d atTop := by
    have h := liminf_add_le
      (f := atTop) (u := e) (v := d)
      (isBoundedUnder_of_eventually_ge he0)
      (isBoundedUnder_of_eventually_le heC)
      (isBoundedUnder_of_eventually_ge hd0)
      (isCoboundedUnder_ge_of_eventually_le atTop hd1)
    rw [he_tendsto.limsup_eq, zero_add] at h
    exact h
  change (1 / 2 : ℝ) * liminf a atTop ≤ liminf d atTop
  exact hscale.trans (hmono.trans hadd)

lemma never_presented_density_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    {K : Set ℕ} (hIK : informationCore family input ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K) K := by
  apply relativeLowerDensity_mono
  · intro z hz
    have hann := core_point_announced family input hstable hcore hz.1
    rcases hann with hin | hout
    · exact False.elim (hz.2 hin)
    · exact ⟨trajectory_generatorFirst family input hout, hIK hz.1⟩
  · exact fun _ hz => hz.2

lemma novel_generation {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      historyCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    {K : Set ℕ} (hIK : informationCore family input ⊆ K) :
    GenLimit.NovelGeneratesInLimit input
      (trajectory (generator family) input) K := by
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨hIK (stable_output_mem family input hstable hcore ht), ?_,
    (generator_fresh family input t).2⟩
  simpa [GenLimit.sample, GenLimit.Generic.sample] using
    (generator_fresh family input t).1

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  refine ⟨Case017Proof.generator family, ?_⟩
  intro input hinjective _ hcore
  let output := Case017Proof.trajectory (Case017Proof.generator family) input
  refine ⟨output, ?_, ?_⟩
  · simpa [output] using
      (Case017Proof.follows_trajectory (Case017Proof.generator family) input)
  · obtain ⟨T, hstable⟩ := Case017Proof.exists_stable_core family input
    intro j hstream
    have hIK : Stage3Case017.informationCore family input ⊆ family j := by
      intro z hz
      exact hz j hstream
    constructor
    · simpa [output] using
        (Case017Proof.novel_generation family input hstable hcore hIK)
    · apply max_le
      · simpa [output] using
          (Case017Proof.half_density_bound family input hinjective hstable hcore
            hIK (hinfinite j))
      · simpa [output] using
          (Case017Proof.never_presented_density_bound family input hstable hcore hIK)
