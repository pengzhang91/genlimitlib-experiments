import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

def prefixCompatible {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (j : Fin m) : Prop :=
  ∀ i, xs i ∈ family j

def currentCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, prefixCompatible family xs j → z ∈ family j}

noncomputable def forbidden {t : ℕ} (xs : Fin (t + 1) → ℕ)
    (ys : Fin t → ℕ) : Finset ℕ :=
  GenLimit.Generic.sequenceSample xs ∪
    GenLimit.Generic.sequenceSample ys

noncomputable def coreGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : ∃ z, z ∈ currentCore family xs ∧ z ∉ forbidden xs ys then
      Nat.find h
    else 0

def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t

theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  rw [run]

theorem coreGenerator_spec {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, z ∈ currentCore family xs ∧ z ∉ forbidden xs ys) :
    coreGenerator family t xs ys ∈ currentCore family xs ∧
      coreGenerator family t xs ys ∉ forbidden xs ys := by
  classical
  rw [coreGenerator, dif_pos h]
  exact Nat.find_spec h

theorem coreGenerator_min {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, z ∈ currentCore family xs ∧ z ∉ forbidden xs ys)
    {z : ℕ} (hzCore : z ∈ currentCore family xs)
    (hzFresh : z ∉ forbidden xs ys) :
    coreGenerator family t xs ys ≤ z := by
  classical
  rw [coreGenerator, dif_pos h]
  exact Nat.find_min' h ⟨hzCore, hzFresh⟩


theorem eventually_prefixCompatible_iff {m : ℕ}
    (family : Fin m → Language) (input : Stream) (j : Fin m) :
    ∀ᶠ t : ℕ in atTop,
      prefixCompatible family (fun i : Fin (t + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  by_cases hIn : GenLimit.Generic.StreamIn input (family j)
  · exact Filter.Eventually.of_forall fun t =>
      ⟨fun _ => hIn, fun _ i => hIn ⟨i, rfl⟩⟩
  · obtain ⟨z, ⟨s, rfl⟩, hz⟩ := Set.not_subset.mp hIn
    filter_upwards [eventually_ge_atTop s] with t ht
    constructor
    · intro hprefix
      exact False.elim (hz (hprefix ⟨s, Nat.lt_succ_of_le ht⟩))
    · intro hstream
      exact False.elim (hIn hstream)

theorem exists_stable_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      currentCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  have hall : ∀ᶠ t : ℕ in atTop, ∀ j : Fin m,
      prefixCompatible family (fun i : Fin (t + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j) := by
    rw [Filter.eventually_all]
    exact fun j => eventually_prefixCompatible_iff family input j
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hall
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  constructor
  · intro hz j hj
    exact hz j ((hT t ht j).2 hj)
  · intro hz j hj
    exact hz j ((hT t ht j).1 hj)

theorem eventual_core_output {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hFollows : Follows (coreGenerator family) input output)
    (hInfinite : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      output t ∈ informationCore family input ∧
      output t ∉ GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t → output s ≠ output t := by
  classical
  obtain ⟨T, hstable⟩ := exists_stable_core family input
  refine ⟨T, ?_⟩
  intro t ht
  let xs : Fin (t + 1) → ℕ := fun i => input i
  let ys : Fin t → ℕ := fun i => output i
  obtain ⟨z, hzCore, hzFresh⟩ :=
    hInfinite.exists_notMem_finset (forbidden xs ys)
  have hcurrent : z ∈ currentCore family xs := by
    rw [hstable t ht]
    exact hzCore
  have hex : ∃ z, z ∈ currentCore family xs ∧ z ∉ forbidden xs ys :=
    ⟨z, hcurrent, hzFresh⟩
  have hspec := coreGenerator_spec family xs ys hex
  have hout : output t = coreGenerator family t xs ys := by
    simpa [xs, ys] using hFollows t
  rw [hout]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hstable t ht]
    exact hspec.1
  · intro hmem
    apply hspec.2
    apply Finset.mem_union_left
    rw [GenLimit.Generic.sequenceSample_prefix]
    exact hmem
  · intro s hst heq
    apply hspec.2
    apply Finset.mem_union_right
    rw [GenLimit.Generic.mem_sequenceSample_iff]
    exact ⟨⟨s, hst⟩, heq⟩


theorem eventual_output_min {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hFollows : Follows (coreGenerator family) input output)
    (hInfinite : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t → ∀ z,
      z ∈ informationCore family input →
      z ∉ GenLimit.Generic.sample input (t + 1) →
      (∀ s, s < t → output s ≠ z) →
      output t ≤ z := by
  classical
  obtain ⟨T, hstable⟩ := exists_stable_core family input
  refine ⟨T, ?_⟩
  intro t ht z hzCore hzInput hzOutput
  let xs : Fin (t + 1) → ℕ := fun i => input i
  let ys : Fin t → ℕ := fun i => output i
  obtain ⟨w, hwCore, hwFresh⟩ :=
    hInfinite.exists_notMem_finset (forbidden xs ys)
  have hwCurrent : w ∈ currentCore family xs := by
    rw [hstable t ht]
    exact hwCore
  have hex : ∃ w, w ∈ currentCore family xs ∧ w ∉ forbidden xs ys :=
    ⟨w, hwCurrent, hwFresh⟩
  have hzCurrent : z ∈ currentCore family xs := by
    rw [hstable t ht]
    exact hzCore
  have hzFresh : z ∉ forbidden xs ys := by
    intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rw [GenLimit.Generic.sequenceSample_prefix] at hz
      exact hzInput hz
    · rw [GenLimit.Generic.mem_sequenceSample_iff] at hz
      obtain ⟨i, hi⟩ := hz
      exact hzOutput i i.isLt hi
  have hmin := coreGenerator_min family xs ys hex hzCurrent hzFresh
  rw [← hFollows t] at hmin
  exact hmin

theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input output : Stream)
    (hFollows : Follows (coreGenerator family) input output)
    (hInfinite : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input output := by
  classical
  obtain ⟨Tnovel, hnovel⟩ :=
    eventual_core_output family input output hFollows hInfinite
  obtain ⟨Tmin, hmin⟩ :=
    eventual_output_min family input output hFollows hInfinite
  let T := max Tnovel Tmin
  intro z hz
  have hzInput : z ∉ Set.range input := hz.2
  by_contra hzFirst
  have hzOutput : ∀ t, output t ≠ z := by
    intro t hout
    apply hzFirst
    refine ⟨t, hout, ?_⟩
    intro s hs hin
    exact hzInput ⟨s, hin⟩
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨output (T + i), Nat.lt_succ_iff.mpr <|
      hmin (T + i) (le_trans (Nat.le_max_right _ _) (Nat.le_add_right T i)) z
        hz.1
        (by
          intro hsample
          rw [GenLimit.Generic.mem_sample_iff] at hsample
          obtain ⟨s, -, hs⟩ := hsample
          exact hzInput ⟨s, hs⟩)
        (by
          intro s hs heq
          exact hzOutput s heq)⟩
  have hf : Function.Injective f := by
    intro i k hik
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hiklt | hkilt
    · have htimes : T + i < T + k := Nat.add_lt_add_left hiklt T
      have hdistinct := (hnovel (T + k)
        (le_trans (Nat.le_max_left _ _) (Nat.le_add_right T k))).2.2
        (T + i) htimes
      have hv : output (T + i) = output (T + k) := by
        simpa [f] using congrArg (fun q : Fin (z + 1) => (q : ℕ)) hik
      exact hdistinct hv
    · have htimes : T + k < T + i := Nat.add_lt_add_left hkilt T
      have hdistinct := (hnovel (T + i)
        (le_trans (Nat.le_max_left _ _) (Nat.le_add_right T i))).2.2
        (T + k) htimes
      have hv : output (T + k) = output (T + i) := by
        simpa [f] using (congrArg (fun q : Fin (z + 1) => (q : ℕ)) hik).symm
      exact hdistinct hv
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega



noncomputable def firstTime (input : Stream) (x : ℕ) : ℕ :=
  Function.invFun input x

theorem adversaryFirst_at_firstTime {input output : Stream}
    (hInjective : Function.Injective input) {x : ℕ}
    (hx : x ∈ GenLimit.AdversaryFirst input output) :
    input (firstTime input x) = x ∧
      ∀ s, s < firstTime input x → output s ≠ x := by
  obtain ⟨t, htx, hbefore⟩ := hx
  have htime : firstTime input x = t := by
    rw [← htx]
    exact Function.leftInverse_invFun hInjective t
  rw [htime]
  exact ⟨htx, hbefore⟩

theorem relativeLowerDensity_mono_left {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let b : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hab : ∀ n, a n ≤ b n := by
    intro n
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
      (Nat.cast_nonneg _)
  have haNonneg : ∀ n, 0 ≤ a n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbLeOne : ∀ n, b n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [b, hn]
    · dsimp [b]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  unfold GenLimit.PatientScope.relativeLowerDensity
  change liminf a atTop ≤ liminf b atTop
  exact liminf_le_liminf (Filter.Eventually.of_forall hab)
    (isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall haNonneg))
    (isCoboundedUnder_ge_of_le atTop hbLeOne)



theorem attacker_prefix_le_defender {m : ℕ}
    (family : Fin m → Language) (input output : Stream)
    (hInjective : Function.Injective input)
    (hFollows : Follows (coreGenerator family) input output)
    (hInfinite : (informationCore family input).Infinite) :
    ∃ r, ∀ n,
      GenLimit.PatientScope.prefixCount
          (GenLimit.AdversaryFirst input output ∩ informationCore family input) n ≤
        GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input output ∩ informationCore family input) n + r := by
  classical
  obtain ⟨Tnovel, hnovel⟩ :=
    eventual_core_output family input output hFollows hInfinite
  obtain ⟨Tmin, hmin⟩ :=
    eventual_output_min family input output hFollows hInfinite
  let T := max Tnovel Tmin
  refine ⟨2 * T + 1, ?_⟩
  intro n
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ informationCore family input) n
  let early := A.filter (fun x => firstTime input x < T)
  let late := A.filter (fun x => T ≤ firstTime input x)
  have htime_inj : Set.InjOn (firstTime input) (↑A : Set ℕ) := by
    intro x hx y hy hxy
    have hxAdv := (GenLimit.PatientScope.mem_prefixFinset.mp hx).2.1
    have hyAdv := (GenLimit.PatientScope.mem_prefixFinset.mp hy).2.1
    have hxAt := (adversaryFirst_at_firstTime hInjective hxAdv).1
    have hyAt := (adversaryFirst_at_firstTime hInjective hyAdv).1
    calc
      x = input (firstTime input x) := hxAt.symm
      _ = input (firstTime input y) := by rw [hxy]
      _ = y := hyAt
  have hearly : early.card ≤ T := by
    have himage : early.image (firstTime input) ⊆ Finset.range T := by
      intro q hq
      obtain ⟨x, hxEarly, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hxEarly).2
    have hinj : Set.InjOn (firstTime input) (↑early : Set ℕ) := by
      intro x hx y hy
      have hx' : x ∈ early := hx
      have hy' : y ∈ early := hy
      change x ∈ A.filter (fun x => firstTime input x < T) at hx'
      change y ∈ A.filter (fun x => firstTime input x < T) at hy'
      exact htime_inj (Finset.mem_filter.mp hx').1 (Finset.mem_filter.mp hy').1
    calc
      early.card = (early.image (firstTime input)).card :=
        (Finset.card_image_iff.mpr hinj).symm
      _ ≤ (Finset.range T).card := Finset.card_le_card himage
      _ = T := Finset.card_range T
  have hsplit : early.card + late.card = A.card := by
    simpa [early, late, Nat.not_lt] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := A) (fun x => firstTime input x < T))
  by_cases hlate : late.Nonempty
  · obtain ⟨xq, hxqLate, hmax⟩ :=
      Finset.exists_max_image late (firstTime input) hlate
    let q := firstTime input xq
    have hxqA : xq ∈ A := by
      have hx := hxqLate
      simp only [late, Finset.mem_filter] at hx
      exact hx.1
    have hTq : T ≤ q := (Finset.mem_filter.mp hxqLate).2
    have hlateCard : late.card ≤ q + 1 := by
      have himage : late.image (firstTime input) ⊆ Finset.range (q + 1) := by
        intro k hk
        obtain ⟨x, hxLate, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_range.mpr <| Nat.lt_succ_iff.mpr (hmax x hxLate)
      have hinj : Set.InjOn (firstTime input) (↑late : Set ℕ) := by
        intro x hx y hy
        have hx' : x ∈ late := hx
        have hy' : y ∈ late := hy
        change x ∈ A.filter (fun x => T ≤ firstTime input x) at hx'
        change y ∈ A.filter (fun x => T ≤ firstTime input x) at hy'
        exact htime_inj (Finset.mem_filter.mp hx').1 (Finset.mem_filter.mp hy').1
      calc
        late.card = (late.image (firstTime input)).card :=
          (Finset.card_image_iff.mpr hinj).symm
        _ ≤ (Finset.range (q + 1)).card := Finset.card_le_card himage
        _ = q + 1 := Finset.card_range (q + 1)
    have hxqData := GenLimit.PatientScope.mem_prefixFinset.mp hxqA
    have hxqAdv : xq ∈ GenLimit.AdversaryFirst input output := hxqData.2.1
    have hxqCore : xq ∈ informationCore family input := hxqData.2.2
    have hxqLt : xq < n := hxqData.1
    have hxqAt := adversaryFirst_at_firstTime hInjective hxqAdv
    let S := (Finset.range (q - T)).image (fun i => output (T + i))
    have houtput_inj : Set.InjOn (fun i => output (T + i))
        (↑(Finset.range (q - T)) : Set ℕ) := by
      intro i hi k hk hik
      have hiBound : i < q - T := Finset.mem_range.mp hi
      have hkBound : k < q - T := Finset.mem_range.mp hk
      rcases lt_trichotomy i k with hiklt | rfl | hkilt
      · have htimes : T + i < T + k := Nat.add_lt_add_left hiklt T
        have hneq := (hnovel (T + k)
          (le_trans (Nat.le_max_left _ _) (Nat.le_add_right T k))).2.2
          (T + i) htimes
        exact False.elim (hneq hik)
      · rfl
      · have htimes : T + k < T + i := Nat.add_lt_add_left hkilt T
        have hneq := (hnovel (T + i)
          (le_trans (Nat.le_max_left _ _) (Nat.le_add_right T i))).2.2
          (T + k) htimes
        exact False.elim (hneq hik.symm)
    have hSCard : S.card = q - T := by
      dsimp [S]
      rw [Finset.card_image_iff.mpr houtput_inj, Finset.card_range]
    have hSsub : S ⊆ D := by
      intro y hy
      obtain ⟨i, hiRange, rfl⟩ := Finset.mem_image.mp hy
      have hi : i < q - T := Finset.mem_range.mp hiRange
      have hsLtQ : T + i < q := by omega
      have hsNovel := hnovel (T + i)
        (le_trans (Nat.le_max_left _ _) (Nat.le_add_right T i))
      have hsMin := hmin (T + i)
        (le_trans (Nat.le_max_right _ _) (Nat.le_add_right T i)) xq hxqCore
        (by
          intro hsample
          rw [GenLimit.Generic.mem_sample_iff] at hsample
          obtain ⟨k, hk, hkx⟩ := hsample
          have hkq : k = q := hInjective <| by
            rw [hkx, hxqAt.1]
          omega)
        (by
          intro k hk hkx
          exact hxqAt.2 k (lt_trans hk hsLtQ) hkx)
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      refine ⟨lt_of_le_of_lt hsMin hxqLt, ?_, hsNovel.1⟩
      refine ⟨T + i, rfl, ?_⟩
      intro k hk hkx
      apply hsNovel.2.1
      rw [GenLimit.Generic.mem_sample_iff]
      exact ⟨k, Nat.lt_succ_iff.mpr hk, hkx⟩
    have hstableCount : q - T ≤ D.card := by
      rw [← hSCard]
      exact Finset.card_le_card hSsub
    have hlateBound : late.card ≤ D.card + T + 1 := by
      calc
        late.card ≤ q + 1 := hlateCard
        _ = (q - T) + T + 1 := by omega
        _ ≤ D.card + T + 1 := by omega
    change A.card ≤ D.card + (2 * T + 1)
    rw [← hsplit]
    omega
  · have hlateZero : late.card = 0 := Finset.not_nonempty_iff_eq_empty.mp hlate ▸ rfl
    change A.card ≤ D.card + (2 * T + 1)
    rw [← hsplit, hlateZero]
    omega



theorem informationCore_subset_target {m : ℕ} (family : Fin m → Language)
    (input : Stream) {j : Fin m}
    (hStream : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j := by
  intro z hz
  exact hz j hStream

theorem density_bounds {m : ℕ} (family : Fin m → Language)
    (hFamilyInfinite : ∀ j, (family j).Infinite)
    (input output : Stream) (hInjective : Function.Injective input)
    (hFollows : Follows (coreGenerator family) input output)
    (hInfinite : (informationCore family input).Infinite) {j : Fin m}
    (hStream : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) *
          GenLimit.PatientScope.relativeLowerDensity
            (informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
  classical
  let I := informationCore family input
  let K := family j
  let A := GenLimit.AdversaryFirst input output
  let D := GenLimit.GeneratorFirst input output
  have hIK : I ⊆ K := informationCore_subset_target family input hStream
  have hmissing : I \ Set.range input ⊆ D ∩ K := by
    intro z hz
    exact ⟨core_diff_range_subset_generatorFirst family input output
      hFollows hInfinite hz, hIK hz.1⟩
  have hmissingDensity :
      GenLimit.PatientScope.relativeLowerDensity (I \ Set.range input) K ≤
        GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K :=
    relativeLowerDensity_mono_left hmissing Set.inter_subset_right
  obtain ⟨r, hAttacker⟩ :=
    attacker_prefix_le_defender family input output hInjective hFollows hInfinite
  have hcount : ∀ n,
      GenLimit.PatientScope.prefixCount I n ≤
        2 * GenLimit.PatientScope.prefixCount (D ∩ K) n + r +
          Nat.log2 (GenLimit.PatientScope.prefixCount K n) := by
    intro n
    let EI := GenLimit.PatientScope.prefixFinset I n
    let AI := GenLimit.PatientScope.prefixFinset (A ∩ I) n
    let DI := GenLimit.PatientScope.prefixFinset (D ∩ I) n
    have hcover : EI ⊆ AI ∪ DI := by
      intro z hz
      have hzData := GenLimit.PatientScope.mem_prefixFinset.mp hz
      have hzI : z ∈ I := hzData.2
      by_cases hzRange : z ∈ Set.range input
      · rcases GenLimit.range_subset_first_announcements input output hzRange with hzA | hzD
        · exact Finset.mem_union_left _ <|
            GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hzData.1, hzA, hzI⟩
        · exact Finset.mem_union_right _ <|
            GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hzData.1, hzD, hzI⟩
      · exact Finset.mem_union_right _ <|
          GenLimit.PatientScope.mem_prefixFinset.mpr
            ⟨hzData.1,
              core_diff_range_subset_generatorFirst family input output
                hFollows hInfinite ⟨hzI, hzRange⟩,
              hzI⟩
    have hEI : EI.card ≤ AI.card + DI.card := by
      exact le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
    have hAI : AI.card ≤ DI.card + r := by
      simpa [AI, DI, A, D, I,
        GenLimit.PatientScope.prefixCount] using hAttacker n
    have hDI : DI.card ≤
        (GenLimit.PatientScope.prefixFinset (D ∩ K) n).card := by
      apply Finset.card_le_card
      intro z hz
      have hzData := GenLimit.PatientScope.mem_prefixFinset.mp hz
      exact GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hzData.1, hzData.2.1, hIK hzData.2.2⟩
    change EI.card ≤
      2 * (GenLimit.PatientScope.prefixFinset (D ∩ K) n).card + r +
        Nat.log2 (GenLimit.PatientScope.prefixCount K n)
    omega
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity I K ≤
        GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
    apply GenLimit.PatientScope.partialDensity_of_counting
      (GenLimit.PatientScope.prefixCount K)
      (GenLimit.PatientScope.prefixCount I)
      (GenLimit.PatientScope.prefixCount (D ∩ K)) r
    · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hFamilyInfinite j)
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono hIK n
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
    · exact hcount
  exact max_le hhalf hmissingDensity


theorem eventual_novel {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hFollows : Follows (coreGenerator family) input output)
    (hInfinite : (informationCore family input).Infinite) {j : Fin m}
    (hStream : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input output (family j) := by
  obtain ⟨T, hT⟩ := eventual_core_output family input output hFollows hInfinite
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hcore, hfresh, hnovel⟩ := hT t ht
  refine ⟨hcore j hStream, ?_, hnovel⟩
  simpa [GenLimit.sample, GenLimit.Generic.sample] using hfresh

end Stage3Case017Proof
