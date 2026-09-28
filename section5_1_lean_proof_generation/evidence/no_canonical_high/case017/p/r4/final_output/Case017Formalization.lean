import Stage3Model
import Mathlib

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017


def viable {m n : ℕ} (family : Fin m → Language) (xs : Fin n → ℕ) (z : ℕ) : Prop :=
  ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j

def available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  viable family xs z ∧ z ∉ Set.range xs ∧ z ∉ Set.range ys

noncomputable def generator {m : ℕ} (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t xs ys => if h : ∃ z, available family xs ys z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

noncomputable def badTime (input : Stream) (L : Language) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input L then 0
    else Nat.find (show ∃ t, input t ∉ L by
      simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using h)

noncomputable def stableTime {m : ℕ} (family : Fin m → Language) (input : Stream) : ℕ :=
  Finset.univ.sup (fun j => badTime input (family j))

theorem badTime_spec {input : Stream} {L : Language}
    (h : ¬ GenLimit.Generic.StreamIn input L) : input (badTime input L) ∉ L := by
  classical
  rw [badTime, dif_neg h]
  exact Nat.find_spec (by simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using h)

theorem prefix_compatible_iff {m t : ℕ} {family : Fin m → Language} {input : Stream}
    (ht : stableTime family input ≤ t) (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hp
    by_contra hbad
    have hle : badTime input (family j) ≤ stableTime family input := by
      exact Finset.le_sup (f := fun k => badTime input (family k)) (by simp)
    have hwit : badTime input (family j) < t + 1 := by omega
    exact badTime_spec hbad (hp ⟨badTime input (family j), hwit⟩)
  · intro hs i
    exact hs ⟨i, rfl⟩

theorem viable_iff_core {m t : ℕ} {family : Fin m → Language} {input : Stream}
    (ht : stableTime family input ≤ t) (z : ℕ) :
    viable family (fun i : Fin (t + 1) => input i) z ↔
      z ∈ informationCore family input := by
  simp only [viable, informationCore]
  constructor <;> intro h j hj
  · exact h j ((prefix_compatible_iff ht j).2 hj)
  · exact h j ((prefix_compatible_iff ht j).1 hj)

theorem exists_available {m t : ℕ} {family : Fin m → Language} {input output : Stream}
    (ht : stableTime family input ≤ t)
    (hcore : (informationCore family input).Infinite) :
    ∃ z, available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i) z := by
  let forbidden : Set ℕ :=
    Set.range (fun i : Fin (t + 1) => input i) ∪ Set.range (fun i : Fin t => output i)
  have hforbidden : forbidden.Finite :=
    (Set.finite_range _).union (Set.finite_range _)
  have hremain := hcore.diff hforbidden
  rcases hremain.nonempty with ⟨z, hzcore, hzforbidden⟩
  refine ⟨z, (viable_iff_core ht z).2 hzcore, ?_, ?_⟩
  · intro hz
    exact hzforbidden (Or.inl hz)
  · intro hz
    exact hzforbidden (Or.inr hz)

theorem generator_spec {m t : ℕ} {family : Fin m → Language}
    {xs : Fin (t + 1) → ℕ} {ys : Fin t → ℕ}
    (h : ∃ z, available family xs ys z) :
    available family xs ys (generator family t xs ys) := by
  classical
  simp only [generator, dif_pos h]
  exact Nat.find_spec h


theorem generator_min {m t : ℕ} {family : Fin m → Language}
    {xs : Fin (t + 1) → ℕ} {ys : Fin t → ℕ}
    (h : ∃ z, available family xs ys z) {z : ℕ}
    (hz : available family xs ys z) : generator family t xs ys ≤ z := by
  classical
  simp only [generator, dif_pos h]
  exact Nat.find_min' h hz

theorem trajectory_available {m t : ℕ} {family : Fin m → Language} {input : Stream}
    (ht : stableTime family input ≤ t)
    (hcore : (informationCore family input).Infinite) :
    available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (generator family) input i)
      (trajectory (generator family) input t) := by
  rw [trajectory]
  exact generator_spec (exists_available ht hcore)

theorem trajectory_min {m t : ℕ} {family : Fin m → Language} {input : Stream}
    (ht : stableTime family input ≤ t)
    (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hzin : z ∉ Set.range (fun i : Fin (t + 1) => input i))
    (hzout : z ∉ Set.range (fun i : Fin t => trajectory (generator family) input i)) :
    trajectory (generator family) input t ≤ z := by
  rw [trajectory]
  apply generator_min (exists_available ht hcore)
  exact ⟨(viable_iff_core ht z).2 hzcore, hzin, hzout⟩

theorem eventual_novel {m : ℕ} {family : Fin m → Language} {input : Stream}
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (trajectory (generator family) input) (family j) := by
  refine ⟨stableTime family input, ?_⟩
  intro t ht
  have hs := trajectory_available ht hcore
  have hcoremem : trajectory (generator family) input t ∈ informationCore family input :=
    (viable_iff_core ht _).1 hs.1
  refine ⟨hcoremem j hj, ?_, ?_⟩
  · intro hsample
    rcases Finset.mem_image.mp hsample with ⟨s, hslt, heq⟩
    exact hs.2.1 ⟨⟨s, by simpa using hslt⟩, heq⟩
  · intro s hst heq
    exact hs.2.2 ⟨⟨s, hst⟩, heq⟩

theorem trajectory_post_injective {m : ℕ} {family : Fin m → Language} {input : Stream}
    (hcore : (informationCore family input).Infinite) :
    Set.InjOn (trajectory (generator family) input)
      {t | stableTime family input ≤ t} := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · have hs := trajectory_available hb hcore
    exact hs.2.2 ⟨⟨a, hablt⟩, hab⟩
  · have hs := trajectory_available ha hcore
    exact hs.2.2 ⟨⟨b, hbalt⟩, hab.symm⟩


theorem missing_core_is_output {m : ℕ} {family : Fin m → Language} {input : Stream}
    (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input) (hzinput : z ∉ Set.range input) :
    z ∈ Set.range (trajectory (generator family) input) := by
  by_contra hzoutput
  let T := stableTime family input
  let f : Fin (z + 1) → Fin z := fun i =>
    ⟨trajectory (generator family) input (T + i), by
      have hle : trajectory (generator family) input (T + i) ≤ z := by
        apply trajectory_min (by simp [T]) hcore hzcore
        · intro h
          rcases h with ⟨q, hq⟩
          exact hzinput ⟨q, hq⟩
        · intro h
          rcases h with ⟨q, hq⟩
          exact hzoutput ⟨q, hq⟩
      have hne : trajectory (generator family) input (T + i) ≠ z := by
        intro h
        exact hzoutput ⟨T + i, h⟩
      omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hout : trajectory (generator family) input (T + (a : ℕ)) =
        trajectory (generator family) input (T + (b : ℕ)) := by
      simpa [f] using congrArg (fun q : Fin z => (q : ℕ)) hab
    have htime : T + (a : ℕ) = T + (b : ℕ) :=
      trajectory_post_injective hcore (by simp [T]) (by simp [T]) hout
    exact Fin.ext (Nat.add_left_cancel htime)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

theorem missing_core_subset_generatorFirst {m : ℕ} {family : Fin m → Language}
    {input : Stream} (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  intro z hz
  rcases missing_core_is_output hcore hz.1 hz.2 with ⟨t, ht⟩
  refine ⟨t, ht, ?_⟩
  intro s hst heq
  exact hz.2 ⟨s, heq⟩


noncomputable def firstInput (input : Stream) (z : ℕ) (hz : z ∈ Set.range input) : ℕ :=
  Nat.find hz

theorem firstInput_spec {input : Stream} {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z hz) = z := by
  exact Nat.find_spec hz

theorem firstInput_min {input : Stream} {z : ℕ} (hz : z ∈ Set.range input)
    {s : ℕ} (hs : input s = z) : firstInput input z hz ≤ s := by
  exact Nat.find_min' hz hs

theorem core_not_generatorFirst_has_input {m : ℕ} {family : Fin m → Language}
    {input : Stream} (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input)) :
    z ∈ Set.range input := by
  by_contra hzin
  exact hznot (missing_core_subset_generatorFirst hcore ⟨hzcore, hzin⟩)

theorem paired_output_generatorFirst {m : ℕ} {family : Fin m → Language}
    {input : Stream} (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input))
    (ht : stableTime family input ≤ firstInput input z
      (core_not_generatorFirst_has_input hcore hzcore hznot)) :
    trajectory (generator family) input
        (firstInput input z (core_not_generatorFirst_has_input hcore hzcore hznot)) ∈
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  let hzinput := core_not_generatorFirst_has_input hcore hzcore hznot
  let t := firstInput input z hzinput
  have hs := trajectory_available ht hcore
  refine ⟨t, rfl, ?_⟩
  intro s hst heq
  exact hs.2.1 ⟨⟨s, by omega⟩, heq⟩


theorem notD_no_output_before_firstInput {m : ℕ} {family : Fin m → Language}
    {input : Stream} (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input))
    {q : ℕ} (hq : q < firstInput input z
      (core_not_generatorFirst_has_input hcore hzcore hznot)) :
    trajectory (generator family) input q ≠ z := by
  intro hout
  apply hznot
  refine ⟨q, hout, ?_⟩
  intro s hs heq
  have hmin := firstInput_min
    (core_not_generatorFirst_has_input hcore hzcore hznot) heq
  omega

theorem crossing_unique {m n : ℕ} {family : Fin m → Language} {input : Stream}
    (hcore : (informationCore family input).Infinite) {z w : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hwcore : w ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input))
    (hwnot : w ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input))
    (hzt : stableTime family input ≤ firstInput input z
      (core_not_generatorFirst_has_input hcore hzcore hznot))
    (hwt : stableTime family input ≤ firstInput input w
      (core_not_generatorFirst_has_input hcore hwcore hwnot))
    (hzn : z < n) (hwn : w < n)
    (hzbad : n ≤ trajectory (generator family) input
      (firstInput input z (core_not_generatorFirst_has_input hcore hzcore hznot)))
    (hwbad : n ≤ trajectory (generator family) input
      (firstInput input w (core_not_generatorFirst_has_input hcore hwcore hwnot))) :
    z = w := by
  by_contra hzw
  let hzinput := core_not_generatorFirst_has_input hcore hzcore hznot
  let hwinput := core_not_generatorFirst_has_input hcore hwcore hwnot
  let tz := firstInput input z hzinput
  let tw := firstInput input w hwinput
  have htzne : tz ≠ tw := by
    intro h
    apply hzw
    calc
      z = input tz := (firstInput_spec hzinput).symm
      _ = input tw := congrArg input h
      _ = w := firstInput_spec hwinput
  rcases lt_or_gt_of_ne htzne with hlt | hgt
  · have hle : trajectory (generator family) input tz ≤ w := by
      apply trajectory_min hzt hcore hwcore
      · intro h
        rcases h with ⟨q, hq⟩
        have hmin := firstInput_min hwinput hq
        omega
      · intro h
        rcases h with ⟨q, hq⟩
        exact notD_no_output_before_firstInput hcore hwcore hwnot (by omega) hq
    have houtlt : trajectory (generator family) input
        (firstInput input z hzinput) < n := by
      exact lt_of_le_of_lt (by simpa [tz] using hle) hwn
    exact (not_lt_of_ge hzbad) houtlt
  · have hle : trajectory (generator family) input tw ≤ z := by
      apply trajectory_min hwt hcore hzcore
      · intro h
        rcases h with ⟨q, hq⟩
        have hmin := firstInput_min hzinput hq
        omega
      · intro h
        rcases h with ⟨q, hq⟩
        exact notD_no_output_before_firstInput hcore hzcore hznot (by omega) hq
    have houtlt : trajectory (generator family) input
        (firstInput input w hwinput) < n := by
      exact lt_of_le_of_lt (by simpa [tw] using hle) hzn
    exact (not_lt_of_ge hwbad) houtlt


noncomputable def firstInputDefault (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if hz : z ∈ Set.range input then firstInput input z hz else 0

noncomputable def pairedValue {m : ℕ} (family : Fin m → Language)
    (input : Stream) (z : ℕ) : ℕ :=
  trajectory (generator family) input (firstInputDefault input z)

theorem firstInputDefault_eq {input : Stream} {z : ℕ} (hz : z ∈ Set.range input) :
    firstInputDefault input z = firstInput input z hz := by
  classical
  simp [firstInputDefault, hz]

@[simp] theorem mem_prefixFinset {S : Set ℕ} {n z : ℕ} :
    z ∈ GenLimit.PatientScope.prefixFinset S n ↔ z < n ∧ z ∈ S := by
  simp [GenLimit.PatientScope.prefixFinset]

noncomputable def loserPrefix {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact  (GenLimit.PatientScope.prefixFinset (informationCore family input) n).filter
    (fun z => z ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input))

noncomputable def earlyLosers {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact  (loserPrefix family input n).filter
    (fun z => firstInputDefault input z < stableTime family input)

noncomputable def lateLosers {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact  (loserPrefix family input n).filter
    (fun z => stableTime family input ≤ firstInputDefault input z)

noncomputable def goodLosers {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact  (lateLosers family input n).filter (fun z => pairedValue family input z < n)

noncomputable def badLosers {m : ℕ} (family : Fin m → Language)
    (input : Stream) (n : ℕ) : Finset ℕ := by
  classical
  exact  (lateLosers family input n).filter (fun z => n ≤ pairedValue family input z)

theorem loser_mem_data {m n : ℕ} {family : Fin m → Language} {input : Stream}
    (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hz : z ∈ loserPrefix family input n) :
    z < n ∧ z ∈ informationCore family input ∧
      z ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input) ∧
      z ∈ Set.range input := by
  classical
  rw [loserPrefix] at hz
  have hz' := (Finset.mem_filter.mp hz)
  have hp := mem_prefixFinset.mp hz'.1
  exact ⟨hp.1, hp.2, hz'.2,
    core_not_generatorFirst_has_input hcore hp.2 hz'.2⟩

theorem earlyLosers_card_le {m n : ℕ} {family : Fin m → Language} {input : Stream}
    (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) :
    (earlyLosers family input n).card ≤ stableTime family input := by
  let E := earlyLosers family input n
  let f : {z // z ∈ E} → Fin (stableTime family input) := fun z =>
    ⟨firstInputDefault input z, by
      exact (Finset.mem_filter.mp z.2).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have haL : a.1 ∈ loserPrefix family input n := (Finset.mem_filter.mp a.2).1
    have hbL : b.1 ∈ loserPrefix family input n := (Finset.mem_filter.mp b.2).1
    obtain ⟨_, _, _, hain⟩ := loser_mem_data hcore haL
    obtain ⟨_, _, _, hbin⟩ := loser_mem_data hcore hbL
    have htime : firstInputDefault input a.1 = firstInputDefault input b.1 :=
      congrArg (fun q : Fin (stableTime family input) => (q : ℕ)) hab
    calc
      a.1 = input (firstInputDefault input a.1) := by
        rw [firstInputDefault_eq hain]
        exact (firstInput_spec hain).symm
      _ = input (firstInputDefault input b.1) := by rw [htime]
      _ = b.1 := by
        rw [firstInputDefault_eq hbin]
        exact firstInput_spec hbin
  have hc := Fintype.card_le_of_injective f hf
  simpa [E] using hc

theorem goodLosers_card_le {m n : ℕ} {family : Fin m → Language} {input : Stream}
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    (goodLosers family input n).card ≤
      (GenLimit.PatientScope.prefixFinset
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j) n).card := by
  let G := goodLosers family input n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j) n
  let f : {z // z ∈ G} → {y // y ∈ D} := fun z =>
    ⟨pairedValue family input z, by
      have hzlate := (Finset.mem_filter.mp z.2).1
      have hzgood := (Finset.mem_filter.mp z.2).2
      have hzloser := (Finset.mem_filter.mp hzlate).1
      obtain ⟨_, hzcore, hznot, hzin⟩ := loser_mem_data hcore hzloser
      apply mem_prefixFinset.mpr
      refine ⟨hzgood, ?_, ?_⟩
      · simpa [pairedValue, firstInputDefault_eq hzin] using
          paired_output_generatorFirst hcore hzcore hznot
            (by simpa [firstInputDefault_eq hzin] using (Finset.mem_filter.mp hzlate).2)
      · have hav := trajectory_available
          (by simpa [firstInputDefault_eq hzin] using (Finset.mem_filter.mp hzlate).2) hcore
        have hcm := (viable_iff_core
          (by simpa [firstInputDefault_eq hzin] using (Finset.mem_filter.mp hzlate).2) _).1 hav.1
        simpa [pairedValue, firstInputDefault_eq hzin] using hcm j hj⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have halate := (Finset.mem_filter.mp a.2).1
    have hblate := (Finset.mem_filter.mp b.2).1
    have haL := (Finset.mem_filter.mp halate).1
    have hbL := (Finset.mem_filter.mp hblate).1
    obtain ⟨_, hacore, hanot, hain⟩ := loser_mem_data hcore haL
    obtain ⟨_, hbcore, hbnot, hbin⟩ := loser_mem_data hcore hbL
    have hout : pairedValue family input a.1 = pairedValue family input b.1 :=
      congrArg Subtype.val hab
    have htime : firstInputDefault input a.1 = firstInputDefault input b.1 := by
      apply trajectory_post_injective hcore
      · exact (Finset.mem_filter.mp halate).2
      · exact (Finset.mem_filter.mp hblate).2
      · simpa [pairedValue] using hout
    calc
      a.1 = input (firstInputDefault input a.1) := by
        rw [firstInputDefault_eq hain]
        exact (firstInput_spec hain).symm
      _ = input (firstInputDefault input b.1) := by rw [htime]
      _ = b.1 := by
        rw [firstInputDefault_eq hbin]
        exact firstInput_spec hbin
  have hc := Fintype.card_le_of_injective f hf
  simpa [G, D] using hc

theorem badLosers_card_le_one {m n : ℕ} {family : Fin m → Language} {input : Stream}
    (hcore : (informationCore family input).Infinite) :
    (badLosers family input n).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz w hw
  have hzlate := (Finset.mem_filter.mp hz).1
  have hwlate := (Finset.mem_filter.mp hw).1
  have hzL := (Finset.mem_filter.mp hzlate).1
  have hwL := (Finset.mem_filter.mp hwlate).1
  obtain ⟨hzn, hzcore, hznot, hzin⟩ := loser_mem_data hcore hzL
  obtain ⟨hwn, hwcore, hwnot, hwin⟩ := loser_mem_data hcore hwL
  apply crossing_unique hcore hzcore hwcore hznot hwnot
  · simpa [firstInputDefault_eq hzin] using (Finset.mem_filter.mp hzlate).2
  · simpa [firstInputDefault_eq hwin] using (Finset.mem_filter.mp hwlate).2
  · exact hzn
  · exact hwn
  · simpa [pairedValue, firstInputDefault_eq hzin] using (Finset.mem_filter.mp hz).2
  · simpa [pairedValue, firstInputDefault_eq hwin] using (Finset.mem_filter.mp hw).2

theorem loserPrefix_card_le {m n : ℕ} {family : Fin m → Language} {input : Stream}
    (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    (loserPrefix family input n).card ≤
      stableTime family input +
      (GenLimit.PatientScope.prefixFinset
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j) n).card + 1 := by
  have hearly := earlyLosers_card_le (n := n) hinj hcore
  have hgood := goodLosers_card_le (n := n) hcore j hj
  have hbad := badLosers_card_le_one (n := n) hcore
  have hsplit1 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := loserPrefix family input n)
    (fun z => firstInputDefault input z < stableTime family input)
  have hsplit2 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := lateLosers family input n) (fun z => pairedValue family input z < n)
  have hlate : (lateLosers family input n).card =
      (goodLosers family input n).card + (badLosers family input n).card := by
    simpa [goodLosers, badLosers, not_lt] using hsplit2.symm
  have hall : (loserPrefix family input n).card =
      (earlyLosers family input n).card + (lateLosers family input n).card := by
    simpa [earlyLosers, lateLosers, not_lt] using hsplit1.symm
  omega


theorem core_prefixCount_le {m n : ℕ} {family : Fin m → Language} {input : Stream}
    (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j) n +
      stableTime family input + 1 := by
  classical
  let C := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j) n
  let W := C.filter
    (fun z => z ∈ GenLimit.GeneratorFirst input (trajectory (generator family) input))
  have hW : W.card ≤ D.card := by
    apply Finset.card_le_card
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact mem_prefixFinset.mpr ⟨(mem_prefixFinset.mp hz'.1).1, hz'.2,
      (mem_prefixFinset.mp hz'.1).2 j hj⟩
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := C) (fun z => z ∈ GenLimit.GeneratorFirst input
      (trajectory (generator family) input))
  have hloser : (loserPrefix family input n).card ≤
      stableTime family input + D.card + 1 := by
    simpa [D, GenLimit.PatientScope.prefixCount] using loserPrefix_card_le hinj hcore j hj
  have hdecomp : C.card = W.card + (loserPrefix family input n).card := by
    simpa [W, C, loserPrefix] using hsplit.symm
  simp only [GenLimit.PatientScope.prefixCount]
  change C.card ≤ 2 * D.card + stableTime family input + 1
  omega

theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  apply Finset.card_le_card
  intro z hz
  exact mem_prefixFinset.mpr ⟨(mem_prefixFinset.mp hz).1, hAB (mem_prefixFinset.mp hz).2⟩

theorem ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

theorem ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · have hAzero : GenLimit.PatientScope.prefixCount A n = 0 :=
      Nat.eq_zero_of_le_zero (hzero ▸ prefixCount_mono hAK n)
    simp [hzero, hAzero]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)).2
    exact_mod_cast prefixCount_mono hAK n

theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_mono hAB n)
        (by positivity)
  · exact isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => ratio_nonneg A K n)
  · exact (isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun n => ratio_le_one hBK n)).isCobounded_flip
 theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => GenLimit.PatientScope.prefixCount K n) atTop atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) (r := 1) Nat.zero_lt_one] at hK
  convert hK using 1
  funext n
  simp only [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxK : x ∈ K
  · simp [hxK, Set.indicator_of_mem]
  · simp [hxK, Set.indicator_of_notMem]

theorem half_density_of_prefix_bound {A B K : Set ℕ}
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hK : K.Infinite) (C : ℕ)
    (hcount : ∀ n, GenLimit.PatientScope.prefixCount A n ≤
      2 * GenLimit.PatientScope.prefixCount B n + C) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  let a : ℕ → ℝ := fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)
  let b : ℕ → ℝ := fun n => (GenLimit.PatientScope.prefixCount B n : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n => (C : ℝ) /
    (GenLimit.PatientScope.prefixCount K n : ℝ)
  have ha0 : ∀ n, 0 ≤ a n := fun n => ratio_nonneg A K n
  have hb0 : ∀ n, 0 ≤ b n := fun n => ratio_nonneg B K n
  have he0 : ∀ n, 0 ≤ e n := by intro n; dsimp [e]; positivity
  have ha1 : ∀ n, a n ≤ 1 := fun n => ratio_le_one hAK n
  have hb1 : ∀ n, b n ≤ 1 := fun n => ratio_le_one hBK n
  have heC : ∀ n, e n ≤ (C : ℝ) := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [e, hzero]
    · have hkone : (1 : ℝ) ≤ GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      dsimp [e]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have herr : Tendsto e atTop (nhds 0) := by
    dsimp [e]
    exact Filter.Tendsto.const_div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (prefixCount_tendsto_atTop hK)) C
  have hpoint : ∀ n, (1 / 2 : ℝ) * a n ≤ e n + b n := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [a, b, e, hzero]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by positivity
      have hc : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount B n : ℝ) + C := by
        exact_mod_cast hcount n
      dsimp [a, b, e]
      rw [← add_div]
      calc
        (1 / 2 : ℝ) * ((GenLimit.PatientScope.prefixCount A n : ℝ) /
            GenLimit.PatientScope.prefixCount K n) =
            ((1 / 2 : ℝ) * GenLimit.PatientScope.prefixCount A n) /
              GenLimit.PatientScope.prefixCount K n := by ring
        _ ≤ (C + GenLimit.PatientScope.prefixCount B n) /
              GenLimit.PatientScope.prefixCount K n := by
          apply (div_le_div_iff₀ hkpos hkpos).2
          nlinarith [show (0 : ℝ) ≤ C by positivity]
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) * liminf a atTop ≤ liminf b atTop
  calc
    (1 / 2 : ℝ) * liminf a atTop ≤
        liminf (fun n => (1 / 2 : ℝ) * a n) atTop := by
      have hconst : liminf (fun _ : ℕ => (1 / 2 : ℝ)) atTop = 1 / 2 :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2))).liminf_eq
      calc
        (1 / 2 : ℝ) * liminf a atTop =
            liminf (fun _ : ℕ => (1 / 2 : ℝ)) atTop * liminf a atTop := by rw [hconst]
        _ ≤ liminf ((fun _ : ℕ => (1 / 2 : ℝ)) * a) atTop := by
          apply le_liminf_mul
          · exact Eventually.of_forall fun _ => by norm_num
          · exact isBoundedUnder_of_eventually_le
              (Eventually.of_forall fun _ => show (1 / 2 : ℝ) ≤ 1 by norm_num)
          · exact Eventually.of_forall ha0
          · exact (isBoundedUnder_of_eventually_le (Eventually.of_forall ha1)).isCobounded_flip
        _ = liminf (fun n => (1 / 2 : ℝ) * a n) atTop := by rfl
    _ ≤ liminf (fun n => e n + b n) atTop := by
      apply Filter.liminf_le_liminf
      · exact Eventually.of_forall hpoint
      · exact isBoundedUnder_of_eventually_ge
          (Eventually.of_forall fun n => mul_nonneg (by norm_num) (ha0 n))
      · exact (isBoundedUnder_of_eventually_le (a := (C : ℝ) + 1)
          (Eventually.of_forall fun n => by nlinarith [heC n, hb1 n])).isCobounded_flip
    _ ≤ limsup e atTop + liminf b atTop := by
      apply liminf_add_le
      · exact isBoundedUnder_of_eventually_ge (Eventually.of_forall he0)
      · exact isBoundedUnder_of_eventually_le (Eventually.of_forall heC)
      · exact isBoundedUnder_of_eventually_ge (Eventually.of_forall hb0)
      · exact (isBoundedUnder_of_eventually_le (Eventually.of_forall hb1)).isCobounded_flip
    _ = liminf b atTop := by rw [herr.limsup_eq]; simp

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.generator family, ?_⟩
  intro input hinj hpresentation hcore
  let output := Stage3Case017Proof.trajectory
    (Stage3Case017Proof.generator family) input
  refine ⟨output, Stage3Case017Proof.trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨Stage3Case017Proof.eventual_novel hcore j hj, ?_⟩
  apply max_le
  · apply Stage3Case017Proof.half_density_of_prefix_bound
      (A := Stage3Case017.informationCore family input)
      (B := GenLimit.GeneratorFirst input output ∩ family j)
      (K := family j)
      (C := Stage3Case017Proof.stableTime family input + 1)
    · intro z hz
      exact hz j hj
    · intro z hz
      exact hz.2
    · exact hfamily j
    · intro n
      have hbound := Stage3Case017Proof.core_prefixCount_le
        (n := n) hinj hcore j hj
      simpa [output] using hbound
  · apply Stage3Case017Proof.relativeLowerDensity_mono
    · intro z hz
      refine ⟨?_, hz.1 j hj⟩
      simpa [output] using
        (Stage3Case017Proof.missing_core_subset_generatorFirst hcore hz)
    · intro z hz
      exact hz.2
