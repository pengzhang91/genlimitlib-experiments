import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

noncomputable section

def prefixCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin t → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

def seen {t : ℕ} (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Finset ℕ := by
  classical
  exact GenLimit.Generic.sequenceSample xs ∪ GenLimit.Generic.sequenceSample ys

def leastFresh (C : Set ℕ) (hC : C.Infinite) (S : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (hC.exists_notMem_finset S)

theorem leastFresh_spec (C : Set ℕ) (hC : C.Infinite) (S : Finset ℕ) :
    leastFresh C hC S ∈ C ∧ leastFresh C hC S ∉ S := by
  classical
  exact Nat.find_spec (hC.exists_notMem_finset S)

theorem leastFresh_min (C : Set ℕ) (hC : C.Infinite) (S : Finset ℕ)
    {z : ℕ} (hzC : z ∈ C) (hzS : z ∉ S) :
    leastFresh C hC S ≤ z := by
  classical
  exact Nat.find_min' (hC.exists_notMem_finset S) ⟨hzC, hzS⟩

def generator {m : ℕ} (family : Fin m → Language) : OnlineGenerator := by
  classical
  exact fun t xs ys =>
    let C := prefixCore family xs
    if hC : C.Infinite then
      leastFresh C hC (seen xs ys)
    else
      leastFresh Set.univ Set.infinite_univ (seen xs ys)

theorem generator_not_seen {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    generator family t xs ys ∉ seen xs ys := by
  classical
  simp only [generator]
  split <;> exact (leastFresh_spec _ _ _).2

theorem generator_mem_of_infinite {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (prefixCore family xs).Infinite) :
    generator family t xs ys ∈ prefixCore family xs := by
  classical
  simp only [generator]
  rw [dif_pos hC]
  exact (leastFresh_spec _ _ _).1

theorem generator_le_of_available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (prefixCore family xs).Infinite) {z : ℕ}
    (hzC : z ∈ prefixCore family xs) (hz : z ∉ seen xs ys) :
    generator family t xs ys ≤ z := by
  classical
  simp only [generator]
  rw [dif_pos hC]
  exact leastFresh_min _ _ _ hzC hz

def states {m : ℕ} (family : Fin m → Language) (input : Stream) : ℕ → Stream
  | 0 => fun _ => 0
  | t + 1 => Function.update (states family input t) t
      (generator family t (fun i => input i)
        (fun i => states family input t i))

def trajectory {m : ℕ} (family : Fin m → Language) (input : Stream) : Stream :=
  fun t => states family input (t + 1) t

theorem states_stable {m : ℕ} (family : Fin m → Language) (input : Stream)
    {i n : ℕ} (hi : i < n) :
    states family input n i = trajectory family input i := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [states]
      by_cases hin : i = n
      · subst i
        simp [trajectory, states]
      · simp only [Function.update, hin, if_false]
        exact ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hin)

theorem trajectory_follows {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Follows (generator family) input (trajectory family input) := by
  intro t
  change states family input (t + 1) t =
    generator family t (fun i => input i) (fun i => trajectory family input i)
  rw [states, Function.update_self]
  congr
  funext i
  exact states_stable family input i.isLt

theorem prefixCore_eq_informationCore_eventually {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  let C : GenLimit.LanguageFamily := fun i =>
    if hi : i < m then family ⟨i, hi⟩ else ∅
  obtain ⟨T, hT⟩ :=
    GenLimit.finite_scope_eventually_consistent_iff_presented_subset
      (C := C) (stream := input) (E := Set.range input) rfl m
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact hj ⟨i, rfl⟩
  · intro hz j hj
    apply hz j
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    have hcon : GenLimit.Consistent C input (t + 1) j := by
      intro x hxsample
      have hxsample' : x ∈ GenLimit.sample input (t + 1) := hxsample
      rw [GenLimit.mem_sample_iff] at hxsample'
      obtain ⟨q, hq, rfl⟩ := hxsample'
      simpa only [C, dif_pos j.isLt] using hj ⟨q, by omega⟩
    have hsub := (hT (t + 1) (by omega) j j.isLt).mp hcon
    simpa only [C, dif_pos j.isLt] using hsub ⟨i, rfl⟩

theorem sequenceSample_input_eq_sample (input : Stream) (t : ℕ) :
    GenLimit.Generic.sequenceSample (fun i : Fin t => input i) =
      GenLimit.Generic.sample input t :=
  GenLimit.Generic.sequenceSample_prefix input t

theorem output_fresh {m : ℕ} (family : Fin m → Language)
    {input output : Stream} (hfollow : Follows (generator family) input output)
    (t : ℕ) :
    output t ∉ GenLimit.Generic.sample input (t + 1) ∧
      ∀ s, s < t → output s ≠ output t := by
  have hnot := generator_not_seen family
    (fun i : Fin (t + 1) => input i) (fun i : Fin t => output i)
  rw [← hfollow t] at hnot
  constructor
  · intro hmem
    apply hnot
    apply Finset.mem_union_left
    rw [sequenceSample_input_eq_sample]
    exact hmem
  · intro s hs heq
    apply hnot
    apply Finset.mem_union_right
    rw [GenLimit.Generic.mem_sequenceSample_iff]
    exact ⟨⟨s, hs⟩, heq⟩


theorem output_injective {m : ℕ} (family : Fin m → Language)
    {input output : Stream} (hfollow : Follows (generator family) input output) :
    Function.Injective output := by
  intro a b hab
  by_cases h : a = b
  · exact h
  rcases lt_or_gt_of_ne h with hablt | hbalt
  · exact False.elim ((output_fresh family hfollow b).2 a hablt hab)
  · exact False.elim ((output_fresh family hfollow a).2 b hbalt hab.symm)

theorem core_eventually_output_or_input {m : ℕ} (family : Fin m → Language)
    {input output : Stream} (hfollow : Follows (generator family) input output)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hz : z ∈ informationCore family input) :
    z ∈ Set.range input ∪ Set.range output := by
  classical
  by_contra hnot
  have hzInput : z ∉ Set.range input := fun h => hnot (Set.mem_union_left _ h)
  have hzOutput : z ∉ Set.range output := fun h => hnot (Set.mem_union_right _ h)
  let f : Fin (z + 2) → Fin (z + 1) := fun k =>
    ⟨output (T + k), by
      have htime : T ≤ T + k := Nat.le_add_right _ _
      have hCeq := hstable (T + k) htime
      have hC : (prefixCore family
          (fun i : Fin (T + k + 1) => input i)).Infinite := by
        rw [hCeq]
        exact hcore
      have hzC : z ∈ prefixCore family
          (fun i : Fin (T + k + 1) => input i) := by
        rw [hCeq]
        exact hz
      have hzSeen : z ∉ seen
          (fun i : Fin (T + k + 1) => input i)
          (fun i : Fin (T + k) => output i) := by
        intro hseen
        rcases Finset.mem_union.mp hseen with hin | hout
        · rw [GenLimit.Generic.mem_sequenceSample_iff] at hin
          obtain ⟨i, hi⟩ := hin
          exact hzInput ⟨i, hi⟩
        · rw [GenLimit.Generic.mem_sequenceSample_iff] at hout
          obtain ⟨i, hi⟩ := hout
          exact hzOutput ⟨i, hi⟩
      have hle := generator_le_of_available family
        (fun i : Fin (T + k + 1) => input i)
        (fun i : Fin (T + k) => output i) hC hzC hzSeen
      rw [← hfollow (T + k)] at hle
      omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hadd : T + a = T + b := by
      apply (output_injective family hfollow)
      exact congrArg Fin.val hab
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard


def firstInput (input : Stream) (x : ℕ) : ℕ := by
  classical
  exact if hx : x ∈ Set.range input then Nat.find hx else 0

theorem firstInput_spec {input : Stream} {x : ℕ} (hx : x ∈ Set.range input) :
    input (firstInput input x) = x := by
  classical
  simp only [firstInput, dif_pos hx]
  exact Nat.find_spec hx

theorem firstInput_min {input : Stream} {x : ℕ} (hx : x ∈ Set.range input)
    {q : ℕ} (hq : input q = x) : firstInput input x ≤ q := by
  classical
  simp only [firstInput, dif_pos hx]
  exact Nat.find_min' hx hq

theorem adversaryFirst_range {input output : Stream} {x : ℕ}
    (hx : x ∈ GenLimit.AdversaryFirst input output) : x ∈ Set.range input := by
  obtain ⟨t, ht, -⟩ := hx
  exact ⟨t, ht⟩

theorem adversaryFirst_no_output_before_firstInput {input output : Stream} {x : ℕ}
    (hx : x ∈ GenLimit.AdversaryFirst input output) {s : ℕ}
    (hs : s < firstInput input x) : output s ≠ x := by
  have hxrange := adversaryFirst_range hx
  obtain ⟨t, ht, hnone⟩ := hx
  apply hnone s
  exact lt_of_lt_of_le hs (firstInput_min hxrange ht)

theorem generatorFirst_of_output {m : ℕ} (family : Fin m → Language)
    {input output : Stream} (hfollow : Follows (generator family) input output)
    (t : ℕ) : output t ∈ GenLimit.GeneratorFirst input output := by
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  exact (output_fresh family hfollow t).1
    (GenLimit.Generic.mem_sample_iff.mpr ⟨s, by omega, heq⟩)

theorem early_attacker_card_le {input output : Stream}
    (hinj : Function.Injective input) (T n : ℕ) :
    ((GenLimit.PatientScope.prefixFinset
      (GenLimit.AdversaryFirst input output) n).filter
        (fun x => firstInput input x < T)).card ≤ T := by
  classical
  let A := (GenLimit.PatientScope.prefixFinset
      (GenLimit.AdversaryFirst input output) n).filter
        (fun x => firstInput input x < T)
  let f : A → Fin T := fun x => ⟨firstInput input x, by
    exact (Finset.mem_filter.mp x.property).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxadv := (GenLimit.PatientScope.mem_prefixFinset.mp
      (Finset.mem_filter.mp x.property).1).2
    have hyadv := (GenLimit.PatientScope.mem_prefixFinset.mp
      (Finset.mem_filter.mp y.property).1).2
    calc
      x = input (firstInput input x) :=
        (firstInput_spec (adversaryFirst_range hxadv)).symm
      _ = input (firstInput input y) := congrArg input (congrArg Fin.val hxy)
      _ = y := firstInput_spec (adversaryFirst_range hyadv)
  simpa [A] using Fintype.card_le_of_injective f hf

theorem late_attacker_card_le {m : ℕ} (family : Fin m → Language)
    {input output : Stream} (hinj : Function.Injective input)
    (hfollow : Follows (generator family) input output)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    (((GenLimit.PatientScope.prefixFinset
      (GenLimit.AdversaryFirst input output ∩ informationCore family input) n).filter
        (fun x => T ≤ firstInput input x)).card) ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ family j) n + 1 := by
  classical
  let A := (GenLimit.PatientScope.prefixFinset
      (GenLimit.AdversaryFirst input output ∩ informationCore family input) n).filter
        (fun x => T ≤ firstInput input x)
  by_cases hA : A.Nonempty
  · obtain ⟨last, hlast, hmax⟩ := Finset.exists_max_image A (firstInput input) hA
    let B := A.erase last
    let f : B → GenLimit.PatientScope.prefixFinset
        (GenLimit.GeneratorFirst input output ∩ family j) n := fun x =>
      ⟨output (firstInput input x), by
        have hxA := (Finset.mem_erase.mp x.property).2
        have hxlate := (Finset.mem_filter.mp hxA).2
        have hxprefix := GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hxA).1
        have hlastPrefix := GenLimit.PatientScope.mem_prefixFinset.mp
          (Finset.mem_filter.mp hlast).1
        have hle := hmax x hxA
        have hneTime : firstInput input x ≠ firstInput input last := by
          intro heq
          apply (Finset.mem_erase.mp x.property).1
          calc
            x = input (firstInput input x) :=
              (firstInput_spec (adversaryFirst_range hxprefix.2.1)).symm
            _ = input (firstInput input last) := congrArg input heq
            _ = last := firstInput_spec (adversaryFirst_range hlastPrefix.2.1)
        have hltTime : firstInput input x < firstInput input last :=
          lt_of_le_of_ne hle hneTime
        have hlastNotSeen : last ∉ seen
            (fun i : Fin (firstInput input x + 1) => input i)
            (fun i : Fin (firstInput input x) => output i) := by
          intro hseen
          rcases Finset.mem_union.mp hseen with hin | hout
          · rw [GenLimit.Generic.mem_sequenceSample_iff] at hin
            obtain ⟨q, hq⟩ := hin
            have hmin := firstInput_min
              (adversaryFirst_range hlastPrefix.2.1) hq
            omega
          · rw [GenLimit.Generic.mem_sequenceSample_iff] at hout
            obtain ⟨q, hq⟩ := hout
            exact adversaryFirst_no_output_before_firstInput
              hlastPrefix.2.1 (lt_trans q.isLt hltTime) hq
        have hCeq := hstable (firstInput input x) hxlate
        have hC : (prefixCore family
            (fun i : Fin (firstInput input x + 1) => input i)).Infinite := by
          rw [hCeq]
          exact hcore
        have hlastC : last ∈ prefixCore family
            (fun i : Fin (firstInput input x + 1) => input i) := by
          rw [hCeq]
          exact hlastPrefix.2.2
        have houtle := generator_le_of_available family
          (fun i : Fin (firstInput input x + 1) => input i)
          (fun i : Fin (firstInput input x) => output i)
          hC hlastC hlastNotSeen
        rw [← hfollow (firstInput input x)] at houtle
        apply GenLimit.PatientScope.mem_prefixFinset.mpr
        refine ⟨lt_of_le_of_lt houtle hlastPrefix.1,
          generatorFirst_of_output family hfollow _, ?_⟩
        have houtC := generator_mem_of_infinite family
          (fun i : Fin (firstInput input x + 1) => input i)
          (fun i : Fin (firstInput input x) => output i) hC
        rw [← hfollow (firstInput input x), hCeq] at houtC
        exact houtC j hj⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hxadv := (GenLimit.PatientScope.mem_prefixFinset.mp
        (Finset.mem_filter.mp (Finset.mem_erase.mp x.property).2).1).2.1
      have hyadv := (GenLimit.PatientScope.mem_prefixFinset.mp
        (Finset.mem_filter.mp (Finset.mem_erase.mp y.property).2).1).2.1
      have htime : firstInput input x = firstInput input y := by
        apply (output_injective family hfollow)
        exact congrArg Subtype.val hxy
      calc
        x = input (firstInput input x) :=
          (firstInput_spec (adversaryFirst_range hxadv)).symm
        _ = input (firstInput input y) := congrArg input htime
        _ = y := firstInput_spec (adversaryFirst_range hyadv)
    have hB : B.card ≤ GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ family j) n := by
      simpa [B, GenLimit.PatientScope.prefixCount] using
        Fintype.card_le_of_injective f hf
    have hcard := Finset.card_erase_add_one hlast
    change A.card ≤ _
    rw [← hcard]
    exact Nat.add_le_add_right hB 1
  · have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [A, this]


theorem core_sub {m : ℕ} {family : Fin m → Language}
    {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j :=
  fun _ hz => hz j hj

theorem announced_first {input output : Stream} {x : ℕ}
    (hx : x ∈ Set.range input ∪ Set.range output) :
    x ∈ GenLimit.AdversaryFirst input output ∪
      GenLimit.GeneratorFirst input output := by
  rcases hx with hx | hx
  · exact GenLimit.range_subset_first_announcements input output hx
  · by_cases hxin : x ∈ Set.range input
    · exact GenLimit.range_subset_first_announcements input output hxin
    · right
      let t := Nat.find hx
      refine ⟨t, Nat.find_spec hx, ?_⟩
      intro s hs heq
      exact hxin ⟨s, heq⟩

theorem core_prefix_counting {m : ℕ} (family : Fin m → Language)
    {input output : Stream} (hinj : Function.Injective input)
    (hfollow : Follows (generator family) input output)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ family j) n + T + 1 := by
  classical
  let P := GenLimit.PatientScope.prefixFinset
    (informationCore family input) n
  let A := GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ family j) n
  have hcover : P ⊆ A ∪ D := by
    intro x hx
    have hxP := GenLimit.PatientScope.mem_prefixFinset.mp hx
    have hann := core_eventually_output_or_input family hfollow hstable hcore hxP.2
    rcases announced_first hann with hxA | hxD
    · apply Finset.mem_union_left
      exact GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxP.1, hxA, hxP.2⟩
    · apply Finset.mem_union_right
      exact GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hxP.1, hxD, (core_sub hj) hxP.2⟩
  have hPA : P.card ≤ A.card + D.card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  let AE := A.filter (fun x => firstInput input x < T)
  let AL := A.filter (fun x => T ≤ firstInput input x)
  have hsplit : AE.card + AL.card = A.card := by
    rw [show AL = A.filter (fun x => ¬ firstInput input x < T) by
      ext x
      simp [AL]]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hAE : AE.card ≤ T := by
    have hsub : AE ⊆
        (GenLimit.PatientScope.prefixFinset
          (GenLimit.AdversaryFirst input output) n).filter
            (fun x => firstInput input x < T) := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨?_, hx'.2⟩
      have hxA := GenLimit.PatientScope.mem_prefixFinset.mp hx'.1
      exact GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hxA.1, hxA.2.1⟩
    exact le_trans (Finset.card_le_card hsub)
      (early_attacker_card_le hinj T n)
  have hAL : AL.card ≤ D.card + 1 := by
    simpa [AL, A, D, GenLimit.PatientScope.prefixCount] using
      late_attacker_card_le family hinj hfollow hstable hcore hj n
  change P.card ≤ 2 * D.card + T + 1
  calc
    P.card ≤ A.card + D.card := hPA
    _ = AE.card + AL.card + D.card := by omega
    _ ≤ T + (D.card + 1) + D.card := by omega
    _ = 2 * D.card + T + 1 := by omega

theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      have hc := GenLimit.PatientScope.prefixCount_mono hAB n
      gcongr
  · apply isBoundedUnder_of_eventually_ge
    exact Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hratio : ∀ n,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
      intro n
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
    exact isCoboundedUnder_ge_of_le atTop hratio

theorem density_bounds {m : ℕ} (family : Fin m → Language)
    {input output : Stream} (hinj : Function.Injective input)
    (hfollow : Follows (generator family) input output)
    {T : ℕ}
    (hstable : ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
  have hhalf : (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
      (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    apply GenLimit.PatientScope.partialDensity_of_counting
      (GenLimit.PatientScope.prefixCount (family j))
      (GenLimit.PatientScope.prefixCount (informationCore family input))
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ family j)) (T + 1)
    · exact GenLimit.PatientScope.tendsto_prefixCount_atTop
        (hcore.mono (core_sub hj))
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono (core_sub hj) n
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
    · intro n
      have h := core_prefix_counting family hinj hfollow hstable hcore hj n
      omega
  have hmissing : informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input output ∩ family j := by
    intro z hz
    have hann := core_eventually_output_or_input family hfollow hstable hcore hz.1
    have hzout : z ∈ Set.range output := by
      rcases hann with hzin | hzout
      · exact False.elim (hz.2 hzin)
      · exact hzout
    obtain ⟨t, ht⟩ := hzout
    refine ⟨⟨t, ht, ?_⟩, (core_sub hj) hz.1⟩
    intro s hs heq
    exact hz.2 ⟨s, heq⟩
  exact max_le hhalf (relativeLowerDensity_mono hmissing Set.inter_subset_right)

theorem core_subset_target {m : ℕ} {family : Fin m → Language}
    {input : Stream} {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    informationCore family input ⊆ family j :=
  fun _ hz => hz j hj

end

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.generator family, ?_⟩
  intro input hinj hpresentation hcore
  let output := Stage3Case017Proof.trajectory family input
  have hfollow : Stage3Case017.Follows
      (Stage3Case017Proof.generator family) input output :=
    Stage3Case017Proof.trajectory_follows family input
  obtain ⟨T, hstable⟩ :=
    Stage3Case017Proof.prefixCore_eq_informationCore_eventually family input
  refine ⟨output, hfollow, ?_⟩
  intro j hj
  constructor
  · refine ⟨T, ?_⟩
    intro t ht
    have hCeq := hstable t ht
    have hC : (Stage3Case017Proof.prefixCore family
        (fun i : Fin (t + 1) => input i)).Infinite := by
      rw [hCeq]
      exact hcore
    have houtC := Stage3Case017Proof.generator_mem_of_infinite family
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i) hC
    rw [← hfollow t, hCeq] at houtC
    have hfresh := Stage3Case017Proof.output_fresh family hfollow t
    refine ⟨houtC j hj, ?_, hfresh.2⟩
    intro hsample
    apply hfresh.1
    rw [GenLimit.Generic.mem_sample_iff]
    rw [GenLimit.mem_sample_iff] at hsample
    exact hsample
  · exact Stage3Case017Proof.density_bounds family hinj hfollow
      hstable hcore hj
