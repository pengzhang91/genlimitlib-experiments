import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter

namespace Stage3Case017Proof

open GenLimit
open GenLimit.Generic
open GenLimit.PatientScope
open Stage3Case017

noncomputable def historySet {n : ℕ} (xs : Fin n → ℕ) : Finset ℕ :=
  sequenceSample xs

def roundCore {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) : Set ℕ :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

theorem exists_fresh (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    ∃ z, z ∈ C ∧ z ∉ seen := by
  have hnonempty := (hC.diff seen.finite_toSet).nonempty
  simpa only [Set.mem_diff, Finset.mem_coe] using hnonempty

noncomputable def leastFresh (C : Set ℕ) (hC : C.Infinite)
    (seen : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (exists_fresh C hC seen)

theorem leastFresh_mem (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFresh C hC seen ∈ C := by
  classical
  exact (Nat.find_spec (exists_fresh C hC seen)).1

theorem leastFresh_not_mem (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ) :
    leastFresh C hC seen ∉ seen := by
  classical
  exact (Nat.find_spec (exists_fresh C hC seen)).2

theorem leastFresh_le (C : Set ℕ) (hC : C.Infinite) (seen : Finset ℕ)
    {z : ℕ} (hzC : z ∈ C) (hzseen : z ∉ seen) :
    leastFresh C hC seen ≤ z := by
  classical
  exact Nat.find_min' (exists_fresh C hC seen) ⟨hzC, hzseen⟩

noncomputable def generator {m : ℕ} (family : Fin m → Set ℕ) : OnlineGenerator := by
  classical
  exact fun t xs ys =>
    let C := roundCore family xs
    let seen := historySet xs ∪ historySet ys
    if hC : C.Infinite then leastFresh C hC seen
    else leastFresh Set.univ Set.infinite_univ seen

theorem generator_not_input {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    generator family t xs ys ∉ historySet xs := by
  classical
  unfold generator
  dsimp only
  split_ifs with hC
  · exact fun h => leastFresh_not_mem _ hC _ (Finset.mem_union_left _ h)
  · exact fun h => leastFresh_not_mem _ Set.infinite_univ _ (Finset.mem_union_left _ h)

theorem generator_not_output {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) :
    generator family t xs ys ∉ historySet ys := by
  classical
  unfold generator
  dsimp only
  split_ifs with hC
  · exact fun h => leastFresh_not_mem _ hC _ (Finset.mem_union_right _ h)
  · exact fun h => leastFresh_not_mem _ Set.infinite_univ _ (Finset.mem_union_right _ h)

theorem generator_mem_of_infinite {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (roundCore family xs).Infinite) :
    generator family t xs ys ∈ roundCore family xs := by
  classical
  simp [generator, hC, leastFresh_mem]

theorem generator_le_of_available {m t : ℕ} (family : Fin m → Set ℕ)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (hC : (roundCore family xs).Infinite) {z : ℕ}
    (hzC : z ∈ roundCore family xs)
    (hzx : z ∉ historySet xs) (hzy : z ∉ historySet ys) :
    generator family t xs ys ≤ z := by
  classical
  simp only [generator, hC, dif_pos]
  apply leastFresh_le _ hC _ hzC
  simp only [Finset.mem_union, not_or]
  exact ⟨hzx, hzy⟩



def run (gen : OnlineGenerator) (input : Stream) : Stream
  | 0 => gen 0 (fun i => input i) (fun i => Fin.elim0 i)
  | t + 1 => gen (t + 1) (fun i => input i) (fun i => run gen input i)

theorem run_eq (gen : OnlineGenerator) (input : Stream) (t : ℕ) :
    run gen input t = gen t (fun i => input i) (fun i => run gen input i) := by
  cases t with
  | zero =>
      rw [run.eq_1]
      congr
      funext i
      exact Fin.elim0 i
  | succ t =>
      rw [run.eq_2]

theorem follows_run (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  exact run_eq gen input t

theorem historySet_input (input : Stream) (t : ℕ) :
    historySet (fun i : Fin t => input i) = Generic.sample input t := by
  exact Generic.sequenceSample_prefix input t

theorem run_fresh_input {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) (t : ℕ) :
    run (generator family) input t ∉ Generic.sample input (t + 1) := by
  rw [run_eq, ← historySet_input]
  exact generator_not_input family _ _

theorem run_fresh_output {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) {s t : ℕ} (hst : s < t) :
    run (generator family) input s ≠ run (generator family) input t := by
  intro heq
  have hmem : run (generator family) input s ∈
      historySet (fun i : Fin t => run (generator family) input i) := by
    unfold historySet
    rw [Generic.mem_sequenceSample_iff]
    exact ⟨⟨s, hst⟩, rfl⟩
  have hnot : run (generator family) input t ∉
      historySet (fun i : Fin t => run (generator family) input i) := by
    rw [run_eq]
    exact generator_not_output family _ _
  exact hnot (heq ▸ hmem)

theorem run_injective {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) : Function.Injective (run (generator family) input) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact run_fresh_output family input hlt hst
  · exact run_fresh_output family input hgt hst.symm


theorem not_streamIn_exists {input : Stream} {L : Set ℕ}
    (h : ¬ StreamIn input L) : ∃ s, input s ∉ L := by
  obtain ⟨x, ⟨s, rfl⟩, hx⟩ := Set.not_subset.mp h
  exact ⟨s, hx⟩

theorem eventually_roundCore_eq_informationCore {m : ℕ}
    (family : Fin m → Set ℕ) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      roundCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  let badTime : Fin m → ℕ := fun j =>
    if h : ¬ StreamIn input (family j) then
      Classical.choose (not_streamIn_exists h)
    else 0
  let T := ∑ j : Fin m, (badTime j + 1)
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  simp only [roundCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact hj ⟨i, rfl⟩
  · intro hz j hjprefix
    apply hz j
    intro x hxrange
    rcases hxrange with ⟨s, rfl⟩
    by_contra hnot
    have hbad : ¬ StreamIn input (family j) := by
      intro hall
      exact hnot (hall ⟨s, rfl⟩)
    have hchosen : input (badTime j) ∉ family j := by
      simp only [badTime, dif_pos hbad]
      exact Classical.choose_spec (not_streamIn_exists hbad)
    have hle : badTime j + 1 ≤ T := by
      apply Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hbadlt : badTime j < t :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (hle.trans ht)
    exact hchosen (hjprefix ⟨badTime j, hbadlt.trans (Nat.lt_succ_self t)⟩)

theorem run_generatorFirst {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) (t : ℕ) :
    run (generator family) input t ∈
      GenLimit.GeneratorFirst input (run (generator family) input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hst heq
  apply run_fresh_input family input t
  rw [Generic.mem_sample_iff]
  exact ⟨s, Nat.lt_succ_iff.mpr hst, heq⟩

theorem stable_run_mem {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) {T t : ℕ}
    (hstable : ∀ q, T ≤ q →
      roundCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hInf : (informationCore family input).Infinite) (ht : T ≤ t) :
    run (generator family) input t ∈ informationCore family input := by
  rw [run_eq]
  have hcore : (roundCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hstable t ht]
    exact hInf
  have hmem := generator_mem_of_infinite family
    (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => run (generator family) input i) hcore
  rwa [hstable t ht] at hmem

theorem stable_run_le {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) {T t z : ℕ}
    (hstable : ∀ q, T ≤ q →
      roundCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hInf : (informationCore family input).Infinite) (ht : T ≤ t)
    (hzI : z ∈ informationCore family input)
    (hzinput : z ∉ Generic.sample input (t + 1))
    (hzoutput : z ∉ Generic.sample (run (generator family) input) t) :
    run (generator family) input t ≤ z := by
  rw [run_eq]
  have hcore : (roundCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hstable t ht]
    exact hInf
  apply generator_le_of_available family _ _ hcore
  · rwa [hstable t ht]
  · rwa [historySet_input]
  · rwa [historySet_input]

theorem core_mem_generatorFirst_of_not_input {m : ℕ}
    (family : Fin m → Set ℕ) (input : Stream) {T z : ℕ}
    (hstable : ∀ q, T ≤ q →
      roundCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hInf : (informationCore family input).Infinite)
    (hzI : z ∈ informationCore family input)
    (hznotinput : z ∉ Set.range input) :
    z ∈ GenLimit.GeneratorFirst input (run (generator family) input) := by
  classical
  by_contra hznotGF
  have hznotoutput : z ∉ Set.range (run (generator family) input) := by
    rintro ⟨t, ht⟩
    exact hznotGF (ht ▸ run_generatorFirst family input t)
  have hrange : Set.range (run (generator family) input) ⊆
      (↑(Generic.sample (run (generator family) input) T ∪ Finset.range (z + 1)) : Set ℕ) := by
    rintro y ⟨t, rfl⟩
    by_cases ht : t < T
    · apply Finset.mem_union_left
      rw [Generic.mem_sample_iff]
      exact ⟨t, ht, rfl⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_range]
      apply Nat.lt_succ_iff.mpr
      apply stable_run_le family input hstable hInf (Nat.le_of_not_gt ht) hzI
      · intro hmem
        rw [Generic.mem_sample_iff] at hmem
        obtain ⟨s, -, hs⟩ := hmem
        exact hznotinput ⟨s, hs⟩
      · intro hmem
        rw [Generic.mem_sample_iff] at hmem
        obtain ⟨s, -, hs⟩ := hmem
        exact hznotoutput ⟨s, hs⟩
  exact (Set.infinite_range_of_injective (run_injective family input))
    ((Generic.sample (run (generator family) input) T ∪ Finset.range (z + 1)).finite_toSet.subset hrange)

theorem core_covered {m : ℕ} (family : Fin m → Set ℕ)
    (input : Stream) {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      roundCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hInf : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (run (generator family) input) ∪
        GenLimit.GeneratorFirst input (run (generator family) input) := by
  intro z hzI
  by_cases hzrange : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements
      input (run (generator family) input) hzrange
  · exact Set.mem_union_right _
      (core_mem_generatorFirst_of_not_input family input hstable hInf hzI hzrange)

noncomputable def firstTime (stream : ℕ → ℕ) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, stream t = z then Classical.choose h else 0

theorem firstTime_spec {stream : ℕ → ℕ} {z : ℕ} (hz : z ∈ Set.range stream) :
    stream (firstTime stream z) = z := by
  classical
  rcases hz with ⟨t, ht⟩
  have hex : ∃ q : ℕ, stream q = z := ⟨t, ht⟩
  simp only [firstTime, dif_pos hex]
  exact Classical.choose_spec hex

theorem firstTime_eq_of_injective {stream : ℕ → ℕ}
    (hinj : Function.Injective stream) {z t : ℕ} (ht : stream t = z) :
    firstTime stream z = t := by
  apply hinj
  exact (firstTime_spec ⟨t, ht⟩).trans ht.symm


theorem attacker_prefix_le_defender_add {m : ℕ}
    (family : Fin m → Set ℕ) (input : Stream) (hinj : Function.Injective input)
    {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      roundCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hInf : (informationCore family input).Infinite) (n : ℕ) :
    prefixCount
        (GenLimit.AdversaryFirst input (run (generator family) input) ∩
          informationCore family input) n ≤
      prefixCount
          (GenLimit.GeneratorFirst input (run (generator family) input) ∩
            informationCore family input) n + T + 1 := by
  classical
  let I := informationCore family input
  let output := run (generator family) input
  let A := prefixFinset (GenLimit.AdversaryFirst input output ∩ I) n
  let D := prefixFinset (GenLimit.GeneratorFirst input output ∩ I) n
  let early := A.filter (fun x => firstTime input x < T)
  let late := A.filter (fun x => T ≤ firstTime input x)
  have hearly : early.card ≤ T := by
    have hcard : early.card ≤ (Finset.range T).card := by
      apply Finset.card_le_card_of_injOn (firstTime input)
      · intro x hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      · intro x hx y hy hxy
        have hxA := (mem_prefixFinset.mp (Finset.mem_filter.mp hx).1).2.1
        have hyA := (mem_prefixFinset.mp (Finset.mem_filter.mp hy).1).2.1
        rcases hxA with ⟨tx, htx, -⟩
        rcases hyA with ⟨ty, hty, -⟩
        calc
          x = input (firstTime input x) := (firstTime_spec ⟨tx, htx⟩).symm
          _ = input (firstTime input y) := congrArg input hxy
          _ = y := firstTime_spec ⟨ty, hty⟩
    simpa using hcard
  have hlate : late.card ≤ D.card + 1 := by
    by_cases hempty : late = ∅
    · simp [hempty]
    · have hnonempty : late.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      let times := late.image (firstTime input)
      have htimes : times.Nonempty := hnonempty.image _
      let q := times.max' htimes
      have hqmem : q ∈ times := Finset.max'_mem times htimes
      obtain ⟨xq, hxqlate, hxqtime⟩ := Finset.mem_image.mp hqmem
      have hxqA : xq ∈ A := (Finset.mem_filter.mp hxqlate).1
      have hxqprefix := mem_prefixFinset.mp hxqA
      have hxqadv : xq ∈ GenLimit.AdversaryFirst input output := hxqprefix.2.1
      have hxqI : xq ∈ I := hxqprefix.2.2
      have hinputq : input q = xq := by
        rw [← hxqtime]
        exact firstTime_spec ⟨Classical.choose hxqadv,
          (Classical.choose_spec hxqadv).1⟩
      have hmap : late.card ≤ (D ∪ {output q}).card := by
        apply Finset.card_le_card_of_injOn
          (fun x => output (firstTime input x))
        · intro x hxlate
          have hxA : x ∈ A := (Finset.mem_filter.mp hxlate).1
          have hxtimeT : T ≤ firstTime input x := (Finset.mem_filter.mp hxlate).2
          have hxprefix := mem_prefixFinset.mp hxA
          have hxadv : x ∈ GenLimit.AdversaryFirst input output := hxprefix.2.1
          have hxtimeMem : firstTime input x ∈ times :=
            Finset.mem_image.mpr ⟨x, hxlate, rfl⟩
          have htleq : firstTime input x ≤ q := Finset.le_max' times _ hxtimeMem
          rcases lt_or_eq_of_le htleq with htlt | hteq
          · apply Finset.mem_union_left
            apply mem_prefixFinset.mpr
            refine ⟨?_, run_generatorFirst family input (firstTime input x), ?_⟩
            · have hxqInputFresh : xq ∉ Generic.sample input (firstTime input x + 1) := by
                intro hmem
                rw [Generic.mem_sample_iff] at hmem
                obtain ⟨s, hs, hsxq⟩ := hmem
                have hsq : s = q := hinj (hsxq.trans hinputq.symm)
                omega
              have hxqOutputFresh : xq ∉ Generic.sample output (firstTime input x) := by
                intro hmem
                rw [Generic.mem_sample_iff] at hmem
                obtain ⟨s, hs, hsxq⟩ := hmem
                rcases hxqadv with ⟨tq, htqxq, hbefore⟩
                have htq : tq = q := hinj (htqxq.trans hinputq.symm)
                exact hbefore s (by omega) hsxq
              have hle := stable_run_le family input hstable hInf hxtimeT hxqI
                hxqInputFresh hxqOutputFresh
              exact lt_of_le_of_lt hle hxqprefix.1
            · exact stable_run_mem family input hstable hInf hxtimeT
          · apply Finset.mem_union_right
            simpa [hteq]
        · intro x hx y hy hxy
          have htime : firstTime input x = firstTime input y :=
            run_injective family input hxy
          have hxadv := (mem_prefixFinset.mp (Finset.mem_filter.mp hx).1).2.1
          have hyadv := (mem_prefixFinset.mp (Finset.mem_filter.mp hy).1).2.1
          rcases hxadv with ⟨tx, htx, -⟩
          rcases hyadv with ⟨ty, hty, -⟩
          calc
            x = input (firstTime input x) := (firstTime_spec ⟨tx, htx⟩).symm
            _ = input (firstTime input y) := congrArg input htime
            _ = y := firstTime_spec ⟨ty, hty⟩
      exact hmap.trans (Finset.card_union_le D {output q})
  have hsubset : A ⊆ early ∪ late := by
    intro x hx
    by_cases h : firstTime input x < T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hx, Nat.le_of_not_gt h⟩)
  have hA : A.card ≤ early.card + late.card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le early late)
  change A.card ≤ D.card + T + 1
  omega


theorem coreCount_le_two_mul_targetDefender {m : ℕ}
    (family : Fin m → Set ℕ) (input : Stream) (hinj : Function.Injective input)
    {T : ℕ}
    (hstable : ∀ q, T ≤ q →
      roundCore family (fun i : Fin (q + 1) => input i) =
        informationCore family input)
    (hInf : (informationCore family input).Infinite)
    {K : Set ℕ} (hIK : informationCore family input ⊆ K) (n : ℕ) :
    prefixCount (informationCore family input) n ≤
      2 * prefixCount
        (GenLimit.GeneratorFirst input (run (generator family) input) ∩ K) n +
        (T + 1) + Nat.log2 (prefixCount K n) := by
  let I := informationCore family input
  let output := run (generator family) input
  let A := GenLimit.AdversaryFirst input output
  let D := GenLimit.GeneratorFirst input output
  have hcover := core_covered family input hstable hInf
  have hownership : prefixCount I n ≤
      prefixCount (A ∩ I) n + prefixCount (D ∩ I) n := by
    classical
    unfold prefixCount
    apply le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro x hx
    have hx' := mem_prefixFinset.mp hx
    rcases hcover hx'.2 with hxA | hxD
    · exact Finset.mem_union_left _ (mem_prefixFinset.mpr ⟨hx'.1, hxA, hx'.2⟩)
    · exact Finset.mem_union_right _ (mem_prefixFinset.mpr ⟨hx'.1, hxD, hx'.2⟩)
  have hattack := attacker_prefix_le_defender_add family input hinj
    hstable hInf n
  have hcoreD : prefixCount (D ∩ I) n ≤ prefixCount (D ∩ K) n := by
    apply prefixCount_mono
    intro z hz
    exact ⟨hz.1, hIK hz.2⟩
  dsimp only [I, output, A, D] at hownership hattack hcoreD ⊢
  omega

theorem relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    relativeLowerDensity A K ≤ relativeLowerDensity B K := by
  unfold relativeLowerDensity
  apply liminf_le_liminf
  · apply Eventually.of_forall
    intro n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_mono hAB n
    · exact_mod_cast Nat.zero_le (prefixCount K n)
  · exact isBoundedUnder_of ⟨0, fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  · exact isCoboundedUnder_ge_of_le atTop (fun n => by
      show ((prefixCount B n : ℝ) / (prefixCount K n : ℝ)) ≤ 1
      by_cases hzero : prefixCount K n = 0
      · have hBzero : prefixCount B n = 0 :=
          Nat.eq_zero_of_le_zero ((prefixCount_mono hBK n).trans_eq hzero)
        simp [hzero, hBzero]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
        exact_mod_cast prefixCount_mono hBK n)

end Stage3Case017Proof

open Stage3Case017Proof
open Stage3Case017
open GenLimit.PatientScope

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Stage3Case017Proof.generator family, ?_⟩
  intro input hinj hexists hInf
  let output := Stage3Case017Proof.run (Stage3Case017Proof.generator family) input
  obtain ⟨T, hstable⟩ :=
    Stage3Case017Proof.eventually_roundCore_eq_informationCore family input
  refine ⟨output, Stage3Case017Proof.follows_run _ _, ?_⟩
  intro j hcompat
  constructor
  · refine ⟨T, ?_⟩
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · exact (Stage3Case017Proof.stable_run_mem family input hstable hInf ht) j hcompat
    · intro hsample
      apply Stage3Case017Proof.run_fresh_input family input t
      rw [GenLimit.Generic.mem_sample_iff]
      rw [GenLimit.mem_sample_iff] at hsample
      simpa [output] using hsample
    · intro s hs
      simpa [output] using Stage3Case017Proof.run_fresh_output family input hs
  · let I := informationCore family input
    let D := GenLimit.GeneratorFirst input output ∩ family j
    have hIK : I ⊆ family j := fun z hz => hz j hcompat
    have hhalf :
        (1 / 2 : ℝ) * relativeLowerDensity I (family j) ≤
          relativeLowerDensity D (family j) := by
      apply GenLimit.PatientScope.partialDensity_of_counting
        (prefixCount (family j)) (prefixCount I) (prefixCount D) (T + 1)
      · exact tendsto_prefixCount_atTop (hfamily j)
      · intro n
        exact prefixCount_mono hIK n
      · intro n
        exact prefixCount_mono Set.inter_subset_right n
      · intro n
        exact Stage3Case017Proof.coreCount_le_two_mul_targetDefender
          family input hinj hstable hInf hIK n
    have homit : I \ Set.range input ⊆ D := by
      intro z hz
      exact ⟨Stage3Case017Proof.core_mem_generatorFirst_of_not_input
        family input hstable hInf hz.1 hz.2, hIK hz.1⟩
    have hmissing :
        relativeLowerDensity (I \ Set.range input) (family j) ≤
          relativeLowerDensity D (family j) :=
      Stage3Case017Proof.relativeLowerDensity_mono homit Set.inter_subset_right
    exact max_le hhalf hmissing
