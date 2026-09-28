import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

abbrev Prefix (n : ℕ) := Fin n → ℕ

def prefixValues {n : ℕ} (xs : Prefix n) : Finset ℕ :=
  Finset.univ.image xs

def currentCore {m t : ℕ} (family : Fin m → Language)
    (xs : Prefix (t + 1)) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

def available {m t : ℕ} (family : Fin m → Language)
    (xs : Prefix (t + 1)) (ys : Prefix t) (z : ℕ) : Prop :=
  z ∈ currentCore family xs ∧ z ∉ prefixValues xs ∧ z ∉ prefixValues ys

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : ∃ z, available family xs ys z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => trajectory gen input i)
termination_by t

@[simp] theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory]

theorem greedy_spec {m t : ℕ} {family : Fin m → Language}
    {xs : Prefix (t + 1)} {ys : Prefix t}
    (h : ∃ z, available family xs ys z) :
    available family xs ys (greedyGenerator family t xs ys) := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_spec h

theorem greedy_min {m t : ℕ} {family : Fin m → Language}
    {xs : Prefix (t + 1)} {ys : Prefix t}
    (h : ∃ z, available family xs ys z) {z : ℕ}
    (hz : available family xs ys z) :
    greedyGenerator family t xs ys ≤ z := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_min' h hz

noncomputable def rejectionTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (show ∃ t, input t ∉ family j by
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp h
    exact ⟨t, ht⟩)

noncomputable def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  Finset.univ.sup (rejectionTime family input)

theorem currentCore_eq_informationCore {m t : ℕ}
    (family : Fin m → Language) (input : Stream)
    (ht : stabilizationTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := by
  classical
  ext z
  constructor
  · intro hz j hj
    apply hz j
    intro i
    exact hj ⟨i, rfl⟩
  · intro hz j hj
    apply hz j
    intro x hx
    obtain ⟨s, rfl⟩ := hx
    by_contra hbad
    have hnot : ¬ GenLimit.Generic.StreamIn input (family j) := by
      intro hall
      exact hbad (hall ⟨s, rfl⟩)
    have hfind : input (rejectionTime family input j) ∉ family j := by
      simp only [rejectionTime, dif_neg hnot]
      exact Nat.find_spec (show ∃ q, input q ∉ family j by
        obtain ⟨_, ⟨q, rfl⟩, hq⟩ := Set.not_subset.mp hnot
        exact ⟨q, hq⟩)
    have hleT : rejectionTime family input j ≤ stabilizationTime family input :=
      Finset.le_sup (Finset.mem_univ j)
    have hlet : rejectionTime family input j ≤ t := le_trans hleT ht
    let i : Fin (t + 1) := ⟨rejectionTime family input j, Nat.lt_succ_of_le hlet⟩
    exact hfind (hj i)


@[simp] theorem mem_prefixValues {n z : ℕ} {xs : Prefix n} :
    z ∈ prefixValues xs ↔ ∃ i, xs i = z := by
  simp [prefixValues]

theorem stable_available {m t : ℕ} (family : Fin m → Language)
    (input output : Stream) (hcore : (informationCore family input).Infinite)
    (ht : stabilizationTime family input ≤ t) :
    ∃ z, available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i) z := by
  classical
  obtain ⟨z, hzcore, hzfresh⟩ := hcore.exists_not_mem_finset
    (prefixValues (fun i : Fin (t + 1) => input i) ∪
      prefixValues (fun i : Fin t => output i))
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [currentCore_eq_informationCore family input ht]
    exact hzcore
  · intro hz
    exact hzfresh (Finset.mem_union_left _ hz)
  · intro hz
    exact hzfresh (Finset.mem_union_right _ hz)

theorem stable_output_spec {m t : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollow : Follows (greedyGenerator family) input output)
    (hcore : (informationCore family input).Infinite)
    (ht : stabilizationTime family input ≤ t) :
    output t ∈ informationCore family input ∧
      output t ∉ GenLimit.sample input (t + 1) ∧
      ∀ s, s < t → output s ≠ output t := by
  classical
  have hex := stable_available family input output hcore ht
  have hspec := greedy_spec hex
  rw [← hfollow t] at hspec
  refine ⟨?_, ?_, ?_⟩
  · have hmem := hspec.1
    rw [currentCore_eq_informationCore family input ht] at hmem
    exact hmem
  · intro hmem
    rw [GenLimit.mem_sample_iff] at hmem
    obtain ⟨s, hs, hval⟩ := hmem
    have hpref : output t ∈ prefixValues (fun i : Fin (t + 1) => input i) := by
      rw [mem_prefixValues]
      exact ⟨⟨s, hs⟩, hval⟩
    exact hspec.2.1 hpref
  · intro s hs heq
    have hpref : output t ∈ prefixValues (fun i : Fin t => output i) := by
      rw [mem_prefixValues]
      exact ⟨⟨s, hs⟩, heq⟩
    exact hspec.2.2 hpref

theorem stable_output_generatorFirst {m t : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollow : Follows (greedyGenerator family) input output)
    (hcore : (informationCore family input).Infinite)
    (ht : stabilizationTime family input ≤ t) :
    output t ∈ GenLimit.GeneratorFirst input output := by
  obtain ⟨_, hfresh, _⟩ :=
    stable_output_spec family input output hfollow hcore ht
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  apply hfresh
  rw [GenLimit.mem_sample_iff]
  exact ⟨s, Nat.lt_succ_of_le hs, heq⟩


theorem core_subset_first_announcements {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollow : Follows (greedyGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input output ∪ GenLimit.GeneratorFirst input output := by
  classical
  intro z hz
  by_cases hin : z ∈ Set.range input
  · exact GenLimit.range_subset_first_announcements input output hin
  by_cases hout : z ∈ Set.range output
  · right
    obtain ⟨t, ht⟩ := hout
    refine ⟨t, ht, ?_⟩
    intro s _ heq
    exact hin ⟨s, heq⟩
  exfalso
  let T := stabilizationTime family input
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨output (T + i), Nat.lt_succ_of_le (by
      have ht : T ≤ T + i := Nat.le_add_right T i
      have havail : available family
          (fun q : Fin (T + i + 1) => input q)
          (fun q : Fin (T + i) => output q) z := by
        refine ⟨?_, ?_, ?_⟩
        · rw [currentCore_eq_informationCore family input ht]
          exact hz
        · intro hmem
          rw [mem_prefixValues] at hmem
          obtain ⟨q, hq⟩ := hmem
          exact hin ⟨q, hq⟩
        · intro hmem
          rw [mem_prefixValues] at hmem
          obtain ⟨q, hq⟩ := hmem
          exact hout ⟨q, hq⟩
      have hex : ∃ w, available family
          (fun q : Fin (T + i + 1) => input q)
          (fun q : Fin (T + i) => output q) w := ⟨z, havail⟩
      have hle := greedy_min hex havail
      rw [← hfollow (T + i)] at hle
      exact hle)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hij'
    have houtEq : output (T + i) = output (T + j) := Fin.mk.inj hij
    rcases lt_or_gt_of_ne hij' with hijlt | hjilt
    · have hspec := stable_output_spec family input output hfollow hcore
        (show T ≤ T + j from Nat.le_add_right T j)
      exact (hspec.2.2 (T + i) (Nat.add_lt_add_left hijlt T)) houtEq
    · have hspec := stable_output_spec family input output hfollow hcore
        (show T ≤ T + i from Nat.le_add_right T i)
      exact (hspec.2.2 (T + j) (Nat.add_lt_add_left hjilt T)) houtEq.symm
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega


noncomputable def inputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

theorem input_at_inputTime {input : Stream} {z : ℕ} (hz : z ∈ Set.range input) :
    input (inputTime input z) = z := by
  classical
  obtain ⟨t, ht⟩ := hz
  simp only [inputTime, dif_pos (show ∃ q, input q = z from ⟨t, ht⟩)]
  exact Nat.find_spec (show ∃ q, input q = z from ⟨t, ht⟩)

theorem inputTime_injective {input : Stream} (hinj : Function.Injective input) :
    Set.InjOn (inputTime input) (Set.range input) := by
  intro x hx y hy hxy
  calc
    x = input (inputTime input x) := (input_at_inputTime hx).symm
    _ = input (inputTime input y) := congrArg input hxy
    _ = y := input_at_inputTime hy

theorem adversaryFirst_in_range {input output : Stream} :
    GenLimit.AdversaryFirst input output ⊆ Set.range input := by
  rintro z ⟨t, ht, _⟩
  exact ⟨t, ht⟩

noncomputable def attackerPrefix (core : Language) (input output : Stream)
    (n : ℕ) : Finset ℕ :=
  GenLimit.PatientScope.prefixFinset
    (GenLimit.AdversaryFirst input output ∩ core) n

noncomputable def defenderPrefix (core : Language) (input output : Stream)
    (n : ℕ) : Finset ℕ :=
  GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ core) n

theorem early_attacker_card_le {m n : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input) :
    ((attackerPrefix (informationCore family input) input output n).filter
      (fun z => inputTime input z < stabilizationTime family input)).card ≤
      stabilizationTime family input := by
  classical
  let A := (attackerPrefix (informationCore family input) input output n).filter
    (fun z => inputTime input z < stabilizationTime family input)
  have hmap : Set.MapsTo (inputTime input) (↑A : Set ℕ)
      (↑(Finset.range (stabilizationTime family input)) : Set ℕ) := by
    intro z hz
    rw [Finset.mem_coe, Finset.mem_filter] at hz
    simpa using hz.2
  have hinjOn : Set.InjOn (inputTime input) (↑A : Set ℕ) := by
    apply (inputTime_injective hinj).mono
    intro z hz
    rw [Finset.mem_coe, Finset.mem_filter] at hz
    exact adversaryFirst_in_range (GenLimit.PatientScope.mem_prefixFinset.mp hz.1).2.1
  have hcard := Finset.card_le_card_of_injOn (inputTime input) hmap hinjOn
  simpa [A] using hcard

theorem stable_attacker_card_le {m n : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollow : Follows (greedyGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    ((attackerPrefix (informationCore family input) input output n).filter
      (fun z => stabilizationTime family input ≤ inputTime input z)).card ≤
      (defenderPrefix (informationCore family input) input output n).card + 1 := by
  classical
  let T := stabilizationTime family input
  let I := informationCore family input
  let A := (attackerPrefix I input output n).filter
    (fun z => T ≤ inputTime input z)
  let D := defenderPrefix I input output n
  by_cases hA : A.Nonempty
  · obtain ⟨last, hlastA, hlast⟩ := Finset.exists_max_image A (inputTime input) hA
    have hmaps : Set.MapsTo (fun z => output (inputTime input z))
        (↑(A.erase last) : Set ℕ) (↑D : Set ℕ) := by
      intro z hz
      rw [Finset.mem_coe, Finset.mem_erase] at hz
      have hzAmem := hz.2
      have hzA := hzAmem
      rw [Finset.mem_filter] at hzA
      have hzprefix := GenLimit.PatientScope.mem_prefixFinset.mp hzA.1
      have hzrange : z ∈ Set.range input :=
        adversaryFirst_in_range hzprefix.2.1
      have hlastFilter := hlastA
      rw [Finset.mem_filter] at hlastFilter
      have hlastPrefix := GenLimit.PatientScope.mem_prefixFinset.mp hlastFilter.1
      have hlastRange : last ∈ Set.range input :=
        adversaryFirst_in_range hlastPrefix.2.1
      have htimesNe : inputTime input z ≠ inputTime input last := by
        intro heq
        exact hz.1 ((inputTime_injective hinj) hzrange hlastRange heq)
      have htlt : inputTime input z < inputTime input last :=
        lt_of_le_of_ne (hlast z hzAmem) htimesNe
      have havail : available family
          (fun q : Fin (inputTime input z + 1) => input q)
          (fun q : Fin (inputTime input z) => output q) last := by
        refine ⟨?_, ?_, ?_⟩
        · rw [currentCore_eq_informationCore family input hzA.2]
          exact hlastPrefix.2.2
        · intro hmem
          rw [mem_prefixValues] at hmem
          obtain ⟨q, hq⟩ := hmem
          have hqeq : q = inputTime input last := by
            apply hinj
            rw [hq, input_at_inputTime hlastRange]
          apply (Nat.not_le_of_gt htlt)
          exact Nat.le_of_lt_succ (by simpa [hqeq] using q.isLt)
        · intro hmem
          rw [mem_prefixValues] at hmem
          obtain ⟨q, hq⟩ := hmem
          obtain ⟨u, hu, hno⟩ := hlastPrefix.2.1
          have hueq : u = inputTime input last := by
            apply hinj
            rw [hu, input_at_inputTime hlastRange]
          exact hno q (by simpa [hueq] using lt_trans q.isLt htlt) hq
      have hex : ∃ w, available family
          (fun q : Fin (inputTime input z + 1) => input q)
          (fun q : Fin (inputTime input z) => output q) w := ⟨last, havail⟩
      have houtLe := greedy_min hex havail
      rw [← hfollow (inputTime input z)] at houtLe
      apply GenLimit.PatientScope.mem_prefixFinset.mpr
      refine ⟨lt_of_le_of_lt houtLe hlastPrefix.1, ?_, ?_⟩
      · exact stable_output_generatorFirst family input output hfollow hcore hzA.2
      · exact (stable_output_spec family input output hfollow hcore hzA.2).1
    have hinjMap : Set.InjOn (fun z => output (inputTime input z))
        (↑(A.erase last) : Set ℕ) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_erase] at hx hy
      have hxA := hx.2
      have hyA := hy.2
      rw [Finset.mem_filter] at hxA hyA
      have hxrange : x ∈ Set.range input :=
        adversaryFirst_in_range
          (GenLimit.PatientScope.mem_prefixFinset.mp hxA.1).2.1
      have hyrange : y ∈ Set.range input :=
        adversaryFirst_in_range
          (GenLimit.PatientScope.mem_prefixFinset.mp hyA.1).2.1
      have htx : T ≤ inputTime input x := hxA.2
      have hty : T ≤ inputTime input y := hyA.2
      by_contra hxy'
      have htne : inputTime input x ≠ inputTime input y := by
        intro heq
        exact hxy' ((inputTime_injective hinj) hxrange hyrange heq)
      rcases lt_or_gt_of_ne htne with hlt | hgt
      · have hspec := stable_output_spec family input output hfollow hcore hty
        exact (hspec.2.2 (inputTime input x) hlt) hxy
      · have hspec := stable_output_spec family input output hfollow hcore htx
        exact (hspec.2.2 (inputTime input y) hgt) hxy.symm
    have herase : (A.erase last).card ≤ D.card :=
      Finset.card_le_card_of_injOn (fun z => output (inputTime input z)) hmaps hinjMap
    have hcard := Finset.card_erase_add_one hlastA
    dsimp [A, D, I, T] at herase hcard ⊢
    omega
  · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ D.card + 1
    rw [hempty]
    simp

theorem attacker_card_le {m n : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollow : Follows (greedyGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    (attackerPrefix (informationCore family input) input output n).card ≤
      (defenderPrefix (informationCore family input) input output n).card +
        stabilizationTime family input + 1 := by
  classical
  let A := attackerPrefix (informationCore family input) input output n
  let T := stabilizationTime family input
  have hearly := early_attacker_card_le family input output hinj (n := n)
  have hstable := stable_attacker_card_le family input output hinj hfollow hcore (n := n)
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := A) (fun z => inputTime input z < T)
  have hneg : A.filter (fun z => ¬ inputTime input z < T) =
      A.filter (fun z => T ≤ inputTime input z) := by
    ext z
    simp [Nat.not_lt]
  rw [hneg] at hsplit
  dsimp [A, T] at hearly hstable hsplit ⊢
  omega


theorem core_count_le {m n : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollow : Follows (greedyGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ informationCore family input) n +
        (stabilizationTime family input + 1) := by
  classical
  let I := informationCore family input
  let E := GenLimit.PatientScope.prefixFinset I n
  let A := attackerPrefix I input output n
  let D := defenderPrefix I input output n
  have hsubset : E ⊆ A ∪ D := by
    intro z hz
    have hz' := GenLimit.PatientScope.mem_prefixFinset.mp hz
    rcases core_subset_first_announcements family input output hfollow hcore hz'.2 with
      hzA | hzD
    · exact Finset.mem_union_left _ <| GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hz'.1, hzA, hz'.2⟩
    · exact Finset.mem_union_right _ <| GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hz'.1, hzD, hz'.2⟩
  have hEA : E.card ≤ A.card + D.card :=
    le_trans (Finset.card_le_card hsubset) (Finset.card_union_le A D)
  have hA := attacker_card_le family input output hinj hfollow hcore (n := n)
  dsimp [E, A, D, I, attackerPrefix, defenderPrefix,
    GenLimit.PatientScope.prefixCount] at hEA hA ⊢
  omega

theorem relativeLowerDensity_mono {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  let aRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let bRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hab : ∀ n, aRatio n ≤ bRatio n := by
    intro n
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
      (Nat.cast_nonneg _)
  have haNonneg : ∀ n, 0 ≤ aRatio n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbLeOne : ∀ n, bRatio n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [bRatio, hn]
    · dsimp [bRatio]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  change liminf aRatio atTop ≤ liminf bRatio atTop
  exact liminf_le_liminf (Eventually.of_forall hab)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall haNonneg))
    (isCoboundedUnder_ge_of_le atTop hbLeOne)

theorem missing_core_subset_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollow : Follows (greedyGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input output := by
  intro z hz
  rcases core_subset_first_announcements family input output hfollow hcore hz.1 with
    hzA | hzD
  · exact False.elim (hz.2 (adversaryFirst_in_range hzA))
  · exact hzD

theorem density_bounds {m : ℕ} (family : Fin m → Language)
    (hallInfinite : ∀ j, (family j).Infinite)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollow : Follows (greedyGenerator family) input output)
    (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    max
        ((1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j))
        (GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j))
      ≤ GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
  have hcoreTarget : informationCore family input ⊆ family j := fun z hz => hz j hj
  have hhalf :
      (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    apply GenLimit.PatientScope.partialDensity_of_counting
      (GenLimit.PatientScope.prefixCount (family j))
      (GenLimit.PatientScope.prefixCount (informationCore family input))
      (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output ∩ family j))
      (stabilizationTime family input + 1)
    · exact GenLimit.PatientScope.tendsto_prefixCount_atTop (hallInfinite j)
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono hcoreTarget n
    · intro n
      exact GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
    · intro n
      have hcount := core_count_le family input output hinj hfollow hcore (n := n)
      have hDmono := GenLimit.PatientScope.prefixCount_mono
        (show GenLimit.GeneratorFirst input output ∩ informationCore family input ⊆
          GenLimit.GeneratorFirst input output ∩ family j by
          intro z hz
          exact ⟨hz.1, hcoreTarget hz.2⟩) n
      omega
  have hmissing :
      GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input \ Set.range input) (family j) ≤
        GenLimit.PatientScope.relativeLowerDensity
          (GenLimit.GeneratorFirst input output ∩ family j) (family j) := by
    apply relativeLowerDensity_mono
    · intro z hz
      exact ⟨missing_core_subset_generatorFirst family input output hfollow hcore hz,
        hcoreTarget hz.1⟩
    · exact Set.inter_subset_right
  exact max_le hhalf hmissing

end Stage3Case017Proof

open Stage3Case017
open Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hallInfinite
  let gen := greedyGenerator family
  refine ⟨gen, ?_⟩
  intro input hinj _ hcore
  let output := trajectory gen input
  have hfollow : Follows gen input output := trajectory_follows gen input
  refine ⟨output, hfollow, ?_⟩
  intro j hj
  constructor
  · refine ⟨stabilizationTime family input, ?_⟩
    intro t ht
    have hspec := stable_output_spec family input output hfollow hcore ht
    exact ⟨hspec.1 j hj, hspec.2.1, hspec.2.2⟩
  · exact density_bounds family hallInfinite input output hinj hfollow hcore j hj
