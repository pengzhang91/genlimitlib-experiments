import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Set Filter
open scoped Topology

namespace Case017

abbrev Language := Stage3Case017.Language
abbrev Stream := Stage3Case017.Stream
abbrev OnlineGenerator := Stage3Case017.OnlineGenerator

private def announced {t : ℕ} (x : Fin (t + 1) → ℕ) (y : Fin t → ℕ) : Finset ℕ :=
  (Finset.univ.image x) ∪ (Finset.univ.image y)

private def prefixCore {m t : ℕ} (family : Fin m → Language)
    (x : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, x i ∈ family j) → z ∈ family j}

noncomputable def generator {m : ℕ} (family : Fin m → Language) : OnlineGenerator :=
  by
  classical
  exact fun t x y =>
    if h : (prefixCore family x).Infinite then
      Nat.find (h.exists_not_mem_finset (announced x y))
    else
      Nat.find (Set.infinite_univ.exists_not_mem_finset (announced x y))

private theorem generator_fresh {m t : ℕ} (family : Fin m → Language)
    (x : Fin (t + 1) → ℕ) (y : Fin t → ℕ) :
    generator family t x y ∉ announced x y := by
  classical
  unfold generator
  split_ifs with h
  · exact (Nat.find_spec (h.exists_not_mem_finset (announced x y))).2
  · exact (Nat.find_spec (Set.infinite_univ.exists_not_mem_finset (announced x y))).2

private theorem generator_mem_core {m t : ℕ} (family : Fin m → Language)
    (x : Fin (t + 1) → ℕ) (y : Fin t → ℕ)
    (h : (prefixCore family x).Infinite) :
    generator family t x y ∈ prefixCore family x := by
  classical
  simp only [generator, dif_pos h]
  exact (Nat.find_spec (h.exists_not_mem_finset (announced x y))).1

private theorem generator_le_of_available {m t : ℕ} (family : Fin m → Language)
    (x : Fin (t + 1) → ℕ) (y : Fin t → ℕ)
    (h : (prefixCore family x).Infinite) {z : ℕ}
    (hzcore : z ∈ prefixCore family x) (hzfresh : z ∉ announced x y) :
    generator family t x y ≤ z := by
  classical
  simp only [generator, dif_pos h]
  exact Nat.find_min' (h.exists_not_mem_finset (announced x y)) ⟨hzcore, hzfresh⟩

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream
  | 0 => gen 0 (fun i => input i) (fun i => Fin.elim0 i)
  | t + 1 => gen (t + 1) (fun i => input i) (fun i => trajectory gen input i)
termination_by t => t

@[simp] theorem trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Stage3Case017.Follows gen input (trajectory gen input) := by
  intro t
  cases t with
  | zero =>
      simp only [trajectory]
      congr
      funext i
      exact Fin.elim0 i
  | succ t => simp [trajectory]

end Case017

namespace Case017


private theorem trajectory_ne_input {m : ℕ} (family : Fin m → Language) (input : Stream)
    {s t : ℕ} (hst : s ≤ t) :
    input s ≠ trajectory (generator family) input t := by
  intro heq
  have hgen : trajectory (generator family) input t ∉
      announced (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (generator family) input i) := by
    rw [trajectory_follows (generator family) input t]
    exact generator_fresh family
      (x := fun i : Fin (t + 1) => input i)
      (y := fun i : Fin t => trajectory (generator family) input i)
  apply hgen
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨⟨s, Nat.lt_succ_of_le hst⟩, Finset.mem_univ _, heq⟩

private theorem trajectory_ne_previous {m : ℕ} (family : Fin m → Language) (input : Stream)
    {s t : ℕ} (hst : s < t) :
    trajectory (generator family) input s ≠ trajectory (generator family) input t := by
  intro heq
  have hgen : trajectory (generator family) input t ∉
      announced (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory (generator family) input i) := by
    rw [trajectory_follows (generator family) input t]
    exact generator_fresh family
      (x := fun i : Fin (t + 1) => input i)
      (y := fun i : Fin t => trajectory (generator family) input i)
  apply hgen
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨⟨s, hst⟩, Finset.mem_univ _, heq⟩

private theorem trajectory_injective {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Function.Injective (trajectory (generator family) input) := by
  intro s t heq
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim ((trajectory_ne_previous family input h) heq)
  · exact h
  · exact False.elim ((trajectory_ne_previous family input h) heq.symm)

private theorem eventually_prefix_compatibility {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hj : ∀ j : Fin m, ∀ᶠ t : ℕ in atTop,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
    intro j
    by_cases hcompat : GenLimit.Generic.StreamIn input (family j)
    · filter_upwards [] with t
      exact ⟨fun _ => hcompat, fun _ i => hcompat ⟨i, rfl⟩⟩
    · have hw : ∃ s, input s ∉ family j := by
        simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using hcompat
      obtain ⟨s, hs⟩ := hw
      filter_upwards [eventually_ge_atTop s] with t ht
      constructor
      · intro hp
        exact False.elim (hs (hp ⟨s, Nat.lt_succ_of_le ht⟩))
      · intro hc
        exact False.elim (hcompat hc)
  have hall : ∀ᶠ t : ℕ in atTop, ∀ j : Fin m,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
    have hu : ∀ᶠ t : ℕ in atTop, ∀ j ∈ (Finset.univ : Finset (Fin m)),
        (∀ i : Fin (t + 1), input i ∈ family j) ↔
          GenLimit.Generic.StreamIn input (family j) :=
      (Finset.eventually_all Finset.univ).2 (fun j _ => hj j)
    simpa using hu
  exact eventually_atTop.mp hall

private theorem eventually_prefixCore_eq {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      prefixCore family (fun i : Fin (t + 1) => input i) =
        Stage3Case017.informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_prefix_compatibility family input
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  simp only [prefixCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hj
    exact hz j ((hT t ht j).2 hj)
  · intro hz j hj
    exact hz j ((hT t ht j).1 hj)

end Case017

namespace Case017

private theorem trajectory_mem_informationCore {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      trajectory (generator family) input t ∈
        Stage3Case017.informationCore family input := by
  obtain ⟨T, hT⟩ := eventually_prefixCore_eq family input
  refine ⟨T, ?_⟩
  intro t ht
  rw [trajectory_follows (generator family) input t]
  have hinf : (prefixCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hT t ht]
    exact hcore
  have hmem := generator_mem_core family
    (x := fun i : Fin (t + 1) => input i)
    (y := fun i : Fin t => trajectory (generator family) input i) hinf
  rw [hT t ht] at hmem
  exact hmem

private theorem trajectory_le_available_core {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {T t z : ℕ} (hstable : ∀ q, T ≤ q →
      prefixCore family (fun i : Fin (q + 1) => input i) =
        Stage3Case017.informationCore family input)
    (ht : T ≤ t) (hzcore : z ∈ Stage3Case017.informationCore family input)
    (hzin : z ∉ Set.range input) (hzout : z ∉ Set.range (trajectory (generator family) input)) :
    trajectory (generator family) input t ≤ z := by
  rw [trajectory_follows (generator family) input t]
  have hinf : (prefixCore family (fun i : Fin (t + 1) => input i)).Infinite := by
    rw [hstable t ht]
    exact hcore
  apply generator_le_of_available family
    (x := fun i : Fin (t + 1) => input i)
    (y := fun i : Fin t => trajectory (generator family) input i) hinf
  · rwa [hstable t ht]
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
      exact hzin ⟨i, hi⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
      exact hzout ⟨i, hi⟩

private theorem informationCore_covered {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input ⊆
      Set.range input ∪ Set.range (trajectory (generator family) input) := by
  intro z hzcore
  by_contra hz
  have hzin : z ∉ Set.range input := fun h => hz (Set.mem_union_left _ h)
  have hzout : z ∉ Set.range (trajectory (generator family) input) :=
    fun h => hz (Set.mem_union_right _ h)
  obtain ⟨T, hstable⟩ := eventually_prefixCore_eq family input
  let tail : ℕ → ℕ := fun n => trajectory (generator family) input (T + n)
  have hinj : Function.Injective tail := by
    intro a b hab
    exact Nat.add_left_cancel (trajectory_injective family input hab)
  have hirange : (Set.range tail).Infinite := Set.infinite_range_of_injective hinj
  have hsubset : Set.range tail ⊆ Set.Iic z := by
    rintro w ⟨n, rfl⟩
    exact trajectory_le_available_core family input hcore hstable
      (Nat.le_add_right T n) hzcore hzin hzout
  exact hirange ((Set.finite_Iic z).subset hsubset)

end Case017

namespace Case017

noncomputable def firstInput (input : Stream) (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = x then Nat.find h else 0

private theorem firstInput_spec (input : Stream) {x : ℕ} (hx : x ∈ Set.range input) :
    input (firstInput input x) = x := by
  classical
  obtain ⟨t, ht⟩ := hx
  have hex : ∃ q, input q = x := ⟨t, ht⟩
  simp only [firstInput, dif_pos hex]
  exact Nat.find_spec hex

private theorem firstInput_le (input : Stream) {x t : ℕ} (ht : input t = x) :
    firstInput input x ≤ t := by
  classical
  have hex : ∃ q, input q = x := ⟨t, ht⟩
  simp only [firstInput, dif_pos hex]
  exact Nat.find_min' hex ht

private theorem output_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    Set.range (trajectory (generator family) input) ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  rintro x ⟨t, rfl⟩
  refine ⟨t, rfl, ?_⟩
  intro s hst
  exact trajectory_ne_input family input hst

private theorem informationCore_first_covered {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input ⊆
      GenLimit.AdversaryFirst input (trajectory (generator family) input) ∪
        GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  intro x hx
  rcases informationCore_covered family input hcore hx with hx | hx
  · exact GenLimit.range_subset_first_announcements input
      (trajectory (generator family) input) hx
  · exact Set.mem_union_right _ (output_subset_generatorFirst family input hx)

private theorem range_input_subset_core {m : ℕ}
    (family : Fin m → Language) (input : Stream) :
    Set.range input ⊆ Stage3Case017.informationCore family input := by
  rintro x ⟨t, rfl⟩ j hj
  exact hj ⟨t, rfl⟩

end Case017

namespace Case017

private theorem adversaryFirst_before_firstInput (input output : Stream) {x : ℕ}
    (hx : x ∈ GenLimit.AdversaryFirst input output) :
    (∀ s, s < firstInput input x → output s ≠ x) := by
  obtain ⟨t, ht, hbefore⟩ := hx
  have hle := firstInput_le input ht
  intro s hs
  exact hbefore s (lt_of_lt_of_le hs hle)

private theorem adversaryFirst_firstInput_eq {input : Stream} (hinj : Function.Injective input)
    {x t : ℕ} (ht : input t = x) : firstInput input x = t := by
  apply hinj
  exact (firstInput_spec input ⟨t, ht⟩).trans ht.symm

private theorem prefix_counting {m : ℕ}
    (family : Fin m → Language) (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (K : Language) (hcoreK : Stage3Case017.informationCore family input ⊆ K) :
    ∃ r : ℕ, ∀ n,
      GenLimit.PatientScope.prefixCount
          (Stage3Case017.informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K) n +
          r + Nat.log2 (GenLimit.PatientScope.prefixCount K n) := by
  classical
  obtain ⟨T, hstable⟩ := eventually_prefixCore_eq family input
  refine ⟨T + 1, ?_⟩
  intro n
  let I := Stage3Case017.informationCore family input
  let out := trajectory (generator family) input
  let P := GenLimit.PatientScope.prefixFinset I n
  let A := P.filter (fun x => x ∈ GenLimit.AdversaryFirst input out)
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input out ∩ K) n
  let early := A.filter (fun x => firstInput input x < T)
  let late := A.filter (fun x => T ≤ firstInput input x)
  have hA_split : A ⊆ early ∪ late := by
    intro x hx
    by_cases hxt : firstInput input x < T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxt⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hx, Nat.le_of_not_gt hxt⟩)
  have hearly : early.card ≤ T := by
    have hmaps : Set.MapsTo (firstInput input) (↑early : Set ℕ)
        (↑(Finset.range T) : Set ℕ) := by
      intro x hx
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
    have hinjEarly : Set.InjOn (firstInput input) (↑early : Set ℕ) := by
      intro x hx y hy hxy
      have hxA := (Finset.mem_filter.mp hx).1
      have hyA := (Finset.mem_filter.mp hy).1
      have hxadv := (Finset.mem_filter.mp hxA).2
      have hyadv := (Finset.mem_filter.mp hyA).2
      have hxrange : x ∈ Set.range input := by
        obtain ⟨t, ht, -⟩ := hxadv
        exact ⟨t, ht⟩
      have hyrange : y ∈ Set.range input := by
        obtain ⟨t, ht, -⟩ := hyadv
        exact ⟨t, ht⟩
      calc
        x = input (firstInput input x) := (firstInput_spec input hxrange).symm
        _ = input (firstInput input y) := by rw [hxy]
        _ = y := firstInput_spec input hyrange
    simpa using Finset.card_le_card_of_injOn
      (firstInput input) hmaps hinjEarly
  have hlate : late.card ≤ D.card + 1 := by
    by_cases hempty : late = ∅
    · simp [hempty]
    · have hne : late.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨xmax, hxmax, hmax⟩ :=
        Finset.exists_max_image late (firstInput input) hne
      have herase : (late.erase xmax).card + 1 = late.card :=
        Finset.card_erase_add_one hxmax
      have hmap : Set.MapsTo
          (fun x => out (firstInput input x))
          (↑(late.erase xmax) : Set ℕ) (↑D : Set ℕ) := by
        intro x hx
        have hxlate := (Finset.mem_erase.mp hx).2
        have hxne := (Finset.mem_erase.mp hx).1
        have hxA := (Finset.mem_filter.mp hxlate).1
        have hxt := (Finset.mem_filter.mp hxlate).2
        have hxP := (Finset.mem_filter.mp hxA).1
        have hxadv := (Finset.mem_filter.mp hxA).2
        have hxmA := (Finset.mem_filter.mp hxmax).1
        have hxmP := (Finset.mem_filter.mp hxmA).1
        have hxmadv := (Finset.mem_filter.mp hxmA).2
        have hxrange : x ∈ Set.range input := by
          obtain ⟨q, hq, -⟩ := hxadv
          exact ⟨q, hq⟩
        have hxmrange : xmax ∈ Set.range input := by
          obtain ⟨q, hq, -⟩ := hxmadv
          exact ⟨q, hq⟩
        have htimele := hmax x hxlate
        have htimelt : firstInput input x < firstInput input xmax := by
          exact lt_of_le_of_ne htimele (fun heq => hxne <| by
            calc
              x = input (firstInput input x) := (firstInput_spec input hxrange).symm
              _ = input (firstInput input xmax) := by rw [heq]
              _ = xmax := firstInput_spec input hxmrange)
        have hxmcore : xmax ∈ I := (GenLimit.PatientScope.mem_prefixFinset.mp hxmP).2
        have hxmfreshInput : xmax ∉ Set.range
            (fun i : Fin (firstInput input x + 1) => input i) := by
          rintro ⟨i, hi⟩
          have := hinj (hi.trans (firstInput_spec input hxmrange).symm)
          omega
        have hxmfreshOutput : xmax ∉ Set.range
            (fun i : Fin (firstInput input x) => out i) := by
          rintro ⟨i, hi⟩
          exact adversaryFirst_before_firstInput input out hxmadv i
            (lt_trans i.isLt htimelt) hi
        have hle : out (firstInput input x) ≤ xmax := by
          change trajectory (generator family) input (firstInput input x) ≤ xmax
          rw [trajectory_follows (generator family) input (firstInput input x)]
          have hinf : (prefixCore family
              (fun i : Fin (firstInput input x + 1) => input i)).Infinite := by
            rw [hstable _ hxt]
            exact hcore
          apply generator_le_of_available family
            (x := fun i : Fin (firstInput input x + 1) => input i)
            (y := fun i : Fin (firstInput input x) => out i) hinf
          · rwa [hstable _ hxt]
          · intro hz
            rcases Finset.mem_union.mp hz with hz | hz
            · exact hxmfreshInput (by simpa [announced] using hz)
            · exact hxmfreshOutput (by simpa [announced] using hz)
        apply GenLimit.PatientScope.mem_prefixFinset.mpr
        refine ⟨lt_of_le_of_lt hle (GenLimit.PatientScope.mem_prefixFinset.mp hxmP).1, ?_⟩
        refine ⟨output_subset_generatorFirst family input ⟨firstInput input x, rfl⟩, ?_⟩
        have houtcore : out (firstInput input x) ∈ I := by
          change trajectory (generator family) input (firstInput input x) ∈ I
          rw [trajectory_follows (generator family) input (firstInput input x)]
          have hinf : (prefixCore family
              (fun i : Fin (firstInput input x + 1) => input i)).Infinite := by
            rw [hstable _ hxt]
            exact hcore
          have hm := generator_mem_core family
            (x := fun i : Fin (firstInput input x + 1) => input i)
            (y := fun i : Fin (firstInput input x) => out i) hinf
          rwa [hstable _ hxt] at hm
        exact hcoreK houtcore
      have hinjmap : Set.InjOn (fun x => out (firstInput input x))
          (↑(late.erase xmax) : Set ℕ) := by
        intro x hx y hy hxy
        have htime := trajectory_injective family input hxy
        have hxA := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).1).2
        have hyA := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).1).2
        have hxrange : x ∈ Set.range input := by
          obtain ⟨q, hq, -⟩ := hxA
          exact ⟨q, hq⟩
        have hyrange : y ∈ Set.range input := by
          obtain ⟨q, hq, -⟩ := hyA
          exact ⟨q, hq⟩
        calc
          x = input (firstInput input x) := (firstInput_spec input hxrange).symm
          _ = input (firstInput input y) := by rw [htime]
          _ = y := firstInput_spec input hyrange
      have hcard := Finset.card_le_card_of_injOn
        (fun x => out (firstInput input x)) hmap hinjmap
      omega
  have hA : A.card ≤ D.card + T + 1 := by
    have hsplit := Finset.card_le_card hA_split
    have hunion := Finset.card_union_le early late
    omega
  have hP : P.card ≤ A.card + D.card := by
    have hsub : P ⊆ A ∪ D := by
      intro x hx
      rcases informationCore_first_covered family input hcore
          (GenLimit.PatientScope.mem_prefixFinset.mp hx).2 with hxadv | hxgen
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxadv⟩)
      · apply Finset.mem_union_right
        apply GenLimit.PatientScope.mem_prefixFinset.mpr
        exact ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hx).1,
          hxgen, hcoreK (GenLimit.PatientScope.mem_prefixFinset.mp hx).2⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le A D)
  change P.card ≤ 2 * D.card + (T + 1) + Nat.log2 (GenLimit.PatientScope.prefixCount K n)
  omega

end Case017

namespace Case017

private theorem relativeLowerDensity_mono {A B K : Language}
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
  have hle : ∀ n, aRatio n ≤ bRatio n := by
    intro n
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
      (Nat.cast_nonneg _)
  have haLower : ∀ n, 0 ≤ aRatio n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbUpper : ∀ n, bRatio n ≤ 1 := by
    intro n
    by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
    · simp [bRatio, hn]
    · dsimp [bRatio]
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  exact liminf_le_liminf (Eventually.of_forall hle)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall haLower))
    (isCoboundedUnder_ge_of_le atTop hbUpper)

private theorem density_half {m : ℕ}
    (family : Fin m → Language) (input : Stream) (hinj : Function.Injective input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (K : Language) (hK : K.Infinite)
    (hcoreK : Stage3Case017.informationCore family input ⊆ K) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K) K := by
  obtain ⟨r, hcount⟩ := prefix_counting family input hinj hcore K hcoreK
  apply GenLimit.PatientScope.partialDensity_of_counting
    (GenLimit.PatientScope.prefixCount K)
    (GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input))
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K)) r
  · exact GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  · exact fun n => GenLimit.PatientScope.prefixCount_mono hcoreK n
  · exact fun n => GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  · exact hcount

private theorem unpresented_core_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (K : Language) (hcoreK : Stage3Case017.informationCore family input ⊆ K) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K := by
  intro x hx
  have hcovered := informationCore_covered family input hcore hx.1
  rcases hcovered with hin | hout
  · exact False.elim (hx.2 hin)
  · exact ⟨output_subset_generatorFirst family input hout, hcoreK hx.1⟩

private theorem novel_for_compatible {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (trajectory (generator family) input) (family j) := by
  obtain ⟨T, hmem⟩ := trajectory_mem_informationCore family input hcore
  refine ⟨T, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_⟩
  · exact (hmem t ht) j hj
  · intro hs
    rw [GenLimit.mem_sample_iff] at hs
    obtain ⟨s, hst, heq⟩ := hs
    exact trajectory_ne_input family input (Nat.lt_succ_iff.mp hst) heq
  · intro s hst
    exact trajectory_ne_previous family input hst

theorem succeeds {m : ℕ} (family : Fin m → Language)
    (hinfinite : ∀ j, (family j).Infinite) :
    Stage3Case017.SucceedsFor family (generator family) := by
  intro input hinj hpresentation hcore
  let output := trajectory (generator family) input
  refine ⟨output, trajectory_follows (generator family) input, ?_⟩
  intro j hj
  have hcoreK : Stage3Case017.informationCore family input ⊆ family j := by
    intro x hx
    exact hx j hj
  refine ⟨novel_for_compatible family input hcore j hj, ?_⟩
  apply max_le
  · exact density_half family input hinj hcore (family j) (hinfinite j) hcoreK
  · apply relativeLowerDensity_mono
      (unpresented_core_subset_generatorFirst family input hcore (family j) hcoreK)
    exact Set.inter_subset_right

end Case017
