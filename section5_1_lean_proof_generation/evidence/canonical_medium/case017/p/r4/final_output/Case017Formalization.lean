import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

noncomputable def viable {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (j : Fin m) : Prop :=
  ∀ i, xs i ∈ family j

noncomputable def available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  (∀ j, viable family xs j → z ∈ family j) ∧
    (∀ i, xs i ≠ z) ∧ (∀ i, ys i ≠ z)

noncomputable def generator {m : ℕ} (family : Fin m → Language) : OnlineGenerator :=
  fun t xs ys => by
    classical
    exact if h : ∃ z, available family xs ys z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => Nat.strongRecOn t (fun t rec => gen t (fun i => input i) (fun i => rec i i.isLt))

lemma trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  rw [trajectory, Nat.strongRecOn_eq]
  congr 1

lemma generator_available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, available family xs ys z) :
    available family xs ys (generator family t xs ys) := by
  classical
  rw [generator, dif_pos h]
  exact Nat.find_spec h

lemma streamIn_iff (input : Stream) (L : Language) :
    GenLimit.Generic.StreamIn input L ↔ ∀ n, input n ∈ L := by
  constructor
  · intro h n
    exact h ⟨n, rfl⟩
  · rintro h z ⟨n, rfl⟩
    exact h n

noncomputable def exclusionTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Nat.find (show ∃ n, input n ∉ family j by
      simpa [streamIn_iff] using h)

lemma exclusionTime_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (exclusionTime family input j) ∉ family j := by
  classical
  rw [exclusionTime, dif_neg h]
  exact Nat.find_spec (show ∃ n, input n ∉ family j by
    simpa [streamIn_iff] using h)

noncomputable def stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  Finset.univ.sup (exclusionTime family input)

lemma exclusionTime_le_stabilizationTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    exclusionTime family input j ≤ stabilizationTime family input := by
  exact Finset.le_sup (Finset.mem_univ j)

lemma viable_iff_streamIn {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t) (j : Fin m) :
    viable family (fun i : Fin (t + 1) => input i) j ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hv
    by_contra hnot
    have hw := exclusionTime_spec family input j hnot
    have hle : exclusionTime family input j < t + 1 :=
      Nat.lt_succ_of_le (le_trans (exclusionTime_le_stabilizationTime family input j) ht)
    exact hw (hv ⟨exclusionTime family input j, hle⟩)
  · intro hs i
    exact (streamIn_iff input (family j)).1 hs i

lemma viable_core {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t) (z : ℕ) :
    (∀ j, viable family (fun i : Fin (t + 1) => input i) j → z ∈ family j) ↔
      z ∈ informationCore family input := by
  simp only [informationCore, mem_setOf_eq]
  constructor <;> intro h j hj
  · exact h j ((viable_iff_streamIn family input ht j).2 hj)
  · exact h j ((viable_iff_streamIn family input ht j).1 hj)

lemma available_exists_of_core_infinite {m t : ℕ} (family : Fin m → Language)
    (input output : Stream) (ht : stabilizationTime family input ≤ t)
    (hcore : (informationCore family input).Infinite) :
    ∃ z, available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i) z := by
  classical
  let forbidden : Finset ℕ :=
    (Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
      (Finset.univ.image (fun i : Fin t => output i))
  obtain ⟨z, hzcore, hzforbidden⟩ := hcore.exists_not_mem_finset forbidden
  refine ⟨z, (viable_core family input ht z).2 hzcore, ?_, ?_⟩
  · intro i hi
    apply hzforbidden
    rw [← hi]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · intro i hi
    apply hzforbidden
    rw [← hi]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

lemma trajectory_tail_available {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t)
    (hcore : (informationCore family input).Infinite) :
    available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => trajectory (generator family) input i)
      (trajectory (generator family) input t) := by
  rw [trajectory_follows (generator family) input t]
  exact generator_available family _ _
    (available_exists_of_core_infinite family input _ ht hcore)

lemma trajectory_tail_core {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t)
    (hcore : (informationCore family input).Infinite) :
    trajectory (generator family) input t ∈ informationCore family input := by
  exact (viable_core family input ht _).1
    (trajectory_tail_available family input ht hcore).1

lemma trajectory_tail_input_fresh {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t)
    (hcore : (informationCore family input).Infinite) (s : ℕ) (hs : s ≤ t) :
    input s ≠ trajectory (generator family) input t := by
  exact (trajectory_tail_available family input ht hcore).2.1 ⟨s, Nat.lt_succ_iff.2 hs⟩

lemma trajectory_tail_output_fresh {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t)
    (hcore : (informationCore family input).Infinite) (s : ℕ) (hs : s < t) :
    trajectory (generator family) input s ≠ trajectory (generator family) input t := by
  exact (trajectory_tail_available family input ht hcore).2.2 ⟨s, hs⟩

lemma trajectory_tail_min {m t z : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stabilizationTime family input ≤ t)
    (hcore : (informationCore family input).Infinite)
    (hzcore : z ∈ informationCore family input)
    (hzinput : ∀ s, s ≤ t → input s ≠ z)
    (hzoutput : ∀ s, s < t → trajectory (generator family) input s ≠ z) :
    trajectory (generator family) input t ≤ z := by
  classical
  let xs : Fin (t + 1) → ℕ := fun i => input i
  let ys : Fin t → ℕ := fun i => trajectory (generator family) input i
  have hav : available family xs ys z := by
    refine ⟨(viable_core family input ht z).2 hzcore, ?_, ?_⟩
    · intro i
      exact hzinput i (Nat.le_of_lt_succ i.isLt)
    · intro i
      exact hzoutput i i.isLt
  have hex : ∃ w, available family xs ys w := ⟨z, hav⟩
  rw [trajectory_follows (generator family) input t, generator, dif_pos hex]
  exact Nat.find_min' hex hav

lemma trajectory_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (trajectory (generator family) input) (family j) := by
  refine ⟨stabilizationTime family input, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_⟩
  · exact (trajectory_tail_core family input ht hcore) j hj
  · simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro s hs
    exact trajectory_tail_input_fresh family input ht hcore s (Nat.lt_succ_iff.1 hs)
  · intro s hs
    exact trajectory_tail_output_fresh family input ht hcore s hs

lemma tail_trajectory_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    Function.Injective (fun n => trajectory (generator family) input
      (stabilizationTime family input + n)) := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hfresh := trajectory_tail_output_fresh family input
      (show stabilizationTime family input ≤ stabilizationTime family input + b by omega)
      hcore (stabilizationTime family input + a) (by omega)
    exact False.elim (hfresh hab)
  · exact heq
  · have hfresh := trajectory_tail_output_fresh family input
      (show stabilizationTime family input ≤ stabilizationTime family input + a by omega)
      hcore (stabilizationTime family input + b) (by omega)
    exact False.elim (hfresh hab.symm)

lemma tail_output_time_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {s t : ℕ} (hs : stabilizationTime family input ≤ s)
    (ht : stabilizationTime family input ≤ t)
    (heq : trajectory (generator family) input s =
      trajectory (generator family) input t) : s = t := by
  rcases lt_trichotomy s t with hlt | hst | hgt
  · exact False.elim ((trajectory_tail_output_fresh family input ht hcore s hlt) heq)
  · exact hst
  · exact False.elim ((trajectory_tail_output_fresh family input hs hcore t hgt) heq.symm)

lemma core_eventually_announced {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ informationCore family input) :
    z ∈ Set.range input ∨ z ∈ Set.range (trajectory (generator family) input) := by
  by_contra h
  push_neg at h
  obtain ⟨w, ⟨n, hn⟩, hw⟩ :=
    (Set.infinite_range_of_injective (tail_trajectory_injective family input hcore)).exists_gt z
  have hmin := trajectory_tail_min family input
    (show stabilizationTime family input ≤ stabilizationTime family input + n by omega)
    hcore hz
    (by intro s hs; exact fun heq => h.1 ⟨s, heq⟩)
    (by intro s hs; exact fun heq => h.2 ⟨s, heq⟩)
  change trajectory (generator family) input (stabilizationTime family input + n) = w at hn
  omega

lemma core_diff_range_subset_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  intro z hz
  obtain ⟨t, ht⟩ := (core_eventually_announced family input hcore hz.1).resolve_left hz.2
  refine ⟨t, ht, ?_⟩
  intro s hs heq
  exact hz.2 ⟨s, heq⟩

noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

lemma firstInput_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  rcases hz with ⟨t, ht⟩
  let hex : ∃ t, input t = z := ⟨t, ht⟩
  rw [firstInput, dif_pos hex]
  exact Nat.find_spec hex

lemma firstInput_min (input : Stream) {z : ℕ} (hz : z ∈ Set.range input)
    {s : ℕ} (hs : s < firstInput input z) : input s ≠ z := by
  classical
  rcases hz with ⟨t, ht⟩
  let hex : ∃ t, input t = z := ⟨t, ht⟩
  rw [firstInput, dif_pos hex] at hs
  exact Nat.find_min (m := s) hex hs

lemma firstInput_injective (input : Stream) :
    Set.InjOn (firstInput input) (Set.range input) := by
  intro x hx y hy hxy
  rw [← firstInput_spec input hx, ← firstInput_spec input hy, hxy]

lemma core_not_generatorFirst_in_input_range {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) {z : ℕ}
    (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input)) :
    z ∈ Set.range input := by
  by_contra hzrange
  exact hznot (core_diff_range_subset_generatorFirst family input hcore ⟨hzcore, hzrange⟩)

lemma later_bad_is_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {x y : ℕ}
    (hxcore : x ∈ informationCore family input)
    (hxnot : x ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input))
    (hxlate : stabilizationTime family input ≤ firstInput input x)
    (hycore : y ∈ informationCore family input)
    (hynot : y ∉ GenLimit.GeneratorFirst input (trajectory (generator family) input))
    (hxy : firstInput input x < firstInput input y) :
    trajectory (generator family) input (firstInput input x) < y + 1 ∧
      trajectory (generator family) input (firstInput input x) ∈
        GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  have hxrange := core_not_generatorFirst_in_input_range family input hcore hxcore hxnot
  have hyrange := core_not_generatorFirst_in_input_range family input hcore hycore hynot
  have hyinput : ∀ s, s ≤ firstInput input x → input s ≠ y := by
    intro s hs
    exact firstInput_min input hyrange (lt_of_le_of_lt hs hxy)
  have hyoutput : ∀ s, s < firstInput input x →
      trajectory (generator family) input s ≠ y := by
    intro s hs heq
    apply hynot
    refine ⟨s, heq, ?_⟩
    intro r hr
    exact hyinput r (le_trans hr (Nat.le_of_lt hs))
  have hle := trajectory_tail_min family input hxlate hcore hycore hyinput hyoutput
  refine ⟨Nat.lt_succ_of_le hle, ?_⟩
  refine ⟨firstInput input x, rfl, ?_⟩
  intro s hs
  exact trajectory_tail_input_fresh family input hxlate hcore s hs

lemma mem_prefixFinset_iff {S : Set ℕ} {n z : ℕ} :
    z ∈ GenLimit.PatientScope.prefixFinset S n ↔ z < n ∧ z ∈ S := by
  simp [GenLimit.PatientScope.prefixFinset]

lemma core_prefix_count_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩
          informationCore family input) n +
        stabilizationTime family input + 1 := by
  classical
  let core := informationCore family input
  let gf := GenLimit.GeneratorFirst input (trajectory (generator family) input)
  let C := GenLimit.PatientScope.prefixFinset core n
  let D := C.filter (fun z => z ∈ gf)
  let B := C.filter (fun z => z ∉ gf)
  let early := B.filter (fun z => firstInput input z < stabilizationTime family input)
  let late := B.filter (fun z => stabilizationTime family input ≤ firstInput input z)
  have hBsplit : early.card + late.card = B.card := by
    simpa [early, late] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := B) (fun z => firstInput input z < stabilizationTime family input))
  have hCsplit : D.card + B.card = C.card := by
    simpa [D, B] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := C) (fun z => z ∈ gf))
  have hearly : early.card ≤ stabilizationTime family input := by
    rw [← Finset.card_range (stabilizationTime family input)]
    apply Finset.card_le_card_of_injOn (s := early)
      (t := Finset.range (stabilizationTime family input)) (firstInput input)
    · intro z hz
      have hzdata : z < n ∧ z ∈ core ∧ z ∉ gf ∧
          firstInput input z < stabilizationTime family input := by
        simpa [early, B, C, GenLimit.PatientScope.prefixFinset, and_assoc] using hz
      exact Finset.mem_range.2 hzdata.2.2.2
    · intro x hx y hy hxy
      have hxdata : x < n ∧ x ∈ core ∧ x ∉ gf ∧
          firstInput input x < stabilizationTime family input := by
        simpa [early, B, C, GenLimit.PatientScope.prefixFinset, and_assoc] using hx
      have hydata : y < n ∧ y ∈ core ∧ y ∉ gf ∧
          firstInput input y < stabilizationTime family input := by
        simpa [early, B, C, GenLimit.PatientScope.prefixFinset, and_assoc] using hy
      apply firstInput_injective input
      · exact core_not_generatorFirst_in_input_range family input hcore hxdata.2.1 hxdata.2.2.1
      · exact core_not_generatorFirst_in_input_range family input hcore hydata.2.1 hydata.2.2.1
      · exact hxy
  have hlate : late.card ≤ D.card + 1 := by
    by_cases hempty : late.Nonempty
    · obtain ⟨last, hlast, hmax⟩ := Finset.exists_max_image late (firstInput input) hempty
      let E := late.erase last
      have hE : E.card + 1 = late.card := Finset.card_erase_add_one hlast
      have hED : E.card ≤ D.card := by
        apply Finset.card_le_card_of_injOn
          (fun z => trajectory (generator family) input (firstInput input z))
        · intro x hxE
          have hxlate : x ∈ late := (Finset.mem_erase.1 hxE).2
          have hxne : x ≠ last := (Finset.mem_erase.1 hxE).1
          have hxB : x ∈ B := (Finset.mem_filter.1 hxlate).1
          have hxthreshold := (Finset.mem_filter.1 hxlate).2
          have hxCmem : x ∈ C := (Finset.mem_filter.1 hxB).1
          have hxC : x < n ∧ x ∈ core := by
            exact (mem_prefixFinset_iff).1 (show x ∈ GenLimit.PatientScope.prefixFinset core n from hxCmem)
          have hxnot : x ∉ gf := (Finset.mem_filter.1 hxB).2
          have hlastB : last ∈ B := (Finset.mem_filter.1 hlast).1
          have hlastCmem : last ∈ C := (Finset.mem_filter.1 hlastB).1
          have hlastC : last < n ∧ last ∈ core := by
            exact (mem_prefixFinset_iff).1
              (show last ∈ GenLimit.PatientScope.prefixFinset core n from hlastCmem)
          have hlastnot : last ∉ gf := (Finset.mem_filter.1 hlastB).2
          have hxrange := core_not_generatorFirst_in_input_range family input hcore hxC.2 hxnot
          have hlastrange := core_not_generatorFirst_in_input_range family input hcore hlastC.2 hlastnot
          have htimele := hmax x hxlate
          have htimene : firstInput input x ≠ firstInput input last := by
            intro heq
            exact hxne (firstInput_injective input hxrange hlastrange heq)
          have htimelt : firstInput input x < firstInput input last := lt_of_le_of_ne htimele htimene
          have hp := later_bad_is_available family input hcore hxC.2 hxnot hxthreshold
            hlastC.2 hlastnot htimelt
          apply Finset.mem_filter.2
          refine ⟨?_, hp.2⟩
          show trajectory (generator family) input (firstInput input x) ∈ C
          simp only [C, GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
          exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_iff.2 hlastC.1),
            trajectory_tail_core family input hxthreshold hcore⟩
        · intro x hx y hy heq
          have hxlate : x ∈ late := (Finset.mem_erase.1 hx).2
          have hylate : y ∈ late := (Finset.mem_erase.1 hy).2
          have hxthreshold := (Finset.mem_filter.1 hxlate).2
          have hythreshold := (Finset.mem_filter.1 hylate).2
          have htimes := tail_output_time_injective family input hcore hxthreshold hythreshold heq
          have hxB : x ∈ B := (Finset.mem_filter.1 hxlate).1
          have hyB : y ∈ B := (Finset.mem_filter.1 hylate).1
          have hxCmem : x ∈ C := (Finset.mem_filter.1 hxB).1
          have hyCmem : y ∈ C := (Finset.mem_filter.1 hyB).1
          have hxC : x < n ∧ x ∈ core := by
            exact (mem_prefixFinset_iff).1 (show x ∈ GenLimit.PatientScope.prefixFinset core n from hxCmem)
          have hyC : y < n ∧ y ∈ core := by
            simpa [C, GenLimit.PatientScope.prefixFinset] using hyCmem
          exact firstInput_injective input
            (core_not_generatorFirst_in_input_range family input hcore hxC.2 (Finset.mem_filter.1 hxB).2)
            (core_not_generatorFirst_in_input_range family input hcore hyC.2 (Finset.mem_filter.1 hyB).2)
            htimes
      omega
    · have : late = ∅ := Finset.not_nonempty_iff_eq_empty.1 hempty
      simp [this]
  have hDcount : D.card = GenLimit.PatientScope.prefixCount (gf ∩ core) n := by
    congr 1
    ext z
    simp [D, C, GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset, gf, core, and_comm, and_left_comm, and_assoc]
  have hCcount : C.card = GenLimit.PatientScope.prefixCount core n := rfl
  rw [← hCcount, ← hDcount]
  omega

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_tendsto_atTop {S : Set ℕ} (hS : S.Infinite) :
    Filter.Tendsto (GenLimit.PatientScope.prefixCount S) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨t, htS, htcard⟩ := hS.exists_subset_card_eq b
  obtain ⟨N, htN⟩ := t.exists_nat_subset_range
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [← htcard]
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
  exact ⟨lt_of_lt_of_le (Finset.mem_range.1 (htN hz)) hn, htS hz⟩

lemma constant_div_prefixCount_tendsto_zero {S : Set ℕ} (hS : S.Infinite) (c : ℝ) :
    Filter.Tendsto (fun n => c / (GenLimit.PatientScope.prefixCount S n : ℝ))
      Filter.atTop (nhds 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_natCast_atTop_atTop.comp (prefixCount_tendsto_atTop hS)

lemma ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

lemma ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  have hcount := prefixCount_mono hAK n
  by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
  · have ha : GenLimit.PatientScope.prefixCount A n = 0 := by omega
    simp [hk, ha]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hk)).2
    exact_mod_cast hcount

lemma ratio_bounded_below (A K : Set ℕ) :
    Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) Filter.atTop
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) := by
  apply Filter.isBoundedUnder_of
  exact ⟨0, ratio_nonneg A K⟩

lemma ratio_cobounded_below {A K : Set ℕ} (hAK : A ⊆ K) :
    Filter.IsCoboundedUnder (fun x y : ℝ => x ≥ y) Filter.atTop
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ)) := by
  exact Filter.isCoboundedUnder_ge_of_le Filter.atTop (ratio_le_one hAK)

lemma liminf_sub_zero_error_ge (u e : ℕ → ℝ)
    (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1)
    (he0 : ∀ n, 0 ≤ e n) (he : Filter.Tendsto e Filter.atTop (nhds 0)) :
    Filter.liminf u Filter.atTop ≤ Filter.liminf (fun n => u n - e n) Filter.atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have heε : ∀ᶠ n in Filter.atTop, e n ≤ ε := he.eventually_le_const hε
  have hmono : Filter.liminf (fun n => u n - ε) Filter.atTop ≤
      Filter.liminf (fun n => u n - e n) Filter.atTop := by
    apply Filter.liminf_le_liminf
    · filter_upwards [heε] with n hn
      linarith
    · apply Filter.isBoundedUnder_of
      exact ⟨-ε, fun n => by linarith [hu0 n]⟩
    · apply Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 1)
      intro n
      linarith [hu1 n, he0 n]
  have hsub := liminf_sub_const Filter.atTop u ε
    (Filter.isCoboundedUnder_ge_of_le Filter.atTop hu1)
    (by apply Filter.isBoundedUnder_of; exact ⟨0, hu0⟩)
  rw [hsub] at hmono
  linarith

lemma relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply Filter.liminf_le_liminf
  · filter_upwards [] with n
    exact div_le_div_of_nonneg_right
      (mod_cast prefixCount_mono hAB n) (Nat.cast_nonneg _)
  · show Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) Filter.atTop
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ))
    apply Filter.isBoundedUnder_of
    refine ⟨0, ?_⟩
    intro n
    exact div_nonneg (show (0 : ℝ) ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) by positivity)
      (show (0 : ℝ) ≤ (GenLimit.PatientScope.prefixCount K n : ℝ) by positivity)
  · apply Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := 1)
    intro n
    have hcount := prefixCount_mono hBK n
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · have hb : GenLimit.PatientScope.prefixCount B n = 0 := by omega
      simp [hk, hb]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hk)).2
      exact_mod_cast hcount

lemma half_core_density_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j))
    (hK : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j)
        (family j) := by
  let core := informationCore family input
  let gf := GenLimit.GeneratorFirst input (trajectory (generator family) input)
  let K := family j
  let dc := gf ∩ core
  let cseq : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount core n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let dseq : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount dc n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let err : ℕ → ℝ := fun n =>
    ((stabilizationTime family input + 1 : ℕ) : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let u : ℕ → ℝ := fun n => (1 / 2 : ℝ) * cseq n
  have hcoreK : core ⊆ K := by
    intro z hz
    exact hz j hj
  have hdcK : dc ⊆ K := fun z hz => hcoreK hz.2
  have hc0 : ∀ n, 0 ≤ cseq n := fun n => ratio_nonneg core K n
  have hc1 : ∀ n, cseq n ≤ 1 := fun n => ratio_le_one hcoreK n
  have hu0 : ∀ n, 0 ≤ u n := by intro n; dsimp [u]; positivity
  have hu1 : ∀ n, u n ≤ 1 := by
    intro n
    dsimp [u]
    nlinarith [hc0 n, hc1 n]
  have herr0 : ∀ n, 0 ≤ err n := by intro n; dsimp [err]; positivity
  have herr : Filter.Tendsto err Filter.atTop (nhds 0) := by
    exact constant_div_prefixCount_tendsto_zero hK _
  have hpoint : ∀ n, u n - err n ≤ dseq n := by
    intro n
    have hcount := core_prefix_count_le family input hcore n
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · have hc : GenLimit.PatientScope.prefixCount core n = 0 := by
        have := prefixCount_mono hcoreK n
        omega
      have hd : GenLimit.PatientScope.prefixCount dc n = 0 := by
        have := prefixCount_mono hdcK n
        omega
      simp [u, cseq, dseq, err, hk, hc, hd]
    · have hkpos : (0 : ℝ) < (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      dsimp [u, cseq, dseq, err]
      have hreal : (GenLimit.PatientScope.prefixCount core n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount dc n : ℝ) +
            (stabilizationTime family input : ℝ) + 1 := by exact_mod_cast hcount
      field_simp [ne_of_gt hkpos]
      norm_num [Nat.cast_add, Nat.cast_one] at *
      nlinarith [hreal]
  have hscale : (1 / 2 : ℝ) * Filter.liminf cseq Filter.atTop =
      Filter.liminf u Filter.atTop := by
    have hmap := Monotone.map_liminf_of_continuousAt (F := Filter.atTop)
      (f := fun x : ℝ => (1 / 2 : ℝ) * x)
      (fun _ _ h => mul_le_mul_of_nonneg_left h (by norm_num)) cseq
      ((continuous_const.mul continuous_id).continuousAt)
      (ratio_cobounded_below hcoreK) (ratio_bounded_below core K)
    simpa [u, Function.comp_def] using hmap
  have hperturb : Filter.liminf u Filter.atTop ≤
      Filter.liminf (fun n => u n - err n) Filter.atTop :=
    liminf_sub_zero_error_ge u err hu0 hu1 herr0 herr
  have htoD : Filter.liminf (fun n => u n - err n) Filter.atTop ≤
      Filter.liminf dseq Filter.atTop := by
    apply Filter.liminf_le_liminf
    · exact Filter.Eventually.of_forall hpoint
    · apply Filter.isBoundedUnder_of
      refine ⟨-((stabilizationTime family input + 1 : ℕ) : ℝ), ?_⟩
      intro n
      have herrle : err n ≤ ((stabilizationTime family input + 1 : ℕ) : ℝ) := by
        dsimp [err]
        by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
        · simp [hk]
          positivity
        · have hkone : (1 : ℝ) ≤ (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
          exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hkone)).2 (by nlinarith)
      linarith [hu0 n]
    · exact ratio_cobounded_below hdcK
  have hdensity : GenLimit.PatientScope.relativeLowerDensity dc K ≤
      GenLimit.PatientScope.relativeLowerDensity (gf ∩ K) K := by
    apply relativeLowerDensity_mono
    · intro z hz
      exact ⟨hz.1, hcoreK hz.2⟩
    · exact inter_subset_right
  change (1 / 2 : ℝ) * Filter.liminf cseq Filter.atTop ≤
    GenLimit.PatientScope.relativeLowerDensity (gf ∩ K) K
  rw [hscale]
  exact (hperturb.trans htoD).trans hdensity

lemma missing_core_density_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) (j : Fin m)
    (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ family j)
        (family j) := by
  apply relativeLowerDensity_mono
  · intro z hz
    exact ⟨core_diff_range_subset_generatorFirst family input hcore hz, hz.1 j hj⟩
  · exact inter_subset_right

end Stage3Case017Proof

open Stage3Case017
open Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨generator family, ?_⟩
  intro input hinj hpresentation hcore
  refine ⟨trajectory (generator family) input, trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨trajectory_novel family input hcore j hj, ?_⟩
  apply max_le
  · exact half_core_density_le family input hcore j hj (hfamily j)
  · exact missing_core_density_le family input hcore j hj
