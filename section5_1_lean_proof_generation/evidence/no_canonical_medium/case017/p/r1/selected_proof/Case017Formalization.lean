import Stage3Model

open Set Filter
open scoped Topology

namespace Case017Proof

noncomputable section

open Classical

open Stage3Case017

def currentCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) : Language :=
  {z | ∀ j, (∀ i, xs i ∈ family j) → z ∈ family j}

def available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) : Set ℕ :=
  currentCore family xs \ (Set.range xs ∪ Set.range ys)

noncomputable def generator {m : ℕ} (family : Fin m → Language) : OnlineGenerator :=
  fun _ xs ys => sInf (available family xs ys)

noncomputable def trajectory {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Stream := by
  let rec go (t : ℕ) : ℕ :=
    generator family t (fun i => input i) (fun i => go i)
  termination_by t
  decreasing_by exact i.isLt
  exact go

theorem trajectory_follows {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Follows (generator family) input (trajectory family input) := by
  intro t
  unfold trajectory
  rw [trajectory.go.eq_def]

def Bad {m : ℕ} (family : Fin m → Language) (input : Stream) : Set (Fin m) :=
  {j | ¬ GenLimit.Generic.StreamIn input (family j)}

noncomputable def witnessTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ :=
  if h : ∃ s, input s ∉ family j then Nat.find h else 0

noncomputable def stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) : ℕ :=
  Finset.univ.sup (witnessTime family input)

theorem witnessTime_spec {m : ℕ} (family : Fin m → Language)
    (input : Stream) {j : Fin m} (hj : j ∈ Bad family input) :
    input (witnessTime family input j) ∉ family j := by
  have hex : ∃ s, input s ∉ family j := by
    rcases Set.not_subset.mp hj with ⟨x, ⟨s, rfl⟩, hx⟩
    exact ⟨s, hx⟩
  rw [witnessTime, dif_pos hex]
  exact Nat.find_spec hex

theorem witnessTime_le_stableTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) :
    witnessTime family input j ≤ stableTime family input := by
  exact Finset.le_sup (Finset.mem_univ j)

theorem currentCore_eq_informationCore {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (ht : stableTime family input ≤ t) :
    currentCore family (fun i : Fin (t + 1) => input i) = informationCore family input := by
  ext z
  constructor
  · intro hz j hj
    exact hz j (fun i => hj ⟨i, rfl⟩)
  · intro hz j hj
    apply hz j
    intro x hx
    rcases hx with ⟨s, rfl⟩
    by_contra hmem
    have hjbad : j ∈ Bad family input := by
      intro hstream
      exact hmem (hstream ⟨s, rfl⟩)
    have hwt := witnessTime_le_stableTime family input j
    have hidx : witnessTime family input j < t + 1 :=
      Nat.lt_succ_of_le (hwt.trans ht)
    exact (witnessTime_spec family input hjbad)
      (hj ⟨witnessTime family input j, hidx⟩)


theorem available_nonempty {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (output : Stream)
    (hcore : (informationCore family input).Infinite)
    (ht : stableTime family input ≤ t) :
    (available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i)).Nonempty := by
  rw [available, currentCore_eq_informationCore family input ht]
  exact (hcore.diff ((Set.finite_range _).union (Set.finite_range _))).nonempty

theorem trajectory_eventual_choice {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (ht : stableTime family input ≤ t) :
    trajectory family input t ∈
      available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => trajectory family input i) := by
  rw [trajectory_follows family input t, generator]
  exact Nat.sInf_mem (available_nonempty family input (trajectory family input) hcore ht)

theorem trajectory_eventual_core {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (ht : stableTime family input ≤ t) :
    trajectory family input t ∈ informationCore family input := by
  have h := (trajectory_eventual_choice family input hcore ht).1
  rwa [currentCore_eq_informationCore family input ht] at h

theorem trajectory_eventual_fresh_input {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (ht : stableTime family input ≤ t) :
    trajectory family input t ∉ GenLimit.sample input (t + 1) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨s, hs, heq⟩
  have hslt : s < t + 1 := Finset.mem_range.mp hs
  have hnot := (trajectory_eventual_choice family input hcore ht).2
  apply hnot
  left
  exact ⟨⟨s, hslt⟩, heq⟩

theorem trajectory_eventual_norepeat {m t : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (ht : stableTime family input ≤ t) :
    ∀ s, s < t → trajectory family input s ≠ trajectory family input t := by
  intro s hs heq
  have hnot := (trajectory_eventual_choice family input hcore ht).2
  apply hnot
  right
  exact ⟨⟨s, hs⟩, heq⟩

theorem core_not_input_eventually_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    ∀ z, z ∈ informationCore family input → z ∉ Set.range input →
      ∃ t, trajectory family input t = z := by
  intro z
  induction z using Nat.strong_induction_on with
  | h z ih =>
      intro hzcore hzinput
      by_cases hzout : ∃ t, trajectory family input t = z
      · exact hzout
      · have hclaim : ∀ w, w < z → w ∈ informationCore family input →
            ∃ s, input s = w ∨ trajectory family input s = w := by
          intro w hwlt hwcore
          by_cases hwinput : w ∈ Set.range input
          · rcases hwinput with ⟨s, hs⟩
            exact ⟨s, Or.inl hs⟩
          · rcases ih w hwlt hwcore hwinput with ⟨s, hs⟩
            exact ⟨s, Or.inr hs⟩
        let claimTime : ℕ → ℕ := fun w =>
          if hw : w < z ∧ w ∈ informationCore family input then
            Nat.find (hclaim w hw.1 hw.2)
          else 0
        let T := max (stableTime family input)
          ((Finset.range z).sup claimTime + 1)
        have hstable : stableTime family input ≤ T := le_max_left _ _
        have hzavail : z ∈ available family (fun i : Fin (T + 1) => input i)
            (fun i : Fin T => trajectory family input i) := by
          constructor
          · rw [currentCore_eq_informationCore family input hstable]
            exact hzcore
          · intro hbad
            rcases hbad with hin | hout
            · rcases hin with ⟨i, hi⟩
              exact hzinput ⟨i, hi⟩
            · rcases hout with ⟨i, hi⟩
              exact hzout ⟨i, hi⟩
        have hle : trajectory family input T ≤ z := by
          rw [trajectory_follows family input T, generator]
          exact Nat.sInf_le hzavail
        have hge : z ≤ trajectory family input T := by
          by_contra hnot
          have houtlt : trajectory family input T < z := Nat.lt_of_not_ge hnot
          have houtcore := trajectory_eventual_core family input hcore hstable
          have hct_le : claimTime (trajectory family input T) ≤
              (Finset.range z).sup claimTime :=
            Finset.le_sup (Finset.mem_range.mpr houtlt)
          have hct_lt : claimTime (trajectory family input T) < T := by
            exact lt_of_lt_of_le (Nat.lt_succ_of_le hct_le) (le_max_right _ _)
          have hspec : input (claimTime (trajectory family input T)) =
                trajectory family input T ∨
              trajectory family input (claimTime (trajectory family input T)) =
                trajectory family input T := by
            dsimp [claimTime]
            rw [dif_pos ⟨houtlt, houtcore⟩]
            exact Nat.find_spec (hclaim _ houtlt houtcore)
          have havail := (trajectory_eventual_choice family input hcore hstable).2
          apply havail
          rcases hspec with hin | hout
          · left
            exact ⟨⟨claimTime (trajectory family input T),
              lt_trans hct_lt (Nat.lt_succ_self T)⟩, hin⟩
          · right
            exact ⟨⟨claimTime (trajectory family input T), hct_lt⟩, hout⟩
        exact ⟨T, Nat.le_antisymm hle hge⟩

theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory family input) := by
  intro z hz
  rcases core_not_input_eventually_output family input hcore z hz.1 hz.2 with ⟨t, ht⟩
  refine ⟨t, ht, ?_⟩
  intro s hs heq
  exact hz.2 ⟨s, heq⟩

theorem prefixCount_mono {A B : Language} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

theorem relativeLowerDensity_mono_left {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply Filter.liminf_le_liminf
  · filter_upwards with n
    exact div_le_div_of_nonneg_right
      (mod_cast prefixCount_mono hAB n) (Nat.cast_nonneg _)
  · refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
        GenLimit.PatientScope.prefixCount K n
    exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · refine ⟨1, ?_⟩
    intro a ha
    change ∀ᶠ n in atTop, a ≤
      (GenLimit.PatientScope.prefixCount B n : ℝ) /
        GenLimit.PatientScope.prefixCount K n at ha
    have hone : ∀ᶠ n in atTop,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
            GenLimit.PatientScope.prefixCount K n ≤ 1 :=
      Eventually.of_forall fun n => by
        by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
        · have hb : GenLimit.PatientScope.prefixCount B n = 0 :=
            Nat.eq_zero_of_le_zero (hk ▸ prefixCount_mono hBK n)
          simp [hk, hb]
        · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))).2
            (mod_cast prefixCount_mono hBK n)
    rcases (ha.and hone).exists with ⟨n, han, hn⟩
    exact han.trans hn

theorem core_diff_density_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) (family j) := by
  apply relativeLowerDensity_mono_left
  · intro z hz
    exact ⟨core_diff_range_subset_generatorFirst family input hcore hz,
        hz.1 j hj⟩
  · exact inter_subset_right


noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ :=
  if h : ∃ t, input t = z then Nat.find h else 0

theorem firstInputTime_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInputTime input z) = z := by
  have h : ∃ t, input t = z := by
    rcases hz with ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  rw [firstInputTime, dif_pos h]
  exact Nat.find_spec h

theorem firstInputTime_min (input : Stream) {z s : ℕ}
    (hz : z ∈ Set.range input) (hs : s < firstInputTime input z) : input s ≠ z := by
  have h : ∃ t, input t = z := by
    rcases hz with ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  rw [firstInputTime, dif_pos h] at hs
  exact fun heq => Nat.find_min h hs heq

noncomputable def partner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (z : ℕ) : ℕ :=
  trajectory family input (firstInputTime input z - 1)

theorem partner_properties {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {z : ℕ} (hzcore : z ∈ informationCore family input)
    (hznot : z ∉ GenLimit.GeneratorFirst input (trajectory family input))
    (hearly : stableTime family input < firstInputTime input z) :
    partner family input z ∈ GenLimit.GeneratorFirst input (trajectory family input) ∧
      partner family input z < z := by
  have hzrange : z ∈ Set.range input := by
    by_contra hzrange
    exact hznot (core_diff_range_subset_generatorFirst family input hcore ⟨hzcore, hzrange⟩)
  let t := firstInputTime input z
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le _) hearly
  have hpred : t - 1 + 1 = t := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr htpos.ne')
  have hstablepred : stableTime family input ≤ t - 1 :=
    (Nat.le_sub_one_iff_lt htpos).2 hearly
  have hzavail : z ∈ available family (fun i : Fin (t - 1 + 1) => input i)
      (fun i : Fin (t - 1) => trajectory family input i) := by
    constructor
    · rw [currentCore_eq_informationCore family input hstablepred]
      exact hzcore
    · intro hbad
      rcases hbad with hin | hout
      · rcases hin with ⟨i, hi⟩
        apply firstInputTime_min input hzrange
        · change (i : ℕ) < t
          omega
        · exact hi
      · rcases hout with ⟨i, hi⟩
        apply hznot
        refine ⟨i, hi, ?_⟩
        intro s hs heq
        exact firstInputTime_min input hzrange
          (lt_of_le_of_lt hs (by change (i : ℕ) < t; omega)) heq
  have hp_le : partner family input z ≤ z := by
    rw [partner, trajectory_follows family input (t - 1), generator]
    exact Nat.sInf_le hzavail
  have hp_first : partner family input z ∈
      GenLimit.GeneratorFirst input (trajectory family input) := by
    refine ⟨t - 1, rfl, ?_⟩
    intro s hs heq
    have hfresh := trajectory_eventual_fresh_input family input hcore hstablepred
    apply hfresh
    apply Finset.mem_image.mpr
    exact ⟨s, Finset.mem_range.mpr (by omega), heq⟩
  refine ⟨hp_first, lt_of_le_of_ne hp_le ?_⟩
  intro heq
  apply hznot
  simpa [heq] using hp_first

theorem partner_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) :
    Set.InjOn (partner family input)
      {z | z ∈ informationCore family input ∧
        z ∉ GenLimit.GeneratorFirst input (trajectory family input) ∧
        stableTime family input < firstInputTime input z} := by
  intro z₁ hz₁ z₂ hz₂ heq
  have hp₁ := partner_properties family input hcore hz₁.1 hz₁.2.1 hz₁.2.2
  have hp₂ := partner_properties family input hcore hz₂.1 hz₂.2.1 hz₂.2.2
  let t₁ := firstInputTime input z₁
  let t₂ := firstInputTime input z₂
  have ht₁ : stableTime family input ≤ t₁ - 1 :=
    (Nat.le_sub_one_iff_lt (lt_of_le_of_lt (Nat.zero_le _) hz₁.2.2)).2 hz₁.2.2
  have ht₂ : stableTime family input ≤ t₂ - 1 :=
    (Nat.le_sub_one_iff_lt (lt_of_le_of_lt (Nat.zero_le _) hz₂.2.2)).2 hz₂.2.2
  have htimes : t₁ - 1 = t₂ - 1 := by
    apply le_antisymm
    · by_contra hnot
      have hlt : t₂ - 1 < t₁ - 1 := Nat.lt_of_not_ge hnot
      exact (trajectory_eventual_norepeat family input hcore ht₁ (t₂ - 1) hlt)
        (by simpa [partner, t₁, t₂] using heq.symm)
    · by_contra hnot
      have hlt : t₁ - 1 < t₂ - 1 := Nat.lt_of_not_ge hnot
      exact (trajectory_eventual_norepeat family input hcore ht₂ (t₁ - 1) hlt)
        (by simpa [partner, t₁, t₂] using heq)
  have ht₁pos : 0 < t₁ := lt_of_le_of_lt (Nat.zero_le _) hz₁.2.2
  have ht₂pos : 0 < t₂ := lt_of_le_of_lt (Nat.zero_le _) hz₂.2.2
  have ht_eq : t₁ = t₂ := by omega
  have hz₁range : z₁ ∈ Set.range input := by
    by_contra h
    exact hz₁.2.1
      (core_diff_range_subset_generatorFirst family input hcore ⟨hz₁.1, h⟩)
  have hz₂range : z₂ ∈ Set.range input := by
    by_contra h
    exact hz₂.2.1
      (core_diff_range_subset_generatorFirst family input hcore ⟨hz₂.1, h⟩)
  calc
    z₁ = input t₁ := (firstInputTime_spec input hz₁range).symm
    _ = input t₂ := congrArg input ht_eq
    _ = z₂ := firstInputTime_spec input hz₂range


theorem core_prefix_le_twice_generator_prefix {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    (hinj : Function.Injective input) {j : Fin m}
    (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n +
      (stableTime family input + 1) := by
  let C := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let D := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n
  let E := (Finset.range (stableTime family input + 1)).image input
  let B := C \ (D ∪ E)
  have hmap : Set.MapsTo (partner family input) (↑B : Set ℕ) (↑D : Set ℕ) := by
    intro z hz
    have hzC : z ∈ C := (Finset.mem_sdiff.mp hz).1
    have hznot : z ∉ D ∪ E := (Finset.mem_sdiff.mp hz).2
    have hzcore : z ∈ informationCore family input := by
      exact (Finset.mem_filter.mp hzC).2
    have hzlt : z < n := Finset.mem_range.mp (Finset.mem_filter.mp hzC).1
    have hznotGF : z ∉ GenLimit.GeneratorFirst input (trajectory family input) := by
      intro hGF
      apply hznot
      apply Finset.mem_union_left E
      have hzD : z ∈ GenLimit.PatientScope.prefixFinset
          (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n := by
        simp [GenLimit.PatientScope.prefixFinset, hzlt, hGF, hzcore j hj]
      simpa only [D] using hzD
    have hzrange : z ∈ Set.range input := by
      by_contra h
      exact hznotGF
        (core_diff_range_subset_generatorFirst family input hcore ⟨hzcore, h⟩)
    have hearly : stableTime family input < firstInputTime input z := by
      by_contra h
      have hle : firstInputTime input z ≤ stableTime family input := Nat.le_of_not_gt h
      apply hznot
      apply Finset.mem_union_right D
      apply Finset.mem_image.mpr
      exact ⟨firstInputTime input z, Finset.mem_range.mpr (Nat.lt_succ_of_le hle),
        firstInputTime_spec input hzrange⟩
    have hp := partner_properties family input hcore hzcore hznotGF hearly
    have hpcore : partner family input z ∈ informationCore family input := by
      unfold partner
      exact trajectory_eventual_core family input hcore
        ((Nat.le_sub_one_iff_lt (lt_of_le_of_lt (Nat.zero_le _) hearly)).2 hearly)
    have hpD : partner family input z ∈ GenLimit.PatientScope.prefixFinset
        (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n := by
      simp [GenLimit.PatientScope.prefixFinset, hp.2.trans hzlt, hp.1, hpcore j hj]
    simpa only [D] using hpD
  have hinjB : Set.InjOn (partner family input) (↑B : Set ℕ) := by
    apply (partner_injective family input hinj hcore).mono
    intro z hz
    have hzC : z ∈ C := (Finset.mem_sdiff.mp hz).1
    have hznot : z ∉ D ∪ E := (Finset.mem_sdiff.mp hz).2
    have hzcore : z ∈ informationCore family input := (Finset.mem_filter.mp hzC).2
    have hzlt : z < n := Finset.mem_range.mp (Finset.mem_filter.mp hzC).1
    have hznotGF : z ∉ GenLimit.GeneratorFirst input (trajectory family input) := by
      intro hGF
      apply hznot
      apply Finset.mem_union_left E
      have hzD : z ∈ GenLimit.PatientScope.prefixFinset
          (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n := by
        simp [GenLimit.PatientScope.prefixFinset, hzlt, hGF, hzcore j hj]
      simpa only [D] using hzD
    have hzrange : z ∈ Set.range input := by
      by_contra h
      exact hznotGF
        (core_diff_range_subset_generatorFirst family input hcore ⟨hzcore, h⟩)
    refine ⟨hzcore, hznotGF, ?_⟩
    by_contra h
    have hle : firstInputTime input z ≤ stableTime family input := Nat.le_of_not_gt h
    apply hznot
    apply Finset.mem_union_right D
    exact Finset.mem_image.mpr
      ⟨firstInputTime input z, Finset.mem_range.mpr (Nat.lt_succ_of_le hle),
        firstInputTime_spec input hzrange⟩
  have hB : B.card ≤ D.card := Finset.card_le_card_of_injOn _ hmap hinjB
  have hE : E.card ≤ stableTime family input + 1 := by
    exact Finset.card_image_le.trans_eq (Finset.card_range _)
  have hC : C.card ≤ B.card + (D ∪ E).card := by
    exact Finset.card_le_card_sdiff_add_card
  have hDE : (D ∪ E).card ≤ D.card + E.card := Finset.card_union_le _ _
  change C.card ≤ 2 * D.card + (stableTime family input + 1)
  omega


theorem prefixCount_tendsto_atTop {K : Language} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  rcases hK.exists_subset_card_eq b with ⟨S, hSK, hcard⟩
  let N := S.sup (fun x : ℕ => x) + 1
  refine ⟨N, fun n hn => ?_⟩
  have hsub : S ⊆ GenLimit.PatientScope.prefixFinset K n := by
    intro z hz
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, hSK hz⟩
    have hzle : z ≤ S.sup (fun x : ℕ => x) :=
      Finset.le_sup (f := fun x : ℕ => x) hz
    exact lt_of_le_of_lt hzle (lt_of_lt_of_le (Nat.lt_succ_self _) hn)
  rw [GenLimit.PatientScope.prefixCount, ← hcard]
  exact Finset.card_le_card hsub

theorem ratio_lower_bounded (A K : Language) :
    IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop
      (fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        GenLimit.PatientScope.prefixCount K n) := by
  apply isBoundedUnder_of_eventually_ge
  exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ratio_cobounded_ge {A K : Language} (hAK : A ⊆ K) :
    IsCoboundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop
      (fun n => (GenLimit.PatientScope.prefixCount A n : ℝ) /
        GenLimit.PatientScope.prefixCount K n) := by
  refine ⟨1, ?_⟩
  intro a ha
  have hone : ∀ᶠ n in atTop,
      (GenLimit.PatientScope.prefixCount A n : ℝ) /
          GenLimit.PatientScope.prefixCount K n ≤ 1 :=
    Eventually.of_forall fun n => by
      by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
      · have hA : GenLimit.PatientScope.prefixCount A n = 0 :=
          Nat.eq_zero_of_le_zero (hk ▸ prefixCount_mono hAK n)
        simp [hk, hA]
      · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))).2
          (mod_cast prefixCount_mono hAK n)
  change ∀ᶠ n in atTop,
    a ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      GenLimit.PatientScope.prefixCount K n at ha
  rcases (ha.and hone).exists with ⟨n, han, hn⟩
  exact han.trans hn

theorem half_core_density_le {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j))
    (hK : (family j).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) (family j) := by
  let A : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (informationCore family input) n : ℝ) /
      GenLimit.PatientScope.prefixCount (family j) n
  let D : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount
      (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n : ℝ) /
      GenLimit.PatientScope.prefixCount (family j) n
  let c : ℝ := stableTime family input + 1
  have hcount := prefixCount_tendsto_atTop hK
  have hden : Tendsto (fun n => (GenLimit.PatientScope.prefixCount (family j) n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hcount
  have herr : Tendsto (fun n => c /
      (GenLimit.PatientScope.prefixCount (family j) n : ℝ)) atTop (𝓝 0) :=
    hden.const_div_atTop c
  change (1 / 2 : ℝ) * liminf A atTop ≤ liminf D atTop
  apply le_of_forall_lt_imp_le_of_dense
  intro x hx
  have hx2 : 2 * x < liminf A atTop := by
    nlinarith
  obtain ⟨y, hxy, hy⟩ := exists_between hx2
  have hAevent : ∀ᶠ n in atTop, y < A n :=
    eventually_lt_of_lt_liminf hy (ratio_lower_bounded _ _)
  have herrEvent : ∀ᶠ n in atTop,
      c / (GenLimit.PatientScope.prefixCount (family j) n : ℝ) < y - 2 * x := by
    apply (tendsto_order.1 herr).2
    linarith
  have hpos : ∀ᶠ n in atTop, 0 < GenLimit.PatientScope.prefixCount (family j) n :=
    (tendsto_atTop.1 hcount 1)
  have hxD : ∀ᶠ n in atTop, x ≤ D n := by
    filter_upwards [hAevent, herrEvent, hpos] with n hAn herrn hKn
    have hnat := core_prefix_le_twice_generator_prefix family input hcore hinj hj n
    have hreal : A n ≤ 2 * D n + c /
        (GenLimit.PatientScope.prefixCount (family j) n : ℝ) := by
      dsimp [A, D, c]
      have hkreal : (0 : ℝ) < GenLimit.PatientScope.prefixCount (family j) n :=
        Nat.cast_pos.mpr hKn
      have hrealCount :
          (GenLimit.PatientScope.prefixCount (informationCore family input) n : ℝ) ≤
            2 * (GenLimit.PatientScope.prefixCount
              (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n : ℝ) +
              ((stableTime family input : ℝ) + 1) := by
        exact_mod_cast hnat
      calc
        _ ≤ (2 * (GenLimit.PatientScope.prefixCount
              (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j) n : ℝ) +
              ((stableTime family input : ℝ) + 1)) /
              GenLimit.PatientScope.prefixCount (family j) n :=
          (div_le_div_iff_of_pos_right hkreal).2 hrealCount
        _ = _ := by ring
    linarith
  exact le_liminf_of_le (ratio_cobounded_ge inter_subset_right) hxD

theorem trajectory_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (trajectory family input) (family j) := by
  refine ⟨stableTime family input, fun t ht => ?_⟩
  refine ⟨?_, trajectory_eventual_fresh_input family input hcore ht,
    trajectory_eventual_norepeat family input hcore ht⟩
  exact (trajectory_eventual_core family input hcore ht) j hj

end

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hfamily
  refine ⟨Case017Proof.generator family, ?_⟩
  intro input hinj hex hcore
  refine ⟨Case017Proof.trajectory family input,
    Case017Proof.trajectory_follows family input, ?_⟩
  intro j hj
  refine ⟨Case017Proof.trajectory_novel family input hcore hj, ?_⟩
  apply max_le
  · exact Case017Proof.half_core_density_le family input hinj hcore hj (hfamily j)
  · exact Case017Proof.core_diff_density_le family input hcore hj
