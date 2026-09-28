import Stage3Model

open Set Filter
open scoped Topology

namespace Case017

abbrev Language := Stage3Case017.Language
abbrev Stream := Stage3Case017.Stream

noncomputable def finSample {n : ℕ} (x : Fin n → ℕ) : Finset ℕ :=
  Finset.univ.image x

noncomputable def versionCore {m n : ℕ} (family : Fin m → Language)
    (x : Fin n → ℕ) : Language :=
  {z | ∀ j, (∀ i, x i ∈ family j) → z ∈ family j}

noncomputable def leastFresh (preferred : Language) (used : Finset ℕ) : ℕ := by
  classical
  exact if h : preferred.Infinite then
    sInf (preferred \ (used : Set ℕ))
  else
    sInf ((Set.univ : Set ℕ) \ (used : Set ℕ))

lemma leastFresh_not_used (preferred : Language) (used : Finset ℕ) :
    leastFresh preferred used ∉ used := by
  classical
  unfold leastFresh
  split_ifs with h
  · have hn : (preferred \ (used : Set ℕ)).Nonempty := by
      obtain ⟨z, hz, hzu⟩ := h.exists_not_mem_finset used
      exact ⟨z, hz, hzu⟩
    exact (Nat.sInf_mem hn).2
  · have hn : ((Set.univ : Set ℕ) \ (used : Set ℕ)).Nonempty := by
      obtain ⟨z, hz⟩ := used.finite_toSet.exists_not_mem
      exact ⟨z, Set.mem_univ z, hz⟩
    exact (Nat.sInf_mem hn).2

lemma leastFresh_mem (preferred : Language) (used : Finset ℕ)
    (h : preferred.Infinite) : leastFresh preferred used ∈ preferred := by
  classical
  unfold leastFresh
  simp only [dif_pos h]
  have hn : (preferred \ (used : Set ℕ)).Nonempty := by
    obtain ⟨z, hz, hzu⟩ := h.exists_not_mem_finset used
    exact ⟨z, hz, hzu⟩
  exact (Nat.sInf_mem hn).1

lemma leastFresh_le (preferred : Language) (used : Finset ℕ)
    (h : preferred.Infinite) {z : ℕ} (hz : z ∈ preferred) (hzu : z ∉ used) :
    leastFresh preferred used ≤ z := by
  classical
  unfold leastFresh
  simp only [dif_pos h]
  exact Nat.sInf_le ⟨hz, hzu⟩

noncomputable def generator {m : ℕ} (family : Fin m → Language) :
    Stage3Case017.OnlineGenerator :=
  fun _ input previous =>
    leastFresh (versionCore family input)
      (finSample input ∪ finSample previous)

noncomputable def trajectory (gen : Stage3Case017.OnlineGenerator)
    (input : Stream) : Stream
  | 0 => gen 0 (fun i => input i) (fun i => Fin.elim0 i)
  | n + 1 => gen (n + 1) (fun i => input i)
      (fun i => trajectory gen input i)

lemma follows_generator {m : ℕ} (family : Fin m → Language) (input : Stream) :
    Stage3Case017.Follows (generator family) input
      (trajectory (generator family) input) := by
  intro t
  cases t with
  | zero =>
      simp [trajectory]
      congr
      funext i
      exact Fin.elim0 i
  | succ n => simp [trajectory]

lemma mem_finSample_iff {n : ℕ} {x : Fin n → ℕ} {z : ℕ} :
    z ∈ finSample x ↔ ∃ i, x i = z := by
  classical
  simp [finSample]

end Case017

namespace Case017

noncomputable def witnessTime {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
    else Classical.choose (Classical.not_forall.mp (Set.range_subset_iff.not.mp h))

lemma witnessTime_bad {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (witnessTime family input j) ∉ family j := by
  classical
  unfold witnessTime
  simp only [dif_neg h]
  exact Classical.choose_spec (Classical.not_forall.mp (Set.range_subset_iff.not.mp h))

lemma prefix_compat_iff {m : ℕ} (family : Fin m → Language)
    (input : Stream) (j : Fin m) {t : ℕ}
    (ht : witnessTime family input j ≤ t) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  classical
  constructor
  · intro hp
    by_cases hs : GenLimit.Generic.StreamIn input (family j)
    · exact hs
    · have hw := witnessTime_bad family input j hs
      exact False.elim (hw (hp ⟨witnessTime family input j, Nat.lt_succ_of_le ht⟩))
  · intro hs i
    exact hs ⟨i, rfl⟩

lemma versionCore_eq_informationCore {m : ℕ} (hm : 0 < m)
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      versionCore family (fun i : Fin (t+1) => input i) =
        Stage3Case017.informationCore family input := by
  classical
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  obtain ⟨j0, hj0⟩ := Finite.exists_max (witnessTime family input)
  refine ⟨witnessTime family input j0, ?_⟩
  intro t ht
  ext z
  simp only [versionCore, Stage3Case017.informationCore, Set.mem_setOf_eq]
  apply forall_congr'
  intro j
  rw [prefix_compat_iff family input j (le_trans (hj0 j) ht)]

lemma trajectory_step {m : ℕ} (family : Fin m → Language) (input : Stream) (t : ℕ) :
    trajectory (generator family) input t =
      leastFresh (versionCore family (fun i : Fin (t+1) => input i))
        (finSample (fun i : Fin (t+1) => input i) ∪
          finSample (fun i : Fin t => trajectory (generator family) input i)) := by
  rw [follows_generator family input t]
  rfl

lemma stable_output_properties {m : ℕ} (family : Fin m → Language)
    (input : Stream) {T t : ℕ} (ht : T ≤ t)
    (hstable : ∀ u, T ≤ u →
      versionCore family (fun i : Fin (u+1) => input i) =
        Stage3Case017.informationCore family input)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    let output := trajectory (generator family) input
    output t ∈ Stage3Case017.informationCore family input ∧
    output t ∉ GenLimit.Generic.sample input (t+1) ∧
    (∀ s, s < t → output s ≠ output t) ∧
    (∀ z ∈ Stage3Case017.informationCore family input,
      z ∉ GenLimit.Generic.sample input (t+1) →
      (∀ s, s < t → output s ≠ z) → output t ≤ z) := by
  classical
  dsimp
  rw [trajectory_step, hstable t ht]
  let used := finSample (fun i : Fin (t+1) => input i) ∪
    finSample (fun i : Fin t => trajectory (generator family) input i)
  have hnot := leastFresh_not_used
    (Stage3Case017.informationCore family input) used
  have hmem := leastFresh_mem
    (Stage3Case017.informationCore family input) used hcore
  refine ⟨hmem, ?_, ?_, ?_⟩
  · intro hs
    apply hnot
    apply Finset.mem_union_left
    have hs' : ∃ s ∈ Finset.range (t+1), input s = leastFresh (Stage3Case017.informationCore family input) used := by
      simpa [GenLimit.Generic.sample] using hs
    rcases hs' with ⟨s, hst, hs⟩
    rw [mem_finSample_iff]
    exact ⟨⟨s, Finset.mem_range.mp hst⟩, hs⟩
  · intro s hst heq
    apply hnot
    apply Finset.mem_union_right
    rw [mem_finSample_iff]
    exact ⟨⟨s, hst⟩, heq⟩
  · intro z hz hzin hzout
    apply leastFresh_le _ used hcore hz
    intro hzu
    rcases Finset.mem_union.mp hzu with hzu | hzu
    · rw [mem_finSample_iff] at hzu
      obtain ⟨i, hi⟩ := hzu
      apply hzin
      simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range]
      exact ⟨i, i.isLt, hi⟩
    · rw [mem_finSample_iff] at hzu
      obtain ⟨i, hi⟩ := hzu
      exact hzout i i.isLt hi

end Case017

namespace Case017

lemma core_minus_range_generated {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u →
      versionCore family (fun i : Fin (u+1) => input i) =
        Stage3Case017.informationCore family input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {z : ℕ} (hz : z ∈ Stage3Case017.informationCore family input)
    (hzinput : z ∉ Set.range input) :
    z ∈ Set.range (trajectory (generator family) input) := by
  classical
  let output := trajectory (generator family) input
  by_contra hzout
  have hoin : ∀ t, output t ≠ z := by
    intro t heq
    exact hzout ⟨t, heq⟩
  have hiin : ∀ t, input t ≠ z := by
    intro t heq
    exact hzinput ⟨t, heq⟩
  have hlt : ∀ i : Fin (z+1), output (T + i) < z := by
    intro i
    have hp := stable_output_properties family input (T := T)
      (t := T + i) (Nat.le_add_right T i) hstable hcore
    have hle := hp.2.2.2 z hz
    have hsample : z ∉ GenLimit.Generic.sample input (T + i + 1) := by
      intro hs
      simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range] at hs
      obtain ⟨k, hk, heq⟩ := hs
      exact hiin k heq
    have hprev : ∀ s, s < T + i → output s ≠ z := by
      intro s hs
      exact hoin s
    exact Nat.lt_of_le_of_ne (hle hsample hprev) (hoin (T+i))
  let f : Fin (z+1) → Fin z := fun i => ⟨output (T+i), hlt i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hout : output (T+i) = output (T+j) := congrArg Fin.val hij
    rcases lt_trichotomy i.val j.val with hijlt | hijeq | hijgt
    · have hp := stable_output_properties family input (T := T)
        (t := T+j) (Nat.le_add_right T j) hstable hcore
      have hne := hp.2.2.1 (T+i) (Nat.add_lt_add_left hijlt T)
      exact False.elim (hne hout)
    · exact hijeq
    · have hp := stable_output_properties family input (T := T)
        (t := T+i) (Nat.le_add_right T i) hstable hcore
      have hne := hp.2.2.1 (T+j) (Nat.add_lt_add_left hijgt T)
      exact False.elim (hne hout.symm)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

lemma core_minus_range_subset_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u →
      versionCore family (fun i : Fin (u+1) => input i) =
        Stage3Case017.informationCore family input)
    (hcore : (Stage3Case017.informationCore family input).Infinite) :
    Stage3Case017.informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (generator family) input) := by
  intro z hz
  obtain ⟨t, ht⟩ := core_minus_range_generated family input T hstable hcore hz.1 hz.2
  refine ⟨t, ht, ?_⟩
  intro s hs heq
  exact hz.2 ⟨s, heq⟩

end Case017

namespace Case017

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, hAB hz.2⟩

lemma relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf (hu := isBoundedUnder_of_eventually_ge (a := 0)
      (Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
    (hv := isCoboundedUnder_ge_of_le atTop (x := 1) (fun n => by
      by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
      · have hb : GenLimit.PatientScope.prefixCount B n = 0 :=
          Nat.eq_zero_of_le_zero (hk ▸ prefixCount_mono hBK n)
        simp [hk, hb]
      · apply (div_le_one (by positivity : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n)).2
        exact Nat.cast_le.mpr (prefixCount_mono hBK n))) 
  filter_upwards [] with n
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (prefixCount_mono hAB n)) (Nat.cast_nonneg _)

end Case017

namespace Case017

noncomputable def inputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

lemma inputTime_spec (input : Stream) {z : ℕ} (hz : z ∈ Set.range input) :
    input (inputTime input z) = z := by
  classical
  unfold inputTime
  simp only [dif_pos hz]
  exact Nat.find_spec hz

lemma loser_has_input {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u →
      versionCore family (fun i : Fin (u+1) => input i) =
        Stage3Case017.informationCore family input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {K : Set ℕ} (hIK : Stage3Case017.informationCore family input ⊆ K)
    {z : ℕ} (hzI : z ∈ Stage3Case017.informationCore family input)
    (hzD : z ∉ GenLimit.GeneratorFirst input
      (trajectory (generator family) input) ∩ K) :
    z ∈ Set.range input := by
  by_contra hzrange
  have hzGF := core_minus_range_subset_generatorFirst family input T hstable hcore
    ⟨hzI, hzrange⟩
  exact hzD ⟨hzGF, hIK hzI⟩

lemma output_at_loser_time {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ)
    (hstable : ∀ u, T ≤ u →
      versionCore family (fun i : Fin (u+1) => input i) =
        Stage3Case017.informationCore family input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {K : Set ℕ} (hIK : Stage3Case017.informationCore family input ⊆ K)
    {z : ℕ} (hzI : z ∈ Stage3Case017.informationCore family input)
    (hzD : z ∉ GenLimit.GeneratorFirst input
      (trajectory (generator family) input) ∩ K)
    (ht : T ≤ inputTime input z) :
    let output := trajectory (generator family) input
    output (inputTime input z) ∈ Stage3Case017.informationCore family input ∧
    output (inputTime input z) ∈ GenLimit.GeneratorFirst input output := by
  classical
  dsimp
  have hzrange := loser_has_input family input T hstable hcore hIK hzI hzD
  let t := inputTime input z
  have hp := stable_output_properties family input (T := T) (t := t) ht hstable hcore
  refine ⟨hp.1, ?_⟩
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  exact hp.2.1 (by
    simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range]
    exact ⟨s, Nat.lt_succ_of_le hs, heq⟩)

lemma loser_no_early_output {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) (T : ℕ)
    (hstable : ∀ u, T ≤ u →
      versionCore family (fun i : Fin (u+1) => input i) =
        Stage3Case017.informationCore family input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {K : Set ℕ} (hIK : Stage3Case017.informationCore family input ⊆ K)
    {z : ℕ} (hzI : z ∈ Stage3Case017.informationCore family input)
    (hzD : z ∉ GenLimit.GeneratorFirst input
      (trajectory (generator family) input) ∩ K) :
    ∀ s, s < inputTime input z → trajectory (generator family) input s ≠ z := by
  classical
  have hzrange := loser_has_input family input T hstable hcore hIK hzI hzD
  intro s hs heq
  apply hzD
  refine ⟨⟨s, heq, ?_⟩, hIK hzI⟩
  intro r hrs hir
  have hit := inputTime_spec input hzrange
  have := congrArg id (hir.trans hit.symm)
  have htimes : r = inputTime input z := hinj this
  omega

lemma half_prefix_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) (T : ℕ)
    (hstable : ∀ u, T ≤ u →
      versionCore family (fun i : Fin (u+1) => input i) =
        Stage3Case017.informationCore family input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {K : Set ℕ} (hIK : Stage3Case017.informationCore family input ⊆ K)
    (n : ℕ) :
    GenLimit.PatientScope.prefixCount
        (Stage3Case017.informationCore family input) n ≤
      2 * GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K) n + T + 1 := by
  classical
  let I := Stage3Case017.informationCore family input
  let output := trajectory (generator family) input
  let D := GenLimit.GeneratorFirst input output ∩ K
  let IP := GenLimit.PatientScope.prefixFinset I n
  let DP := GenLimit.PatientScope.prefixFinset D n
  let L := IP \ DP
  have hloser (z : {z // z ∈ L}) :
      z.1 ∈ I ∧ z.1 < n ∧ z.1 ∉ D := by
    have hz := z.2
    simp only [L, IP, DP, GenLimit.PatientScope.prefixFinset,
      Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hz
    exact ⟨hz.1.2, hz.1.1, fun hD => hz.2 ⟨hz.1.1, hD⟩⟩
  let charge : {z // z ∈ L} → Fin T ⊕ (Unit ⊕ {y // y ∈ DP}) := fun z =>
    if ht : inputTime input z.1 < T then
      Sum.inl ⟨inputTime input z.1, ht⟩
    else if hy : output (inputTime input z.1) < n then
      Sum.inr (Sum.inr ⟨output (inputTime input z.1), by
        have hz := hloser z
        have hop := output_at_loser_time family input T hstable hcore hIK hz.1 hz.2.2
          (Nat.le_of_not_gt ht)
        simp only [DP, GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
          Finset.mem_range]
        exact ⟨hy, hop.2, hIK hop.1⟩⟩)
    else Sum.inr (Sum.inl ())
  have hcharge : Function.Injective charge := by
    intro z w hzw
    have hz := hloser z
    have hw := hloser w
    dsimp only [charge] at hzw
    by_cases hzt : inputTime input z.1 < T
    · by_cases hwt : inputTime input w.1 < T
      · have ht : inputTime input z.1 = inputTime input w.1 := by
          rw [dif_pos hzt, dif_pos hwt] at hzw
          exact congrArg Fin.val (Sum.inl.inj hzw)
        apply Subtype.ext
        have hzr := loser_has_input family input T hstable hcore hIK hz.1 hz.2.2
        have hwr := loser_has_input family input T hstable hcore hIK hw.1 hw.2.2
        rw [← inputTime_spec input hzr, ← inputTime_spec input hwr, ht]
      · by_cases hwy : output (inputTime input w.1) < n <;> simp [hzt, hwt, hwy] at hzw
    · by_cases hwt : inputTime input w.1 < T
      · by_cases hzy : output (inputTime input z.1) < n <;> simp [hzt, hwt, hzy] at hzw
      · by_cases hzy : output (inputTime input z.1) < n
        · by_cases hwy : output (inputTime input w.1) < n
          · have hout : output (inputTime input z.1) = output (inputTime input w.1) := by
              have hzw' := hzw
              simp only [dif_neg hzt, dif_neg hwt, dif_pos hzy, dif_pos hwy,
                Sum.inr.injEq] at hzw'
              exact congrArg Subtype.val hzw'
            have hzle := Nat.le_of_not_gt hzt
            have hwle := Nat.le_of_not_gt hwt
            have htime : inputTime input z.1 = inputTime input w.1 := by
              rcases lt_trichotomy (inputTime input z.1) (inputTime input w.1) with hlt | heq | hgt
              · have hp := stable_output_properties family input (T := T)
                    (t := inputTime input w.1) hwle hstable hcore
                exact False.elim (hp.2.2.1 _ hlt hout)
              · exact heq
              · have hp := stable_output_properties family input (T := T)
                    (t := inputTime input z.1) hzle hstable hcore
                exact False.elim (hp.2.2.1 _ hgt hout.symm)
            apply Subtype.ext
            have hzr := loser_has_input family input T hstable hcore hIK hz.1 hz.2.2
            have hwr := loser_has_input family input T hstable hcore hIK hw.1 hw.2.2
            rw [← inputTime_spec input hzr, ← inputTime_spec input hwr, htime]
          · simp [charge, hzt, hwt, hzy, hwy] at hzw
        · by_cases hwy : output (inputTime input w.1) < n
          · simp [charge, hzt, hwt, hzy, hwy] at hzw
          · have hzle := Nat.le_of_not_gt hzt
            have hwle := Nat.le_of_not_gt hwt
            have htime : inputTime input z.1 = inputTime input w.1 := by
              rcases lt_trichotomy (inputTime input z.1) (inputTime input w.1) with hlt | heq | hgt
              · have hwno := loser_no_early_output family input hinj T hstable hcore hIK hw.1 hw.2.2
                have hp := stable_output_properties family input (T := T)
                    (t := inputTime input z.1) hzle hstable hcore
                have hwr := loser_has_input family input T hstable hcore hIK hw.1 hw.2.2
                have havail : w.1 ∉ GenLimit.Generic.sample input (inputTime input z.1 + 1) := by
                  intro hs
                  simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range] at hs
                  obtain ⟨r, hr, hre⟩ := hs
                  have hir := inputTime_spec input hwr
                  have : r = inputTime input w.1 := hinj (hre.trans hir.symm)
                  omega
                have hprev : ∀ s, s < inputTime input z.1 → output s ≠ w.1 :=
                  fun s hs => hwno s (lt_trans hs hlt)
                have hle := hp.2.2.2 w.1 hw.1 havail hprev
                change output (inputTime input z.1) ≤ w.1 at hle
                omega
              · exact heq
              · have hzno := loser_no_early_output family input hinj T hstable hcore hIK hz.1 hz.2.2
                have hp := stable_output_properties family input (T := T)
                    (t := inputTime input w.1) hwle hstable hcore
                have hzr := loser_has_input family input T hstable hcore hIK hz.1 hz.2.2
                have havail : z.1 ∉ GenLimit.Generic.sample input (inputTime input w.1 + 1) := by
                  intro hs
                  simp only [GenLimit.Generic.sample, Finset.mem_image, Finset.mem_range] at hs
                  obtain ⟨r, hr, hre⟩ := hs
                  have hir := inputTime_spec input hzr
                  have : r = inputTime input z.1 := hinj (hre.trans hir.symm)
                  omega
                have hprev : ∀ s, s < inputTime input w.1 → output s ≠ z.1 :=
                  fun s hs => hzno s (lt_trans hs hgt)
                have hle := hp.2.2.2 z.1 hz.1 havail hprev
                change output (inputTime input w.1) ≤ z.1 at hle
                omega
            apply Subtype.ext
            have hzr := loser_has_input family input T hstable hcore hIK hz.1 hz.2.2
            have hwr := loser_has_input family input T hstable hcore hIK hw.1 hw.2.2
            rw [← inputTime_spec input hzr, ← inputTime_spec input hwr, htime]
  have hcard := Fintype.card_le_of_injective charge hcharge
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit,
    Fintype.card_coe] at hcard
  have hpartition : IP.card = L.card + (IP ∩ DP).card := by
    exact (Finset.card_sdiff_add_card_inter IP DP).symm
  have hinter : (IP ∩ DP).card ≤ DP.card := Finset.card_le_card (Finset.inter_subset_right)
  change IP.card ≤ 2 * DP.card + T + 1
  omega

end Case017

namespace Case017

lemma prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨s, hsK, hscard⟩ := hK.exists_subset_card_eq b
  obtain ⟨N, hsN⟩ := s.exists_nat_subset_range
  refine ⟨N, ?_⟩
  intro n hn
  rw [← hscard]
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range]
  exact ⟨lt_of_lt_of_le (Finset.mem_range.mp (hsN hz)) hn, hsK hz⟩

lemma half_density_bound {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hinj : Function.Injective input) (T : ℕ)
    (hstable : ∀ u, T ≤ u →
      versionCore family (fun i : Fin (u+1) => input i) =
        Stage3Case017.informationCore family input)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {K : Set ℕ} (hIK : Stage3Case017.informationCore family input ⊆ K)
    (hK : K.Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (Stage3Case017.informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K) K := by
  let I := Stage3Case017.informationCore family input
  let D := GenLimit.GeneratorFirst input (trajectory (generator family) input) ∩ K
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount I n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let d : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hDsub : D ⊆ K := fun z hz => hz.2
  have ha0 : ∀ n, 0 ≤ a n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd0 : ∀ n, 0 ≤ d n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd1 : ∀ n, d n ≤ 1 := by
    intro n
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · have hd : GenLimit.PatientScope.prefixCount D n = 0 :=
        Nat.eq_zero_of_le_zero (hk ▸ prefixCount_mono hDsub n)
      simp [d, hk, hd]
    · apply (div_le_one (by positivity : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n)).2
      exact Nat.cast_le.mpr (prefixCount_mono hDsub n)
  have hcount := prefixCount_tendsto_atTop hK
  have hcast : Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hcount
  let e : ℕ → ℝ := fun n =>
    (((T + 1 : ℕ) : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)) / 2
  have he : Tendsto e atTop (𝓝 0) := by
    dsimp [e]
    convert (tendsto_const_nhds.div_atTop hcast).div_const 2 using 1 <;> norm_num
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) * liminf a atTop ≤ liminf d atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop (x := 1) hd1)
    (isBoundedUnder_of_eventually_ge (a := 0) (Eventually.of_forall hd0))).2
  intro c hc
  let q : ℝ := ((2 * c) + liminf a atTop) / 2
  have h2cq : 2 * c < q := by dsimp [q]; linarith
  have hq : q < liminf a atTop := by dsimp [q]; linarith
  have hmargin : 0 < q / 2 - c := by linarith
  have haevent : ∀ᶠ n in atTop, q < a n :=
    eventually_lt_of_lt_liminf hq
      (isBoundedUnder_of_eventually_ge (a := 0) (Eventually.of_forall ha0))
  have heevent : ∀ᶠ n in atTop, e n < q / 2 - c :=
    he.eventually_lt_const hmargin
  have hkpos : ∀ᶠ n in atTop, 0 < GenLimit.PatientScope.prefixCount K n :=
    (tendsto_atTop.1 hcount 1).mono fun n hn => Nat.zero_lt_of_lt hn
  filter_upwards [haevent, heevent, hkpos] with n han hen hkn
  have hprefix := half_prefix_bound family input hinj T hstable hcore hIK n
  have hprefixR :
      (GenLimit.PatientScope.prefixCount I n : ℝ) ≤
        2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + T + 1 := by
    exact_mod_cast hprefix
  have hratio : (1 / 2 : ℝ) * a n ≤ d n + e n := by
    dsimp [a, d, e]
    have hkR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hkn
    calc
      (1 / 2 : ℝ) *
          ((GenLimit.PatientScope.prefixCount I n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ)) =
          (GenLimit.PatientScope.prefixCount I n : ℝ) /
            (2 * GenLimit.PatientScope.prefixCount K n) := by ring
      _ ≤ (2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + T + 1) /
            (2 * GenLimit.PatientScope.prefixCount K n) := by
          exact div_le_div_of_nonneg_right hprefixR (by positivity)
      _ = (GenLimit.PatientScope.prefixCount D n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) +
          (((T + 1 : ℕ) : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ)) / 2 := by
          field_simp
          <;> norm_num [Nat.cast_add, Nat.cast_one]
          <;> ring
  linarith

end Case017

theorem stage3_result : Stage3Case017.MainClaim := by
  classical
  intro m hm family hfamily
  refine ⟨Case017.generator family, ?_⟩
  intro input hinj hpartial hcore
  obtain ⟨T, hstable⟩ := Case017.versionCore_eq_informationCore hm family input
  refine ⟨Case017.trajectory (Case017.generator family) input,
    Case017.follows_generator family input, ?_⟩
  intro j hj
  have hIK : Stage3Case017.informationCore family input ⊆ family j := by
    intro z hz
    exact hz j hj
  constructor
  · refine ⟨T, ?_⟩
    intro t ht
    have hp := Case017.stable_output_properties family input ht hstable hcore
    have hsamp : GenLimit.sample input (t + 1) =
        GenLimit.Generic.sample input (t + 1) := by
      ext z
      simp [GenLimit.sample, GenLimit.Generic.sample]
    exact ⟨hIK hp.1, hsamp ▸ hp.2.1, hp.2.2.1⟩
  · apply max_le
    · exact Case017.half_density_bound family input hinj T hstable hcore hIK (hfamily j)
    · have hGF := Case017.core_minus_range_subset_generatorFirst
          family input T hstable hcore
      apply Case017.relativeLowerDensity_mono
      · intro z hz
        exact ⟨hGF hz, hIK hz.1⟩
      · intro z hz
        exact hz.2
