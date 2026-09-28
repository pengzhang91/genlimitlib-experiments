import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity
import GenLimit.Paper39_DenseGeneration.Abstract.TargetMain

open Filter
open scoped Topology

namespace Case017Helpers

open Stage3Case017

noncomputable def currentCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) : Language :=
  {z | ∀ j, (∀ i : Fin (t + 1), input i ∈ family j) → z ∈ family j}

noncomputable def available {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (z : ℕ) : Prop :=
  (∀ j, (∀ i, input i ∈ family j) → z ∈ family j) ∧
    (∀ i, input i ≠ z) ∧ (∀ i, output i ≠ z)

theorem fresh_exists (t : ℕ) (input : Fin (t + 1) → ℕ)
    (output : Fin t → ℕ) :
    ∃ z, (∀ i, input i ≠ z) ∧ (∀ i, output i ≠ z) := by
  classical
  let used : Finset ℕ :=
    (Finset.univ.image input) ∪ (Finset.univ.image output)
  obtain ⟨z, -, hz⟩ := Set.infinite_univ.exists_notMem_finset used
  refine ⟨z, ?_, ?_⟩
  · intro i hi
    exact hz (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, hi⟩))
  · intro i hi
    exact hz (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, hi⟩))

noncomputable def onlineRule {m : ℕ} (family : Fin m → Language) : OnlineGenerator :=
  fun t input output => by
    classical
    exact if h : ∃ z, available family t input output z then Nat.find h
      else Nat.find (fresh_exists t input output)

noncomputable def history {m : ℕ} (family : Fin m → Language)
    (input : Stream) : (t : ℕ) → Fin t → ℕ
  | 0 => Fin.elim0
  | t + 1 =>
      Fin.snoc (history family input t)
        (onlineRule family t (fun i => input i) (history family input t))

noncomputable def trajectory {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Stream :=
  fun t => onlineRule family t (fun i => input i) (history family input t)

@[simp] theorem history_snoc {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    history family input (t + 1) =
      Fin.snoc (history family input t) (trajectory family input t) := rfl

@[simp] theorem history_castSucc {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t : ℕ} (i : Fin t) :
    history family input (t + 1) i.castSucc = history family input t i := by
  simp [history_snoc]

@[simp] theorem history_last {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    history family input (t + 1) (Fin.last t) = trajectory family input t := by
  simp [history_snoc]

@[simp] theorem history_eq_trajectory {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) (i : Fin t) :
    history family input t i = trajectory family input i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp
      · simpa using ih k

 theorem follows_trajectory {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Follows (onlineRule family) input (trajectory family input) := by
  intro t
  simp only [trajectory]
  congr 1
  funext i
  exact history_eq_trajectory family input t i

 theorem eventual_currentCore {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t → currentCore family input t = informationCore family input := by
  classical
  have hj : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      ((∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hcompat : GenLimit.Generic.StreamIn input (family j)
    · exact ⟨0, fun _ _ => ⟨fun _ => hcompat, fun _ i => hcompat ⟨i, rfl⟩⟩⟩
    · have hbad : ∃ q, input q ∉ family j := by
        by_contra h
        apply hcompat
        intro x hx
        obtain ⟨q, rfl⟩ := hx
        exact not_not.mp (not_exists.mp h q)
      obtain ⟨q, hq⟩ := hbad
      refine ⟨q, ?_⟩
      intro t hqt
      constructor
      · intro hpref
        exact False.elim (hq (hpref ⟨q, Nat.lt_succ_of_le hqt⟩))
      · intro h
        exact False.elim (hcompat h)
  choose bound hbound using hj
  let T := (Finset.univ : Finset (Fin m)).sup bound
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  simp only [currentCore, informationCore, Set.mem_setOf_eq]
  constructor
  · intro hz j hcompat
    exact hz j ((hbound j t (le_trans (Finset.le_sup (Finset.mem_univ j)) ht)).2 hcompat)
  · intro hz j hpref
    exact hz j ((hbound j t (le_trans (Finset.le_sup (Finset.mem_univ j)) ht)).1 hpref)

 theorem available_exists_of_stable {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {T t : ℕ} (hstable : ∀ s, T ≤ s →
      currentCore family input s = informationCore family input)
    (ht : T ≤ t) :
    ∃ z, available family t (fun i => input i) (history family input t) z := by
  classical
  let used : Finset ℕ :=
    (Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
      (Finset.univ.image (fun i : Fin t => history family input t i))
  obtain ⟨z, hzcore, hzused⟩ := hcore.exists_notMem_finset used
  refine ⟨z, ?_, ?_, ?_⟩
  · intro j hj
    have hzcur : z ∈ currentCore family input t := by
      rw [hstable t ht]
      exact hzcore
    exact hzcur j hj
  · intro i hi
    apply hzused
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  · intro i hi
    apply hzused
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

 theorem onlineRule_spec {m : ℕ} (family : Fin m → Language)
    {t : ℕ} {input : Fin (t + 1) → ℕ} {output : Fin t → ℕ}
    (h : ∃ z, available family t input output z) :
    available family t input output (onlineRule family t input output) := by
  classical
  simp only [onlineRule, dif_pos h]
  exact Nat.find_spec h


 theorem onlineRule_fresh {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    (∀ i, input i ≠ onlineRule family t input output) ∧
      (∀ i, output i ≠ onlineRule family t input output) := by
  classical
  by_cases h : ∃ z, available family t input output z
  · have hs := onlineRule_spec family h
    exact hs.2
  · simp only [onlineRule, dif_neg h]
    exact Nat.find_spec (fresh_exists t input output)

 theorem trajectory_fresh {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) :
    (∀ s, s ≤ t → input s ≠ trajectory family input t) ∧
      (∀ s, s < t → trajectory family input s ≠ trajectory family input t) := by
  have h := onlineRule_fresh family (fun i => input i) (history family input t)
  refine ⟨?_, ?_⟩
  · intro s hs
    exact h.1 ⟨s, Nat.lt_succ_of_le hs⟩
  · intro s hs
    simpa using h.2 ⟨s, hs⟩

 theorem trajectory_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Function.Injective (trajectory family input) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · exact (trajectory_fresh family input j).2 i hij' hij
  · exact (trajectory_fresh family input i).2 j hji' hij.symm

 theorem trajectory_range_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Set.range (trajectory family input) =
      GenLimit.GeneratorFirst input (trajectory family input) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl, (trajectory_fresh family input t).1⟩
  · rintro ⟨t, ht, -⟩
    exact ⟨t, ht⟩

 theorem trajectory_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {T t : ℕ} (hstable : ∀ s, T ≤ s →
      currentCore family input s = informationCore family input)
    (ht : T ≤ t) :
    available family t (fun i => input i) (history family input t)
      (trajectory family input t) := by
  exact onlineRule_spec family (available_exists_of_stable family input hcore hstable ht)

 theorem trajectory_novel {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {T t : ℕ} (hstable : ∀ s, T ≤ s →
      currentCore family input s = informationCore family input)
    (ht : T ≤ t) :
    trajectory family input t ∈ informationCore family input ∧
      (∀ s, s ≤ t → input s ≠ trajectory family input t) ∧
      (∀ s, s < t → trajectory family input s ≠ trajectory family input t) := by
  have h := trajectory_available family input hcore hstable ht
  refine ⟨?_, ?_, ?_⟩
  · have hcur : trajectory family input t ∈ currentCore family input t := h.1
    rwa [hstable t ht] at hcur
  · intro s hst
    exact h.2.1 ⟨s, Nat.lt_succ_of_le hst⟩
  · intro s hst
    have hh := h.2.2 ⟨s, hst⟩
    simpa using hh

end Case017Helpers

namespace Case017Helpers

open Stage3Case017

 theorem onlineRule_le_of_available {m : ℕ} (family : Fin m → Language)
    {t : ℕ} {input : Fin (t + 1) → ℕ} {output : Fin t → ℕ} {z : ℕ}
    (hz : available family t input output z) :
    onlineRule family t input output ≤ z := by
  classical
  have h : ∃ x, available family t input output x := ⟨z, hz⟩
  simp only [onlineRule, dif_pos h]
  exact Nat.find_min' h hz

 theorem trajectory_le_of_available {m : ℕ} (family : Fin m → Language)
    (input : Stream) {t z : ℕ}
    (hz : available family t (fun i => input i) (history family input t) z) :
    trajectory family input t ≤ z := by
  exact onlineRule_le_of_available family hz

 theorem core_covered_by_ranges {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ t, T ≤ t →
      currentCore family input t = informationCore family input) :
    informationCore family input ⊆
      Set.range input ∪ Set.range (trajectory family input) := by
  intro z hzcore
  by_contra hznot
  have hzinput : ∀ q, input q ≠ z := by
    intro q hq
    exact hznot (Set.mem_union_left _ ⟨q, hq⟩)
  have hzoutput : ∀ q, trajectory family input q ≠ z := by
    intro q hq
    exact hznot (Set.mem_union_right _ ⟨q, hq⟩)
  have havail : ∀ k, available family (T + k)
      (fun i => input i) (history family input (T + k)) z := by
    intro k
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have hzcur : z ∈ currentCore family input (T + k) := by
        rw [hstable (T + k) (Nat.le_add_right T k)]
        exact hzcore
      exact hzcur j hj
    · intro i
      exact hzinput i
    · intro i
      simpa using hzoutput i
  have hle : ∀ k, trajectory family input (T + k) ≤ z := by
    intro k
    exact trajectory_le_of_available family input (havail k)
  have hinj : Function.Injective (fun k => trajectory family input (T + k)) := by
    intro a b hab
    apply Nat.add_left_cancel
    exact trajectory_injective family input hab
  have hinfinite : (Set.range (fun k => trajectory family input (T + k))).Infinite :=
    Set.infinite_range_of_injective hinj
  have hfinite : (Set.range (fun k => trajectory family input (T + k))).Finite := by
    apply (Set.finite_Iic z).subset
    rintro x ⟨k, rfl⟩
    exact hle k
  exact hinfinite hfinite

 theorem core_covered_by_announcements {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ t, T ≤ t →
      currentCore family input t = informationCore family input) :
    informationCore family input ⊆
      GenLimit.AdversaryFirst input (trajectory family input) ∪
        GenLimit.GeneratorFirst input (trajectory family input) := by
  intro z hz
  rcases core_covered_by_ranges family input hcore hstable hz with hzI | hzO
  · exact GenLimit.range_subset_first_announcements input (trajectory family input) hzI
  · exact Set.mem_union_right _ ((trajectory_range_generatorFirst family input) ▸ hzO)

 theorem missing_core_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ t, T ≤ t →
      currentCore family input t = informationCore family input) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory family input) := by
  intro z hz
  rcases core_covered_by_ranges family input hcore hstable hz.1 with hzI | hzO
  · exact False.elim (hz.2 hzI)
  · rwa [← trajectory_range_generatorFirst family input]

end Case017Helpers

namespace Case017Helpers

open Stage3Case017

 theorem relativeLowerDensity_mono_left {A B K : Set ℕ}
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
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · simp [a, b, hk]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      exact (div_le_div_iff_of_pos_right hkpos).2 (by
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n)
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    exact div_nonneg (by positivity) (by positivity)
  have hb1 : ∀ n, b n ≤ 1 := by
    intro n
    by_cases hk : GenLimit.PatientScope.prefixCount K n = 0
    · simp [b, hk]
    · have hkpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      rw [div_le_one hkpos]
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
  change liminf a atTop ≤ liminf b atTop
  exact liminf_le_liminf (Filter.Eventually.of_forall hab)
    (Filter.isBoundedUnder_of ⟨0, ha0⟩)
    (isCoboundedUnder_ge_of_le atTop hb1)

noncomputable def firstInputTime (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : z ∈ Set.range input then Nat.find h else 0

 theorem firstInputTime_spec {input : Stream} {z : ℕ}
    (h : z ∈ Set.range input) : input (firstInputTime input z) = z := by
  classical
  simp only [firstInputTime, dif_pos h]
  exact Nat.find_spec h

 theorem firstInputTime_min {input : Stream} {z q : ℕ}
    (h : z ∈ Set.range input) (hq : input q = z) :
    firstInputTime input z ≤ q := by
  classical
  simp only [firstInputTime, dif_pos h]
  exact Nat.find_min' h hq

noncomputable def earlyAttacker {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ) : Finset ℕ := by
  classical
  exact (GenLimit.sample input (T + 1)).filter
    (fun z => z ∈ GenLimit.AdversaryFirst input (trajectory family input))

noncomputable def partner {m : ℕ} (family : Fin m → Language)
    (input : Stream) (z : ℕ) : ℕ :=
  trajectory family input (firstInputTime input z - 1)

 theorem ordinary_attacker_data {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ) {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker
      (informationCore family input)
      (GenLimit.AdversaryFirst input (trajectory family input))
      (∅ : Set ℕ) (earlyAttacker family input T)) :
    let q := firstInputTime input z
    T < q ∧ input q = z ∧
      (∀ s, s < q → input s ≠ z) ∧
      (∀ s, s < q → trajectory family input s ≠ z) ∧
      z ∈ informationCore family input := by
  classical
  have hzatt : z ∈ GenLimit.AdversaryFirst input (trajectory family input) := hz.1.1
  have hzcore : z ∈ informationCore family input := hz.1.2
  have hzrange : z ∈ Set.range input := by
    obtain ⟨q, hq, -⟩ := hzatt
    exact ⟨q, hq⟩
  have hspec := firstInputTime_spec (input := input) (z := z) hzrange
  have hinput : ∀ s, s < firstInputTime input z → input s ≠ z := by
    intro s hs hsz
    exact (Nat.not_lt_of_ge (firstInputTime_min hzrange hsz)) hs
  have houtput : ∀ s, s < firstInputTime input z →
      trajectory family input s ≠ z := by
    obtain ⟨q, hq, hno⟩ := hzatt
    intro s hs
    apply hno s
    exact lt_of_lt_of_le hs (firstInputTime_min hzrange hq)
  have hlate : T < firstInputTime input z := by
    by_contra hnot
    have hle : firstInputTime input z ≤ T := Nat.le_of_not_gt hnot
    have hsample : z ∈ GenLimit.sample input (T + 1) := by
      rw [GenLimit.mem_sample_iff]
      exact ⟨firstInputTime input z, Nat.lt_succ_of_le hle, hspec⟩
    have hearly : z ∈ earlyAttacker family input T := by
      simp [earlyAttacker, hsample, hzatt]
    exact hz.2 (Set.mem_union_left _ hearly)
  exact ⟨hlate, hspec, hinput, houtput, hzcore⟩

 theorem partner_properties {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ t, T ≤ t →
      currentCore family input t = informationCore family input)
    {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker
      (informationCore family input)
      (GenLimit.AdversaryFirst input (trajectory family input))
      (∅ : Set ℕ) (earlyAttacker family input T)) :
    partner family input z ∈
        GenLimit.GeneratorFirst input (trajectory family input) ∩
          informationCore family input ∧
      partner family input z < z := by
  classical
  let q := firstInputTime input z
  have hd := ordinary_attacker_data family input T hz
  have hTpred : T ≤ q - 1 := by omega
  have hzavail : available family (q - 1) (fun i => input i)
      (history family input (q - 1)) z := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      have hzcur : z ∈ currentCore family input (q - 1) := by
        rw [hstable (q - 1) hTpred]
        exact hd.2.2.2.2
      exact hzcur j hj
    · intro i
      exact hd.2.2.1 i (by omega)
    · intro i
      simpa using hd.2.2.2.1 i (by omega)
  have hle : partner family input z ≤ z := by
    exact trajectory_le_of_available family input hzavail
  have hne : partner family input z ≠ z := by
    exact hd.2.2.2.1 (q - 1) (by omega)
  refine ⟨⟨?_, ?_⟩, lt_of_le_of_ne hle hne⟩
  · rw [← trajectory_range_generatorFirst family input]
    exact ⟨q - 1, rfl⟩
  · exact (trajectory_novel family input hcore hstable hTpred).1

 theorem partner_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ) :
    Set.InjOn (partner family input)
      (GenLimit.PatientScope.ordinaryAttacker
        (informationCore family input)
        (GenLimit.AdversaryFirst input (trajectory family input))
        (∅ : Set ℕ) (earlyAttacker family input T)) := by
  intro x hx y hy hxy
  have htime : firstInputTime input x - 1 = firstInputTime input y - 1 := by
    apply trajectory_injective family input
    exact hxy
  have hxlate := (ordinary_attacker_data family input T hx).1
  have hylate := (ordinary_attacker_data family input T hy).1
  have hq : firstInputTime input x = firstInputTime input y := by omega
  calc
    x = input (firstInputTime input x) :=
      (ordinary_attacker_data family input T hx).2.1.symm
    _ = input (firstInputTime input y) := by rw [hq]
    _ = y := (ordinary_attacker_data family input T hy).2.1

end Case017Helpers

namespace Case017Helpers

open Stage3Case017

 theorem input_range_subset_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Set.range input ⊆ informationCore family input := by
  rintro z ⟨t, rfl⟩ j hj
  exact hj ⟨t, rfl⟩

 theorem attacker_subset_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    GenLimit.AdversaryFirst input (trajectory family input) ⊆
      informationCore family input := by
  rintro z ⟨t, htz, -⟩
  exact input_range_subset_core family input ⟨t, htz⟩

 theorem ordinary_target_to_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (T : ℕ) (j : Fin m) {z : ℕ}
    (hz : z ∈ GenLimit.PatientScope.ordinaryAttacker
      (family j) (GenLimit.AdversaryFirst input (trajectory family input))
      (∅ : Set ℕ) (earlyAttacker family input T)) :
    z ∈ GenLimit.PatientScope.ordinaryAttacker
      (informationCore family input)
      (GenLimit.AdversaryFirst input (trajectory family input))
      (∅ : Set ℕ) (earlyAttacker family input T) := by
  exact ⟨⟨hz.1.1, attacker_subset_core family input hz.1.1⟩, hz.2⟩

noncomputable def partialCertificate {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    (T : ℕ) (hstable : ∀ t, T ≤ t →
      currentCore family input t = informationCore family input)
    (j : Fin m) (hcompat : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.PartialEnumerationCertificate where
  target := family j
  enumerated := informationCore family input
  enumerated_subset_target := fun z hz => hz j hcompat
  attacker := GenLimit.AdversaryFirst input (trajectory family input)
  defender := GenLimit.GeneratorFirst input (trajectory family input)
  output := trajectory family input
  output_range := trajectory_range_generatorFirst family input
  output_injective := trajectory_injective family input
  validFrom := T
  eventual_target := fun t ht =>
    (trajectory_novel family input hcore hstable ht).1 j hcompat
  enumerated_covered := core_covered_by_announcements family input hcore hstable
  attacker_subset_target := by
    rintro z ⟨t, htz, -⟩
    exact hcompat ⟨t, htz⟩
  ownership_disjoint :=
    GenLimit.adversaryFirst_disjoint_generatorFirst input (trajectory family input)
  earlyAttacker := earlyAttacker family input T
  switchLoss := ∅
  switchLoss_subset := by simp
  partner := partner family input
  partner_mem := fun z hz => by
    have hp := partner_properties family input hcore hstable
      (ordinary_target_to_core family input T j hz)
    exact ⟨hp.1.1, hp.1.2 j hcompat⟩
  partner_lt := fun z hz => (partner_properties family input hcore hstable
    (ordinary_target_to_core family input T j hz)).2
  partner_injective := by
    intro x hx y hy hxy
    exact partner_injective family input T
      (ordinary_target_to_core family input T j hx)
      (ordinary_target_to_core family input T j hy) hxy
  switchBudget := fun _ => 0
  switch_prefix_le := by simp [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset]

 theorem half_core_density {m : ℕ}
    (family : Fin m → Language) (hinfinite : ∀ j, (family j).Infinite)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ t, T ≤ t →
      currentCore family input t = informationCore family input)
    (j : Fin m) (hcompat : GenLimit.Generic.StreamIn input (family j)) :
    (1 / 2 : ℝ) *
        GenLimit.PatientScope.relativeLowerDensity
          (informationCore family input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j)
        (family j) := by
  let P := partialCertificate family input hcore T hstable j hcompat
  have hlog : ∀ n, GenLimit.PatientScope.prefixCount P.switchLoss n ≤
      Nat.log2 (P.targetCount n) := by
    intro n
    change GenLimit.PatientScope.prefixCount (∅ : Set ℕ) n ≤ _
    simp [GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset]
  have h :=
    GenLimit.PatientScope.PartialEnumerationCertificate.theorem_3_17
      P (by change (family j).Infinite; exact hinfinite j) hlog
  simpa [P, partialCertificate,
    GenLimit.PatientScope.PartialEnumerationCertificate.lowerDensity] using h

 theorem missing_core_density {m : ℕ}
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {T : ℕ} (hstable : ∀ t, T ≤ t →
      currentCore family input t = informationCore family input)
    (j : Fin m) (hcompat : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input \ Set.range input) (family j) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input (trajectory family input) ∩ family j)
        (family j) := by
  apply relativeLowerDensity_mono_left
  · intro z hz
    exact ⟨missing_core_subset_generatorFirst family input hcore hstable hz,
      hz.1 j hcompat⟩
  · exact Set.inter_subset_right

end Case017Helpers
