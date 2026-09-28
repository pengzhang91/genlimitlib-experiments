import Stage3Model
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Set Filter
open scoped Topology

namespace Case017Proof

open Stage3Case017

noncomputable def eligible {m : ℕ} (family : Fin m → Language)
    {t : ℕ} (input : Fin (t + 1) → ℕ) (z : ℕ) : Prop :=
  ∀ j, (∀ i, input i ∈ family j) → z ∈ family j

noncomputable def available {m : ℕ} (family : Fin m → Language)
    (t : ℕ) (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) (z : ℕ) : Prop :=
  eligible family input z ∧ (∀ i, input i ≠ z) ∧ (∀ i, output i ≠ z)

noncomputable def greedy {m : ℕ} (family : Fin m → Language) : OnlineGenerator :=
  fun t input output => by
    classical
    exact if h : ∃ z, available family t input output z then Nat.find h else 0

noncomputable def trajectory (gen : OnlineGenerator) (input : Stream) : Stream :=
  fun t => Nat.strongRecOn t fun t rec =>
    gen t (fun i => input i) (fun i => rec i i.isLt)

lemma trajectory_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (trajectory gen input) := by
  intro t
  unfold trajectory
  rw [Nat.strongRecOn, WellFounded.fix_eq]
  congr 1

lemma compatible_eligible {m : ℕ} {family : Fin m → Language}
    {input : Stream} {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j))
    {t z} (hz : eligible family (fun i : Fin (t + 1) => input i) z) :
    z ∈ family j := by
  apply hz j
  intro i
  apply hj
  exact ⟨i, rfl⟩

lemma candidates_stabilize {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input : Stream) :
    ∃ T, ∀ t, T ≤ t → ∀ j,
      (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
  classical
  have bad_has_time : ∀ j : Fin m,
      ¬ GenLimit.Generic.StreamIn input (family j) →
        ∃ s, input s ∉ family j := by
    intro j hj
    obtain ⟨z, ⟨s, rfl⟩, hz⟩ := Set.not_subset.mp hj
    exact ⟨s, hz⟩
  let badTime : Fin m → ℕ := fun j =>
    if h : ¬ GenLimit.Generic.StreamIn input (family j) then
      Classical.choose (bad_has_time j h)
    else 0
  let T := (Finset.univ.image badTime).max' (Finset.univ_nonempty.image _)
  refine ⟨T, ?_⟩
  intro t ht j
  constructor
  · intro hp
    by_contra hbad
    have houtside : input (badTime j) ∉ family j := by
      simpa [badTime, hbad] using (Classical.choose_spec (bad_has_time j hbad))
    have htime : badTime j ≤ T :=
      Finset.le_max' (Finset.univ.image badTime) (badTime j) (by simp)
    have hlt : badTime j < t + 1 := Nat.lt_succ_iff.mpr (htime.trans ht)
    exact houtside (hp ⟨badTime j, hlt⟩)
  · intro hstream i
    apply hstream
    exact ⟨i, rfl⟩

lemma available_exists_eventually {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input output : Stream)
    (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      ∃ z, available family t (fun i => input i) (fun i => output i) z := by
  classical
  obtain ⟨T, hT⟩ := candidates_stabilize family input
  refine ⟨T, fun t ht => ?_⟩
  let F : Finset ℕ :=
    (Finset.univ.image (fun i : Fin (t + 1) => input i)) ∪
      (Finset.univ.image (fun i : Fin t => output i))
  obtain ⟨z, hzcore, hzF⟩ := hcore.exists_not_mem_finset F
  refine ⟨z, ?_, ?_, ?_⟩
  · intro j hj
    exact hzcore j ((hT t ht j).mp hj)
  · intro i hiz
    apply hzF
    simp only [F, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl ⟨i, hiz⟩
  · intro i hiz
    apply hzF
    simp only [F, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨i, hiz⟩

lemma greedy_spec {m : ℕ} (family : Fin m → Language) {t}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ)
    (h : ∃ z, available family t input output z) :
    available family t input output (greedy family t input output) := by
  classical
  simp only [greedy, dif_pos h]
  exact Nat.find_spec h

lemma greedy_min {m : ℕ} (family : Fin m → Language) {t}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ)
    (h : ∃ z, available family t input output z) {z}
    (hz : available family t input output z) :
    greedy family t input output ≤ z := by
  classical
  simp only [greedy, dif_pos h]
  exact Nat.find_min' h hz



lemma eventual_output_available {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    let output := trajectory (greedy family) input
    ∃ T, ∀ t, T ≤ t →
      available family t (fun i => input i) (fun i => output i) (output t) := by
  let output := trajectory (greedy family) input
  obtain ⟨T, hT⟩ := available_exists_eventually family input output hcore
  refine ⟨T, fun t ht => ?_⟩
  rw [trajectory_follows (greedy family) input t]
  exact greedy_spec family _ _ (hT t ht)

lemma trajectory_novel {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (trajectory (greedy family) input) (family j) := by
  obtain ⟨T, hT⟩ := eventual_output_available family input hcore
  refine ⟨T, fun t ht => ?_⟩
  have hs := hT t ht
  refine ⟨compatible_eligible hj hs.1, ?_, ?_⟩
  · intro hmem
    simp only [GenLimit.sample, Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨s, hst, hsout⟩ := hmem
    exact hs.2.1 ⟨s, hst⟩ hsout
  · intro s hst heq
    exact hs.2.2 ⟨s, hst⟩ heq

lemma eventual_output_core {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    let output := trajectory (greedy family) input
    ∃ T, ∀ t, T ≤ t → output t ∈ informationCore family input := by
  obtain ⟨Ts, hstab⟩ := candidates_stabilize family input
  obtain ⟨Ta, havail⟩ := eventual_output_available family input hcore
  refine ⟨max Ts Ta, fun t ht j hj => ?_⟩
  have hs := havail t (le_trans (le_max_right _ _) ht)
  exact hs.1 j ((hstab t (le_trans (le_max_left _ _) ht) j).mpr hj)


lemma unpresented_core_subset_generatorFirst {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (trajectory (greedy family) input) := by
  classical
  let output := trajectory (greedy family) input
  obtain ⟨Ts, hstab⟩ := candidates_stabilize family input
  obtain ⟨Ta, havail⟩ := available_exists_eventually family input output hcore
  let T := max Ts Ta
  intro z hz
  have hinput : ∀ s, input s ≠ z := by
    intro s heq
    exact hz.2 ⟨s, heq⟩
  by_contra hnotGF
  have houtput : ∀ s, output s ≠ z := by
    intro s heq
    apply hnotGF
    exact ⟨s, heq, fun r _ => hinput r⟩
  have hzavail : ∀ t, T ≤ t →
      available family t (fun i => input i) (fun i => output i) z := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      exact hz.1 j ((hstab t (le_trans (le_max_left _ _) ht) j).mp hj)
    · intro i
      exact hinput i
    · intro i
      exact houtput i
  have hout_le : ∀ n, output (T + n) ≤ z := by
    intro n
    have ht : T ≤ T + n := Nat.le_add_right T n
    dsimp only [output]
    rw [trajectory_follows (greedy family) input (T + n)]
    exact greedy_min family _ _ (havail (T + n) (le_trans (le_max_right _ _) ht))
      (hzavail (T + n) ht)
  have hout_ne_of_lt : ∀ {a b}, a < b → output (T + a) ≠ output (T + b) := by
    intro a b hlt heq
    have hbT : T ≤ T + b := Nat.le_add_right T b
    have hs := (greedy_spec family
      (fun i : Fin (T + b + 1) => input i)
      (fun i : Fin (T + b) => output i)
      (havail (T + b) (le_trans (le_max_right _ _) hbT))).2.2
    apply hs ⟨T + a, Nat.add_lt_add_left hlt T⟩
    calc
      output (T + a) = output (T + b) := heq
      _ = greedy family (T + b) (fun i => input i) (fun i => output i) :=
        trajectory_follows (greedy family) input (T + b)
  have hout_inj : Function.Injective (fun n => output (T + n)) := by
    intro a b heq
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hout_ne_of_lt hlt heq
    · exact hout_ne_of_lt hgt heq.symm
  have hinfinite : (Set.range (fun n => output (T + n))).Infinite :=
    Set.infinite_range_of_injective hout_inj
  have hsubset : Set.range (fun n => output (T + n)) ⊆ Set.Iic z := by
    rintro x ⟨n, rfl⟩
    exact hout_le n
  exact (Set.finite_Iic z).not_infinite (hinfinite.mono hsubset)


noncomputable def firstInput (input : Stream) (z : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, input t = z then Nat.find h else 0

lemma firstInput_spec {input : Stream} {z : ℕ} (hz : z ∈ Set.range input) :
    input (firstInput input z) = z := by
  classical
  simp only [Set.mem_range] at hz
  unfold firstInput
  rw [dif_pos hz]
  exact Nat.find_spec hz

lemma firstInput_injective (input : Stream) (hinj : Function.Injective input) :
    Set.InjOn (firstInput input) (Set.range input) := by
  intro x hx y hy heq
  calc
    x = input (firstInput input x) := (firstInput_spec hx).symm
    _ = input (firstInput input y) := congrArg input heq
    _ = y := firstInput_spec hy

lemma firstInput_le {input : Stream} {z q : ℕ} (hz : z ∈ Set.range input)
    (hq : input q = z) : firstInput input z ≤ q := by
  classical
  simp only [Set.mem_range] at hz
  unfold firstInput
  rw [dif_pos hz]
  exact Nat.find_min' hz hq

lemma prefix_race_bound {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite) :
    let output := trajectory (greedy family) input
    ∃ C, ∀ n,
      GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output) n + C := by
  classical
  let output := trajectory (greedy family) input
  obtain ⟨Ts, hstab⟩ := candidates_stabilize family input
  obtain ⟨Ta, havail⟩ := available_exists_eventually family input output hcore
  let T := max Ts Ta
  refine ⟨T + 1, fun n => ?_⟩
  let Cn := GenLimit.PatientScope.prefixFinset (informationCore family input) n
  let Dn := GenLimit.PatientScope.prefixFinset (GenLimit.GeneratorFirst input output) n
  let An := Cn \ Dn
  let early := An.filter (fun z => firstInput input z < T)
  let bad := An.filter (fun z => T ≤ firstInput input z ∧ n ≤ output (firstInput input z))
  let good := An.filter (fun z => T ≤ firstInput input z ∧ output (firstInput input z) < n)
  have hA_range : ∀ z ∈ An, z ∈ Set.range input := by
    intro z hz
    have hzC : z ∈ informationCore family input := by
      have hp : z < n ∧ z ∈ informationCore family input := by
        simpa [Cn, GenLimit.PatientScope.prefixFinset] using (Finset.mem_sdiff.mp hz).1
      exact hp.2
    have hznotD := (Finset.mem_sdiff.mp hz).2
    have hznotGF : z ∉ GenLimit.GeneratorFirst input output := by
      intro hGF
      apply hznotD
      have hzlt : z < n := by
        have hp : z < n ∧ z ∈ informationCore family input := by
          simpa [Cn, GenLimit.PatientScope.prefixFinset] using (Finset.mem_sdiff.mp hz).1
        exact hp.1
      simp [Dn, GenLimit.PatientScope.prefixFinset, hzlt, hGF]
    by_contra hzrange
    have hsub := unpresented_core_subset_generatorFirst family input hcore
    exact hznotGF (hsub ⟨hzC, hzrange⟩)
  have hA_cover : An ⊆ early ∪ bad ∪ good := by
    intro z hz
    by_cases hearly : firstInput input z < T
    · simp [early, hz, hearly]
    · have hlate : T ≤ firstInput input z := Nat.le_of_not_gt hearly
      by_cases hbad : n ≤ output (firstInput input z)
      · simp [bad, hz, hlate, hbad]
      · have hgood : output (firstInput input z) < n := Nat.lt_of_not_ge hbad
        simp [good, hz, hlate, hgood]
  have hearly_card : early.card ≤ T := by
    simpa using (Finset.card_le_card_of_injOn (s := early) (t := Finset.range T)
      (firstInput input) (by
        intro z hz
        have hz' : z ∈ An ∧ firstInput input z < T := by simpa [early] using hz
        simpa using hz'.2) (by
        apply (firstInput_injective input hinj).mono
        intro z hz
        have hz' : z ∈ An ∧ firstInput input z < T := by simpa [early] using hz
        exact hA_range z hz'.1))
  have hlate_available : ∀ z ∈ An, T ≤ firstInput input z →
      available family (firstInput input z)
        (fun i => input i) (fun i => output i) (output (firstInput input z)) := by
    intro z hz hlate
    dsimp only [output]
    rw [trajectory_follows (greedy family) input (firstInput input z)]
    exact greedy_spec family _ _
      (havail (firstInput input z) (le_trans (le_max_right _ _) hlate))
  have hgood_card : good.card ≤ Dn.card := by
    apply Finset.card_le_card_of_injOn (fun z => output (firstInput input z))
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      have hs := hlate_available z hz'.1 hz'.2.1
      have hGF : output (firstInput input z) ∈ GenLimit.GeneratorFirst input output := by
        refine ⟨firstInput input z, rfl, ?_⟩
        intro r hr
        exact hs.2.1 ⟨r, Nat.lt_succ_iff.mpr hr⟩
      simp [Dn, GenLimit.PatientScope.prefixFinset, hz'.2.2, hGF]
    · intro x hx y hy heq
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have htx := hx'.2.1
      have hty := hy'.2.1
      have htimes : firstInput input x = firstInput input y := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hs := (hlate_available y hy'.1 hty).2.2
          exact hs ⟨firstInput input x, hlt⟩ heq
        · have hs := (hlate_available x hx'.1 htx).2.2
          exact hs ⟨firstInput input y, hgt⟩ heq.symm
      exact (firstInput_injective input hinj)
        (hA_range x hx'.1) (hA_range y hy'.1) htimes
  have hbad_not_lt : ∀ {x y}, x ∈ bad → y ∈ bad →
      ¬ firstInput input x < firstInput input y := by
    intro x y hx hy hlt
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hyPair : y < n ∧ y ∈ informationCore family input := by
      simpa [Cn, GenLimit.PatientScope.prefixFinset] using (Finset.mem_sdiff.mp hy'.1).1
    have hyC := hyPair.2
    have hylt := hyPair.1
    have hy_notGF : y ∉ GenLimit.GeneratorFirst input output := by
      intro hGF
      exact (Finset.mem_sdiff.mp hy'.1).2 (by
        simp [Dn, GenLimit.PatientScope.prefixFinset, hylt, hGF])
    have hy_not_output_before : ∀ r, r < firstInput input y → output r ≠ y := by
      intro r hr heq
      apply hy_notGF
      refine ⟨r, heq, ?_⟩
      intro q hq hin
      have hfirst_le : firstInput input y ≤ q := firstInput_le (hA_range y hy'.1) hin
      omega
    have hy_available_at_x : available family (firstInput input x)
        (fun i => input i) (fun i => output i) y := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        exact hyC j ((hstab _ (le_trans (le_max_left _ _) hx'.2.1) j).mp hj)
      · intro i heq
        have hfirst_le : firstInput input y ≤ i := firstInput_le (hA_range y hy'.1) heq
        omega
      · intro i
        exact hy_not_output_before i (lt_trans i.isLt hlt)
    have hout_le_y : output (firstInput input x) ≤ y := by
      dsimp only [output]
      rw [trajectory_follows (greedy family) input (firstInput input x)]
      exact greedy_min family _ _
        (havail _ (le_trans (le_max_right _ _) hx'.2.1)) hy_available_at_x
    omega
  have hbad_card : bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have htime_eq : firstInput input x = firstInput input y := by
      apply Nat.le_antisymm
      · exact Nat.le_of_not_gt (hbad_not_lt hy hx)
      · exact Nat.le_of_not_gt (hbad_not_lt hx hy)
    exact (firstInput_injective input hinj)
      (hA_range x (Finset.mem_filter.mp hx).1)
      (hA_range y (Finset.mem_filter.mp hy).1) htime_eq
  have hA_card : An.card ≤ T + 1 + Dn.card := by
    calc
      An.card ≤ (early ∪ bad ∪ good).card := Finset.card_le_card hA_cover
      _ ≤ (early ∪ bad).card + good.card := Finset.card_union_le _ _
      _ ≤ (early.card + bad.card) + good.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (T + 1) + Dn.card := by omega
  have hinter_card : (Cn ∩ Dn).card ≤ Dn.card := Finset.card_le_card (Finset.inter_subset_right)
  unfold GenLimit.PatientScope.prefixCount
  change Cn.card ≤ 2 * Dn.card + (T + 1)
  have hsplit := Finset.card_sdiff_add_card_inter Cn Dn
  have hEq : An.card + (Cn ∩ Dn).card = Cn.card := by
    simpa [An, Finset.inter_comm] using hsplit
  omega


lemma generatorFirst_target_prefix_bound {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input : Stream)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    let output := trajectory (greedy family) input
    ∃ C, ∀ n,
      GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n ≤
        GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ family j) n + C := by
  classical
  let output := trajectory (greedy family) input
  obtain ⟨T, hT⟩ := eventual_output_core family input hcore
  refine ⟨T, fun n => ?_⟩
  let P := GenLimit.PatientScope.prefixFinset (GenLimit.GeneratorFirst input output) n
  let Q := GenLimit.PatientScope.prefixFinset
    (GenLimit.GeneratorFirst input output ∩ family j) n
  let E := Finset.image output (Finset.range T)
  have hsub : P ⊆ Q ∪ E := by
    intro z hz
    have hzP : z < n ∧ z ∈ GenLimit.GeneratorFirst input output := by
      simpa [P, GenLimit.PatientScope.prefixFinset] using hz
    by_cases hzK : z ∈ family j
    · have hzQ : z ∈ Q := by
        simp [Q, GenLimit.PatientScope.prefixFinset, hzP.1, hzP.2, hzK]
      exact Finset.mem_union_left E hzQ
    · obtain ⟨t, htout, -⟩ := hzP.2
      have ht : t < T := by
        by_contra hnot
        have houtcore := hT t (Nat.le_of_not_gt hnot)
        apply hzK
        rw [← htout]
        exact houtcore j hj
      have hzE : z ∈ E := by
        exact Finset.mem_image.mpr ⟨t, by simp [ht], htout⟩
      exact Finset.mem_union_right Q hzE
  unfold GenLimit.PatientScope.prefixCount
  change P.card ≤ Q.card + T
  calc
    P.card ≤ (Q ∪ E).card := Finset.card_le_card hsub
    _ ≤ Q.card + E.card := Finset.card_union_le _ _
    _ ≤ Q.card + T := Nat.add_le_add_left (Finset.card_image_le.trans_eq (Finset.card_range T)) _

lemma prefix_race_target_bound {m : ℕ} [Nonempty (Fin m)]
    (family : Fin m → Language) (input : Stream) (hinj : Function.Injective input)
    (hcore : (informationCore family input).Infinite)
    {j : Fin m} (hj : GenLimit.Generic.StreamIn input (family j)) :
    let output := trajectory (greedy family) input
    ∃ C, ∀ n,
      GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input output ∩ family j) n + C := by
  let output := trajectory (greedy family) input
  obtain ⟨C₁, h₁⟩ := prefix_race_bound family input hinj hcore
  obtain ⟨C₂, h₂⟩ := generatorFirst_target_prefix_bound family input hcore hj
  refine ⟨C₁ + 2 * C₂, fun n => ?_⟩
  have ha := h₁ n
  have hb := h₂ n
  omega

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma relativeLowerDensity_mono {A B K : Set ℕ}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  unfold GenLimit.PatientScope.relativeLowerDensity
  apply liminf_le_liminf
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_mono hAB n
    · positivity
  · change ∃ a : ℝ, ∀ᶠ n : ℕ in atTop, a ≤
        (GenLimit.PatientScope.prefixCount A n : ℝ) /
          (GenLimit.PatientScope.prefixCount K n : ℝ)
    refine ⟨0, Filter.Eventually.of_forall (fun n => ?_)⟩
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply Filter.isCoboundedUnder_ge_of_le (x := (1 : ℝ)) atTop
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · apply (div_le_one (show (0 : ℝ) < (GenLimit.PatientScope.prefixCount K n : ℝ) by
        exact_mod_cast Nat.pos_of_ne_zero hzero)).2
      exact_mod_cast prefixCount_mono hBK n


lemma prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (GenLimit.PatientScope.prefixCount K) atTop atTop := by
  rw [tendsto_atTop]
  intro N
  obtain ⟨F, hFK, hcard⟩ := hK.exists_subset_card_eq N
  by_cases hF : F.Nonempty
  · filter_upwards [eventually_ge_atTop (F.max' hF + 1)] with n hn
    have hsub : F ⊆ GenLimit.PatientScope.prefixFinset K n := by
      intro z hz
      have hzle : z ≤ F.max' hF := Finset.le_max' F z hz
      simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
        Finset.mem_range]
      exact ⟨lt_of_le_of_lt hzle (Nat.lt_succ_self _ |>.trans_le hn), hFK hz⟩
    simpa [GenLimit.PatientScope.prefixCount, hcard] using Finset.card_le_card hsub
  · have hN : N = 0 := by
      rw [← hcard]
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hF)
    simp [hN]


lemma relativeLowerDensity_half_of_prefix_bound {A D K : Set ℕ}
    (hAK : A ⊆ K) (hDK : D ⊆ K) (hK : K.Infinite)
    (C : ℕ) (hcount : ∀ n,
      GenLimit.PatientScope.prefixCount A n ≤
        2 * GenLimit.PatientScope.prefixCount D n + C) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity D K := by
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let d : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount D n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    ((C : ℝ) / 2) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hKnat := prefixCount_tendsto_atTop hK
  have hKreal : Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKnat
  have he : Tendsto e atTop (𝓝 0) := by
    exact hKreal.const_div_atTop ((C : ℝ) / 2)
  have ha0 : ∀ᶠ n in atTop, 0 ≤ a n :=
    Filter.Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd0 : ∀ᶠ n in atTop, 0 ≤ d n :=
    Filter.Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have ha1 : ∀ n, a n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [a, hzero]
    · apply (div_le_one (show (0 : ℝ) < (GenLimit.PatientScope.prefixCount K n : ℝ) by
        exact_mod_cast Nat.pos_of_ne_zero hzero)).2
      exact_mod_cast prefixCount_mono hAK n
  have hd1 : ∀ n, d n ≤ 1 := by
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [d, hzero]
    · apply (div_le_one (show (0 : ℝ) < (GenLimit.PatientScope.prefixCount K n : ℝ) by
        exact_mod_cast Nat.pos_of_ne_zero hzero)).2
      exact_mod_cast prefixCount_mono hDK n
  have ha_bdd_ge : IsBoundedUnder (· ≥ ·) atTop a :=
    isBoundedUnder_of_eventually_ge ha0
  have ha_bdd_le : IsBoundedUnder (· ≤ ·) atTop a :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall ha1)
  have hd_bdd_ge : IsBoundedUnder (· ≥ ·) atTop d :=
    isBoundedUnder_of_eventually_ge hd0
  have hd_bdd_le : IsBoundedUnder (· ≤ ·) atTop d :=
    isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall hd1)
  have hpoint : ∀ᶠ n in atTop, (1 / 2 : ℝ) * a n ≤ e n + d n := by
    apply Filter.Eventually.of_forall
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [a, d, e, hzero]
    · have hpos : (0 : ℝ) < (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      apply (div_le_div_iff_of_pos_right hpos).mp
      have hc : (GenLimit.PatientScope.prefixCount A n : ℝ) ≤
          2 * (GenLimit.PatientScope.prefixCount D n : ℝ) + C := by
        exact_mod_cast hcount n
      dsimp [a, d, e]
      field_simp
      linarith
  have hhalf_liminf :
      (1 / 2 : ℝ) * liminf a atTop ≤
        liminf (fun n => (1 / 2 : ℝ) * a n) atTop := by
    have hconst0 : ∀ᶠ _ : ℕ in atTop, (0 : ℝ) ≤ 1 / 2 :=
      Filter.Eventually.of_forall fun _ => by norm_num
    have hconst_bdd : IsBoundedUnder (· ≤ ·) atTop (fun _ : ℕ => (1 / 2 : ℝ)) :=
      isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun _ => le_rfl)
    simpa using (le_liminf_mul hconst0 hconst_bdd ha0 ha_bdd_le.isCoboundedUnder_ge)
  have hprod_bdd_ge : IsBoundedUnder (· ≥ ·) atTop
      (fun n => (1 / 2 : ℝ) * a n) := by
    apply isBoundedUnder_of_eventually_ge
    filter_upwards [ha0] with n hn
    positivity
  have hsum_cobdd_ge : IsCoboundedUnder (· ≥ ·) atTop (e + d) :=
    (isBoundedUnder_le_add he.isBoundedUnder_le hd_bdd_le).isCoboundedUnder_ge
  have hpoint_liminf : liminf (fun n => (1 / 2 : ℝ) * a n) atTop ≤
      liminf (e + d) atTop := by
    exact liminf_le_liminf hpoint hprod_bdd_ge hsum_cobdd_ge
  have hsum_liminf : liminf (e + d) atTop ≤ liminf d atTop := by
    calc
      liminf (e + d) atTop ≤ limsup e atTop + liminf d atTop :=
        liminf_add_le he.isBoundedUnder_ge he.isBoundedUnder_le
          hd_bdd_ge hd_bdd_le.isCoboundedUnder_ge
      _ = liminf d atTop := by rw [he.limsup_eq]; simp
  unfold GenLimit.PatientScope.relativeLowerDensity
  change (1 / 2 : ℝ) * liminf a atTop ≤ liminf d atTop
  exact hhalf_liminf.trans (hpoint_liminf.trans hsum_liminf)

lemma relativeLowerDensity_inter_of_subset {A K : Set ℕ} (hAK : A ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K =
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  congr 1
  exact (inter_eq_left.mpr hAK).symm

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  refine ⟨Case017Proof.greedy family, ?_⟩
  intro input hinj _ hcore
  let output := Case017Proof.trajectory (Case017Proof.greedy family) input
  refine ⟨output, Case017Proof.trajectory_follows _ _, ?_⟩
  intro j hj
  refine ⟨Case017Proof.trajectory_novel family input hcore hj, ?_⟩
  apply max_le
  · obtain ⟨C, hcount⟩ :=
      Case017Proof.prefix_race_target_bound family input hinj hcore hj
    apply Case017Proof.relativeLowerDensity_half_of_prefix_bound
      (K := family j) (C := C)
    · intro z hz
      exact hz j hj
    · exact Set.inter_subset_right
    · exact hinfinite j
    · exact hcount
  · apply Case017Proof.relativeLowerDensity_mono
    · intro z hz
      exact ⟨Case017Proof.unpresented_core_subset_generatorFirst family input hcore hz,
        hz.1 j hj⟩
    · exact Set.inter_subset_right
