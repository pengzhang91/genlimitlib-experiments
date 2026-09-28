import Stage3Model
import GenLimit.Paper39_DenseGeneration.Abstract.Announcements
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity
import GenLimit.Paper39_DenseGeneration.Abstract.PartialDensity

open Filter
open scoped Topology

namespace Stage3Case017Proof

open Stage3Case017

def PrefixIn {m t : ℕ} (family : Fin m → Language)
    (xs : Fin t → ℕ) (j : Fin m) : Prop :=
  ∀ i, xs i ∈ family j

def ActiveCore {m t : ℕ} (family : Fin m → Language)
    (xs : Fin t → ℕ) : Language :=
  {z | ∀ j, PrefixIn family xs j → z ∈ family j}

def Available {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  z ∈ ActiveCore family xs ∧
    (∀ i, xs i ≠ z) ∧
    (∀ i, ys i ≠ z)

noncomputable def onlineGenerator {m : ℕ}
    (family : Fin m → Language) : OnlineGenerator := by
  intro t xs ys
  classical
  exact if h : ∃ z, Available family xs ys z then Nat.find h else 0

theorem onlineGenerator_spec {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, Available family xs ys z) :
    Available family xs ys (onlineGenerator family t xs ys) := by
  classical
  simp only [onlineGenerator, dif_pos h]
  exact Nat.find_spec h

theorem onlineGenerator_minimal {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) {z : ℕ}
    (hz : Available family xs ys z) :
    onlineGenerator family t xs ys ≤ z := by
  classical
  have h : ∃ w, Available family xs ys w := ⟨z, hz⟩
  simp only [onlineGenerator, dif_pos h]
  exact Nat.find_min' h hz

theorem eventually_activeCore_eq {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∃ T, ∀ t, T ≤ t →
      ActiveCore family (fun i : Fin (t + 1) => input i) =
        informationCore family input := by
  classical
  have hindex : ∀ j : Fin m, ∃ T, ∀ t, T ≤ t →
      (PrefixIn family (fun i : Fin (t + 1) => input i) j ↔
        GenLimit.Generic.StreamIn input (family j)) := by
    intro j
    by_cases hj : GenLimit.Generic.StreamIn input (family j)
    · refine ⟨0, ?_⟩
      intro t ht
      constructor
      · intro hprefix
        exact hj
      · intro hstream i
        exact hstream ⟨i, rfl⟩
    · have hex : ∃ s, input s ∉ family j := by
        simpa [GenLimit.Generic.StreamIn, Set.range_subset_iff] using hj
      obtain ⟨s, hs⟩ := hex
      refine ⟨s, ?_⟩
      intro t ht
      constructor
      · intro hprefix
        exfalso
        exact hs (hprefix ⟨s, by omega⟩)
      · intro hstream
        exact False.elim (hj hstream)
  choose cutoff hcutoff using hindex
  let T := Finset.univ.sup cutoff
  refine ⟨T, ?_⟩
  intro t ht
  ext z
  constructor
  · intro hz j hj
    exact hz j ((hcutoff j t
      (le_trans (Finset.le_sup (s := Finset.univ) (f := cutoff)
        (Finset.mem_univ j)) ht)).2 hj)
  · intro hz j hj
    exact hz j ((hcutoff j t
      (le_trans (Finset.le_sup (s := Finset.univ) (f := cutoff)
        (Finset.mem_univ j)) ht)).1 hj)

theorem eventual_available {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollow : Follows (onlineGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      Available family (fun i : Fin (t + 1) => input i)
        (fun i : Fin t => output i) (output t) := by
  obtain ⟨T, hT⟩ := eventually_activeCore_eq family input
  refine ⟨T, ?_⟩
  intro t ht
  have hactive : ActiveCore family (fun i : Fin (t + 1) => input i) =
      informationCore family input := hT t ht
  classical
  let forbidden : Finset ℕ :=
    Finset.univ.image (fun i : Fin (t + 1) => input i) ∪
      Finset.univ.image (fun i : Fin t => output i)
  obtain ⟨z, hzcore, hzforbidden⟩ := hcore.exists_notMem_finset forbidden
  have hzavail : Available family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i) z := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [hactive] using hzcore
    · intro i hi
      apply hzforbidden
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    · intro i hi
      apply hzforbidden
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  rw [hfollow t]
  exact onlineGenerator_spec family _ _ ⟨z, hzavail⟩

theorem eventual_activeCore {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hfollow : Follows (onlineGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    ∃ T, ∀ t, T ≤ t →
      output t ∈ informationCore family input ∧
      (∀ s, s ≤ t → input s ≠ output t) ∧
      (∀ s, s < t → output s ≠ output t) := by
  obtain ⟨T, hT⟩ := eventual_available family input output hfollow hcore
  obtain ⟨Tc, hTc⟩ := eventually_activeCore_eq family input
  refine ⟨max T Tc, ?_⟩
  intro t ht
  have havail := hT t (le_trans (Nat.le_max_left _ _) ht)
  have hactive := hTc t (le_trans (Nat.le_max_right _ _) ht)
  refine ⟨?_, ?_, ?_⟩
  · simpa [Available, hactive] using havail.1
  · intro s hs hEq
    exact havail.2.1 ⟨s, by omega⟩ hEq
  · intro s hs hEq
    exact havail.2.2 ⟨s, hs⟩ hEq

theorem core_diff_range_subset_generatorFirst {m : ℕ}
    (family : Fin m → Language) (input output : Stream)
    (hinj : Function.Injective input)
    (hfollow : Follows (onlineGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input output := by
  classical
  obtain ⟨T, hT⟩ := eventual_available family input output hfollow hcore
  obtain ⟨Tc, hTc⟩ := eventually_activeCore_eq family input
  let S := max T Tc
  intro z hz
  have hzcore : z ∈ informationCore family input := hz.1
  have hzinput : z ∉ Set.range input := hz.2
  by_contra hzfirst
  have hzoutput : z ∉ Set.range output := by
    intro hzrange
    obtain ⟨t, ht⟩ := hzrange
    apply hzfirst
    refine ⟨t, ht, ?_⟩
    intro s hs his
    exact hzinput ⟨s, his⟩
  let f : Fin (z + 2) → Fin (z + 1) := fun i =>
    ⟨output (S + i), by
      have ht : S ≤ S + (i : ℕ) := Nat.le_add_right _ _
      have havail := hT (S + i)
        (le_trans (Nat.le_max_left _ _) ht)
      have hactive := hTc (S + i)
        (le_trans (Nat.le_max_right _ _) ht)
      have hzavail : Available family
          (fun k : Fin (S + (i : ℕ) + 1) => input k)
          (fun k : Fin (S + (i : ℕ)) => output k) z := by
        refine ⟨?_, ?_, ?_⟩
        · simpa [hactive] using hzcore
        · intro k hk
          exact hzinput ⟨k, hk⟩
        · intro k hk
          exact hzoutput ⟨k, hk⟩
      rw [hfollow (S + i)]
      exact Nat.lt_succ_of_le (onlineGenerator_minimal family _ _ hzavail)⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    have hijNat : (i : ℕ) ≠ (j : ℕ) := by simpa using hne
    rcases lt_or_gt_of_ne hijNat with hijlt | hjilt
    · have havail := hT (S + j)
        (le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _))
      exact havail.2.2 ⟨S + i, by omega⟩ (Fin.mk.inj hij)
    · have havail := hT (S + i)
        (le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _))
      exact havail.2.2 ⟨S + j, by omega⟩ (Fin.mk.inj hij.symm)
  have hcard := Fintype.card_le_of_injective f hfinj
  simp at hcard


noncomputable def inputTime (input : Stream) (x : ℕ) : ℕ := by
  classical
  exact if h : x ∈ Set.range input then Nat.find h else 0

theorem inputTime_spec (input : Stream) {x : ℕ} (hx : x ∈ Set.range input) :
    input (inputTime input x) = x := by
  classical
  simp only [inputTime, dif_pos hx]
  exact Nat.find_spec hx

theorem attacker_count_le {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollow : Follows (onlineGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    ∃ r, ∀ n,
      GenLimit.PatientScope.prefixCount
          (informationCore family input \
            (GenLimit.GeneratorFirst input output ∩
              informationCore family input)) n ≤
        GenLimit.PatientScope.prefixCount
            (GenLimit.GeneratorFirst input output ∩
              informationCore family input) n + r := by
  classical
  obtain ⟨T, hT⟩ := eventual_available family input output hfollow hcore
  obtain ⟨Tc, hTc⟩ := eventually_activeCore_eq family input
  let S := max T Tc
  let core := informationCore family input
  let defender := GenLimit.GeneratorFirst input output ∩ core
  let attacker := core \ defender
  let early : Finset ℕ := (Finset.range (S + 1)).image input
  let partner : ℕ → ℕ := fun x => output (inputTime input x - 1)
  refine ⟨S + 1, ?_⟩
  intro n
  let ordinary := GenLimit.PatientScope.prefixFinset attacker n \ early
  have hordinary_maps : Set.MapsTo partner (↑ordinary : Set ℕ)
      (↑(GenLimit.PatientScope.prefixFinset defender n) : Set ℕ) := by
    intro x hx
    have hxord := Finset.mem_sdiff.mp hx
    have hxattPrefix := GenLimit.PatientScope.mem_prefixFinset.mp hxord.1
    have hxcore : x ∈ core := hxattPrefix.2.1
    have hxnotdef : x ∉ defender := hxattPrefix.2.2
    have hxrange : x ∈ Set.range input := by
      by_contra hxrange
      have hxgen := core_diff_range_subset_generatorFirst family input output hinj
        hfollow hcore ⟨hxcore, hxrange⟩
      exact hxnotdef ⟨hxgen, hxcore⟩
    let tx := inputTime input x
    have htx : input tx = x := inputTime_spec input hxrange
    have hStx : S < tx := by
      by_contra hnot
      have htxS : tx ≤ S := Nat.le_of_not_gt hnot
      apply hxord.2
      exact Finset.mem_image.mpr
        ⟨tx, Finset.mem_range.mpr (by omega), htx⟩
    have hqS : S ≤ tx - 1 := by omega
    have havail := hT (tx - 1)
      (le_trans (Nat.le_max_left _ _) hqS)
    have hactive := hTc (tx - 1)
      (le_trans (Nat.le_max_right _ _) hqS)
    have hxavail : Available family
        (fun k : Fin (tx - 1 + 1) => input k)
        (fun k : Fin (tx - 1) => output k) x := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [core, hactive] using hxcore
      · intro k hk
        have hklt : (k : ℕ) < tx := by omega
        have hkeq : (k : ℕ) = tx := hinj (hk.trans htx.symm)
        omega
      · intro k hk
        apply hxnotdef
        refine ⟨?_, hxcore⟩
        refine ⟨k, hk, ?_⟩
        intro s hs his
        have hslt : s < tx := by omega
        have hseq : s = tx := hinj (his.trans htx.symm)
        omega
    have hpartner_le : partner x ≤ x := by
      dsimp [partner]
      rw [hfollow (tx - 1)]
      exact onlineGenerator_minimal family _ _ hxavail
    apply GenLimit.PatientScope.mem_prefixFinset.mpr
    refine ⟨lt_of_le_of_lt hpartner_le hxattPrefix.1, ?_⟩
    refine ⟨?_, ?_⟩
    · dsimp [partner]
      refine ⟨tx - 1, rfl, ?_⟩
      intro s hs his
      exact havail.2.1 ⟨s, by omega⟩ his
    · dsimp [partner]
      simpa [core, hactive] using havail.1
  have hordinary_inj : Set.InjOn partner (↑ordinary : Set ℕ) := by
    intro x hx y hy hxy
    have hxord := Finset.mem_sdiff.mp hx
    have hyord := Finset.mem_sdiff.mp hy
    have hxatt := (GenLimit.PatientScope.mem_prefixFinset.mp hxord.1).2
    have hyatt := (GenLimit.PatientScope.mem_prefixFinset.mp hyord.1).2
    have hxrange : x ∈ Set.range input := by
      by_contra hxrange
      exact hxatt.2 ⟨core_diff_range_subset_generatorFirst family input output hinj
        hfollow hcore ⟨hxatt.1, hxrange⟩, hxatt.1⟩
    have hyrange : y ∈ Set.range input := by
      by_contra hyrange
      exact hyatt.2 ⟨core_diff_range_subset_generatorFirst family input output hinj
        hfollow hcore ⟨hyatt.1, hyrange⟩, hyatt.1⟩
    let tx := inputTime input x
    let ty := inputTime input y
    have htx : input tx = x := inputTime_spec input hxrange
    have hty : input ty = y := inputTime_spec input hyrange
    have hStx : S < tx := by
      by_contra hnot
      apply hxord.2
      exact Finset.mem_image.mpr
        ⟨tx, Finset.mem_range.mpr (by omega), htx⟩
    have hSty : S < ty := by
      by_contra hnot
      apply hyord.2
      exact Finset.mem_image.mpr
        ⟨ty, Finset.mem_range.mpr (by omega), hty⟩
    have htimes : tx - 1 = ty - 1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hSy : S ≤ ty - 1 := by omega
        have havail := hT (ty - 1)
          (le_trans (Nat.le_max_left _ _) hSy)
        exact havail.2.2 ⟨tx - 1, hlt⟩ hxy
      · have hSx : S ≤ tx - 1 := by omega
        have havail := hT (tx - 1)
          (le_trans (Nat.le_max_left _ _) hSx)
        exact havail.2.2 ⟨ty - 1, hgt⟩ hxy.symm
    have htxy : tx = ty := by omega
    calc
      x = input tx := htx.symm
      _ = input ty := by rw [htxy]
      _ = y := hty
  have hordCard : ordinary.card ≤
      (GenLimit.PatientScope.prefixFinset defender n).card :=
    Finset.card_le_card_of_injOn partner hordinary_maps hordinary_inj
  have hsubset : GenLimit.PatientScope.prefixFinset attacker n ⊆
      ordinary ∪ early := by
    intro x hx
    by_cases hearly : x ∈ early
    · exact Finset.mem_union_right _ hearly
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hearly⟩)
  calc
    GenLimit.PatientScope.prefixCount attacker n =
        (GenLimit.PatientScope.prefixFinset attacker n).card := rfl
    _ ≤ (ordinary ∪ early).card := Finset.card_le_card hsubset
    _ ≤ ordinary.card + early.card := Finset.card_union_le _ _
    _ ≤ (GenLimit.PatientScope.prefixFinset defender n).card + (S + 1) := by
      apply Nat.add_le_add hordCard
      exact le_trans Finset.card_image_le (by simp [early])
    _ = GenLimit.PatientScope.prefixCount defender n + (S + 1) := rfl

theorem relativeLowerDensity_mono_left {A B K : Language}
    (hAB : A ⊆ B) (hBK : B ⊆ K) :
    GenLimit.PatientScope.relativeLowerDensity A K ≤
      GenLimit.PatientScope.relativeLowerDensity B K := by
  apply liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n => by
      gcongr
      exact_mod_cast GenLimit.PatientScope.prefixCount_mono hAB n
  · exact Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hratio : ∀ n,
        (GenLimit.PatientScope.prefixCount B n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
      intro n
      by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
      · have hBn : GenLimit.PatientScope.prefixCount B n = 0 := by
          apply Nat.eq_zero_of_le_zero
          simpa [hn] using GenLimit.PatientScope.prefixCount_mono hBK n
        simp [hn, hBn]
      · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
        exact_mod_cast GenLimit.PatientScope.prefixCount_mono hBK n
    exact Filter.isCoboundedUnder_ge_of_le atTop hratio

theorem half_core_density {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollow : Follows (onlineGenerator family) input output)
    (hcore : (informationCore family input).Infinite) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) (informationCore family input) ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ informationCore family input)
        (informationCore family input) := by
  let core := informationCore family input
  let defender := GenLimit.GeneratorFirst input output ∩ core
  let attacker := core \ defender
  obtain ⟨r, hcharge⟩ := attacker_count_le family input output hinj hfollow hcore
  have hpartition : ∀ n,
      GenLimit.PatientScope.prefixCount defender n +
          GenLimit.PatientScope.prefixCount attacker n =
        GenLimit.PatientScope.prefixCount core n := by
    intro n
    classical
    have hdisj : Disjoint
        (GenLimit.PatientScope.prefixFinset defender n)
        (GenLimit.PatientScope.prefixFinset attacker n) := by
      rw [Finset.disjoint_left]
      intro x hxD hxA
      have hxD' := (GenLimit.PatientScope.mem_prefixFinset.mp hxD).2
      have hxA' := (GenLimit.PatientScope.mem_prefixFinset.mp hxA).2
      exact hxA'.2 hxD'
    have hunion :
        GenLimit.PatientScope.prefixFinset defender n ∪
            GenLimit.PatientScope.prefixFinset attacker n =
          GenLimit.PatientScope.prefixFinset core n := by
      ext x
      simp only [GenLimit.PatientScope.mem_prefixFinset, Finset.mem_union]
      constructor
      · rintro (hx | hx)
        · exact ⟨hx.1, hx.2.2⟩
        · exact ⟨hx.1, hx.2.1⟩
      · intro hx
        by_cases hd : x ∈ defender
        · exact Or.inl ⟨hx.1, hd⟩
        · exact Or.inr ⟨hx.1, hx.2, hd⟩
    change (GenLimit.PatientScope.prefixFinset defender n).card +
        (GenLimit.PatientScope.prefixFinset attacker n).card =
      (GenLimit.PatientScope.prefixFinset core n).card
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hcharge' : ∀ n,
      GenLimit.PatientScope.prefixCount attacker n ≤
        GenLimit.PatientScope.prefixCount defender n + r +
          Nat.log2 (GenLimit.PatientScope.prefixCount core n) := by
    intro n
    have hc := hcharge n
    change GenLimit.PatientScope.prefixCount attacker n ≤
      GenLimit.PatientScope.prefixCount defender n + r at hc
    omega
  have hhalf := GenLimit.PatientScope.lowerDensity_half_of_target_counting
    core hcore
    (fun n => GenLimit.PatientScope.prefixCount defender n)
    (fun n => GenLimit.PatientScope.prefixCount attacker n) r
    hpartition hcharge'
  have hself : GenLimit.PatientScope.relativeLowerDensity core core = 1 := by
    have hpos : ∀ᶠ n : ℕ in atTop,
        0 < GenLimit.PatientScope.prefixCount core n :=
      (GenLimit.PatientScope.tendsto_prefixCount_atTop hcore).eventually
        (eventually_gt_atTop 0)
    have htend : Tendsto
        (fun n : ℕ =>
          (GenLimit.PatientScope.prefixCount core n : ℝ) /
            (GenLimit.PatientScope.prefixCount core n : ℝ))
        atTop (𝓝 (1 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hpos] with n hn
      simp [Nat.ne_of_gt hn]
    exact htend.liminf_eq
  rw [show GenLimit.PatientScope.relativeLowerDensity
      (informationCore family input) (informationCore family input) = 1 by
        simpa [core] using hself]
  norm_num
  simpa [GenLimit.PatientScope.relativeLowerDensity, core, defender] using hhalf


theorem half_core_density_in_target {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hinj : Function.Injective input)
    (hfollow : Follows (onlineGenerator family) input output)
    (hcore : (informationCore family input).Infinite)
    (K : Language) (hK : K.Infinite)
    (hcoreK : informationCore family input ⊆ K) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity
        (informationCore family input) K ≤
      GenLimit.PatientScope.relativeLowerDensity
        (GenLimit.GeneratorFirst input output ∩ informationCore family input) K := by
  let core := informationCore family input
  let defender := GenLimit.GeneratorFirst input output ∩ core
  let attacker := core \ defender
  obtain ⟨r, hcharge⟩ := attacker_count_le family input output hinj hfollow hcore
  have hpartition : ∀ n,
      GenLimit.PatientScope.prefixCount defender n +
          GenLimit.PatientScope.prefixCount attacker n =
        GenLimit.PatientScope.prefixCount core n := by
    intro n
    classical
    have hdisj : Disjoint
        (GenLimit.PatientScope.prefixFinset defender n)
        (GenLimit.PatientScope.prefixFinset attacker n) := by
      rw [Finset.disjoint_left]
      intro x hxD hxA
      exact (GenLimit.PatientScope.mem_prefixFinset.mp hxA).2.2
        (GenLimit.PatientScope.mem_prefixFinset.mp hxD).2
    have hunion :
        GenLimit.PatientScope.prefixFinset defender n ∪
            GenLimit.PatientScope.prefixFinset attacker n =
          GenLimit.PatientScope.prefixFinset core n := by
      ext x
      simp only [GenLimit.PatientScope.mem_prefixFinset, Finset.mem_union]
      constructor
      · rintro (hx | hx)
        · exact ⟨hx.1, hx.2.2⟩
        · exact ⟨hx.1, hx.2.1⟩
      · intro hx
        by_cases hd : x ∈ defender
        · exact Or.inl ⟨hx.1, hd⟩
        · exact Or.inr ⟨hx.1, hx.2, hd⟩
    change (GenLimit.PatientScope.prefixFinset defender n).card +
        (GenLimit.PatientScope.prefixFinset attacker n).card =
      (GenLimit.PatientScope.prefixFinset core n).card
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hcount : ∀ n,
      GenLimit.PatientScope.prefixCount core n ≤
        2 * GenLimit.PatientScope.prefixCount defender n + r +
          Nat.log2 (GenLimit.PatientScope.prefixCount K n) := by
    intro n
    have hc := hcharge n
    change GenLimit.PatientScope.prefixCount attacker n ≤
      GenLimit.PatientScope.prefixCount defender n + r at hc
    have hp := hpartition n
    omega
  have h := GenLimit.PatientScope.partialDensity_of_counting
    (fun n => GenLimit.PatientScope.prefixCount K n)
    (fun n => GenLimit.PatientScope.prefixCount core n)
    (fun n => GenLimit.PatientScope.prefixCount defender n) r
    (GenLimit.PatientScope.tendsto_prefixCount_atTop hK)
    (fun n => GenLimit.PatientScope.prefixCount_mono hcoreK n)
    (fun n => GenLimit.PatientScope.prefixCount_mono
      (Set.Subset.trans Set.inter_subset_right hcoreK) n)
    hcount
  simpa [GenLimit.PatientScope.relativeLowerDensity, core, defender] using h

noncomputable def trajectory {m : ℕ} (family : Fin m → Language)
    (input : Stream) (t : ℕ) : ℕ :=
  onlineGenerator family t (fun i => input i)
    (fun i => trajectory family input i)
termination_by t

@[simp] theorem trajectory_follows {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    Follows (onlineGenerator family) input (trajectory family input) := by
  intro t
  rw [trajectory]

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  refine ⟨Stage3Case017Proof.onlineGenerator family, ?_⟩
  intro input hinj hexists hcore
  let output := Stage3Case017Proof.trajectory family input
  have hfollow : Stage3Case017.Follows
      (Stage3Case017Proof.onlineGenerator family) input output :=
    Stage3Case017Proof.trajectory_follows family input
  refine ⟨output, hfollow, ?_⟩
  intro j hstream
  have hcoreSub : Stage3Case017.informationCore family input ⊆ family j := by
    intro z hz
    exact hz j hstream
  have hnovel : GenLimit.NovelGeneratesInLimit input output (family j) := by
    obtain ⟨T, hT⟩ := Stage3Case017Proof.eventual_activeCore
      family input output hfollow hcore
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨hmem, hfreshInput, hfreshOutput⟩ := hT t ht
    refine ⟨hcoreSub hmem, ?_, hfreshOutput⟩
    intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, his⟩ := hsample
    exact hfreshInput s (by omega) his
  refine ⟨hnovel, ?_⟩
  apply max_le
  · have hhalf := Stage3Case017Proof.half_core_density_in_target
      family input output hinj hfollow hcore (family j) (hinfinite j) hcoreSub
    exact le_trans hhalf
      (Stage3Case017Proof.relativeLowerDensity_mono_left
        (K := family j)
        (by
          intro z hz
          exact ⟨hz.1, hcoreSub hz.2⟩)
        Set.inter_subset_right)
  · apply Stage3Case017Proof.relativeLowerDensity_mono_left
      (K := family j)
  
    · intro z hz
      exact ⟨Stage3Case017Proof.core_diff_range_subset_generatorFirst
        family input output hinj hfollow hcore hz, hcoreSub hz.1⟩
    · exact Set.inter_subset_right
