import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Set Filter
open scoped Topology

namespace Case017Proof

open Stage3Case017

noncomputable def inputSeen {t : ℕ} (xs : Fin (t + 1) → ℕ) : Finset ℕ :=
  Finset.univ.image xs

noncomputable def outputSeen {t : ℕ} (ys : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image ys

noncomputable def eligible {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ) (z : ℕ) : Prop :=
  (∀ j, (∀ i, xs i ∈ family j) → z ∈ family j) ∧
    z ∉ inputSeen xs ∧ z ∉ outputSeen ys

noncomputable def greedyGenerator {m : ℕ} (family : Fin m → Language) :
    OnlineGenerator := by
  classical
  exact fun t xs ys =>
    if h : ∃ z, eligible family xs ys z then Nat.find h else 0

noncomputable def run (gen : OnlineGenerator) (input : Stream) (t : ℕ) : ℕ :=
  gen t (fun i => input i) (fun i => run gen input i)
termination_by t

theorem run_follows (gen : OnlineGenerator) (input : Stream) :
    Follows gen input (run gen input) := by
  intro t
  rw [run]

@[simp] theorem mem_inputSeen {t : ℕ} (xs : Fin (t + 1) → ℕ) (z : ℕ) :
    z ∈ inputSeen xs ↔ ∃ i, xs i = z := by
  simp [inputSeen]

@[simp] theorem mem_outputSeen {t : ℕ} (ys : Fin t → ℕ) (z : ℕ) :
    z ∈ outputSeen ys ↔ ∃ i, ys i = z := by
  simp [outputSeen]

theorem greedy_eligible {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, eligible family xs ys z) :
    eligible family xs ys (greedyGenerator family t xs ys) := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_spec h

theorem greedy_min {m t : ℕ} (family : Fin m → Language)
    (xs : Fin (t + 1) → ℕ) (ys : Fin t → ℕ)
    (h : ∃ z, eligible family xs ys z) {z : ℕ}
    (hz : eligible family xs ys z) :
    greedyGenerator family t xs ys ≤ z := by
  classical
  simp only [greedyGenerator, dif_pos h]
  exact Nat.find_min' h hz

theorem eventually_prefix_characterizes {m : ℕ} (family : Fin m → Language)
    (input : Stream) :
    ∀ᶠ t in atTop, ∀ j, (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  classical
  have hall : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      ∀ᶠ t in atTop, (∀ i : Fin (t + 1), input i ∈ family j) ↔
        GenLimit.Generic.StreamIn input (family j) := by
    intro j hjmem
    by_cases hj : GenLimit.Generic.StreamIn input (family j)
    · exact Filter.Eventually.of_forall fun _ => ⟨fun _ => hj, fun _ i => hj ⟨i, rfl⟩⟩
    · rw [GenLimit.Generic.StreamIn, Set.range_subset_iff] at hj
      push_neg at hj
      obtain ⟨k, hk⟩ := hj
      filter_upwards [eventually_ge_atTop k] with t ht
      constructor
      · intro hp
        exact (hk (hp ⟨k, Nat.lt_succ_of_le ht⟩)).elim
      · intro h
        exact (hk (h ⟨k, rfl⟩)).elim
  have h := (eventually_all_finset (Finset.univ : Finset (Fin m))).2 hall
  simpa only [Finset.mem_univ, true_implies] using h

theorem stable_eligible {m : ℕ} (family : Fin m → Language)
    (input output : Stream) (hcore : (informationCore family input).Infinite) :
    ∀ᶠ t in atTop, ∃ z, eligible family (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => output i) z := by
  filter_upwards [eventually_prefix_characterizes family input] with t ht
  let seen := inputSeen (fun i : Fin (t + 1) => input i) ∪
    outputSeen (fun i : Fin t => output i)
  obtain ⟨z, hzcore, hzseen⟩ := hcore.exists_notMem_finset seen
  refine ⟨z, ?_, ?_, ?_⟩
  · intro j hj
    exact hzcore j ((ht j).mp hj)
  · intro hz
    exact hzseen (Finset.mem_union_left _ hz)
  · intro hz
    exact hzseen (Finset.mem_union_right _ hz)


noncomputable abbrev greedyOutput {m : ℕ} (family : Fin m → Language)
    (input : Stream) : Stream := run (greedyGenerator family) input

theorem eventually_greedy {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    ∀ᶠ t in atTop,
      greedyOutput family input t ∈ informationCore family input ∧
      greedyOutput family input t ∉ GenLimit.sample input (t + 1) ∧
      (∀ s, s < t → greedyOutput family input s ≠ greedyOutput family input t) ∧
      ∀ z ∈ informationCore family input,
        z ∉ GenLimit.sample input (t + 1) →
        (∀ s, s < t → greedyOutput family input s ≠ z) →
        greedyOutput family input t ≤ z := by
  filter_upwards [eventually_prefix_characterizes family input,
    stable_eligible family input (greedyOutput family input) hcore] with t ht hex
  let xs : Fin (t + 1) → ℕ := fun i => input i
  let ys : Fin t → ℕ := fun i => greedyOutput family input i
  have hout : greedyOutput family input t = greedyGenerator family t xs ys := by
    simpa [xs, ys] using (run_follows (greedyGenerator family) input t)
  have hel := greedy_eligible family xs ys hex
  have hcoreout : greedyOutput family input t ∈ informationCore family input := by
    rw [hout]
    intro j hj
    exact hel.1 j ((ht j).mpr hj)
  refine ⟨hcoreout, ?_, ?_, ?_⟩
  · intro hmem
    rw [GenLimit.sample, Finset.mem_image] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    have hsfin : s < t + 1 := Finset.mem_range.mp hs
    have hin : greedyGenerator family t xs ys ∈ inputSeen xs := by
      rw [mem_inputSeen]
      exact ⟨⟨s, hsfin⟩, by simpa [xs, hout] using heq⟩
    exact hel.2.1 hin
  · intro s hs heq
    have houtseen : greedyGenerator family t xs ys ∈ outputSeen ys := by
      rw [mem_outputSeen]
      exact ⟨⟨s, hs⟩, by simpa [ys, hout] using heq⟩
    exact hel.2.2 houtseen
  · intro z hzcore hzinput hzoutput
    have hzinputSeen : z ∉ inputSeen xs := by
      intro hmem
      rw [mem_inputSeen] at hmem
      obtain ⟨i, hi⟩ := hmem
      apply hzinput
      rw [GenLimit.sample, Finset.mem_image]
      exact ⟨i, Finset.mem_range.mpr i.isLt, hi⟩
    have hzoutputSeen : z ∉ outputSeen ys := by
      intro hmem
      rw [mem_outputSeen] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact hzoutput i i.isLt hi
    have hzel : eligible family xs ys z := by
      refine ⟨?_, hzinputSeen, hzoutputSeen⟩
      intro j hj
      exact hzcore j ((ht j).mp (by simpa [xs] using hj))
    rw [hout]
    exact greedy_min family xs ys hex hzel

theorem eventually_novel_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    GenLimit.NovelGeneratesInLimit input (greedyOutput family input)
      (informationCore family input) := by
  rw [GenLimit.NovelGeneratesInLimit]
  have hg := eventually_greedy family input hcore
  rw [eventually_atTop] at hg
  obtain ⟨T, hT⟩ := hg
  refine ⟨T, ?_⟩
  intro t ht
  exact ⟨(hT t ht).1, (hT t ht).2.1, (hT t ht).2.2.1⟩

theorem novel_of_core {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input (greedyOutput family input) (family j) := by
  obtain ⟨T, hT⟩ := eventually_novel_core family input hcore
  refine ⟨T, ?_⟩
  intro t ht
  exact ⟨(hT t ht).1 j hj, (hT t ht).2.1, (hT t ht).2.2⟩




@[simp] theorem mem_prefixFinset' (S : Set ℕ) (n x : ℕ) :
    x ∈ GenLimit.PatientScope.prefixFinset S n ↔ x < n ∧ x ∈ S := by
  classical
  simp [GenLimit.PatientScope.prefixFinset]

theorem post_output_mem_generatorFirst {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    {T t : ℕ} (hT : ∀ u, T ≤ u →
      greedyOutput family input u ∈ informationCore family input ∧
      greedyOutput family input u ∉ GenLimit.sample input (u + 1) ∧
      (∀ s, s < u → greedyOutput family input s ≠ greedyOutput family input u) ∧
      ∀ z ∈ informationCore family input,
        z ∉ GenLimit.sample input (u + 1) →
        (∀ s, s < u → greedyOutput family input s ≠ z) →
        greedyOutput family input u ≤ z)
    (ht : T ≤ t) :
    greedyOutput family input t ∈ GenLimit.GeneratorFirst input (greedyOutput family input) := by
  refine ⟨t, rfl, ?_⟩
  intro s hs heq
  apply (hT t ht).2.1
  rw [GenLimit.sample, Finset.mem_image]
  exact ⟨s, Finset.mem_range.mpr (Nat.lt_succ_of_le hs), heq⟩

theorem post_output_injective {m : ℕ} (family : Fin m → Language)
    (input : Stream)
    {T a b : ℕ} (hT : ∀ u, T ≤ u →
      (∀ s, s < u → greedyOutput family input s ≠ greedyOutput family input u))
    (ha : T ≤ a) (hb : T ≤ b)
    (heq : greedyOutput family input a = greedyOutput family input b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact ((hT b hb a hab) heq).elim
  · exact hab
  · exact ((hT a ha b hab) heq.symm).elim

theorem missing_core_subset {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite) :
    informationCore family input \ Set.range input ⊆
      GenLimit.GeneratorFirst input (greedyOutput family input) := by
  have hg := eventually_greedy family input hcore
  rw [eventually_atTop] at hg
  obtain ⟨T, hT⟩ := hg
  intro z hz
  by_contra hzfirst
  have hzout : ∀ t, greedyOutput family input t ≠ z := by
    intro t heq
    apply hzfirst
    refine ⟨t, heq, ?_⟩
    intro s hs hinput
    exact hz.2 ⟨s, hinput⟩
  have hsmall : ∀ i : Fin (z + 1), greedyOutput family input (T + i) < z := by
    intro i
    have ht : T ≤ T + i := by omega
    have hsample : z ∉ GenLimit.sample input (T + i + 1) := by
      intro hm
      rw [GenLimit.sample, Finset.mem_image] at hm
      obtain ⟨s, hs, hsval⟩ := hm
      exact hz.2 ⟨s, hsval⟩
    have hprev : ∀ s, s < T + i → greedyOutput family input s ≠ z :=
      fun s hs => hzout s
    have hle := (hT (T + i) ht).2.2.2 z hz.1 hsample hprev
    exact lt_of_le_of_ne hle (hzout (T + i))
  let f : Fin (z + 1) → Fin z := fun i => ⟨greedyOutput family input (T + i), hsmall i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hout : greedyOutput family input (T + i) = greedyOutput family input (T + j) :=
      congrArg Fin.val hij
    have htime := post_output_injective family input
      (fun u hu => (hT u hu).2.2.1) (by omega) (by omega) hout
    omega
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at this
  omega

theorem greedy_prefix_count {m : ℕ} (family : Fin m → Language)
    (input : Stream) (hcore : (informationCore family input).Infinite)
    (K : Language) (hcoreK : informationCore family input ⊆ K) :
    ∃ C, ∀ n,
      GenLimit.PatientScope.prefixCount (informationCore family input) n ≤
        2 * GenLimit.PatientScope.prefixCount
          (GenLimit.GeneratorFirst input (greedyOutput family input) ∩ K) n + C := by
  classical
  have hg := eventually_greedy family input hcore
  rw [eventually_atTop] at hg
  obtain ⟨T, hT⟩ := hg
  refine ⟨2 * T + 1, ?_⟩
  intro n
  let core := informationCore family input
  let D := GenLimit.GeneratorFirst input (greedyOutput family input) ∩ K
  let S := GenLimit.PatientScope.prefixFinset core n
  let DF := GenLimit.PatientScope.prefixFinset D n
  let q := DF.card
  have hpostD : ∀ t, T ≤ t → greedyOutput family input t ∈ D := by
    intro t ht
    exact ⟨post_output_mem_generatorFirst family input hcore hT ht,
      hcoreK (hT t ht).1⟩
  have houtside : ∃ i : Fin (q + 1), greedyOutput family input (T + i) ∉ DF := by
    by_contra hall
    push_neg at hall
    let f : Fin (q + 1) → {x // x ∈ DF} := fun i =>
      ⟨greedyOutput family input (T + i), hall i⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      have hout : greedyOutput family input (T + i) = greedyOutput family input (T + j) :=
        congrArg Subtype.val hij
      have htime := post_output_injective family input
        (fun u hu => (hT u hu).2.2.1) (by omega) (by omega) hout
      omega
    have hc := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin, Fintype.card_coe, q] at hc
    omega
  obtain ⟨i, hi⟩ := houtside
  let r := T + (i : ℕ)
  have hrT : T ≤ r := by simp [r]
  have hrq : r ≤ T + q := by simp [r]; omega
  have hrge : n ≤ greedyOutput family input r := by
    have hd := hpostD r hrT
    by_contra hlt
    apply hi
    rw [mem_prefixFinset']
    exact ⟨Nat.lt_of_not_ge hlt, hd⟩
  let preOut := (Finset.range T).image (greedyOutput family input)
  let inSeen := (Finset.range (r + 1)).image input
  have hsubset : S \ DF ⊆ preOut ∪ inSeen := by
    intro z hz
    rw [Finset.mem_sdiff, mem_prefixFinset'] at hz
    by_cases hpre : z ∈ preOut
    · exact Finset.mem_union_left _ hpre
    · apply Finset.mem_union_right
      by_contra hin
      have hzsample : z ∉ GenLimit.sample input (r + 1) := by
        simpa [GenLimit.sample, inSeen] using hin
      have hzprev : ∀ s, s < r → greedyOutput family input s ≠ z := by
        intro s hs heq
        by_cases hsT : s < T
        · apply hpre
          simpa [preOut] using
            (show z ∈ (Finset.range T).image (greedyOutput family input) from
              Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hsT, heq⟩)
        · have hsd : greedyOutput family input s ∈ D := hpostD s (Nat.le_of_not_gt hsT)
          apply hz.2
          rw [mem_prefixFinset']
          exact ⟨hz.1.1, by simpa [heq] using hsd⟩
      have hle := (hT r hrT).2.2.2 z (by simpa [core] using hz.1.2) hzsample hzprev
      omega
  have hsdiff : (S \ DF).card ≤ q + (2 * T + 1) := by
    calc
      (S \ DF).card ≤ (preOut ∪ inSeen).card := Finset.card_le_card hsubset
      _ ≤ preOut.card + inSeen.card := Finset.card_union_le _ _
      _ ≤ T + (r + 1) := Nat.add_le_add
        (by
          simpa [preOut] using (Finset.card_image_le :
            ((Finset.range T).image (greedyOutput family input)).card ≤ (Finset.range T).card))
        (by
          simpa [inSeen] using (Finset.card_image_le :
            ((Finset.range (r + 1)).image input).card ≤ (Finset.range (r + 1)).card))
      _ ≤ q + (2 * T + 1) := by omega
  have hinter : (S ∩ DF).card ≤ q := by
    exact Finset.card_le_card (Finset.inter_subset_right)
  have hcard : S.card ≤ 2 * q + (2 * T + 1) := by
    rw [← Finset.card_sdiff_add_card_inter S DF]
    omega
  simpa [GenLimit.PatientScope.prefixCount, S, DF, q, core, D,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

namespace Density

open GenLimit.PatientScope

@[simp] theorem mem_prefixFinset (S : Set ℕ) (n x : ℕ) :
    x ∈ prefixFinset S n ↔ x < n ∧ x ∈ S := by
  simp [prefixFinset]

theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n := by
  apply Finset.card_le_card
  intro x hx
  rw [mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

theorem prefixCount_le (A : Set ℕ) (n : ℕ) : prefixCount A n ≤ n := by
  classical
  simpa [prefixCount, prefixFinset] using
    (Finset.card_filter_le (Finset.range n) (fun x => x ∈ A))

theorem prefixCount_tendsto {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => prefixCount K n) atTop atTop := by
  have h := (Set.infinite_iff_tendsto_sum_indicator_atTop
    (R := ℕ) (s := K) (r := 1) Nat.zero_lt_one).mp hK
  simpa [prefixCount, prefixFinset, Set.indicator] using h

theorem ratio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (prefixCount A n : ℝ) / (prefixCount K n : ℝ) := by positivity

theorem ratio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : prefixCount K n = 0
  · simp [hzero]
  · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero))).2
    exact_mod_cast prefixCount_mono hAK n

theorem relativeLowerDensity_mono {A B K : Set ℕ} (hAB : A ⊆ B)
    (hBK : B ⊆ K) :
    relativeLowerDensity A K ≤ relativeLowerDensity B K := by
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right (by exact_mod_cast prefixCount_mono hAB n)
        (Nat.cast_nonneg _)
  · exact isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => ratio_nonneg A K n)
  · exact isCoboundedUnder_ge_of_eventually_le atTop
      (Filter.Eventually.of_forall fun n => ratio_le_one hBK n)

theorem half_density_of_count {A D K : Set ℕ} (hAK : A ⊆ K) (hDK : D ⊆ K)
    (hK : K.Infinite) (C : ℕ)
    (hcount : ∀ n, prefixCount A n ≤ 2 * prefixCount D n + C) :
    (1 / 2 : ℝ) * relativeLowerDensity A K ≤ relativeLowerDensity D K := by
  let a : ℕ → ℝ := fun n => (prefixCount A n : ℝ) / (prefixCount K n : ℝ)
  let d : ℕ → ℝ := fun n => (prefixCount D n : ℝ) / (prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n => (C : ℝ) / (2 * (prefixCount K n : ℝ))
  have hpoint : ∀ n, (1 / 2 : ℝ) * a n ≤ d n + e n := by
    intro n
    by_cases hk0 : prefixCount K n = 0
    · simp [a, d, e, hk0]
    · have hkpos : (0 : ℝ) < prefixCount K n := by exact_mod_cast Nat.pos_of_ne_zero hk0
      dsimp [a, d, e]
      have hc : (prefixCount A n : ℝ) ≤ 2 * prefixCount D n + C := by
        exact_mod_cast hcount n
      field_simp [hk0]
      nlinarith
  have hkNat := prefixCount_tendsto hK
  have hkReal : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hkNat
  have he : Tendsto e atTop (𝓝 0) := by
    have hdiv := hkReal.const_div_atTop ((C : ℝ) / 2)
    convert hdiv using 1 <;> simp [e] <;> ring
  have ha_cob : atTop.IsCoboundedUnder (· ≥ ·) a :=
    isCoboundedUnder_ge_of_eventually_le atTop
      (Filter.Eventually.of_forall fun n => ratio_le_one hAK n)
  have ha_bdd : atTop.IsBoundedUnder (· ≥ ·) a :=
    isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => ratio_nonneg A K n)
  have hd_cob : atTop.IsCoboundedUnder (· ≥ ·) d :=
    isCoboundedUnder_ge_of_eventually_le atTop
      (Filter.Eventually.of_forall fun n => ratio_le_one hDK n)
  have hd_bdd : atTop.IsBoundedUnder (· ≥ ·) d :=
    isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => ratio_nonneg D K n)
  have hscale : Filter.liminf (fun n => (1 / 2 : ℝ) * a n) atTop =
      (1 / 2 : ℝ) * Filter.liminf a atTop := by
    symm
    exact (Monotone.map_liminf_of_continuousAt
      (f := fun x : ℝ => (1 / 2 : ℝ) * x)
      (fun _ _ h => mul_le_mul_of_nonneg_left h (by positivity)) a
      (continuous_const.mul continuous_id).continuousAt ha_cob ha_bdd)
  rw [relativeLowerDensity, relativeLowerDensity]
  change (1 / 2 : ℝ) * Filter.liminf a atTop ≤ Filter.liminf d atTop
  rw [← hscale]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hevent : ∀ᶠ n in atTop, e n ≤ ε :=
    ((tendsto_order.1 he).2 _ hε).mono fun _ h => h.le
  have hcomp : ∀ᶠ n in atTop, (1 / 2 : ℝ) * a n ≤ d n + ε := by
    filter_upwards [hevent] with n hn
    exact (hpoint n).trans (add_le_add_left hn (d n))
  have hlim := Filter.liminf_le_liminf hcomp
    (u := fun n => (1 / 2 : ℝ) * a n) (v := fun n => d n + ε)
    (isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => mul_nonneg (by norm_num) (ratio_nonneg A K n)))
    (isCoboundedUnder_ge_of_eventually_le atTop
      (Filter.Eventually.of_forall fun n => add_le_add_right (ratio_le_one hDK n) ε))
  rw [liminf_add_const atTop d ε hd_cob hd_bdd] at hlim
  exact hlim

end Density

end Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  intro m hm family hinfinite
  let gen := Case017Proof.greedyGenerator family
  refine ⟨gen, ?_⟩
  intro input hinjective hpresentation hcore
  let output := Case017Proof.greedyOutput family input
  refine ⟨output, ?_, ?_⟩
  · simpa [gen, output, Case017Proof.greedyOutput] using
      Case017Proof.run_follows gen input
  · intro j hcompat
    have hcoreK : Stage3Case017.informationCore family input ⊆ family j := by
      intro z hz
      exact hz j hcompat
    have hnovel := Case017Proof.novel_of_core family input hcore j hcompat
    refine ⟨by simpa [output] using hnovel, ?_⟩
    let D := GenLimit.GeneratorFirst input output ∩ family j
    obtain ⟨C, hcount⟩ := Case017Proof.greedy_prefix_count family input hcore
      (family j) hcoreK
    have hhalf :
        (1 / 2 : ℝ) *
            GenLimit.PatientScope.relativeLowerDensity
              (Stage3Case017.informationCore family input) (family j) ≤
          GenLimit.PatientScope.relativeLowerDensity D (family j) := by
      apply Case017Proof.Density.half_density_of_count hcoreK
        (Set.inter_subset_right) (hinfinite j) C
      simpa [D, output] using hcount
    have hmissing :
        GenLimit.PatientScope.relativeLowerDensity
              (Stage3Case017.informationCore family input \ Set.range input) (family j) ≤
          GenLimit.PatientScope.relativeLowerDensity D (family j) := by
      apply Case017Proof.Density.relativeLowerDensity_mono
        (B := D) (K := family j) ?_ Set.inter_subset_right
      intro z hz
      refine ⟨?_, hcoreK hz.1⟩
      simpa [output] using
        (Case017Proof.missing_core_subset family input hcore hz)
    simpa [D] using (max_le hhalf hmissing)
