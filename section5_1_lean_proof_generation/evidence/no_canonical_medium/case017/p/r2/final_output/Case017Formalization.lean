import Stage3Model
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.Order.LiminfLimsup
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology

namespace Stage3Case017Proof

noncomputable def roundPool {m : ℕ} (family : Fin m → Stage3Case017.Language)
    {t : ℕ} (xs : Fin (t + 1) → ℕ) : Set ℕ :=
  {z | (∀ j, (∀ i, xs i ∈ family j) → z ∈ family j) ∧ ∀ i, z ≠ xs i}

noncomputable def generator {m : ℕ} (family : Fin m → Stage3Case017.Language) :
    Stage3Case017.OnlineGenerator :=
  fun t xs _ => Nat.nth (fun z => z ∈ roundPool family xs) t

lemma exists_bad_time {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    ∃ n, input n ∉ family j := by
  obtain ⟨z, ⟨n, rfl⟩, hn⟩ := Set.not_subset.mp h
  exact ⟨n, hn⟩

noncomputable def badTime {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (j : Fin m) : ℕ := by
  classical
  exact if h : GenLimit.Generic.StreamIn input (family j) then 0
  else Nat.find (exists_bad_time family input j h)

lemma badTime_spec {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (j : Fin m)
    (h : ¬ GenLimit.Generic.StreamIn input (family j)) :
    input (badTime family input j) ∉ family j := by
  classical
  rw [badTime, dif_neg h]
  exact Nat.find_spec (exists_bad_time family input j h)

noncomputable def stableTime {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) : ℕ :=
  Finset.univ.sup (badTime family input)

lemma badTime_le_stableTime {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) (j : Fin m) :
    badTime family input j ≤ stableTime family input := by
  exact Finset.le_sup (Finset.mem_univ j)

lemma viable_iff_streamIn {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) {t : ℕ}
    (ht : stableTime family input ≤ t) (j : Fin m) :
    (∀ i : Fin (t + 1), input i ∈ family j) ↔
      GenLimit.Generic.StreamIn input (family j) := by
  constructor
  · intro hprefix
    by_contra hnot
    have hbad := badTime_spec family input j hnot
    have hle : badTime family input j < t + 1 :=
      Nat.lt_succ_of_le ((badTime_le_stableTime family input j).trans ht)
    exact hbad (hprefix ⟨badTime family input j, hle⟩)
  · intro hin i
    exact hin ⟨i, rfl⟩

lemma roundPool_eq {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) {t : ℕ}
    (ht : stableTime family input ≤ t) :
    roundPool family (fun i : Fin (t + 1) => input i) =
      Stage3Case017.informationCore family input \
        Set.range (fun i : Fin (t + 1) => input i) := by
  ext z
  simp only [roundPool, mem_setOf_eq, mem_diff, mem_range]
  constructor
  · rintro ⟨hcore, hfresh⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      exact hcore j ((viable_iff_streamIn family input ht j).2 hj)
    · rintro ⟨i, rfl⟩
      exact hfresh i rfl
  · rintro ⟨hcore, hfresh⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      exact hcore j ((viable_iff_streamIn family input ht j).1 hj)
    · intro i hi
      exact hfresh ⟨i, hi.symm⟩

lemma roundPool_infinite {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    (roundPool family (fun i : Fin (t + 1) => input i)).Infinite := by
  rw [roundPool_eq family input ht]
  exact hcore.diff (Set.finite_range _)

lemma output_mem_pool {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    generator family t (fun i => input i) (fun _ => 0) ∈
      roundPool family (fun i : Fin (t + 1) => input i) := by
  exact Nat.nth_mem_of_infinite (roundPool_infinite family input hcore ht) t

end Stage3Case017Proof

namespace Stage3Case017Proof

lemma nth_le_nth_of_subset {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (hp : {n | p n}.Infinite) (hq : {n | q n}.Infinite)
    (hsub : ∀ n, q n → p n) (k : ℕ) :
    Nat.nth p k ≤ Nat.nth q k := by
  classical
  by_contra hnot
  have hlt : Nat.nth q k < Nat.nth p k := Nat.lt_of_not_ge hnot
  have hqmem : q (Nat.nth q k) := Nat.nth_mem_of_infinite hq k
  have hpmem : p (Nat.nth q k) := hsub _ hqmem
  have hcountlt := Nat.count_strict_mono hpmem hlt
  have hcountle : Nat.count q (Nat.nth q k) ≤ Nat.count p (Nat.nth q k) :=
    Nat.count_mono_left hsub
  rw [Nat.count_nth_of_infinite hp] at hcountlt
  rw [Nat.count_nth_of_infinite hq] at hcountle
  exact (not_lt_of_ge hcountle) hcountlt

lemma pool_subset_of_le {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) {s t : ℕ}
    (hs : stableTime family input ≤ s) (hst : s ≤ t) :
    roundPool family (fun i : Fin (t + 1) => input i) ⊆
      roundPool family (fun i : Fin (s + 1) => input i) := by
  rw [roundPool_eq family input (hs.trans hst), roundPool_eq family input hs]
  intro z hz
  refine ⟨hz.1, ?_⟩
  rintro ⟨i, hi⟩
  exact hz.2 ⟨⟨i, Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.isLt).trans hst)⟩, hi⟩

lemma stable_output_strictMono {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {s t : ℕ} (hs : stableTime family input ≤ s) (hst : s < t) :
    generator family s (fun i => input i) (fun _ => 0) <
      generator family t (fun i => input i) (fun _ => 0) := by
  classical
  let ps : ℕ → Prop := fun z => z ∈ roundPool family (fun i : Fin (s + 1) => input i)
  let pt : ℕ → Prop := fun z => z ∈ roundPool family (fun i : Fin (t + 1) => input i)
  have hps : {z | ps z}.Infinite := roundPool_infinite family input hcore hs
  have hpt : {z | pt z}.Infinite :=
    roundPool_infinite family input hcore (hs.trans hst.le)
  have hsubset : ∀ z, pt z → ps z :=
    pool_subset_of_le family input hs hst.le
  calc
    generator family s (fun i => input i) (fun _ => 0) = Nat.nth ps s := rfl
    _ < Nat.nth ps t := (Nat.nth_lt_nth hps).2 hst
    _ ≤ Nat.nth pt t := nth_le_nth_of_subset hps hpt hsubset t
    _ = generator family t (fun i => input i) (fun _ => 0) := rfl

lemma output_ge_time {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    t ≤ generator family t (fun i => input i) (fun _ => 0) := by
  apply Nat.le_nth
  intro hfinite
  exact (roundPool_infinite family input hcore ht hfinite).elim

noncomputable def noveltyTime {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) : ℕ :=
  max (stableTime family input)
    ((Finset.range (stableTime family input)).sup
      (fun s => generator family s (fun i => input i) (fun _ => 0)) + 1)

lemma follows_generator {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) :
    Stage3Case017.Follows (generator family) input
      (fun t => generator family t (fun i => input i) (fun _ => 0)) := by
  intro t
  rfl

lemma novel_generation {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) :
    GenLimit.NovelGeneratesInLimit input
      (fun t => generator family t (fun i => input i) (fun _ => 0)) (family j) := by
  refine ⟨noveltyTime family input, ?_⟩
  intro t ht
  have htstable : stableTime family input ≤ t :=
    (le_max_left _ _).trans ht
  have hmem := output_mem_pool family input hcore htstable
  rw [roundPool_eq family input htstable] at hmem
  refine ⟨hmem.1 j hj, ?_, ?_⟩
  · intro hsample
    rw [GenLimit.sample, Finset.mem_image] at hsample
    obtain ⟨r, hr, heq⟩ := hsample
    have hrlt : r < t + 1 := by simpa using hr
    exact hmem.2 ⟨⟨r, hrlt⟩, heq⟩
  · intro s hst heq
    by_cases hs : stableTime family input ≤ s
    · exact (ne_of_lt (stable_output_strictMono family input hcore hs hst)) heq
    · have hslt : s < stableTime family input := Nat.lt_of_not_ge hs
      have hsle : generator family s (fun i => input i) (fun _ => 0) <
          (Finset.range (stableTime family input)).sup
            (fun r => generator family r (fun i => input i) (fun _ => 0)) + 1 := by
        exact Nat.lt_succ_of_le
          (Finset.le_sup (f := fun r => generator family r (fun i => input i) (fun _ => 0))
            (Finset.mem_range.mpr hslt))
      have hbound :
          (Finset.range (stableTime family input)).sup
              (fun r => generator family r (fun i => input i) (fun _ => 0)) + 1 ≤ t :=
        (le_max_right _ _).trans ht
      have houtge := output_ge_time family input hcore htstable
      have : generator family s (fun i => input i) (fun _ => 0) <
          generator family t (fun i => input i) (fun _ => 0) :=
        hsle.trans_le (hbound.trans houtge)
      exact (ne_of_lt this) heq

end Stage3Case017Proof

namespace Stage3Case017Proof

noncomputable def outputStream {m : ℕ} (family : Fin m → Stage3Case017.Language)
    (input : Stage3Case017.Stream) : Stage3Case017.Stream :=
  fun t => generator family t (fun i => input i) (fun _ => 0)

lemma stable_output_generatorFirst {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    outputStream family input t ∈ GenLimit.GeneratorFirst input (outputStream family input) := by
  have hmem := output_mem_pool family input hcore ht
  rw [roundPool_eq family input ht] at hmem
  refine ⟨t, rfl, ?_⟩
  intro s hst heq
  exact hmem.2 ⟨⟨s, Nat.lt_succ_of_le hst⟩, heq⟩

lemma stable_output_mem_core {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {t : ℕ} (ht : stableTime family input ≤ t) :
    outputStream family input t ∈ Stage3Case017.informationCore family input := by
  have hmem := output_mem_pool family input hcore ht
  rw [roundPool_eq family input ht] at hmem
  exact hmem.1

lemma stable_output_lt_of_count {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    {t n : ℕ} (ht : stableTime family input ≤ t)
    (hcount : t < GenLimit.PatientScope.prefixCount
      (roundPool family (fun i : Fin (t + 1) => input i)) n) :
    outputStream family input t < n := by
  classical
  apply Nat.nth_lt_of_lt_count
  simpa [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range] using hcount

lemma missing_core_prefix_subset_pool {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    {t n : ℕ} (ht : stableTime family input ≤ t) :
    GenLimit.PatientScope.prefixFinset
        (Stage3Case017.informationCore family input \ Set.range input) n ⊆
      GenLimit.PatientScope.prefixFinset
        (roundPool family (fun i : Fin (t + 1) => input i)) n := by
  classical
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range, Set.mem_diff, Set.mem_range] at hz ⊢
  refine ⟨hz.1, ?_⟩
  rw [roundPool_eq family input ht]
  refine ⟨hz.2.1, ?_⟩
  rintro ⟨i, hi⟩
  exact hz.2.2 ⟨i, hi⟩

lemma missing_count_le_pool_count {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    {t n : ℕ} (ht : stableTime family input ≤ t) :
    GenLimit.PatientScope.prefixCount
        (Stage3Case017.informationCore family input \ Set.range input) n ≤
      GenLimit.PatientScope.prefixCount
        (roundPool family (fun i : Fin (t + 1) => input i)) n := by
  unfold GenLimit.PatientScope.prefixCount
  exact Finset.card_le_card (missing_core_prefix_subset_pool family input ht)

lemma core_count_le_pool_count_add {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    {t n : ℕ} (ht : stableTime family input ≤ t) :
    GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n ≤
      GenLimit.PatientScope.prefixCount
          (roundPool family (fun i : Fin (t + 1) => input i)) n + (t + 1) := by
  classical
  let observed : Finset ℕ :=
    (Finset.univ : Finset (Fin (t + 1))).image (fun i : Fin (t + 1) => input i)
  have hsubset :
      GenLimit.PatientScope.prefixFinset (Stage3Case017.informationCore family input) n ⊆
        GenLimit.PatientScope.prefixFinset
            (roundPool family (fun i : Fin (t + 1) => input i)) n ∪ observed := by
    intro z hz
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range] at hz ⊢
    by_cases hfresh : ∀ i : Fin (t + 1), z ≠ input i
    · rw [Finset.mem_union]
      left
      change z ∈ GenLimit.PatientScope.prefixFinset
        (roundPool family (fun i : Fin (t + 1) => input i)) n
      unfold GenLimit.PatientScope.prefixFinset
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hz.1, ?_⟩
      rw [roundPool_eq family input ht]
      refine ⟨hz.2, ?_⟩
      rintro ⟨i, hi⟩
      exact hfresh i hi.symm
    · rw [Finset.mem_union]
      right
      simp only [observed, Finset.mem_image, Finset.mem_univ, true_and]
      push_neg at hfresh
      obtain ⟨i, hi⟩ := hfresh
      exact ⟨i, hi.symm⟩
  calc
    GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n =
        (GenLimit.PatientScope.prefixFinset
          (Stage3Case017.informationCore family input) n).card := rfl
    _ ≤ (GenLimit.PatientScope.prefixFinset
          (roundPool family (fun i : Fin (t + 1) => input i)) n ∪ observed).card :=
      Finset.card_le_card hsubset
    _ ≤ (GenLimit.PatientScope.prefixFinset
          (roundPool family (fun i : Fin (t + 1) => input i)) n).card + observed.card :=
      Finset.card_union_le _ _
    _ ≤ GenLimit.PatientScope.prefixCount
          (roundPool family (fun i : Fin (t + 1) => input i)) n + (t + 1) := by
      change _ + observed.card ≤ _ + (t + 1)
      exact Nat.add_le_add_left
        (Finset.card_image_le.trans_eq (Fintype.card_fin (t + 1))) _

lemma output_prefix_count_lower {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j))
    (bound n : ℕ)
    (hsmall : ∀ t, stableTime family input ≤ t → t < bound → outputStream family input t < n) :
    bound - stableTime family input ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (outputStream family input) ∩ family j) n := by
  classical
  let times := Finset.Ico (stableTime family input) bound
  let values := times.image (outputStream family input)
  have hinj : Set.InjOn (outputStream family input) (↑times : Set ℕ) := by
    intro a ha b hb hab
    change a ∈ Finset.Ico (stableTime family input) bound at ha
    change b ∈ Finset.Ico (stableTime family input) bound at hb
    simp only [Finset.mem_Ico] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hablt | hbalt
    · exact (ne_of_lt (stable_output_strictMono family input hcore ha.1 hablt)) hab
    · exact (ne_of_lt (stable_output_strictMono family input hcore hb.1 hbalt)) hab.symm
  have hvalues : values ⊆
      GenLimit.PatientScope.prefixFinset
        (GenLimit.GeneratorFirst input (outputStream family input) ∩ family j) n := by
    intro z hz
    simp only [values, Finset.mem_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
      Finset.mem_range, Set.mem_inter_iff]
    change t ∈ Finset.Ico (stableTime family input) bound at ht
    simp only [Finset.mem_Ico] at ht
    refine ⟨hsmall t ht.1 ht.2, stable_output_generatorFirst family input hcore ht.1, ?_⟩
    exact stable_output_mem_core family input hcore ht.1 j hj
  calc
    bound - stableTime family input = times.card := by simp [times]
    _ = values.card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ _ := Finset.card_le_card hvalues

lemma missing_prefix_bound {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount
        (Stage3Case017.informationCore family input \ Set.range input) n -
        stableTime family input ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (outputStream family input) ∩ family j) n := by
  apply output_prefix_count_lower family input hcore j hj _ n
  intro t ht htbound
  apply stable_output_lt_of_count family input hcore ht
  exact htbound.trans_le (missing_count_le_pool_count family input ht)

lemma half_prefix_bound {m : ℕ}
    (family : Fin m → Stage3Case017.Language) (input : Stage3Case017.Stream)
    (hcore : (Stage3Case017.informationCore family input).Infinite)
    (j : Fin m) (hj : GenLimit.Generic.StreamIn input (family j)) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Stage3Case017.informationCore family input) n / 2 -
        stableTime family input ≤
      GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input (outputStream family input) ∩ family j) n := by
  apply output_prefix_count_lower family input hcore j hj _ n
  intro t ht htbound
  apply stable_output_lt_of_count family input hcore ht
  have hle := core_count_le_pool_count_add family input ht (n := n)
  omega

end Stage3Case017Proof

namespace Stage3Case017Proof

lemma prefixCount_tendsto_atTop (K : Stage3Case017.Language) (hK : K.Infinite) :
    Tendsto (fun n => GenLimit.PatientScope.prefixCount K n) atTop atTop := by
  have h := (Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℕ) Nat.zero_lt_one).1 hK
  simpa only [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Finset.card_eq_sum_ones, Finset.sum_filter, Set.indicator_apply, ite_apply,
    one_mul, zero_mul] using h

lemma prefixCount_cast_tendsto_atTop (K : Stage3Case017.Language) (hK : K.Infinite) :
    Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop := by
  rw [tendsto_natCast_atTop_iff]
  exact prefixCount_tendsto_atTop K hK

lemma constant_div_prefixCount_tendsto_zero (K : Stage3Case017.Language)
    (hK : K.Infinite) (C : ℕ) :
    Tendsto (fun n => (C : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ))
      atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul
      (prefixCount_cast_tendsto_atTop K hK).inv_tendsto_atTop)

lemma prefixCount_mono {A K : Stage3Case017.Language} (hAK : A ⊆ K) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount K n := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro z hz
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range] at hz ⊢
  exact ⟨hz.1, hAK hz.2⟩

lemma ratio_nonneg (A K : Stage3Case017.Language) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by positivity

lemma ratio_le_one {A K : Stage3Case017.Language} (hAK : A ⊆ K) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hzero]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono hAK n

lemma liminf_add_tendsto_zero {a e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0))
    (ha_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop a)
    (ha_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop a) :
    liminf (a + e) atTop = liminf a atTop := by
  have he_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop e :=
    he.isBoundedUnder_ge
  have he_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop e :=
    he.isBoundedUnder_le
  have ha_cobelow : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop a :=
    ha_above.isCoboundedUnder_ge
  have he_cobelow : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop e :=
    he_above.isCoboundedUnder_ge
  have hu := liminf_add_le (f := atTop) (u := e) (v := a)
    he_below he_above ha_below ha_cobelow
  have hl := le_liminf_add (f := atTop) (u := a) (v := e)
    ha_below ha_above he_below he_cobelow
  apply le_antisymm
  · calc
      liminf (a + e) atTop = liminf (e + a) atTop := by rw [add_comm a e]
      _ ≤ limsup e atTop + liminf a atTop := hu
      _ = liminf a atTop := by rw [he.limsup_eq]; exact zero_add _
  · calc
      liminf a atTop = liminf a atTop + liminf e atTop := by rw [he.liminf_eq]; exact (add_zero _).symm
      _ ≤ liminf (a + e) atTop := hl

lemma relativeLowerDensity_mono_up_to_constant
    {A B K : Stage3Case017.Language} (hK : K.Infinite)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (C : ℕ)
    (hcount : ∀ n, GenLimit.PatientScope.prefixCount B n - C ≤
      GenLimit.PatientScope.prefixCount A n) :
    GenLimit.PatientScope.relativeLowerDensity B K ≤
      GenLimit.PatientScope.relativeLowerDensity A K := by
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let b : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    (C : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have he : Tendsto e atTop (𝓝 0) := constant_div_prefixCount_tendsto_zero K hK C
  have ha0 : ∀ n, 0 ≤ a n := fun n => ratio_nonneg A K n
  have ha1 : ∀ n, a n ≤ 1 := fun n => ratio_le_one hAK n
  have hb0 : ∀ n, 0 ≤ b n := fun n => ratio_nonneg B K n
  have hb1 : ∀ n, b n ≤ 1 := fun n => ratio_le_one hBK n
  have hpoint : ∀ᶠ n in atTop, b n ≤ a n + e n := by
    filter_upwards [(prefixCount_tendsto_atTop K hK).eventually (eventually_ge_atTop 1)] with n hn
    have hkpos : 0 < (GenLimit.PatientScope.prefixCount K n : ℝ) := by exact_mod_cast hn
    have hnat := Nat.le_add_of_sub_le (hcount n)
    have hreal : (GenLimit.PatientScope.prefixCount B n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount A n : ℝ) + C := by exact_mod_cast hnat
    dsimp [a, b, e]
    rw [← add_div]
    exact (div_le_div_iff_of_pos_right hkpos).2 hreal
  have hb_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop b :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hb0)
  have ha_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop a :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall ha1)
  have ha_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop a :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall ha0)
  have he_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop e := he.isBoundedUnder_ge
  have he_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop e := he.isBoundedUnder_le
  have hae_cobelow : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop (a + e) :=
    isCoboundedUnder_ge_add ha_above he_above.isCoboundedUnder_ge
  have hba : liminf b atTop ≤ liminf (a + e) atTop :=
    liminf_le_liminf hpoint hb_below hae_cobelow
  have hsum : liminf (a + e) atTop = liminf a atTop :=
    liminf_add_tendsto_zero he ha_below ha_above
  change liminf b atTop ≤ liminf a atTop
  exact hba.trans_eq hsum

end Stage3Case017Proof

namespace Stage3Case017Proof

lemma liminf_const_mul_of_nonneg {r : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hr0 : ∀ n, 0 ≤ r n)
    (hr_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop r) :
    liminf (fun n => c * r n) atTop = c * liminf r atTop := by
  let u : ℕ → ℝ := fun _ => c
  have hu0 : ∀ᶠ n in atTop, 0 ≤ u n := Eventually.of_forall (fun _ => hc)
  have hu_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun _ => le_rfl))
  have hr0' : ∀ᶠ n in atTop, 0 ≤ r n := Eventually.of_forall hr0
  have hr_cobelow : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop r :=
    hr_above.isCoboundedUnder_ge
  have hl := le_liminf_mul (f := atTop) (u := u) (v := r)
    hu0 hu_above hr0' hr_cobelow
  have hu := liminf_mul_le (f := atTop) (u := u) (v := r)
    hu0 hu_above hr0' hr_cobelow
  change liminf (u * r) atTop = c * liminf r atTop
  apply le_antisymm
  · calc
      liminf (u * r) atTop ≤ limsup u atTop * liminf r atTop := hu
      _ = c * liminf r atTop := by rw [limsup_const]
  · calc
      c * liminf r atTop = liminf u atTop * liminf r atTop := by rw [liminf_const]
      _ ≤ liminf (u * r) atTop := hl

lemma half_relativeLowerDensity_le
    {A B K : Stage3Case017.Language} (hK : K.Infinite)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (C : ℕ)
    (hcount : ∀ n, GenLimit.PatientScope.prefixCount B n / 2 - C ≤
      GenLimit.PatientScope.prefixCount A n) :
    (1 / 2 : ℝ) * GenLimit.PatientScope.relativeLowerDensity B K ≤
      GenLimit.PatientScope.relativeLowerDensity A K := by
  let a : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount A n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let b : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount B n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n =>
    ((C + 1 : ℕ) : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have he : Tendsto e atTop (𝓝 0) :=
    constant_div_prefixCount_tendsto_zero K hK (C + 1)
  have ha0 : ∀ n, 0 ≤ a n := fun n => ratio_nonneg A K n
  have ha1 : ∀ n, a n ≤ 1 := fun n => ratio_le_one hAK n
  have hb0 : ∀ n, 0 ≤ b n := fun n => ratio_nonneg B K n
  have hb1 : ∀ n, b n ≤ 1 := fun n => ratio_le_one hBK n
  have hpoint : ∀ᶠ n in atTop, (1 / 2 : ℝ) * b n ≤ a n + e n := by
    filter_upwards [(prefixCount_tendsto_atTop K hK).eventually (eventually_ge_atTop 1)] with n hn
    have hkpos : 0 < (GenLimit.PatientScope.prefixCount K n : ℝ) := by exact_mod_cast hn
    have hhalf := Nat.le_add_of_sub_le (hcount n)
    have hnat : GenLimit.PatientScope.prefixCount B n ≤
        2 * GenLimit.PatientScope.prefixCount A n + 2 * (C + 1) := by omega
    have hreal : (GenLimit.PatientScope.prefixCount B n : ℝ) ≤
        2 * (GenLimit.PatientScope.prefixCount A n : ℝ) + 2 * (C + 1 : ℝ) := by
      exact_mod_cast hnat
    have hhalfreal : (1 / 2 : ℝ) * (GenLimit.PatientScope.prefixCount B n : ℝ) ≤
        (GenLimit.PatientScope.prefixCount A n : ℝ) + (C + 1 : ℝ) := by
      nlinarith
    dsimp [a, b, e]
    calc
      (1 / 2 : ℝ) *
          ((GenLimit.PatientScope.prefixCount B n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ)) =
          ((1 / 2 : ℝ) * (GenLimit.PatientScope.prefixCount B n : ℝ)) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by ring
      _ ≤ ((GenLimit.PatientScope.prefixCount A n : ℝ) + (C + 1 : ℝ)) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) :=
        (div_le_div_iff_of_pos_right hkpos).2 hhalfreal
      _ = (GenLimit.PatientScope.prefixCount A n : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) +
          ((C + 1 : ℕ) : ℝ) /
            (GenLimit.PatientScope.prefixCount K n : ℝ) := by
        norm_num [add_div]
  have hb_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop b :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hb1)
  have hscaled_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => (1 / 2 : ℝ) * b n) :=
    isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (fun n => mul_nonneg (by norm_num) (hb0 n)))
  have ha_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop a :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall ha1)
  have ha_below : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop a :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall ha0)
  have he_above : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop e := he.isBoundedUnder_le
  have hae_cobelow : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop (a + e) :=
    isCoboundedUnder_ge_add ha_above he_above.isCoboundedUnder_ge
  have hba : liminf (fun n => (1 / 2 : ℝ) * b n) atTop ≤ liminf (a + e) atTop :=
    liminf_le_liminf hpoint hscaled_below hae_cobelow
  have hsum : liminf (a + e) atTop = liminf a atTop :=
    liminf_add_tendsto_zero he ha_below ha_above
  change (1 / 2 : ℝ) * liminf b atTop ≤ liminf a atTop
  rw [← liminf_const_mul_of_nonneg (r := b) (c := (1 / 2 : ℝ)) (by norm_num) hb0 hb_above]
  exact hba.trans_eq hsum

end Stage3Case017Proof

theorem stage3_result : Stage3Case017.MainClaim := by
  unfold Stage3Case017.MainClaim
  intro m _ family hfamily
  refine ⟨Stage3Case017Proof.generator family, ?_⟩
  unfold Stage3Case017.SucceedsFor
  intro input _ _ hcore
  refine ⟨Stage3Case017Proof.outputStream family input, ?_, ?_⟩
  · exact Stage3Case017Proof.follows_generator family input
  · intro j hj
    refine ⟨Stage3Case017Proof.novel_generation family input hcore j hj, ?_⟩
    apply max_le
    · apply Stage3Case017Proof.half_relativeLowerDensity_le
        (A := GenLimit.GeneratorFirst input
          (Stage3Case017Proof.outputStream family input) ∩ family j)
        (B := Stage3Case017.informationCore family input) (K := family j)
        (hfamily j) Set.inter_subset_right
        (fun z hz => hz j hj) (Stage3Case017Proof.stableTime family input)
      exact Stage3Case017Proof.half_prefix_bound family input hcore j hj
    · apply Stage3Case017Proof.relativeLowerDensity_mono_up_to_constant
        (A := GenLimit.GeneratorFirst input
          (Stage3Case017Proof.outputStream family input) ∩ family j)
        (B := Stage3Case017.informationCore family input \ Set.range input)
        (K := family j) (hfamily j) Set.inter_subset_right
        (fun z hz => hz.1 j hj) (Stage3Case017Proof.stableTime family input)
      exact Stage3Case017Proof.missing_prefix_bound family input hcore j hj
