import Stage3Model
import Mathlib.Data.Nat.Sqrt
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology

namespace Case024

abbrev Language := Stage3Case024.Language
abbrev Stream := Stage3Case024.Stream

noncomputable def squares : Language := {n | Nat.sqrt n ^ 2 = n}

lemma mem_squares_iff (n : ℕ) : n ∈ squares ↔ ∃ k : ℕ, k ^ 2 = n := by
  simp only [squares, Set.mem_setOf_eq]
  exact (Nat.exists_mul_self' n).symm

lemma squares_infinite : squares.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  refine ⟨(n + 1) ^ 2, ?_, ?_⟩
  · exact (mem_squares_iff _).2 ⟨n + 1, rfl⟩
  · nlinarith

lemma squares_compl_infinite : squaresᶜ.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  refine ⟨(n + 1) ^ 2 + 1, ?_, by nlinarith⟩
  rw [Set.mem_compl_iff, mem_squares_iff]
  intro h
  exact Nat.not_exists_sq' (m := n + 1) (by omega) (by simp [pow_two]; nlinarith) h

noncomputable def sparseEquiv : squares ≃ (squaresᶜ : Set ℕ) := by
  letI : Infinite squares := Set.infinite_coe_iff.mpr squares_infinite
  letI : Infinite (squaresᶜ : Set ℕ) := Set.infinite_coe_iff.mpr squares_compl_infinite
  exact Classical.choice inferInstance

noncomputable def commonStream : Stream := by
  classical
  exact fun t =>
    if h : t ∈ squares then (sparseEquiv ⟨t, h⟩ : (squaresᶜ : Set ℕ)).1
    else (sparseEquiv.symm ⟨t, h⟩ : squares).1

lemma commonStream_in_squares_iff (t : ℕ) : commonStream t ∈ squares ↔ t ∉ squares := by
  classical
  unfold commonStream
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    exact (sparseEquiv ⟨t, h⟩).2
  · simp only [h, not_false_eq_true, iff_true]
    exact (sparseEquiv.symm ⟨t, h⟩).2

lemma commonStream_injective : Function.Injective commonStream := by
  classical
  intro a b hab
  by_cases ha : a ∈ squares <;> by_cases hb : b ∈ squares
  · simp only [commonStream, dif_pos ha, dif_pos hb] at hab
    exact Subtype.ext_iff.mp (sparseEquiv.injective (Subtype.ext hab))
  · simp only [commonStream, dif_pos ha, dif_neg hb] at hab
    exact False.elim ((sparseEquiv ⟨a, ha⟩).2 (hab ▸ (sparseEquiv.symm ⟨b, hb⟩).2))
  · simp only [commonStream, dif_neg ha, dif_pos hb] at hab
    exact False.elim ((sparseEquiv ⟨b, hb⟩).2 (hab ▸ (sparseEquiv.symm ⟨a, ha⟩).2))
  · simp only [commonStream, dif_neg ha, dif_neg hb] at hab
    exact Subtype.ext_iff.mp (sparseEquiv.symm.injective (Subtype.ext hab))

lemma commonStream_surjective : Function.Surjective commonStream := by
  classical
  intro x
  by_cases hx : x ∈ squares
  · let t : (squaresᶜ : Set ℕ) := sparseEquiv ⟨x, hx⟩
    refine ⟨t.1, ?_⟩
    simp only [commonStream, t, dif_neg t.2]
    exact congrArg Subtype.val (sparseEquiv.symm_apply_apply ⟨x, hx⟩)
  · let t : squares := sparseEquiv.symm ⟨x, hx⟩
    refine ⟨t.1, ?_⟩
    simp only [commonStream, t, dif_pos t.2]
    exact congrArg Subtype.val (sparseEquiv.apply_symm_apply ⟨x, hx⟩)

lemma prefixCount_univ (n : ℕ) : GenLimit.PatientScope.prefixCount Set.univ n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤ GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n ≤ Nat.sqrt n + 1 := by
  classical
  have hmap : Set.MapsTo Nat.sqrt
      (↑(GenLimit.PatientScope.prefixFinset squares n) : Set ℕ)
      (↑(Finset.range (Nat.sqrt n + 1)) : Set ℕ) := by
    intro x hx
    have hxn : x < n := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    change Nat.sqrt x ∈ Finset.range (Nat.sqrt n + 1)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_sqrt (Nat.le_of_lt hxn)))
  have hinj : Set.InjOn Nat.sqrt
      (↑(GenLimit.PatientScope.prefixFinset squares n) : Set ℕ) := by
    intro x hx y hy hxy
    have hxs : x ∈ squares := (Finset.mem_filter.mp hx).2
    have hys : y ∈ squares := (Finset.mem_filter.mp hy).2
    rw [show x = Nat.sqrt x ^ 2 from hxs.symm,
      show y = Nat.sqrt y ^ 2 from hys.symm, hxy]
  simpa [GenLimit.PatientScope.prefixCount] using
    Finset.card_le_card_of_injOn Nat.sqrt hmap hinj

lemma tendsto_sqrt_ratio : Tendsto (fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 < N ∧ (2 : ℝ) / N < ε := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    refine ⟨N + 1, Nat.succ_pos _, ?_⟩
    have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hpos]
    have hmul := (div_lt_iff₀ hε).1 hN
    push_cast at hmul ⊢
    nlinarith
  refine ⟨N ^ 2, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (pow_pos hN.1 2) hn
  have hsqrt : N ≤ Nat.sqrt n := Nat.le_sqrt'.2 hn
  have hsqrtpos : (0 : ℝ) < Nat.sqrt n := by exact_mod_cast lt_of_lt_of_le hN.1 hsqrt
  have hsqrt_sq : (Nat.sqrt n : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hsone : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hN.1.trans_le hsqrt
  have hratio : ((Nat.sqrt n + 1 : ℕ) : ℝ) / n ≤ 2 / Nat.sqrt n := by
    push_cast
    rw [div_le_iff₀ hnpos, div_mul_eq_mul_div, le_div_iff₀ hsqrtpos]
    nlinarith
  have hsmall : (2 : ℝ) / Nat.sqrt n ≤ 2 / N := by
    apply div_le_div_of_nonneg_left (by positivity)
    · exact_mod_cast hN.1
    · exact_mod_cast hsqrt
  simp only [sub_zero]
  rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity : (0 : ℝ) ≤ n))]
  exact lt_of_le_of_lt hratio (lt_of_le_of_lt hsmall hN.2)

lemma tendsto_square_prefix_ratio : Tendsto
    (fun n : ℕ => (GenLimit.PatientScope.prefixCount squares n : ℝ) / n)
    atTop (nhds 0) := by
  apply squeeze_zero' (g := fun n : ℕ => ((Nat.sqrt n + 1 : ℕ) : ℝ) / n)
  · filter_upwards [] with n
    positivity
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast prefixCount_squares_le n
    · positivity
  · exact tendsto_sqrt_ratio

lemma commonStream_noise : GenLimit.InfiniteContamination.VanishingNoise commonStream squares := by
  have heq : GenLimit.InfiniteContamination.empiricalNoiseRate commonStream squares =
      fun n => (GenLimit.PatientScope.prefixCount squares n : ℝ) / n := by
    funext n
    classical
    by_cases hn : n = 0
    · subst n
      simp [GenLimit.InfiniteContamination.empiricalNoiseRate,
        GenLimit.InfiniteContamination.noiseCount,
        GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]
    · simp only [GenLimit.InfiniteContamination.empiricalNoiseRate, hn, if_false,
        GenLimit.InfiniteContamination.noiseCount, GenLimit.PatientScope.prefixCount,
        GenLimit.PatientScope.prefixFinset]
      apply congrArg (fun k : ℕ => (k : ℝ) / n)
      apply congrArg Finset.card
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      rw [commonStream_in_squares_iff]
      tauto
  unfold GenLimit.InfiniteContamination.VanishingNoise
  rw [heq]
  exact tendsto_square_prefix_ratio

lemma legal_squares : Stage3Case024.Legal commonStream squares := by
  refine ⟨squares_infinite, commonStream_injective, ?_, commonStream_noise⟩
  intro x hx
  exact commonStream_surjective x

lemma legal_univ : Stage3Case024.Legal commonStream Set.univ := by
  refine ⟨Set.infinite_univ, commonStream_injective, ?_, ?_⟩
  · intro x hx
    exact commonStream_surjective x
  · have : GenLimit.InfiniteContamination.empiricalNoiseRate commonStream Set.univ = 0 := by
      funext n
      simp [GenLimit.InfiniteContamination.empiricalNoiseRate,
        GenLimit.InfiniteContamination.noiseCount]
    unfold GenLimit.InfiniteContamination.VanishingNoise
    rw [this]
    exact tendsto_const_nhds

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n + GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simpa [Finset.filter_or] using
    Finset.card_union_le ((Finset.range n).filter fun x => x ∈ A)
      ((Finset.range n).filter fun x => x ∈ B)

lemma prefixCount_coe_finset_le (s : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (↑s : Set ℕ) n ≤ s.card := by
  classical
  have hprefix :
      (↑(GenLimit.PatientScope.prefixFinset (↑s : Set ℕ) n) : Set ℕ) =
        Set.Iio n ∩ (↑s : Set ℕ) := by
    ext x
    simp [GenLimit.PatientScope.prefixFinset]
  have hsub :
      (↑(GenLimit.PatientScope.prefixFinset (↑s : Set ℕ) n) : Set ℕ) ⊆
        (↑s : Set ℕ) := by
    rw [hprefix]
    exact inter_subset_right
  simpa only [GenLimit.PatientScope.prefixCount, Set.ncard_coe_finset] using
    Set.ncard_le_ncard hsub

lemma tendsto_sparse_bound (C : ℕ) : Tendsto
    (fun n : ℕ => (((Nat.sqrt n + 1 + C : ℕ) : ℝ) / n)) atTop (nhds 0) := by
  have hC : Tendsto (fun n : ℕ => (C : ℝ) / n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  convert tendsto_sqrt_ratio.add hC using 1 <;> simp [add_div]

lemma density_univ_zero_of_eventual_squares {input output : Stream}
    (h : GenLimit.NovelGeneratesInLimit input output squares) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := h
  let early : Finset ℕ := (Finset.range T).image output
  have hrange : Set.range output ⊆ squares ∪ (↑early : Set ℕ) := by
    rintro x ⟨t, rfl⟩
    by_cases ht : T ≤ t
    · exact Or.inl (hT t ht).1
    · exact Or.inr (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (Nat.lt_of_not_ge ht), rfl⟩)
  have hfirst : GenLimit.GeneratorFirst input output ⊆ Set.range output := by
    rintro x ⟨t, htx, -⟩
    exact ⟨t, htx⟩
  have hbound (n : ℕ) :
      GenLimit.PatientScope.prefixCount (GenLimit.GeneratorFirst input output) n ≤
        Nat.sqrt n + 1 + early.card := by
    calc
      _ ≤ GenLimit.PatientScope.prefixCount (squares ∪ (↑early : Set ℕ)) n :=
        prefixCount_mono (hfirst.trans hrange) n
      _ ≤ GenLimit.PatientScope.prefixCount squares n +
          GenLimit.PatientScope.prefixCount (↑early : Set ℕ) n := prefixCount_union_le _ _ _
      _ ≤ (Nat.sqrt n + 1) + early.card := Nat.add_le_add (prefixCount_squares_le n)
        (prefixCount_coe_finset_le early n)
  have htend : Tendsto
      (fun n : ℕ => (GenLimit.PatientScope.prefixCount
        (GenLimit.GeneratorFirst input output) n : ℝ) / n) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ => (((Nat.sqrt n + 1 + early.card : ℕ) : ℝ) / n))
    · filter_upwards [] with n
      positivity
    · filter_upwards [] with n
      exact div_le_div_of_nonneg_right (by exact_mod_cast hbound n) (by positivity)
    · exact tendsto_sparse_bound early.card
  unfold Stage3Case024.relativeUpperDensity
  simp only [inter_univ, prefixCount_univ]
  exact htend.limsup_eq

lemma relativeUpperDensity_le_one (A K : Language) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop (x := 0) (fun n => ?_)) ?_
  · positivity
  filter_upwards [] with n
  by_cases hn : GenLimit.PatientScope.prefixCount K n = 0
  · simp [hn]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono (inter_subset_right : A ∩ K ⊆ K) n

lemma pair_obstruction : Stage3Case024.PairObstruction squares Set.univ commonStream := by
  intro Ω _ μ _ gen output hfollow hmeas hint0 hint1 hev0 hev1
  have hzero_ae : (fun ω => Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ) =ᵐ[μ] 0 :=
    hev0.mono fun ω hω => density_univ_zero_of_eventual_squares hω
  have hE1 : Stage3Case024.expectedUpperDensity μ Set.univ commonStream output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzero_ae]
    exact integral_zero Ω ℝ
  have hE0 : Stage3Case024.expectedUpperDensity μ squares commonStream output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      _ ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := integral_mono hint0 (integrable_const 1)
        (fun ω => relativeUpperDensity_le_one _ _)
      _ = 1 := by simp
  constructor
  · rw [hE1, add_zero]
    exact hE0
  · rw [hE1]
    intro h
    linarith [h.2]


lemma noiseCount_mono_of_subset {K : Language} (hsub : squares ⊆ K) (n : ℕ) :
    GenLimit.InfiniteContamination.noiseCount commonStream K n ≤
      GenLimit.InfiniteContamination.noiseCount commonStream squares n := by
  classical
  unfold GenLimit.InfiniteContamination.noiseCount
  apply Finset.card_le_card
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨ht.1, fun hs => ht.2 (hsub hs)⟩

lemma legal_of_squares_subset {K : Language} (hsub : squares ⊆ K) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨squares_infinite.mono hsub, commonStream_injective, ?_, ?_⟩
  · intro x hx
    exact commonStream_surjective x
  · unfold GenLimit.InfiniteContamination.VanishingNoise
    apply squeeze_zero' (g := GenLimit.InfiniteContamination.empiricalNoiseRate commonStream squares)
    · filter_upwards [] with n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split_ifs <;> positivity
    · filter_upwards [] with n
      unfold GenLimit.InfiniteContamination.empiricalNoiseRate
      split_ifs with hn
      · simp
      · exact div_le_div_of_nonneg_right (by exact_mod_cast noiseCount_mono_of_subset hsub n)
          (by positivity)
    · exact commonStream_noise

noncomputable def nonsquareEmbedding : ℕ ↪ (squaresᶜ : Set ℕ) :=
  squares_compl_infinite.natEmbedding

noncomputable def extras (j : ℕ) : Finset ℕ :=
  (Finset.range j).image (fun k => (nonsquareEmbedding k).1)

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Language :=
  if j.1 + 1 = r then Set.univ else squares ∪ (↑(extras j.1) : Set ℕ)

lemma squares_subset_nestedFamily {r : ℕ} (j : Fin r) : squares ⊆ nestedFamily r j := by
  classical
  unfold nestedFamily
  split_ifs
  · exact subset_univ _
  · exact subset_union_left

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, by omega⟩ = squares := by
  classical
  simp [nestedFamily, extras, show 1 ≠ r by omega]

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  classical
  simp [nestedFamily, Nat.sub_add_cancel (by omega : 1 ≤ r)]

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  classical
  intro i j hij
  have hiNot : i.1 + 1 ≠ r := by omega
  by_cases hjLast : j.1 + 1 = r
  · rw [nestedFamily, if_neg hiNot, nestedFamily, if_pos hjLast]
    refine ssubset_univ_iff.mpr ?_
    intro hEq
    have hx : (nonsquareEmbedding i.1).1 ∈ squares ∪ (↑(extras i.1) : Set ℕ) := by
      rw [hEq]
      trivial
    rcases hx with hs | he
    · exact (nonsquareEmbedding i.1).2 hs
    · simp only [extras, Finset.mem_coe, Finset.mem_image] at he
      obtain ⟨k, hk, hki⟩ := he
      have hki' : k = i.1 := nonsquareEmbedding.injective (Subtype.ext hki)
      subst k
      exact (Nat.lt_irrefl i.1) (Finset.mem_range.mp hk)
  · rw [nestedFamily, if_neg hiNot, nestedFamily, if_neg hjLast]
    constructor
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by
          simp only [extras, Finset.mem_coe, Finset.mem_image] at hx ⊢
          obtain ⟨k, hk, rfl⟩ := hx
          exact ⟨k, Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk) hij), rfl⟩)
    · intro hrev
      have hxj : (nonsquareEmbedding i.1).1 ∈ squares ∪ (↑(extras j.1) : Set ℕ) :=
        Or.inr (by
          simp only [extras, Finset.mem_coe, Finset.mem_image]
          exact ⟨i.1, Finset.mem_range.mpr hij, rfl⟩)
      have hxi := hrev hxj
      rcases hxi with hs | he
      · exact (nonsquareEmbedding i.1).2 hs
      · simp only [extras, Finset.mem_coe, Finset.mem_image] at he
        obtain ⟨k, hk, hki⟩ := he
        have hki' : k = i.1 := nonsquareEmbedding.injective (Subtype.ext hki)
        subst k
        exact (Nat.lt_irrefl i.1) (Finset.mem_range.mp hk)

def growingBase (input : Stream) (t : ℕ) : ℕ :=
  t + 1 + ∑ i : Fin (t + 1), input i

def squareOutput (input : Stream) (t : ℕ) : ℕ :=
  (growingBase input t) ^ 2

def squareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ => (t + 1 + ∑ i, input i) ^ 2

lemma squareOutput_follows (input : Stream) :
    Stage3Case024.Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

lemma prefixSum_mono (input : Stream) {s t : ℕ} (hst : s < t) :
    (∑ i : Fin (s + 1), input i) ≤ ∑ i : Fin (t + 1), input i := by
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by omega)
  · intro i hi hnot
    omega

lemma input_le_prefixSum (input : Stream) (t : ℕ) (i : Fin (t + 1)) :
    input i ≤ ∑ j : Fin (t + 1), input j := by
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin (t + 1) => input j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma squareOutput_fresh (input : Stream) (t : ℕ) :
    squareOutput input t ∉ GenLimit.sample input (t + 1) := by
  intro hmem
  unfold GenLimit.sample at hmem
  obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hmem
  have hterm := input_le_prefixSum input t ⟨s, Finset.mem_range.mp hs⟩
  change input s ≤ ∑ j : Fin (t + 1), input j at hterm
  have hslt : input s < growingBase input t := by
    unfold growingBase
    omega
  have hbasepos : 1 ≤ growingBase input t := by
    unfold growingBase
    omega
  have hbasele : growingBase input t ≤ squareOutput input t := by
    unfold squareOutput
    nlinarith
  have : input s < squareOutput input t := lt_of_lt_of_le hslt hbasele
  omega

lemma squareOutput_ne_of_lt (input : Stream) {s t : ℕ} (hst : s < t) :
    squareOutput input s ≠ squareOutput input t := by
  have hsum := prefixSum_mono input hst
  have hbase : growingBase input s < growingBase input t := by
    unfold growingBase
    omega
  unfold squareOutput
  nlinarith [show 0 ≤ growingBase input s from Nat.zero_le _]

lemma squareOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) squares := by
  refine ⟨0, fun t _ => ?_⟩
  refine ⟨(mem_squares_iff _).2 ⟨growingBase input t, rfl⟩,
    squareOutput_fresh input t, ?_⟩
  intro s hst
  exact squareOutput_ne_of_lt input hst

lemma nestedFamily_globallyFeasible {r : ℕ} :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨squareGenerator, fun input _ => ?_⟩
  refine ⟨squareOutput input, squareOutput_follows input, fun j => ?_⟩
  obtain ⟨T, hT⟩ := squareOutput_novel input
  refine ⟨T, fun t ht => ?_⟩
  have hnow := hT t ht
  exact ⟨squares_subset_nestedFamily j hnow.1, hnow.2.1, hnow.2.2⟩

lemma nestedFamily_obstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonStream := by
  intro Ω _ μ _ gen output hfollow hmeas hint hev
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hevSquares : ∀ᵐ ω ∂μ,
      GenLimit.NovelGeneratesInLimit commonStream (output ω) squares := by
    simpa [first, nestedFamily_zero hr] using hev first
  have hzero_ae : (fun ω => Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ) =ᵐ[μ] 0 :=
    hevSquares.mono fun ω hω => density_univ_zero_of_eventual_squares hω
  refine ⟨last, ?_⟩
  rw [show nestedFamily r last = Set.univ by simpa [last] using nestedFamily_last hr]
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae hzero_ae]
  exact integral_zero Ω ℝ

end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024.squares, Set.univ, Case024.commonStream, ?_,
      Case024.legal_squares, Case024.legal_univ, Case024.pair_obstruction⟩
    refine ssubset_univ_iff.mpr ?_
    intro hEq
    exact (Case024.nonsquareEmbedding 0).2 (by rw [hEq]; trivial)
  · intro r hr
    refine ⟨Case024.nestedFamily r, Case024.commonStream, ?_⟩
    exact ⟨Case024.nestedFamily_strict hr,
      fun j => Case024.legal_of_squares_subset (Case024.squares_subset_nestedFamily j),
      Case024.nestedFamily_globallyFeasible,
      Case024.nestedFamily_obstruction hr⟩
