import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Pairing

open Filter MeasureTheory
open scoped Topology

namespace Case024Helpers

open GenLimit.InfiniteContamination

abbrev Sq : Set ℕ := {n | SparseSquare n}

noncomputable local instance : DecidablePred SparseSquare := Classical.decPred _

lemma sq_infinite : Sq.Infinite := by
  let f : ℕ → ℕ := fun n => n * n
  have hf : Function.Injective f := by
    apply StrictMono.injective
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [f]
    nlinarith
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n, rfl⟩
  exact sparseSquare_mul_self n

lemma sq_disjoint_nonsq : Disjoint Sq {n | SparseNonSquare n} := by
  rw [Set.disjoint_left]
  intro n hn hnn
  exact hnn hn

lemma sq_union_nonsq : Sq ∪ {n | SparseNonSquare n} = Set.univ := by
  ext n
  constructor
  · intro _
    trivial
  · intro _
    by_cases hn : SparseSquare n
    · exact Or.inl hn
    · exact Or.inr hn

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_sq (n : ℕ) :
    GenLimit.PatientScope.prefixCount Sq n = Nat.count SparseSquare n := by
  classical
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Nat.count_eq_card_filter_range]

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simp only [Set.mem_union]
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

lemma prefixCount_Iio_le (C n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.Iio C) n ≤ C := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simp only [Set.mem_Iio]
  calc
    ((Finset.range n).filter (fun x => x < C)).card ≤ (Finset.range C).card := by
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
    _ = C := Finset.card_range C

lemma prefixCount_tail_lower (N n : ℕ) :
    n - N ≤ GenLimit.PatientScope.prefixCount (Set.Ici N) n := by
  classical
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simp only [Set.mem_Ici]
  have heq : (Finset.range n).filter (fun x => N ≤ x) = Finset.Ico N n := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [heq]
  simp

lemma tendsto_sparse_plus_const_div (C : ℕ) :
    Tendsto (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + C) / (n : ℝ))
      atTop (𝓝 0) := by
  have hbase := tendsto_sparseSqrt_add_one_div
  have hconst : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (C : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 (C * 0)))
  simpa [add_div] using hbase.add hconst

lemma density_zero_of_subset_sq_union_Iio
    (A : Set ℕ) (C N : ℕ)
    (hA : A ⊆ Sq ∪ Set.Iio C) :
    Stage3Case024.relativeUpperDensity A (Sq ∪ Set.Ici N) = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop (2 * N + 1)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hhalfNat : n ≤ 2 * (n - N) := by omega
    have hhalf : (n : ℝ) / 2 ≤ (n - N : ℕ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast (by simpa [mul_comm] using hhalfNat)
    have hdenNat : n - N ≤ GenLimit.PatientScope.prefixCount (Sq ∪ Set.Ici N) n :=
      (prefixCount_tail_lower N n).trans (prefixCount_mono (Set.subset_union_right) n)
    have hden : (n : ℝ) / 2 ≤
        (GenLimit.PatientScope.prefixCount (Sq ∪ Set.Ici N) n : ℝ) :=
      hhalf.trans (by exact_mod_cast hdenNat)
    have hnumNat : GenLimit.PatientScope.prefixCount (A ∩ (Sq ∪ Set.Ici N)) n ≤
        Nat.sqrt n + 1 + C := by
      calc
        GenLimit.PatientScope.prefixCount (A ∩ (Sq ∪ Set.Ici N)) n
            ≤ GenLimit.PatientScope.prefixCount A n :=
          prefixCount_mono Set.inter_subset_left n
        _ ≤ GenLimit.PatientScope.prefixCount (Sq ∪ Set.Iio C) n :=
          prefixCount_mono hA n
        _ ≤ GenLimit.PatientScope.prefixCount Sq n +
              GenLimit.PatientScope.prefixCount (Set.Iio C) n :=
          prefixCount_union_le Sq (Set.Iio C) n
        _ ≤ Nat.sqrt n + 1 + C := by
          rw [prefixCount_sq]
          exact Nat.add_le_add
            (count_sparseSquare_le_sqrt_add_one n)
            (prefixCount_Iio_le C n)
    have hnum : (GenLimit.PatientScope.prefixCount (A ∩ (Sq ∪ Set.Ici N)) n : ℝ) ≤
        (Nat.sqrt n : ℝ) + 1 + C := by exact_mod_cast hnumNat
    have hdenpos : 0 < (GenLimit.PatientScope.prefixCount (Sq ∪ Set.Ici N) n : ℝ) :=
      lt_of_lt_of_le (half_pos hnpos) hden
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ (Sq ∪ Set.Ici N)) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (Sq ∪ Set.Ici N) n : ℝ)
          ≤ ((Nat.sqrt n : ℝ) + 1 + C) /
              (GenLimit.PatientScope.prefixCount (Sq ∪ Set.Ici N) n : ℝ) :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ ≤ ((Nat.sqrt n : ℝ) + 1 + C) / ((n : ℝ) / 2) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact half_pos hnpos
        · exact hden
      _ = 2 * (((Nat.sqrt n : ℝ) + 1 + C) / n) := by field_simp
  · simpa using (tendsto_const_nhds.mul (tendsto_sparse_plus_const_div C) :
      Tendsto (fun n : ℕ => (2 : ℝ) * (((Nat.sqrt n : ℝ) + 1 + C) / n))
        atTop (𝓝 (2 * 0)))

lemma generatorFirst_subset_sq_union_early
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Sq) :
    ∃ C : ℕ, GenLimit.GeneratorFirst input output ⊆ Sq ∪ Set.Iio C := by
  obtain ⟨T, hT⟩ := hvalid
  let C : ℕ := (Finset.range T).sup output + 1
  refine ⟨C, ?_⟩
  intro x hx
  obtain ⟨t, rfl, -⟩ := hx
  by_cases ht : T ≤ t
  · exact Set.mem_union_left _ (hT t ht).1
  · apply Set.mem_union_right
    change output t < C
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_of_not_ge ht)))

lemma relative_density_dense_zero
    {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Sq) (N : ℕ) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) (Sq ∪ Set.Ici N) = 0 := by
  obtain ⟨C, hC⟩ := generatorFirst_subset_sq_union_early hvalid
  exact density_zero_of_subset_sq_union_Iio _ C N hC

lemma relative_density_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  let u : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hnonneg : ∀ n, 0 ≤ u n := fun n =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hone : ∀ n, u n ≤ 1 := by
    intro n
    have hcount := prefixCount_mono (A := A ∩ K) (B := K) Set.inter_subset_right n
    by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [u, hz]
    · dsimp [u]
      rw [div_le_one (by positivity)]
      exact_mod_cast hcount
  unfold Stage3Case024.relativeUpperDensity
  change limsup u atTop ≤ 1
  rw [Filter.limsup_le_iff
    (Filter.isCoboundedUnder_le_of_eventually_le atTop
      (Eventually.of_forall hnonneg))
    (Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall hone))]
  intro y hy
  exact Eventually.of_forall fun n => (hone n).trans_lt hy


noncomputable def squareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _ =>
    let base := Nat.pair t ((Finset.univ.sup input) + 1)
    base * base

noncomputable def squareOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t => squareGenerator t (fun i => input i) (fun i => 0)

lemma squareOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows squareGenerator input (squareOutput input) := by
  intro t
  rfl

lemma squareOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (squareOutput input) Sq := by
  refine ⟨0, ?_⟩
  intro t _
  let maximum := Finset.univ.sup (fun i : Fin (t + 1) => input i)
  let base := Nat.pair t (maximum + 1)
  have hbasePos : 0 < base := by
    have := Nat.right_le_pair t (maximum + 1)
    omega
  have hmem : squareOutput input t ∈ Sq := by
    exact ⟨base, by rfl⟩
  have hfresh : squareOutput input t ∉ GenLimit.sample input (t + 1) := by
    rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hst, hs⟩
    let i : Fin (t + 1) := ⟨s, hst⟩
    have himax : input s ≤ maximum := by
      exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin (t + 1) => input j)
        (Finset.mem_univ i)
    have hmaxbase : maximum < base := by
      have := Nat.right_le_pair t (maximum + 1)
      omega
    have hbaseSq : base ≤ base * base := by nlinarith
    have houtgt : input s < squareOutput input t := by
      change input s < base * base
      omega
    omega
  refine ⟨hmem, hfresh, ?_⟩
  intro s hst heq
  let maximumS := Finset.univ.sup (fun i : Fin (s + 1) => input i)
  let baseS := Nat.pair s (maximumS + 1)
  have hbaseEq : baseS = base := by
    change baseS * baseS = base * base at heq
    nlinarith
  have hpair := (Nat.pair_eq_pair.mp hbaseEq).1
  omega

noncomputable def nestedFamily (r : ℕ) (i : Fin r) : Set ℕ :=
  if i.1 = 0 then Sq
  else Sq ∪ Set.Ici (sparseBetweenSquares (r - i.1))

lemma nestedFamily_core (r : ℕ) (i : Fin r) : Sq ⊆ nestedFamily r i := by
  intro x hx
  simp only [nestedFamily]
  split
  · exact hx
  · exact Set.mem_union_left _ hx

lemma nestedFamily_zero (r : ℕ) (h : 0 < r) :
    nestedFamily r ⟨0, h⟩ = Sq := by
  simp [nestedFamily]

lemma nestedFamily_one (r : ℕ) (h : 1 < r) :
    nestedFamily r ⟨1, h⟩ =
      Sq ∪ Set.Ici (sparseBetweenSquares (r - 1)) := by
  simp [nestedFamily]

lemma nestedFamily_strict {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  rw [Set.ssubset_iff_subset_ne]
  have hjpos : j.1 ≠ 0 := by omega
  by_cases hizero : i.1 = 0
  · constructor
    · simpa [nestedFamily, hizero, hjpos] using
        (Set.subset_union_left : Sq ⊆ Sq ∪ Set.Ici (sparseBetweenSquares (r - j.1)))
    · intro heq
      let witness := sparseBetweenSquares (r - j.1)
      have hwj : witness ∈ nestedFamily r j := by
        simp [nestedFamily, hjpos, witness]
      have hwi : witness ∉ nestedFamily r i := by
        intro hw
        have hs : SparseSquare witness := by
          simpa [nestedFamily, hizero] using hw
        exact sparseBetweenSquares_nonsquare _ hs
      rw [heq] at hwi
      exact hwi hwj
  · have hsubNat : r - j.1 < r - i.1 := by omega
    have hthreshold : sparseBetweenSquares (r - j.1) <
        sparseBetweenSquares (r - i.1) :=
      sparseBetweenSquares_strictMono hsubNat
    constructor
    · intro x hx
      simp only [nestedFamily, hizero, hjpos, if_false, Set.mem_union,
        Set.mem_Ici] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (hthreshold.le.trans hx)
    · intro heq
      let witness := sparseBetweenSquares (r - j.1)
      have hwj : witness ∈ nestedFamily r j := by
        simp [nestedFamily, hjpos, witness]
      have hwi : witness ∉ nestedFamily r i := by
        simp only [nestedFamily, hizero, if_false, Set.mem_union, Set.mem_Ici,
          witness]
        push_neg
        exact ⟨sparseBetweenSquares_nonsquare _, hthreshold⟩
      rw [heq] at hwi
      exact hwi hwj

noncomputable def commonInput : Stage3Case024.Stream :=
  squareSparseMerge Sq {n | SparseNonSquare n} sq_infinite sparseNonSquare_infinite

lemma commonInput_legal (K : Set ℕ) (hcore : Sq ⊆ K) :
    Stage3Case024.Legal commonInput K := by
  refine ⟨sq_infinite.mono hcore, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact squareSparseMerge_injective sq_infinite sparseNonSquare_infinite
      sq_disjoint_nonsq
  · unfold GenLimit.InfiniteContamination.NoOmissions
    rw [show Set.range commonInput = Sq ∪ {n | SparseNonSquare n} by
      exact range_squareSparseMerge sq_infinite sparseNonSquare_infinite]
    rw [sq_union_nonsq]
    exact Set.subset_univ K
  · exact squareSparseMerge_vanishingNoise_of_core_subset
      sq_infinite sparseNonSquare_infinite hcore

lemma nestedFamily_feasible {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨squareGenerator, ?_⟩
  intro input _
  refine ⟨squareOutput input, squareOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := squareOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨nestedFamily_core r j hmem, hfresh, hnovel⟩

end Case024Helpers
