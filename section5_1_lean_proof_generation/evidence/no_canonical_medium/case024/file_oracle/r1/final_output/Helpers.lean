import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024

abbrev Square : Set ℕ := {n | GenLimit.InfiniteContamination.SparseSquare n}

noncomputable local instance : DecidablePred GenLimit.InfiniteContamination.SparseSquare := Classical.decPred _

lemma square_infinite : Square.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => k * k) := by
    intro a b h
    exact Nat.mul_self_inj.mp h
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro _ ⟨k, rfl⟩
    exact GenLimit.InfiniteContamination.sparseSquare_mul_self k)

lemma prefixCount_square (n : ℕ) :
    GenLimit.PatientScope.prefixCount Square n =
      Nat.count GenLimit.InfiniteContamination.SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  classical
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  calc
    (GenLimit.PatientScope.prefixFinset (A ∪ B) n).card =
        (GenLimit.PatientScope.prefixFinset A n ∪
          GenLimit.PatientScope.prefixFinset B n).card := by
            congr 1
            ext x
            simp only [GenLimit.PatientScope.mem_prefixFinset,
              Finset.mem_union, Set.mem_union]
            aesop
    _ ≤ _ := Finset.card_union_le _ _

lemma prefixCount_finite_range_le (output : ℕ → ℕ) (T n : ℕ) :
    GenLimit.PatientScope.prefixCount
      (Set.range (fun i : Fin T => output i)) n ≤ T := by
  classical
  calc
    GenLimit.PatientScope.prefixCount
      (Set.range (fun i : Fin T => output i)) n ≤
        (Finset.univ.image (fun i : Fin T => output i)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [GenLimit.PatientScope.mem_prefixFinset] at hx
          obtain ⟨i, hi⟩ := hx.2
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = T := by simp

lemma tendsto_sparse_add_const_div (T : ℕ) :
    Tendsto (fun n : ℕ => ((n.sqrt : ℝ) + 1 + T) / n) atTop (𝓝 0) := by
  have h1 := GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div
  have h2 : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat T
  simpa only [add_div, zero_add] using h1.add h2

lemma relativeUpperDensity_univ_zero_of_eventually_square
    (A : Set ℕ) (output : ℕ → ℕ) (T : ℕ)
    (hA : A ⊆ Square ∪ Set.range (fun i : Fin T => output i)) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero (g := fun n : ℕ => ((n.sqrt : ℝ) + 1 + T) / n)
  · intro n
    positivity
  · intro n
    rw [prefixCount_univ]
    by_cases hn : n = 0
    · simp [hn]
    · apply (div_le_div_iff_of_pos_right (by exact_mod_cast Nat.pos_of_ne_zero hn)).2
      norm_cast
      calc
        GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n =
            GenLimit.PatientScope.prefixCount A n := by simp
        _ ≤ GenLimit.PatientScope.prefixCount
              (Square ∪ Set.range (fun i : Fin T => output i)) n :=
            prefixCount_mono hA n
        _ ≤ GenLimit.PatientScope.prefixCount Square n +
              GenLimit.PatientScope.prefixCount
                (Set.range (fun i : Fin T => output i)) n :=
            prefixCount_union_le _ _ _
        _ ≤ (n.sqrt + 1) + T := by
            apply Nat.add_le_add
            · rw [prefixCount_square]
              exact GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n
            · exact prefixCount_finite_range_le output T n
  · exact tendsto_sparse_add_const_div T

lemma generatorFirst_subset_eventually_square
    {input output : ℕ → ℕ} {T : ℕ}
    (h : ∀ t, T ≤ t → output t ∈ Square) :
    GenLimit.GeneratorFirst input output ⊆
      Square ∪ Set.range (fun i : Fin T => output i) := by
  rintro x ⟨t, rfl, -⟩
  by_cases ht : T ≤ t
  · exact Or.inl (h t ht)
  · exact Or.inr ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩

private lemma ratio_bounds (A K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        GenLimit.PatientScope.prefixCount K n ∧
      (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        GenLimit.PatientScope.prefixCount K n ≤ 1 := by
  constructor
  · positivity
  · by_cases hz : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hz]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono Set.inter_subset_right n

lemma relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  let u := fun n : ℕ =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  have hlo : ∀ n, 0 ≤ u n := fun n => (ratio_bounds A K n).1
  have hhi : ∀ n, u n ≤ 1 := fun n => (ratio_bounds A K n).2
  apply (Filter.le_limsup_iff
    (Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hlo)).isCoboundedUnder_le
    (Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall hhi))).2
  intro y hy
  exact (Filter.Eventually.of_forall (fun n => lt_of_lt_of_le hy (hlo n))).frequently

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  let u := fun n : ℕ =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  have hlo : ∀ n, 0 ≤ u n := fun n => (ratio_bounds A K n).1
  have hhi : ∀ n, u n ≤ 1 := fun n => (ratio_bounds A K n).2
  apply (Filter.limsup_le_iff
    (Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hlo)).isCoboundedUnder_le
    (Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall hhi))).2
  intro y hy
  exact Filter.Eventually.of_forall (fun n => lt_of_le_of_lt (hhi n) hy)


def freshSquareGenerator : Stage3Case024.OnlineGenerator :=
  fun t xs _ =>
    let m := ∑ i, xs i + t + 1
    m * m

def freshSquareOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream :=
  fun t =>
    let m := (Finset.range (t + 1)).sum input + t + 1
    m * m

lemma freshSquare_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshSquareGenerator input (freshSquareOutput input) := by
  intro t
  simp [freshSquareGenerator, freshSquareOutput, Fin.sum_univ_eq_sum_range]

private lemma input_le_mass (input : ℕ → ℕ) {s t : ℕ} (hst : s ≤ t) :
    input s < (Finset.range (t + 1)).sum input + t + 1 := by
  have hs : s ∈ Finset.range (t + 1) := Finset.mem_range.mpr (lt_of_le_of_lt hst (Nat.lt_succ_self t))
  have hle : input s ≤ (Finset.range (t + 1)).sum input :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs
  omega

private lemma mass_strictMono (input : ℕ → ℕ) :
    StrictMono (fun t => (Finset.range (t + 1)).sum input + t + 1) := by
  intro s t hst
  have hsub : Finset.range (s + 1) ⊆ Finset.range (t + 1) :=
    Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt hst))
  have hsum : (Finset.range (s + 1)).sum input ≤
      (Finset.range (t + 1)).sum input := Finset.sum_le_sum_of_subset hsub
  dsimp only
  omega

lemma freshSquare_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (freshSquareOutput input) Square := by
  refine ⟨0, ?_⟩
  intro t _
  let m := (Finset.range (t + 1)).sum input + t + 1
  have hm : 0 < m := by dsimp [m]; omega
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨m, by simp [freshSquareOutput, m]⟩
  · rw [GenLimit.mem_sample_iff]
    rintro ⟨s, hst, hs⟩
    have hlt : input s < m := input_le_mass input (Nat.le_of_lt_succ hst)
    have hmm : m ≤ m * m := by nlinarith
    rw [hs] at hlt
    simp [freshSquareOutput, m] at hlt
  · intro s hst hEq
    have hmass := mass_strictMono input hst
    simp only [freshSquareOutput] at hEq
    exact (ne_of_lt hmass) (Nat.mul_self_inj.mp hEq)

lemma globallyFeasible_of_square_subset {r : ℕ} (family : Fin r → Set ℕ)
    (hsquare : ∀ j, Square ⊆ family j) :
    Stage3Case024.GloballyFeasible family := by
  refine ⟨freshSquareGenerator, ?_⟩
  intro input _
  refine ⟨freshSquareOutput input, freshSquare_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshSquare_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hsquare j hmem, hfresh, hnovel⟩


noncomputable def commonInput : Stage3Case024.Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation
    Square (Set.univ \ Square) square_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply GenLimit.InfiniteContamination.sparseMergePresentation_injective square_infinite
  exact Set.disjoint_sdiff_right

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput,
    GenLimit.InfiniteContamination.range_sparseMergePresentation square_infinite]
  exact Set.union_diff_cancel (Set.subset_univ Square)

lemma legal_commonInput {K : Set ℕ} (hsquare : Square ⊆ K) :
    Stage3Case024.Legal commonInput K := by
  refine ⟨square_infinite.mono hsquare, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
      square_infinite hsquare

lemma path_density_univ_zero {input output : ℕ → ℕ}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Square) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  obtain ⟨T, hT⟩ := hvalid
  apply relativeUpperDensity_univ_zero_of_eventually_square _ output T
  apply generatorFirst_subset_eventually_square
  intro t ht
  exact (hT t ht).1

end Case024
