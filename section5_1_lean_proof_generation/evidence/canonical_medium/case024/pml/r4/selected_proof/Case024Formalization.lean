import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

abbrev squares : Set ℕ := {n | GenLimit.InfiniteContamination.SparseSquare n}
abbrev nonsquares : Set ℕ := squaresᶜ

lemma sparseSquare_infinite : squares.Infinite := by
  exact Set.infinite_range_of_injective (f := fun n : ℕ => n * n) (by
    intro a b h
    nlinarith) |>.mono (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, rfl⟩)

noncomputable def commonStream : Stage3Case024.Stream :=
  GenLimit.InfiniteContamination.sparseMergePresentation squares nonsquares
    sparseSquare_infinite

lemma squares_disjoint_nonsquares : Disjoint squares nonsquares := by
  rw [Set.disjoint_left]
  intro x hx hs
  exact hs hx

lemma commonStream_injective : Function.Injective commonStream := by
  exact GenLimit.InfiniteContamination.sparseMergePresentation_injective
    sparseSquare_infinite squares_disjoint_nonsquares

lemma commonStream_range : Set.range commonStream = Set.univ := by
  rw [commonStream,
    GenLimit.InfiniteContamination.range_sparseMergePresentation sparseSquare_infinite]
  exact Set.union_compl_self squares

lemma commonStream_vanishing {K : Set ℕ} (h : squares ⊆ K) :
    GenLimit.InfiniteContamination.VanishingNoise commonStream K := by
  exact GenLimit.InfiniteContamination.sparseMergePresentation_vanishingNoise_of_core_subset
    sparseSquare_infinite h

lemma commonStream_legal {K : Set ℕ} (hinf : K.Infinite) (h : squares ⊆ K) :
    Stage3Case024.Legal commonStream K := by
  refine ⟨hinf, commonStream_injective, ?_, commonStream_vanishing h⟩
  rw [GenLimit.InfiniteContamination.NoOmissions, commonStream_range]
  exact Set.subset_univ K

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount Set.univ n = n := by
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  simp

lemma prefixCount_inter_le_right (A K : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∩ K) n ≤
      GenLimit.PatientScope.prefixCount K n :=
  prefixCount_mono Set.inter_subset_right n

lemma relativeUpperDensity_nonneg (A K : Set ℕ) :
    0 ≤ Stage3Case024.relativeUpperDensity A K := by
  unfold Stage3Case024.relativeUpperDensity
  apply le_limsup_of_frequently_le
  · exact Frequently.of_forall (fun n => div_nonneg (by positivity) (by positivity))
  · exact isBoundedUnder_of ⟨1, fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by positivity)]
        exact_mod_cast prefixCount_inter_le_right A K n⟩

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop
      (fun n => div_nonneg (by positivity) (by positivity))
  · exact Eventually.of_forall (fun n => by
      by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
      · simp [hzero]
      · rw [div_le_one (by positivity)]
        exact_mod_cast prefixCount_inter_le_right A K n)

lemma prefixCount_squares_le (n : ℕ) :
    GenLimit.PatientScope.prefixCount squares n ≤ Nat.sqrt n + 1 := by
  simpa [GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixFinset, squares, Nat.count_eq_card_filter_range]
    using GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ B) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount GenLimit.PatientScope.prefixFinset
  classical
  simpa only [Set.mem_union, Finset.filter_or] using Finset.card_union_le
    ((Finset.range n).filter fun x => x ∈ A)
    ((Finset.range n).filter fun x => x ∈ B)

lemma prefixCount_le_ncard (F : Set ℕ) (hF : F.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount F n ≤ F.ncard := by
  rw [Set.ncard_eq_toFinset_card F hF]
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx
  simpa using hx.2

lemma tendsto_sparse_bound (c : ℕ) :
    Tendsto (fun n : ℕ => (((Nat.sqrt n : ℝ) + 1 + c) / n))
      atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ => (c : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  convert GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.add hc using 1 <;>
    simp [add_div]

lemma relativeUpperDensity_univ_eq_zero_of_finite_outside
    (A : Set ℕ) (hfinite : (A \ squares).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  let F := A \ squares
  have hsub : A ⊆ squares ∪ F := by
    intro x hx
    by_cases hs : x ∈ squares
    · exact Or.inl hs
    · exact Or.inr ⟨hx, hs⟩
  have htend : Tendsto
      (fun n : ℕ =>
        (GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n : ℝ) /
          GenLimit.PatientScope.prefixCount Set.univ n)
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun n : ℕ => (((Nat.sqrt n : ℝ) + 1 + F.ncard) / n))
    · exact Eventually.of_forall fun n => div_nonneg (by positivity) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [prefixCount_univ]
      have hcount : GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n ≤
          Nat.sqrt n + 1 + F.ncard := by
        calc
          GenLimit.PatientScope.prefixCount (A ∩ Set.univ) n =
              GenLimit.PatientScope.prefixCount A n := by simp
          _ ≤ GenLimit.PatientScope.prefixCount (squares ∪ F) n :=
            prefixCount_mono hsub n
          _ ≤ GenLimit.PatientScope.prefixCount squares n +
                GenLimit.PatientScope.prefixCount F n := prefixCount_union_le _ _ _
          _ ≤ (Nat.sqrt n + 1) + F.ncard :=
            Nat.add_le_add (prefixCount_squares_le n)
              (prefixCount_le_ncard F hfinite n)
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
    · exact tendsto_sparse_bound F.ncard
  exact htend.limsup_eq

lemma generatorFirst_subset_range (input output : ℕ → ℕ) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, ht, -⟩
  exact ⟨t, ht⟩

lemma finite_outside_of_eventual_mem
    (output : ℕ → ℕ) (h : ∃ T, ∀ t, T ≤ t → output t ∈ squares) :
    (Set.range output \ squares).Finite := by
  obtain ⟨T, hT⟩ := h
  apply (Set.finite_range (fun t : Fin T => output t)).subset
  rintro x ⟨⟨t, rfl⟩, htSquare⟩
  have ht : t < T := by
    by_contra hnot
    exact htSquare (hT t (Nat.le_of_not_gt hnot))
  exact ⟨⟨t, ht⟩, rfl⟩

lemma generatorFirst_density_zero
    (input output : ℕ → ℕ)
    (hvalid : GenLimit.NovelGeneratesInLimit input output squares) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 := by
  apply relativeUpperDensity_univ_eq_zero_of_finite_outside
  apply (finite_outside_of_eventual_mem output ?_).subset
  · intro x hx
    exact ⟨generatorFirst_subset_range input output hx.1, hx.2⟩
  · obtain ⟨T, hT⟩ := hvalid
    exact ⟨T, fun t ht => (hT t ht).1⟩

def finiteForbidden {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : Set ℕ :=
  Set.range input ∪ Set.range output

lemma finiteForbidden_finite {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    (finiteForbidden input output).Finite :=
  (Set.finite_range input).union (Set.finite_range output)

lemma availableSquares_infinite {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    (squares \ finiteForbidden input output).Infinite :=
  sparseSquare_infinite.diff (finiteForbidden_finite input output)

noncomputable def freshSquare {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) : ℕ :=
  Nat.nth (fun x => x ∈ squares \ finiteForbidden input output) 0

lemma freshSquare_spec {t : ℕ}
    (input : Fin (t + 1) → ℕ) (output : Fin t → ℕ) :
    freshSquare input output ∈ squares \ finiteForbidden input output :=
  Nat.nth_mem_of_infinite (availableSquares_infinite input output) 0

noncomputable def freshGenerator : Stage3Case024.OnlineGenerator :=
  fun _ input output => freshSquare input output

noncomputable def freshOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream
  | t => freshSquare (t := t)
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => freshOutput input i)

lemma freshOutput_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshGenerator input (freshOutput input) := by
  intro t
  rw [freshOutput]
  rfl

lemma freshOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (freshOutput input) squares := by
  refine ⟨0, ?_⟩
  intro t _
  have hout : freshOutput input t = freshSquare
      (fun i : Fin (t + 1) => input i)
      (fun i : Fin t => freshOutput input i) := by
    rw [freshOutput]
  rw [hout]
  have hs := freshSquare_spec (fun i : Fin (t + 1) => input i)
    (fun i : Fin t => freshOutput input i)
  refine ⟨hs.1, ?_, ?_⟩
  · intro hsample
    obtain ⟨i, hi, heq⟩ := GenLimit.mem_sample_iff.mp hsample
    exact hs.2 (Or.inl ⟨⟨i, hi⟩, heq⟩)
  · intro q hq heq
    exact hs.2 (Or.inr ⟨⟨q, hq⟩, heq⟩)

lemma globallyFeasible_of_squares_subset {r : ℕ}
    (family : Fin r → Set ℕ) (hsub : ∀ j, squares ⊆ family j) :
    Stage3Case024.GloballyFeasible family := by
  refine ⟨freshGenerator, ?_⟩
  intro input _
  refine ⟨freshOutput input, freshOutput_follows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := freshOutput_novel input
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hsub j hmem, hfresh, hnovel⟩

def extras (i : ℕ) : Set ℕ :=
  {x | ∃ k, k < i ∧ x = GenLimit.InfiniteContamination.sparseBetweenSquares k}

lemma extras_mono {i j : ℕ} (hij : i ≤ j) : extras i ⊆ extras j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

lemma sparseBetweenSquares_not_mem_extras (i : ℕ) :
    GenLimit.InfiniteContamination.sparseBetweenSquares i ∉ extras i := by
  rintro ⟨k, hk, heq⟩
  have := GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective heq
  omega

noncomputable def nestedFamily (r : ℕ) (i : Fin r) : Set ℕ :=
  if (i : ℕ) + 1 = r then Set.univ else squares ∪ extras i

lemma squares_subset_nestedFamily (r : ℕ) (i : Fin r) :
    squares ⊆ nestedFamily r i := by
  intro x hx
  simp only [nestedFamily]
  split
  · exact Set.mem_univ x
  · exact Or.inl hx

lemma nestedFamily_infinite (r : ℕ) (i : Fin r) :
    (nestedFamily r i).Infinite :=
  sparseSquare_infinite.mono (squares_subset_nestedFamily r i)

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, lt_of_lt_of_le (by omega) hr⟩ = squares := by
  ext x
  simp [nestedFamily, extras, show (1 : ℕ) ≠ r by omega]

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [nestedFamily, show r - 1 + 1 = r by omega]

lemma strictlyNested_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hiNotLast : (i : ℕ) + 1 ≠ r := by omega
  by_cases hjLast : (j : ℕ) + 1 = r
  · rw [nestedFamily, if_neg hiNotLast, nestedFamily, if_pos hjLast]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hAll
    let z := GenLimit.InfiniteContamination.sparseBetweenSquares (i : ℕ)
    have hz : z ∈ squares ∪ extras (i : ℕ) := hAll (Set.mem_univ z)
    rcases hz with hz | hz
    · exact GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare _ hz
    · exact sparseBetweenSquares_not_mem_extras _ hz
  · rw [nestedFamily, if_neg hiNotLast, nestedFamily, if_neg hjLast]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (extras_mono (Nat.le_of_lt hij) hx)
    · intro hEq
      have hz : GenLimit.InfiniteContamination.sparseBetweenSquares (i : ℕ) ∈
          squares ∪ extras (i : ℕ) :=
        hEq (Or.inr ⟨i, hij, rfl⟩)
      rcases hz with hz | hz
      · exact GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare _ hz
      · exact sparseBetweenSquares_not_mem_extras _ hz

lemma nestedFamily_legal (r : ℕ) (i : Fin r) :
    Stage3Case024.Legal commonStream (nestedFamily r i) :=
  commonStream_legal (nestedFamily_infinite r i) (squares_subset_nestedFamily r i)

lemma manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, lt_of_lt_of_le (by omega) hr⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hfirst := hvalid first
  have hfirstSquares : Stage3Case024.EventuallyFreshValid μ squares commonStream output := by
    simpa [first, nestedFamily_zero hr] using hfirst
  have hzero :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hfirstSquares] with ω hω
    exact generatorFirst_density_zero commonStream (output ω) hω
  rw [Stage3Case024.expectedUpperDensity]
  simpa [last, nestedFamily_last hr] using integral_eq_zero_of_ae hzero

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonStream := by
  refine ⟨strictlyNested_nestedFamily hr, ?_,
    globallyFeasible_of_squares_subset (nestedFamily r) (squares_subset_nestedFamily r),
    manyTargetObstruction hr⟩
  intro j
  exact nestedFamily_legal r j

lemma squares_ssubset_univ : squares ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have hx : GenLimit.InfiniteContamination.sparseBetweenSquares 0 ∈ squares :=
    h (Set.mem_univ _)
  exact GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare 0 hx

lemma pairObstruction :
    Stage3Case024.PairObstruction squares Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hintSquares hintUniv hvalidSquares _
  have hzero :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hvalidSquares] with ω hω
    exact generatorFirst_density_zero commonStream (output ω) hω
  have hexpectUniv :
      Stage3Case024.expectedUpperDensity μ Set.univ commonStream output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    exact integral_eq_zero_of_ae hzero
  have hexpectSquares :
      Stage3Case024.expectedUpperDensity μ squares commonStream output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonStream (output ω)) squares ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hintSquares (integrable_const 1)
            exact Eventually.of_forall fun ω => relativeUpperDensity_le_one _ _
      _ = 1 := by simp
  constructor
  · simpa [hexpectUniv] using hexpectSquares
  · rw [hexpectUniv]
    intro h
    linarith [hexpectSquares]

end Case024

open Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨squares, Set.univ, commonStream, squares_ssubset_univ, ?_, ?_, pairObstruction⟩
    · exact commonStream_legal sparseSquare_infinite (fun _ h => h)
    · exact commonStream_legal Set.infinite_univ (Set.subset_univ _)
  · intro r hr
    exact ⟨nestedFamily r, commonStream, manyTargetWitness hr⟩
