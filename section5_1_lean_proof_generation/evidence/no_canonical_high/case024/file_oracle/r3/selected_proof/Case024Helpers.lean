import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation

open Filter MeasureTheory
open scoped Topology

namespace Case024

open GenLimit
open GenLimit.InfiniteContamination
open GenLimit.KleinbergWei

abbrev Squares : Set ℕ := {n | SparseSquare n}

def marker (k : ℕ) : ℕ := sparseBetweenSquares k

lemma marker_not_square (k : ℕ) : marker k ∉ Squares :=
  sparseBetweenSquares_nonsquare k

lemma marker_injective : Function.Injective marker :=
  sparseBetweenSquares_strictMono.injective

lemma squares_infinite : Squares.Infinite := by
  apply Set.infinite_range_of_injective (Nat.pow_left_injective (by omega : 2 ≠ 0)) |>.mono
  rintro _ ⟨k, rfl⟩
  exact ⟨k, by simp [pow_two]⟩

noncomputable def commonInput : Stage3Case024.Stream :=
  sparseMergePresentation Squares Squaresᶜ squares_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply sparseMergePresentation_injective squares_infinite
  rw [Set.disjoint_left]
  intro x hx hxcomp
  exact hxcomp hx

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [commonInput, range_sparseMergePresentation squares_infinite]
  exact Set.union_compl_self Squares

lemma legal_of_squares_subset {K : Set ℕ} (hK : Squares ⊆ K) :
    Stage3Case024.Legal commonInput K := by
  refine ⟨squares_infinite.mono hK, commonInput_injective, ?_, ?_⟩
  · intro x hx
    rw [commonInput_range]
    trivial
  · exact sparseMergePresentation_vanishingNoise_of_core_subset squares_infinite hK

noncomputable def natOrder : OrderedLanguage where
  carrier := Set.univ
  enumeration := id
  enumeration_injective := Function.injective_id
  range_enumeration := Set.range_id

lemma natOrder_prefixCount (A : Set ℕ) (n : ℕ) :
    natOrder.prefixCount A n = GenLimit.PatientScope.prefixCount A n := by
  rfl

lemma relativeUpperDensity_univ (A : Set ℕ) :
    Stage3Case024.relativeUpperDensity A Set.univ = natOrder.upperDensity A := by
  unfold Stage3Case024.relativeUpperDensity OrderedLanguage.upperDensity
  congr 2
  funext n
  rw [Set.inter_univ]
  by_cases hn : n = 0
  · simp [hn, OrderedLanguage.prefixRatio]
  · simp [OrderedLanguage.prefixRatio, hn, natOrder, OrderedLanguage.prefixCount,
      GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma squares_prefixRatio_tendsto_zero :
    Tendsto (natOrder.prefixRatio Squares) atTop (𝓝 0) := by
  apply squeeze_zero'
      (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1) / n)
  · exact Eventually.of_forall (fun n => natOrder.prefixRatio_nonneg Squares n)
  · exact Eventually.of_forall (fun n => by
      by_cases hn : n = 0
      · simp [OrderedLanguage.prefixRatio, hn]
      · simp only [OrderedLanguage.prefixRatio, hn, if_false]
        apply div_le_div_of_nonneg_right
        · rw [natOrder_prefixCount, GenLimit.PatientScope.prefixCount,
            GenLimit.PatientScope.prefixFinset, ← Nat.count_eq_card_filter_range]
          exact_mod_cast count_sparseSquare_le_sqrt_add_one n
        · positivity)
  · exact tendsto_sparseSqrt_add_one_div

lemma squares_upperDensity_zero : natOrder.upperDensity Squares = 0 := by
  exact squares_prefixRatio_tendsto_zero.limsup_eq

lemma upperDensity_zero_of_eventually_squares {A : Set ℕ}
    (hfinite : (A \ Squares).Finite) : natOrder.upperDensity A = 0 := by
  have hsubset : A ⊆ Squares ∪ (A \ Squares) := by
    intro x hx
    by_cases hs : x ∈ Squares
    · exact Or.inl hs
    · exact Or.inr ⟨hx, hs⟩
  apply le_antisymm
  · calc
      natOrder.upperDensity A ≤ natOrder.upperDensity (Squares ∪ (A \ Squares)) :=
        natOrder.upperDensity_mono hsubset
      _ ≤ natOrder.upperDensity Squares + natOrder.upperDensity (A \ Squares) :=
        natOrder.upperDensity_union_le _ _
      _ = 0 := by rw [squares_upperDensity_zero,
        natOrder.upperDensity_eq_zero_of_finite hfinite, zero_add]
  · exact natOrder.upperDensity_nonneg A

lemma relativeUpperDensity_univ_zero_of_eventually_squares {A : Set ℕ}
    (hfinite : (A \ Squares).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  rw [relativeUpperDensity_univ]
  exact upperDensity_zero_of_eventually_squares hfinite

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop (fun n => by positivity)
  · apply Eventually.of_forall
    intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)]
      exact_mod_cast (Finset.card_le_card (by
        intro x hx
        exact GenLimit.PatientScope.mem_prefixFinset.mpr
          ⟨(GenLimit.PatientScope.mem_prefixFinset.mp hx).1,
            (GenLimit.PatientScope.mem_prefixFinset.mp hx).2.2⟩))

lemma generatorFirst_diff_squares_finite {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Squares) :
    (GenLimit.GeneratorFirst input output \ Squares).Finite := by
  obtain ⟨T, hT⟩ := hvalid
  apply (Set.finite_range fun t : Fin T => output t).subset
  intro x hx
  obtain ⟨t, hout, -⟩ := hx.1
  have ht : t < T := by
    by_contra hnot
    have hmem := (hT t (Nat.le_of_not_gt hnot)).1
    rw [hout] at hmem
    exact hx.2 hmem
  exact ⟨⟨t, ht⟩, hout⟩

lemma generatorFirst_univ_density_zero {input output : Stage3Case024.Stream}
    (hvalid : GenLimit.NovelGeneratesInLimit input output Squares) :
    Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input output) Set.univ = 0 :=
  relativeUpperDensity_univ_zero_of_eventually_squares
    (generatorFirst_diff_squares_finite hvalid)

end Case024

namespace Case024

lemma pairObstruction :
    Stage3Case024.PairObstruction Squares Set.univ commonInput := by
  intro Ω _ μ _ gen output _ _ hintSquares hintUniv hvalidSquares _
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hvalidSquares.mono (fun ω hω => generatorFirst_univ_density_zero hω)
  have huniv : Stage3Case024.expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzero]
    simp
  have hsquares :
      Stage3Case024.expectedUpperDensity μ Squares commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) Squares ∂μ) ≤
          ∫ _ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hintSquares (integrable_const 1)
            exact Filter.Eventually.of_forall (fun ω =>
              relativeUpperDensity_le_one
                (GenLimit.GeneratorFirst commonInput (output ω)) Squares)
      _ = 1 := by simp
  constructor
  · rw [huniv, add_zero]
    exact hsquares
  · rw [huniv]
    intro h
    linarith [hsquares]

lemma squares_ssubset_univ : Squares ⊂ (Set.univ : Set ℕ) := by
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have hm : marker 0 ∈ Squares := by rw [h]; trivial
  exact marker_not_square 0 hm

lemma pairWitness :
    ∃ K₀ K₁ : Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      K₀ ⊂ K₁ ∧ Stage3Case024.Legal input K₀ ∧
        Stage3Case024.Legal input K₁ ∧
        Stage3Case024.PairObstruction K₀ K₁ input := by
  refine ⟨Squares, Set.univ, commonInput, squares_ssubset_univ,
    legal_of_squares_subset (fun _ h => h), legal_of_squares_subset (Set.subset_univ _),
    pairObstruction⟩

end Case024

namespace Case024

noncomputable def finMax {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  Finset.univ.sup f

lemma le_finMax {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : f i ≤ finMax f := by
  exact Finset.le_sup (Finset.mem_univ i)

def nextSquare (n : ℕ) : ℕ := (n + 1) * (n + 1)

lemma lt_nextSquare (n : ℕ) : n < nextSquare n := by
  unfold nextSquare
  nlinarith

lemma nextSquare_mem (n : ℕ) : nextSquare n ∈ Squares := by
  exact ⟨n + 1, rfl⟩

noncomputable def feasibleGenerator : Stage3Case024.OnlineGenerator :=
  fun t input previous =>
    if ht : t = 0 then nextSquare (finMax input)
    else nextSquare (max (finMax input) (previous ⟨t - 1, Nat.sub_lt (Nat.zero_lt_of_ne_zero ht) (by omega)⟩))

noncomputable def feasibleOutput (input : Stage3Case024.Stream) : Stage3Case024.Stream
  | 0 => nextSquare (finMax (fun i : Fin 1 => input i))
  | t + 1 => nextSquare (max (finMax (fun i : Fin (t + 2) => input i)) (feasibleOutput input t))

lemma feasibleFollows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows feasibleGenerator input (feasibleOutput input) := by
  intro t
  cases t with
  | zero => simp [feasibleOutput, feasibleGenerator]
  | succ t => simp [feasibleOutput, feasibleGenerator]

lemma input_lt_feasibleOutput (input : Stage3Case024.Stream)
    (t : ℕ) (i : Fin (t + 1)) : input i < feasibleOutput input t := by
  cases t with
  | zero =>
      simp only [feasibleOutput]
      exact lt_of_le_of_lt (le_finMax (fun i : Fin 1 => input i) i)
        (lt_nextSquare _)
  | succ t =>
      simp only [feasibleOutput]
      exact lt_of_le_of_lt
        ((le_finMax (fun i : Fin (t + 2) => input i) i).trans (Nat.le_max_left _ _))
        (lt_nextSquare _)

lemma feasibleOutput_lt_succ (input : Stage3Case024.Stream) (t : ℕ) :
    feasibleOutput input t < feasibleOutput input (t + 1) := by
  simp only [feasibleOutput]
  exact lt_of_le_of_lt (Nat.le_max_right _ _) (lt_nextSquare _)

lemma feasibleOutput_strictMono (input : Stage3Case024.Stream) :
    StrictMono (feasibleOutput input) :=
  strictMono_nat_of_lt_succ (feasibleOutput_lt_succ input)

lemma feasibleOutput_novel (input : Stage3Case024.Stream) :
    GenLimit.NovelGeneratesInLimit input (feasibleOutput input) Squares := by
  refine ⟨0, ?_⟩
  intro t _
  refine ⟨?_, ?_, ?_⟩
  · cases t with
    | zero => exact nextSquare_mem _
    | succ t => exact nextSquare_mem _
  · intro hsample
    rw [GenLimit.mem_sample_iff] at hsample
    obtain ⟨s, hs, heq⟩ := hsample
    have hlt := input_lt_feasibleOutput input t ⟨s, hs⟩
    exact (Nat.ne_of_lt hlt) heq
  · intro s hs heq
    exact (feasibleOutput_strictMono input hs).ne heq

lemma globallyFeasible_of_squares_subset {r : ℕ}
    (family : Fin r → Stage3Case024.Language)
    (hfamily : ∀ j, Squares ⊆ family j) :
    Stage3Case024.GloballyFeasible family := by
  refine ⟨feasibleGenerator, ?_⟩
  intro input _
  refine ⟨feasibleOutput input, feasibleFollows input, ?_⟩
  intro j
  obtain ⟨T, hT⟩ := feasibleOutput_novel input
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨hmem, hfresh, hnovel⟩ := hT t ht
  exact ⟨hfamily j hmem, hfresh, hnovel⟩

end Case024

namespace Case024

def markerSet (j : ℕ) : Set ℕ := marker '' Set.Iio j

def nestedFamily (r : ℕ) (j : Fin r) : Stage3Case024.Language :=
  if (j : ℕ) + 1 = r then Set.univ else Squares ∪ markerSet j

lemma squares_subset_nestedFamily (r : ℕ) (j : Fin r) :
    Squares ⊆ nestedFamily r j := by
  intro x hx
  by_cases hj : (j : ℕ) + 1 = r
  · simp [nestedFamily, hj]
  · simp [nestedFamily, hj, hx]

noncomputable def lastFin (r : ℕ) (hr : 0 < r) : Fin r :=
  ⟨r - 1, Nat.sub_lt hr (by omega)⟩

lemma lastFin_is_last (r : ℕ) (hr : 0 < r) :
    ((lastFin r hr : Fin r) : ℕ) + 1 = r := by
  simp [lastFin]
  omega

lemma nestedFamily_last {r : ℕ} (hr : 0 < r) :
    nestedFamily r (lastFin r hr) = Set.univ := by
  simp [nestedFamily, lastFin_is_last r hr]

lemma marker_mem_markerSet {i j : ℕ} (hij : i < j) : marker i ∈ markerSet j := by
  exact ⟨i, hij, rfl⟩

lemma marker_not_mem_markerSet_self (i : ℕ) : marker i ∉ markerSet i := by
  rintro ⟨k, hk, heq⟩
  exact (Nat.ne_of_lt hk) (marker_injective heq)

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, lt_of_lt_of_le (by omega) hr⟩ = Squares := by
  have hne : 0 + 1 ≠ r := by omega
  simp [nestedFamily, hne, markerSet]

lemma strictlyNested_nestedFamily {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  rw [Set.ssubset_iff_subset_ne]
  have hiNotLast : (i : ℕ) + 1 ≠ r := by omega
  have hiEq : nestedFamily r i = Squares ∪ markerSet i := by
    simp [nestedFamily, hiNotLast]
  by_cases hjLast : (j : ℕ) + 1 = r
  · have hjEq : nestedFamily r j = Set.univ := by
      simp [nestedFamily, hjLast]
    refine ⟨?_, ?_⟩
    · rw [hjEq]
      exact Set.subset_univ _
    · intro heq
      have hm : marker i ∈ nestedFamily r i := by
        rw [heq, hjEq]
        trivial
      rw [hiEq] at hm
      rcases hm with hm | hm
      · exact marker_not_square i hm
      · exact marker_not_mem_markerSet_self i hm
  · have hjEq : nestedFamily r j = Squares ∪ markerSet j := by
      simp [nestedFamily, hjLast]
    have hsubset : nestedFamily r i ⊆ nestedFamily r j := by
      rw [hiEq, hjEq]
      intro x hx
      rcases hx with hx | ⟨k, hk, hkx⟩
      · exact Or.inl hx
      · exact Or.inr ⟨k, lt_trans hk hij, hkx⟩
    refine ⟨hsubset, ?_⟩
    intro heq
    have hmj : marker i ∈ nestedFamily r j := by
      rw [hjEq]
      exact Or.inr (marker_mem_markerSet hij)
    have hmi : marker i ∈ nestedFamily r i := by rw [heq]; exact hmj
    rw [hiEq] at hmi
    rcases hmi with hmi | hmi
    · exact marker_not_square i hmi
    · exact marker_not_mem_markerSet_self i hmi

lemma nestedFamily_legal {r : ℕ} (j : Fin r) :
    Stage3Case024.Legal commonInput (nestedFamily r j) :=
  legal_of_squares_subset (squares_subset_nestedFamily r j)

lemma nestedFamily_globallyFeasible (r : ℕ) :
    Stage3Case024.GloballyFeasible (nestedFamily r) :=
  globallyFeasible_of_squares_subset (nestedFamily r)
    (squares_subset_nestedFamily r)

lemma nestedFamily_obstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, lt_of_lt_of_le (by omega) hr⟩
  let last : Fin r := lastFin r (by omega)
  have hfirst : nestedFamily r first = Squares := nestedFamily_zero hr
  have hlast : nestedFamily r last = Set.univ := nestedFamily_last (by omega)
  have hvalidSquares : Stage3Case024.EventuallyFreshValid μ Squares commonInput output := by
    simpa [first, hfirst] using hvalid first
  have hzero : ∀ᵐ ω ∂μ,
      Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ = 0 :=
    hvalidSquares.mono (fun ω hω => generatorFirst_univ_density_zero hω)
  refine ⟨last, ?_⟩
  unfold Stage3Case024.expectedUpperDensity
  rw [hlast, integral_congr_ae hzero]
  simp

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonInput := by
  refine ⟨strictlyNested_nestedFamily hr, ?_, nestedFamily_globallyFeasible r,
    nestedFamily_obstruction hr⟩
  exact fun j => nestedFamily_legal (r := r) j

lemma manyWitnesses :
    ∀ r : ℕ, 2 ≤ r →
      ∃ family : Fin r → Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
        Stage3Case024.ManyTargetWitness family input := by
  intro r hr
  exact ⟨nestedFamily r, commonInput, manyTargetWitness hr⟩

end Case024
