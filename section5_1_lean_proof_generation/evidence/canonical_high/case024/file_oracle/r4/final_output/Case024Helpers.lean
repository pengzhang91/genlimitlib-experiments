import Stage3Model
import GenLimit.Paper17_InfiniteContamination.SharedVanishingPresentation
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

namespace Case024

namespace IC
abbrev SparseSquare := GenLimit.InfiniteContamination.SparseSquare
abbrev SparseNonSquare := GenLimit.InfiniteContamination.SparseNonSquare
abbrev sparseBetweenSquares := GenLimit.InfiniteContamination.sparseBetweenSquares
end IC

abbrev sparseCore : Set ℕ := {n | IC.SparseSquare n}

noncomputable local instance : DecidablePred IC.SparseSquare := Classical.decPred _

lemma squareMap_injective : Function.Injective (fun n : ℕ => n * n) := by
  intro a b hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact False.elim ((Nat.mul_self_lt_mul_self hlt).ne hab)
  · exact heq
  · exact False.elim ((Nat.mul_self_lt_mul_self hgt).ne hab.symm)

lemma sparseCore_infinite : sparseCore.Infinite := by
  apply (Set.infinite_range_of_injective squareMap_injective).mono
  rintro _ ⟨k, rfl⟩
  exact ⟨k, rfl⟩

lemma sparseCore_compl_infinite : sparseCoreᶜ.Infinite := by
  simpa [sparseCore, IC.SparseNonSquare] using
    GenLimit.InfiniteContamination.sparseNonSquare_infinite

noncomputable abbrev commonInput : Stage3Case024.Stream :=
  GenLimit.InfiniteContamination.squareSparseMerge
    sparseCore sparseCoreᶜ sparseCore_infinite sparseCore_compl_infinite

lemma commonInput_injective : Function.Injective commonInput := by
  apply GenLimit.InfiniteContamination.squareSparseMerge_injective
  rw [Set.disjoint_compl_right_iff_subset]

lemma commonInput_range : Set.range commonInput = Set.univ := by
  rw [GenLimit.InfiniteContamination.range_squareSparseMerge
    sparseCore_infinite sparseCore_compl_infinite]
  exact Set.union_compl_self sparseCore

lemma commonInput_legal_of_core_subset {K : Set ℕ}
    (hKinf : K.Infinite) (hcore : sparseCore ⊆ K) :
    Stage3Case024.Legal commonInput K := by
  refine ⟨hKinf, commonInput_injective, ?_, ?_⟩
  · rw [GenLimit.InfiniteContamination.NoOmissions, commonInput_range]
    exact Set.subset_univ K
  · exact
      GenLimit.InfiniteContamination.squareSparseMerge_vanishingNoise_of_core_subset
        sparseCore_infinite sparseCore_compl_infinite hcore

lemma prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount B n := by
  unfold GenLimit.PatientScope.prefixCount
  apply Finset.card_le_card
  intro x hx
  rw [GenLimit.PatientScope.mem_prefixFinset] at hx ⊢
  exact ⟨hx.1, hAB hx.2⟩

lemma prefixCount_univ (n : ℕ) :
    GenLimit.PatientScope.prefixCount (Set.univ : Set ℕ) n = n := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset]

lemma prefixCount_sparseCore (n : ℕ) :
    GenLimit.PatientScope.prefixCount sparseCore n = Nat.count IC.SparseSquare n := by
  classical
  rw [Nat.count_eq_card_filter_range]
  rfl

lemma relativeUpperDensity_le_one (A K : Set ℕ) :
    Stage3Case024.relativeUpperDensity A K ≤ 1 := by
  unfold Stage3Case024.relativeUpperDensity
  let f : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    positivity
  have hf_le : ∀ n, f n ≤ 1 := by
    intro n
    dsimp [f]
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · rw [div_le_one]
      · exact_mod_cast prefixCount_mono Set.inter_subset_right n
      · exact_mod_cast Nat.pos_of_ne_zero hzero
  apply (Filter.limsup_le_iff
    (h₁ := Filter.isCoboundedUnder_le_of_le atTop hf_nonneg)
    (h₂ := Filter.isBoundedUnder_of ⟨1, hf_le⟩)).2
  intro y hy
  apply Eventually.of_forall
  intro n
  exact lt_of_le_of_lt (hf_le n) hy

lemma prefixCount_le_sparse_add_finite {A : Set ℕ}
    (hfinite : (A \ sparseCore).Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      Nat.count IC.SparseSquare n + hfinite.toFinset.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  have hsub : GenLimit.PatientScope.prefixFinset A n ⊆
      GenLimit.PatientScope.prefixFinset sparseCore n ∪ hfinite.toFinset := by
    intro x hx
    rw [GenLimit.PatientScope.mem_prefixFinset] at hx
    by_cases hxc : x ∈ sparseCore
    · exact Finset.mem_union_left _
        (GenLimit.PatientScope.mem_prefixFinset.mpr ⟨hx.1, hxc⟩)
    · exact Finset.mem_union_right _
        ((Set.Finite.mem_toFinset hfinite).2 ⟨hx.2, hxc⟩)
  calc
    (GenLimit.PatientScope.prefixFinset A n).card
        ≤ (GenLimit.PatientScope.prefixFinset sparseCore n ∪
            hfinite.toFinset).card := Finset.card_le_card hsub
    _ ≤ (GenLimit.PatientScope.prefixFinset sparseCore n).card +
          hfinite.toFinset.card := Finset.card_union_le _ _
    _ = Nat.count IC.SparseSquare n + hfinite.toFinset.card := by
      rw [← prefixCount_sparseCore]
      rfl

lemma relativeUpperDensity_univ_eq_zero_of_finite_diff {A : Set ℕ}
    (hfinite : (A \ sparseCore).Finite) :
    Stage3Case024.relativeUpperDensity A Set.univ = 0 := by
  unfold Stage3Case024.relativeUpperDensity
  simp only [Set.inter_univ, prefixCount_univ]
  apply Filter.Tendsto.limsup_eq
  let C : ℕ := hfinite.toFinset.card
  have hC : Tendsto (fun n : ℕ => (C : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper : Tendsto
      (fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + C) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa [add_div] using
      GenLimit.InfiniteContamination.tendsto_sparseSqrt_add_one_div.add hC
  apply squeeze_zero
    (g := fun n : ℕ => ((Nat.sqrt n : ℝ) + 1 + C) / (n : ℝ))
  · intro n
    positivity
  · intro n
    apply div_le_div_of_nonneg_right
    · exact_mod_cast
        (prefixCount_le_sparse_add_finite hfinite n |>.trans
          (Nat.add_le_add_right
            (GenLimit.InfiniteContamination.count_sparseSquare_le_sqrt_add_one n) C))
    · positivity
  · exact hupper

lemma range_diff_finite_of_novel {input output : ℕ → ℕ} {K : Set ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output K) :
    (Set.range output \ K).Finite := by
  obtain ⟨T, hT⟩ := h
  apply ((Set.finite_Iio T).image output).subset
  rintro x ⟨⟨t, rfl⟩, hnot⟩
  have ht : t < T := by
    by_contra hge
    exact hnot (hT t (Nat.le_of_not_gt hge)).1
  exact ⟨t, ht, rfl⟩

lemma generatorFirst_subset_range (input output : ℕ → ℕ) :
    GenLimit.GeneratorFirst input output ⊆ Set.range output := by
  rintro x ⟨t, rfl, -⟩
  exact ⟨t, rfl⟩

lemma generatorFirst_diff_core_finite_of_novel
    {input output : ℕ → ℕ}
    (h : GenLimit.NovelGeneratesInLimit input output sparseCore) :
    (GenLimit.GeneratorFirst input output \ sparseCore).Finite := by
  apply (range_diff_finite_of_novel h).subset
  rintro x ⟨hx, hxc⟩
  exact ⟨generatorFirst_subset_range input output hx, hxc⟩

end Case024

namespace Case024

lemma sparseCore_ssubset_univ : sparseCore ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have hmem : IC.sparseBetweenSquares 0 ∈ sparseCore := h (Set.mem_univ _)
  exact GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare 0 hmem

lemma pairObstruction_core_univ :
    Stage3Case024.PairObstruction sparseCore Set.univ commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas hIntCore _hIntUniv hValidCore _hValidUniv
  have hzero_ae :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hValidCore] with ω hω
    exact relativeUpperDensity_univ_eq_zero_of_finite_diff
      (generatorFirst_diff_core_finite_of_novel hω)
  have hExpectedUniv :
      Stage3Case024.expectedUpperDensity μ Set.univ commonInput output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzero_ae]
    simp
  have hExpectedCore :
      Stage3Case024.expectedUpperDensity μ sparseCore commonInput output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonInput (output ω)) sparseCore ∂μ)
          ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
            apply integral_mono_ae hIntCore (integrable_const 1)
            exact ae_of_all μ fun ω =>
              relativeUpperDensity_le_one
                (GenLimit.GeneratorFirst commonInput (output ω)) sparseCore
      _ = 1 := by simp [integral_const]
  constructor
  · rw [hExpectedUniv, add_zero]
    exact hExpectedCore
  · rw [hExpectedUniv]
    intro h
    linarith

end Case024

namespace Case024

abbrev marker (n : ℕ) : ℕ := IC.sparseBetweenSquares n

def markerPrefix (n : ℕ) : Set ℕ := marker '' Set.Iio n

lemma marker_not_core (n : ℕ) : marker n ∉ sparseCore :=
  GenLimit.InfiniteContamination.sparseBetweenSquares_nonsquare n

lemma marker_in_prefix {i j : ℕ} (hij : i < j) : marker i ∈ markerPrefix j := by
  exact ⟨i, hij, rfl⟩

lemma marker_not_prefix_self (i : ℕ) : marker i ∉ markerPrefix i := by
  rintro ⟨k, hk, hki⟩
  have hki' : k = i :=
    GenLimit.InfiniteContamination.sparseBetweenSquares_strictMono.injective hki
  exact (Nat.ne_of_lt hk) hki'

lemma markerPrefix_mono {i j : ℕ} (hij : i ≤ j) :
    markerPrefix i ⊆ markerPrefix j := by
  rintro x ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hij, rfl⟩

lemma core_union_markerPrefix_ssubset {i j : ℕ} (hij : i < j) :
    sparseCore ∪ markerPrefix i ⊂ sparseCore ∪ markerPrefix j := by
  refine ⟨Set.union_subset_union_right _ (markerPrefix_mono hij.le), ?_⟩
  intro hsub
  have hm : marker i ∈ sparseCore ∪ markerPrefix i :=
    hsub (Set.mem_union_right _ (marker_in_prefix hij))
  rcases hm with hm | hm
  · exact marker_not_core i hm
  · exact marker_not_prefix_self i hm

lemma core_union_markerPrefix_ssubset_univ (i : ℕ) :
    sparseCore ∪ markerPrefix i ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro hsub
  have hm : marker i ∈ sparseCore ∪ markerPrefix i := hsub (Set.mem_univ _)
  rcases hm with hm | hm
  · exact marker_not_core i hm
  · exact marker_not_prefix_self i hm

noncomputable def nestedFamily (r : ℕ) (j : Fin r) : Set ℕ :=
  if j.val + 1 = r then Set.univ else sparseCore ∪ markerPrefix j.val

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    nestedFamily r ⟨0, lt_of_lt_of_le (by omega) hr⟩ = sparseCore := by
  simp [nestedFamily, markerPrefix]
  omega

lemma nestedFamily_eq_univ_of_last {r : ℕ} (j : Fin r)
    (hj : j.val + 1 = r) : nestedFamily r j = Set.univ := by
  simp [nestedFamily, hj]

lemma sparseCore_subset_nestedFamily {r : ℕ} (j : Fin r) :
    sparseCore ⊆ nestedFamily r j := by
  unfold nestedFamily
  split
  · exact Set.subset_univ _
  · exact Set.subset_union_left

lemma nestedFamily_infinite {r : ℕ} (j : Fin r) :
    (nestedFamily r j).Infinite :=
  sparseCore_infinite.mono (sparseCore_subset_nestedFamily j)

lemma nestedFamily_strictlyNested {r : ℕ} :
    Stage3Case024.StrictlyNested (nestedFamily r) := by
  intro i j hij
  have hi : i.val + 1 ≠ r := by omega
  by_cases hj : j.val + 1 = r
  · rw [nestedFamily_eq_univ_of_last j hj]
    simp only [nestedFamily, hi, if_false]
    exact core_union_markerPrefix_ssubset_univ i.val
  · simp only [nestedFamily, hi, hj, if_false]
    exact core_union_markerPrefix_ssubset hij

lemma nestedFamily_legal {r : ℕ} (j : Fin r) :
    Stage3Case024.Legal commonInput (nestedFamily r j) :=
  commonInput_legal_of_core_subset (nestedFamily_infinite j)
    (sparseCore_subset_nestedFamily j)

end Case024

namespace Case024

noncomputable def freshSquareGenerator : Stage3Case024.OnlineGenerator :=
  fun t input _output =>
    let q := t + 1 + ∑ i, input i
    q * q

noncomputable def freshSquareOutput (input : Stage3Case024.Stream) :
    Stage3Case024.Stream :=
  fun t =>
    let q := t + 1 + ∑ k ∈ Finset.range (t + 1), input k
    q * q

lemma freshSquare_follows (input : Stage3Case024.Stream) :
    Stage3Case024.Follows freshSquareGenerator input (freshSquareOutput input) := by
  intro t
  simp [freshSquareGenerator, freshSquareOutput, Fin.sum_univ_eq_sum_range]

lemma freshSquareBase_strictMono (input : Stage3Case024.Stream) :
    StrictMono (fun t => t + 1 + ∑ k ∈ Finset.range (t + 1), input k) := by
  intro s t hst
  have hsum :
      (∑ k ∈ Finset.range (s + 1), input k) ≤
        ∑ k ∈ Finset.range (t + 1), input k := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (Nat.succ_le_succ hst.le)
  show s + 1 + (∑ k ∈ Finset.range (s + 1), input k) <
    t + 1 + ∑ k ∈ Finset.range (t + 1), input k
  omega

lemma freshSquareOutput_strictMono (input : Stage3Case024.Stream) :
    StrictMono (freshSquareOutput input) := by
  intro s t hst
  apply Nat.mul_self_lt_mul_self
  exact freshSquareBase_strictMono input hst

lemma freshSquareOutput_mem_core (input : Stage3Case024.Stream) (t : ℕ) :
    freshSquareOutput input t ∈ sparseCore := by
  let q := t + 1 + ∑ k ∈ Finset.range (t + 1), input k
  exact ⟨q, rfl⟩

lemma freshSquareOutput_not_input_sample (input : Stage3Case024.Stream) (t : ℕ) :
    freshSquareOutput input t ∉ GenLimit.sample input (t + 1) := by
  rw [GenLimit.mem_sample_iff]
  rintro ⟨s, hs, heq⟩
  have hsle : input s ≤ ∑ k ∈ Finset.range (t + 1), input k := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    exact Finset.mem_range.mpr hs
  let q := t + 1 + ∑ k ∈ Finset.range (t + 1), input k
  have hsq : input s < q * q := by
    have hlt : input s < q := by
      dsimp [q]
      omega
    have hqpos : 0 < q := by
      dsimp [q]
      omega
    exact lt_of_lt_of_le hlt (Nat.le_mul_of_pos_left q hqpos)
  rw [freshSquareOutput] at heq
  exact (Nat.ne_of_lt hsq) heq

lemma freshSquare_novel (input : Stage3Case024.Stream) {K : Set ℕ}
    (hcore : sparseCore ⊆ K) :
    GenLimit.NovelGeneratesInLimit input (freshSquareOutput input) K := by
  refine ⟨0, ?_⟩
  intro t _ht
  refine ⟨hcore (freshSquareOutput_mem_core input t),
    freshSquareOutput_not_input_sample input t, ?_⟩
  intro s hst
  exact (freshSquareOutput_strictMono input hst).ne

lemma nestedFamily_globallyFeasible {r : ℕ} :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨freshSquareGenerator, ?_⟩
  intro input _hlegal
  refine ⟨freshSquareOutput input, freshSquare_follows input, ?_⟩
  intro j
  exact freshSquare_novel input (sparseCore_subset_nestedFamily j)

end Case024

namespace Case024

lemma nestedFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonInput := by
  intro Ω _ μ _ gen output _hfollow _hmeas _hInt hValid
  let j0 : Fin r := ⟨0, by omega⟩
  have hValidCore := hValid j0
  have hj0 : nestedFamily r j0 = sparseCore := by
    simpa [j0] using nestedFamily_zero hr
  rw [hj0] at hValidCore
  have hzero_ae :
      (fun ω => Stage3Case024.relativeUpperDensity
        (GenLimit.GeneratorFirst commonInput (output ω)) Set.univ) =ᵐ[μ]
        (fun _ => 0) := by
    filter_upwards [hValidCore] with ω hω
    exact relativeUpperDensity_univ_eq_zero_of_finite_diff
      (generatorFirst_diff_core_finite_of_novel hω)
  let jlast : Fin r := ⟨r - 1, by omega⟩
  refine ⟨jlast, ?_⟩
  have hjlast : nestedFamily r jlast = Set.univ := by
    apply nestedFamily_eq_univ_of_last
    dsimp [jlast]
    omega
  rw [hjlast]
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae hzero_ae]
  simp

lemma nestedFamily_witness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonInput := by
  exact ⟨nestedFamily_strictlyNested, nestedFamily_legal,
    nestedFamily_globallyFeasible, nestedFamily_manyTargetObstruction hr⟩

end Case024
