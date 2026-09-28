import Helpers

open Filter MeasureTheory Set
open scoped Topology

namespace Case024

lemma expected_univ_zero {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : Stage3Case024.Stream) (output : Ω → Stage3Case024.Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ squares input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.expectedUpperDensity
  rw [MeasureTheory.integral_congr_ae (ae_density_univ_zero μ input output hvalid)]
  simp

lemma expected_density_le_one {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : Language) (input : Stage3Case024.Stream)
    (output : Ω → Stage3Case024.Stream)
    (hint : Stage3Case024.DensityIntegrable μ K input output) :
    Stage3Case024.expectedUpperDensity μ K input output ≤ 1 := by
  unfold Stage3Case024.expectedUpperDensity
  have hle := MeasureTheory.integral_mono hint (MeasureTheory.integrable_const (1 : ℝ))
    (fun ω => relativeUpperDensity_le_one (GenLimit.GeneratorFirst input (output ω)) K)
  simpa [MeasureTheory.integral_const, MeasureTheory.measureReal_def] using hle

lemma pair_obstruction : Stage3Case024.PairObstruction squares Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hintSquares _ hvalidSquares _
  have hzero := expected_univ_zero μ commonStream output hvalidSquares
  have hle := expected_density_le_one μ squares commonStream output hintSquares
  constructor
  · rw [hzero]
    linarith
  · rintro ⟨hhalf0, hhalf1⟩
    rw [hzero] at hhalf1
    linarith

def finiteFamily (r : ℕ) (j : Fin r) : Language :=
  if j.val + 1 = r then Set.univ
  else squares ∪ {x | ∃ k < j.val, tag k = x}

lemma squares_subset_finiteFamily (r : ℕ) (j : Fin r) :
    squares ⊆ finiteFamily r j := by
  intro x hx
  simp only [finiteFamily]
  split_ifs
  · trivial
  · exact Or.inl hx

lemma finiteFamily_zero (r : ℕ) (hr : 2 ≤ r) :
    finiteFamily r ⟨0, by omega⟩ = squares := by
  ext x
  simp [finiteFamily, show 1 ≠ r by omega]

lemma finiteFamily_last (r : ℕ) (hr : 2 ≤ r) :
    finiteFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [finiteFamily, Nat.sub_add_cancel (by omega : 1 ≤ r)]

lemma finiteFamily_strict (r : ℕ) : Stage3Case024.StrictlyNested (finiteFamily r) := by
  intro i j hij
  have hi : i.val + 1 ≠ r := by omega
  by_cases hj : j.val + 1 = r
  · rw [finiteFamily, if_neg hi, finiteFamily, if_pos hj]
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · exact Set.subset_univ _
    · intro heq
      have hmem : tag i.val ∈ squares ∪ {x | ∃ k < i.val, tag k = x} := by
        rw [heq]
        trivial
      rcases hmem with hs | ⟨k, hk, htag⟩
      · exact tag_not_square i.val hs
      · exact (Nat.ne_of_lt hk) (tag_injective htag)
  · rw [finiteFamily, if_neg hi, finiteFamily, if_neg hj]
    rw [Set.ssubset_iff_subset_ne]
    constructor
    · rintro x (hs | ⟨k, hk, rfl⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨k, lt_trans hk hij, rfl⟩
    · intro heq
      have hmemRight : tag i.val ∈ squares ∪ {x | ∃ k < j.val, tag k = x} :=
        Or.inr ⟨i.val, hij, rfl⟩
      have hmemLeft : tag i.val ∈ squares ∪ {x | ∃ k < i.val, tag k = x} := by
        rw [heq]
        exact hmemRight
      rcases hmemLeft with hs | ⟨k, hk, htag⟩
      · exact tag_not_square i.val hs
      · exact (Nat.ne_of_lt hk) (tag_injective htag)

lemma finiteFamily_legal (r : ℕ) (j : Fin r) :
    Stage3Case024.Legal commonStream (finiteFamily r j) := by
  have hsub := squares_subset_finiteFamily r j
  exact commonStream_legal_of_superset _ (squares_infinite.mono hsub) hsub

lemma finiteFamily_globallyFeasible (r : ℕ) :
    Stage3Case024.GloballyFeasible (finiteFamily r) := by
  refine ⟨squareGenerator, fun input _ => ?_⟩
  obtain ⟨output, hfollows, hvalid⟩ := squareGenerator_success input
  refine ⟨output, hfollows, fun j => ?_⟩
  obtain ⟨T, hT⟩ := hvalid
  refine ⟨T, fun t ht => ?_⟩
  have hs := hT t ht
  exact ⟨squares_subset_finiteFamily r j hs.1, hs.2.1, hs.2.2⟩

lemma finiteFamily_obstruction (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (finiteFamily r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let zero : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  have hzvalid : Stage3Case024.EventuallyFreshValid μ squares commonStream output := by
    simpa [zero, finiteFamily_zero r hr] using hvalid zero
  refine ⟨last, ?_⟩
  simpa [last, finiteFamily_last r hr] using
    (expected_univ_zero μ commonStream output hzvalid)

lemma finiteFamily_witness (r : ℕ) (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (finiteFamily r) commonStream := by
  exact ⟨finiteFamily_strict r, finiteFamily_legal r,
    finiteFamily_globallyFeasible r, finiteFamily_obstruction r hr⟩

end Case024

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨Case024.squares, Set.univ, Case024.commonStream, ?_,
      Case024.commonStream_legal_squares, ?_, Case024.pair_obstruction⟩
    · rw [Set.ssubset_iff_subset_ne]
      exact ⟨Set.subset_univ _, fun h => Case024.tag_not_square 0 (h ▸ Set.mem_univ _)⟩
    · exact Case024.commonStream_legal_of_superset Set.univ Set.infinite_univ (Set.subset_univ _)
  · intro r hr
    exact ⟨Case024.finiteFamily r, Case024.commonStream, Case024.finiteFamily_witness r hr⟩
