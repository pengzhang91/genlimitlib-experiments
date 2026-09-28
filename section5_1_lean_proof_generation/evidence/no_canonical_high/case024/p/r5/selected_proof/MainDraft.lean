import Helpers

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Case024

lemma expected_univ_eq_zero_of_eventually_squares
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (input : Stream) (output : Ω → Stream)
    (hvalid : Stage3Case024.EventuallyFreshValid μ squares input output) :
    Stage3Case024.expectedUpperDensity μ Set.univ input output = 0 := by
  unfold Stage3Case024.EventuallyFreshValid at hvalid
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) Set.univ ∂μ) =
        ∫ _ : Ω, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hvalid] with ω hω
          exact path_univ_density_zero hω
    _ = 0 := by simp

lemma expected_density_le_one
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : Language) (input : Stream) (output : Ω → Stream)
    (hint : Stage3Case024.DensityIntegrable μ K input output) :
    Stage3Case024.expectedUpperDensity μ K input output ≤ 1 := by
  unfold Stage3Case024.DensityIntegrable at hint
  unfold Stage3Case024.expectedUpperDensity
  calc
    (∫ ω, Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst input (output ω)) K ∂μ) ≤
        ∫ _ : Ω, (1 : ℝ) ∂μ := by
          apply integral_mono_ae hint (integrable_const 1)
          exact Filter.Eventually.of_forall (fun ω =>
            relativeUpperDensity_le_one (GenLimit.GeneratorFirst input (output ω)) K)
    _ = 1 := by simp

lemma pairObstruction_squares_univ :
    Stage3Case024.PairObstruction squares Set.univ sparseEnumeration := by
  intro Ω _ μ _ gen output _ _ hintSquares _ hvalidSquares _
  have hout : Stage3Case024.expectedUpperDensity μ Set.univ sparseEnumeration output = 0 :=
    expected_univ_eq_zero_of_eventually_squares μ sparseEnumeration output hvalidSquares
  have hin : Stage3Case024.expectedUpperDensity μ squares sparseEnumeration output ≤ 1 :=
    expected_density_le_one μ squares sparseEnumeration output hintSquares
  constructor
  · rw [hout]
    simpa using hin
  · intro hboth
    rw [hout] at hboth
    linarith

noncomputable def freshSquareGenerator : Stage3Case024.OnlineGenerator :=
  fun _ input previous =>
    ((∑ i, input i) + (∑ i, previous i) + 1) ^ 2

noncomputable def freshSquareOutput (input : Stream) (t : ℕ) : ℕ :=
  freshSquareGenerator t (fun i => input i) (fun i => freshSquareOutput input i)
termination_by t

lemma freshSquareOutput_follows (input : Stream) :
    Stage3Case024.Follows freshSquareGenerator input (freshSquareOutput input) := by
  intro t
  rw [freshSquareOutput]

lemma fin_value_le_input_sum {t : ℕ} (input : Fin (t + 1) → ℕ) (i : Fin (t + 1)) :
    input i ≤ ∑ j, input j := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (input j)) (Finset.mem_univ i)

lemma fin_value_le_output_sum {t : ℕ} (output : Fin t → ℕ) (i : Fin t) :
    output i ≤ ∑ j, output j := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (output j)) (Finset.mem_univ i)

lemma freshSquareOutput_novel (input : Stream) :
    GenLimit.NovelGeneratesInLimit input (freshSquareOutput input) squares := by
  refine ⟨0, fun t _ => ?_⟩
  let base := (∑ i : Fin (t + 1), input i) +
    (∑ i : Fin t, freshSquareOutput input i) + 1
  have hout : freshSquareOutput input t = base ^ 2 := by
    rw [freshSquareOutput]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    simp [squares]
  · intro hmem
    rw [GenLimit.sample, Finset.mem_image] at hmem
    obtain ⟨s, hs, heq⟩ := hmem
    have hslt : s < t + 1 := Finset.mem_range.mp hs
    let si : Fin (t + 1) := ⟨s, hslt⟩
    have hle : input s ≤ ∑ i : Fin (t + 1), input i :=
      fin_value_le_input_sum (fun i : Fin (t + 1) => input i) si
    have hbasepos : 0 < base := by simp [base]
    have hsq : base ≤ base ^ 2 := by
      nlinarith
    have hstrict : input s < base := by
      dsimp [base]
      omega
    rw [hout] at heq
    omega
  · intro s hst heq
    let si : Fin t := ⟨s, hst⟩
    have hle : freshSquareOutput input s ≤
        ∑ i : Fin t, freshSquareOutput input i :=
      fin_value_le_output_sum (fun i : Fin t => freshSquareOutput input i) si
    have hbasepos : 0 < base := by simp [base]
    have hsq : base ≤ base ^ 2 := by
      nlinarith
    have hstrict : freshSquareOutput input s < base := by
      dsimp [base]
      omega
    rw [hout] at heq
    omega

lemma globallyFeasible_of_squares_subset {r : ℕ} (family : Fin r → Language)
    (hfamily : ∀ j, squares ⊆ family j) :
    Stage3Case024.GloballyFeasible family := by
  refine ⟨freshSquareGenerator, fun input _ =>
    ⟨freshSquareOutput input, freshSquareOutput_follows input, ?_⟩⟩
  intro j
  unfold Stage3Case024.EventuallyFreshValidPath
  obtain ⟨T, hT⟩ := freshSquareOutput_novel input
  exact ⟨T, fun t ht => by
    obtain ⟨hsq, hfresh, hnovel⟩ := hT t ht
    exact ⟨hfamily j hsq, hfresh, hnovel⟩⟩

def boundedGaps (j : ℕ) : Language :=
  {x | ∃ n < j, x = gapEven n}

def targetFamily (r : ℕ) (j : Fin r) : Language :=
  if j.val = r - 1 then Set.univ else squares ∪ boundedGaps j.val

lemma squares_subset_targetFamily {r : ℕ} (j : Fin r) :
    squares ⊆ targetFamily r j := by
  intro x hx
  unfold targetFamily
  split_ifs
  · trivial
  · exact Or.inl hx

lemma targetFamily_zero {r : ℕ} (hr : 2 ≤ r) :
    targetFamily r ⟨0, by omega⟩ = squares := by
  ext x
  simp [targetFamily, boundedGaps]
  omega

lemma targetFamily_last {r : ℕ} (hr : 1 ≤ r) :
    targetFamily r ⟨r - 1, by omega⟩ = Set.univ := by
  simp [targetFamily]

lemma targetFamily_infinite {r : ℕ} (j : Fin r) :
    (targetFamily r j).Infinite :=
  squares_infinite.mono (squares_subset_targetFamily j)

lemma targetFamily_strictlyNested {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.StrictlyNested (targetFamily r) := by
  intro i j hij
  have hilast : i.val ≠ r - 1 := by
    intro hi
    have hjle : j.val ≤ r - 1 := by omega
    omega
  by_cases hjlast : j.val = r - 1
  · simp only [targetFamily, hjlast, hilast, if_pos, if_neg]
    refine ⟨Set.subset_univ _, ?_⟩
    intro hrev
    have hgap : gapOdd 0 ∈ squares ∪ boundedGaps i.val := hrev (Set.mem_univ _)
    rcases hgap with hsq | ⟨n, hn, heq⟩
    · exact gapOdd_not_square 0 hsq
    · exact gapOdd_ne_gapEven 0 n heq
  · simp only [targetFamily, hjlast, hilast, if_pos, if_neg]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hsq | ⟨n, hn, heq⟩
      · exact Or.inl hsq
      · exact Or.inr ⟨n, lt_trans hn hij, heq⟩
    · intro hrev
      have hjmem : gapEven i.val ∈ squares ∪ boundedGaps j.val :=
        Or.inr ⟨i.val, hij, rfl⟩
      have himem := hrev hjmem
      rcases himem with hsq | ⟨n, hn, heq⟩
      · exact gapEven_not_square i.val hsq
      · have : n = i.val := gapEven_injective heq.symm
        omega

lemma targetFamily_manyTargetObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (targetFamily r) sparseEnumeration := by
  intro Ω _ μ _ gen output _ _ _ hvalid
  let first : Fin r := ⟨0, by omega⟩
  let last : Fin r := ⟨r - 1, by omega⟩
  refine ⟨last, ?_⟩
  have hfirst := hvalid first
  rw [targetFamily_zero hr] at hfirst
  have hzero := expected_univ_eq_zero_of_eventually_squares
    μ sparseEnumeration output hfirst
  rw [show targetFamily r last = Set.univ by
    simpa [last] using (targetFamily_last (r := r) (by omega))]
  exact hzero

lemma targetFamily_witness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (targetFamily r) sparseEnumeration := by
  refine ⟨targetFamily_strictlyNested hr, ?_,
    globallyFeasible_of_squares_subset (targetFamily r) squares_subset_targetFamily,
    targetFamily_manyTargetObstruction hr⟩
  intro j
  exact (sparseEnumeration_legal (targetFamily r j) (squares_subset_targetFamily j)).2
    (targetFamily_infinite j)

end Case024
