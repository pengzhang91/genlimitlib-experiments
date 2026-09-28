import «output».Density

open Filter MeasureTheory
open scoped Topology

namespace Case024

lemma squares_ssubset_univ : squares ⊂ (Set.univ : Set ℕ) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro h
  have htwo : 2 ∈ squares := h (Set.mem_univ 2)
  rcases htwo with ⟨k, hk⟩
  change k^2 = 2 at hk
  exact Nat.prime_two.not_isSquare ⟨k, by simpa [pow_two] using hk.symm⟩

lemma pairObstruction : Stage3Case024.PairObstruction squares Set.univ commonStream := by
  intro Ω _ μ _ gen output _ _ hint0 hint1 hev0 _
  have hzero_ae : (fun ω => Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ) =ᶠ[ae μ] 0 := by
    filter_upwards [hev0] with ω hω
    exact relativeUpperDensity_univ_eq_zero hω
  have hzero : Stage3Case024.expectedUpperDensity μ Set.univ commonStream output = 0 := by
    unfold Stage3Case024.expectedUpperDensity
    rw [integral_congr_ae hzero_ae]
    simp
  have hle_ae : (fun ω => Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst commonStream (output ω)) squares) ≤ᶠ[ae μ]
      (fun _ => (1 : ℝ)) := by
    filter_upwards with ω
    exact relativeUpperDensity_le_one _ _ squares_infinite
  have honeint : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  have hle : Stage3Case024.expectedUpperDensity μ squares commonStream output ≤ 1 := by
    unfold Stage3Case024.expectedUpperDensity
    calc
      (∫ ω, Stage3Case024.relativeUpperDensity
          (GenLimit.GeneratorFirst commonStream (output ω)) squares ∂μ) ≤
          ∫ _ : Ω, (1 : ℝ) ∂μ := integral_mono_ae hint0 honeint hle_ae
      _ = 1 := by simp
  constructor
  · rw [hzero, add_zero]
    exact hle
  · rw [hzero]
    intro hboth
    linarith [hboth.1]

lemma pairWitness :
    ∃ K₀ K₁ : Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      K₀ ⊂ K₁ ∧ Stage3Case024.Legal input K₀ ∧ Stage3Case024.Legal input K₁ ∧
        Stage3Case024.PairObstruction K₀ K₁ input := by
  exact ⟨squares, Set.univ, commonStream, squares_ssubset_univ,
    commonStream_legal_squares, commonStream_legal_univ, pairObstruction⟩

end Case024
