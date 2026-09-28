import Case024Helpers

open Filter MeasureTheory
open scoped Topology

open Stage3Case024

namespace Stage3Case024Proof

 theorem pair_obstruction :
    PairObstruction squareCore (familyLanguage 1) (commonInput 2 (by omega)) := by
  intro Ω _ μ _ gen output _ _ hint0 _ hev0 _
  have hzeroAE :
      (fun ω => relativeUpperDensity
        (GenLimit.GeneratorFirst (commonInput 2 (by omega)) (output ω))
        (familyLanguage 1)) =ᵐ[μ] 0 := by
    filter_upwards [hev0] with ω hω
    exact relativeUpperDensity_zero_of_eventual_square hω
  have hzero :
      expectedUpperDensity μ (familyLanguage 1) (commonInput 2 (by omega)) output = 0 := by
    unfold expectedUpperDensity
    exact integral_eq_zero_of_ae hzeroAE
  have hone :
      expectedUpperDensity μ squareCore (commonInput 2 (by omega)) output ≤ 1 := by
    unfold DensityIntegrable at hint0
    unfold expectedUpperDensity
    have hle := integral_mono hint0 (integrable_const (1 : ℝ))
      (fun ω => relativeUpperDensity_le_one
        (GenLimit.GeneratorFirst (commonInput 2 (by omega)) (output ω)) squareCore)
    simpa using hle
  constructor
  · rw [hzero]
    linarith
  · rw [hzero]
    intro h
    linarith

 theorem many_obstruction (r : ℕ) (hr : 2 ≤ r) :
    ManyTargetObstruction (fun i : Fin r => familyLanguage i)
      (commonInput r (by omega)) := by
  intro Ω _ μ _ gen output _ _ _ hev
  let zero : Fin r := ⟨0, by omega⟩
  let one : Fin r := ⟨1, by omega⟩
  have hsquare :
      ∀ᵐ ω ∂μ, GenLimit.NovelGeneratesInLimit
        (commonInput r (by omega)) (output ω) squareCore := by
    filter_upwards [hev zero] with ω hω
    simpa [zero, familyLanguage] using hω
  have hzeroAE :
      (fun ω => relativeUpperDensity
        (GenLimit.GeneratorFirst (commonInput r (by omega)) (output ω))
        (familyLanguage 1)) =ᵐ[μ] 0 := by
    filter_upwards [hsquare] with ω hω
    exact relativeUpperDensity_zero_of_eventual_square hω
  refine ⟨one, ?_⟩
  unfold expectedUpperDensity
  simpa [one] using integral_eq_zero_of_ae hzeroAE

 theorem many_witness (r : ℕ) (hr : 2 ≤ r) :
    ManyTargetWitness (fun i : Fin r => familyLanguage i)
      (commonInput r (by omega)) := by
  refine ⟨?_, ?_, family_globallyFeasible r, many_obstruction r hr⟩
  · intro i j hij
    exact familyLanguage_strict hij
  · intro j
    exact commonInput_legal r (by omega) j

end Stage3Case024Proof

open Stage3Case024Proof

theorem stage3_result : Stage3Case024.MainClaim := by
  constructor
  · refine ⟨squareCore, familyLanguage 1, commonInput 2 (by omega), ?_, ?_, ?_,
      pair_obstruction⟩
    · simpa [familyLanguage] using
        (familyLanguage_strict (i := 0) (j := 1) (by omega))
    · exact commonInput_legal 2 (by omega) ⟨0, by omega⟩
    · exact commonInput_legal 2 (by omega) ⟨1, by omega⟩
  · intro r hr
    exact ⟨(fun i : Fin r => familyLanguage i), commonInput r (by omega),
      many_witness r hr⟩
