import «output».Family

open Filter MeasureTheory
open scoped Topology

namespace Case024

lemma novel_mono {input output : ℕ → ℕ} {K L : Set ℕ} (hKL : K ⊆ L)
    (h : GenLimit.NovelGeneratesInLimit input output K) :
    GenLimit.NovelGeneratesInLimit input output L := by
  rcases h with ⟨T, hT⟩
  exact ⟨T, fun t ht => ⟨hKL (hT t ht).1, (hT t ht).2⟩⟩

lemma squares_subset_nestedFamily {r : ℕ} (i : Fin r) : squares ⊆ nestedFamily r i := by
  unfold nestedFamily
  split
  · exact Set.subset_univ _
  · exact squares_subset_finiteExtension i

lemma nestedFamily_globallyFeasible {r : ℕ} :
    Stage3Case024.GloballyFeasible (nestedFamily r) := by
  refine ⟨squareGenerator, fun input _ => ⟨squareOutput input, squareOutput_follows input, ?_⟩⟩
  intro j
  exact novel_mono (squares_subset_nestedFamily j) (squareOutput_novel input)

noncomputable def zeroIndex (r : ℕ) (hr : 2 ≤ r) : Fin r :=
  ⟨0, by omega⟩

lemma nestedFamily_zero {r : ℕ} (hr : 2 ≤ r) : nestedFamily r (zeroIndex r hr) = squares := by
  have hne : ((zeroIndex r hr : Fin r) : ℕ) + 1 ≠ r := by simp [zeroIndex]; omega
  unfold nestedFamily
  rw [if_neg hne]
  ext x
  simp [finiteExtension, zeroIndex]

noncomputable def lastIndex (r : ℕ) (hr : 2 ≤ r) : Fin r :=
  ⟨r - 1, by omega⟩

lemma nestedFamily_last {r : ℕ} (hr : 2 ≤ r) : nestedFamily r (lastIndex r hr) = Set.univ := by
  have hlast : ((lastIndex r hr : Fin r) : ℕ) + 1 = r := by
    simp [lastIndex]
    omega
  simp [nestedFamily, hlast]

lemma nestedFamily_manyObstruction {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetObstruction (nestedFamily r) commonStream := by
  intro Ω _ μ _ gen output _ _ _ hev
  have hev0 : ∀ᵐ ω ∂μ, GenLimit.NovelGeneratesInLimit commonStream (output ω) squares := by
    have hz := hev (zeroIndex r hr)
    simpa only [nestedFamily_zero hr] using hz
  have hzero_ae : (fun ω => Stage3Case024.relativeUpperDensity
      (GenLimit.GeneratorFirst commonStream (output ω)) Set.univ) =ᶠ[ae μ] 0 := by
    filter_upwards [hev0] with ω hω
    exact relativeUpperDensity_univ_eq_zero hω
  refine ⟨lastIndex r hr, ?_⟩
  rw [nestedFamily_last hr]
  unfold Stage3Case024.expectedUpperDensity
  rw [integral_congr_ae hzero_ae]
  simp

lemma manyTargetWitness {r : ℕ} (hr : 2 ≤ r) :
    Stage3Case024.ManyTargetWitness (nestedFamily r) commonStream := by
  exact ⟨nestedFamily_strict hr, nestedFamily_legal,
    nestedFamily_globallyFeasible, nestedFamily_manyObstruction hr⟩

lemma manyWitnesses : ∀ r : ℕ, 2 ≤ r →
    ∃ family : Fin r → Stage3Case024.Language, ∃ input : Stage3Case024.Stream,
      Stage3Case024.ManyTargetWitness family input := by
  intro r hr
  exact ⟨nestedFamily r, commonStream, manyTargetWitness hr⟩

end Case024
