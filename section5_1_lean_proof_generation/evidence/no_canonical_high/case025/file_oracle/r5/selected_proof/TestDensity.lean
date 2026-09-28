import Stage3Model
import GenLimit.Paper39_DenseGeneration.Patient.Main
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable section

private theorem prefixCount_inter_union_le
    (D K : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n ≤
      GenLimit.PatientScope.prefixCount (D ∩ K) n + F.card := by
  classical
  unfold GenLimit.PatientScope.prefixCount
  have hsub :
      GenLimit.PatientScope.prefixFinset (D ∩ (K ∪ (F : Set ℕ))) n ⊆
        GenLimit.PatientScope.prefixFinset (D ∩ K) n ∪ F := by
    intro x hx
    have hx' := GenLimit.PatientScope.mem_prefixFinset.mp hx
    rcases hx'.2.2 with hxK | hxF
    · apply Finset.mem_union_left
      exact GenLimit.PatientScope.mem_prefixFinset.mpr
        ⟨hx'.1, hx'.2.1, hxK⟩
    · exact Finset.mem_union_right _ hxF
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _)

private theorem relativeRatio_nonneg (D K : Set ℕ) (n : ℕ) :
    0 ≤ (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) := by
  positivity

private theorem relativeRatio_le_one (D K : Set ℕ) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ) ≤ 1 := by
  have hcount :
      GenLimit.PatientScope.prefixCount (D ∩ K) n ≤
        GenLimit.PatientScope.prefixCount K n :=
    GenLimit.PatientScope.prefixCount_mono Set.inter_subset_right n
  by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
  · have hnum : GenLimit.PatientScope.prefixCount (D ∩ K) n = 0 :=
      Nat.eq_zero_of_le_zero (hzero ▸ hcount)
    simp [hzero, hnum]
  · have hpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast hcount

private theorem relativeLowerDensity_finite_extension_le
    (D K : Set ℕ) (F : Finset ℕ) (hK : K.Infinite) :
    GenLimit.PatientScope.relativeLowerDensity
        (D ∩ (K ∪ (F : Set ℕ))) (K ∪ (F : Set ℕ)) ≤
      GenLimit.PatientScope.relativeLowerDensity (D ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
      (GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
      (GenLimit.PatientScope.prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ)
  have hcount := GenLimit.PatientScope.tendsto_prefixCount_atTop hK
  have herror : Tendsto error atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hcount)
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < GenLimit.PatientScope.prefixCount K n :=
    hcount.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hpositive] with n hn
    have hnR : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hdenNat :
        GenLimit.PatientScope.prefixCount K n ≤
          GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n :=
      GenLimit.PatientScope.prefixCount_mono Set.subset_union_left n
    have hdenR :
        (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n := by
      exact_mod_cast hdenNat
    have hnumNat := prefixCount_inter_union_le D K F n
    have hnumR :
        (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (D ∩ K) n + F.card := by
      exact_mod_cast hnumNat
    dsimp [source, target, error]
    calc
      (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
          (GenLimit.PatientScope.prefixCount (K ∪ (F : Set ℕ)) n : ℝ)
          ≤ (GenLimit.PatientScope.prefixCount (D ∩ (K ∪ (F : Set ℕ))) n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnR hdenR
      _ ≤ ((GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) + F.card) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            exact div_le_div_of_nonneg_right hnumR hnR.le
      _ = (GenLimit.PatientScope.prefixCount (D ∩ K) n : ℝ) /
              (GenLimit.PatientScope.prefixCount K n : ℝ) +
            (F.card : ℝ) / (GenLimit.PatientScope.prefixCount K n : ℝ) := by
            rw [add_div]
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => relativeRatio_le_one D K n))
    (isBoundedUnder_of
      ⟨0, fun n => relativeRatio_nonneg D K n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hsourceEventually : ∀ᶠ n : ℕ in atTop, r < source n := by
    exact eventually_lt_of_lt_liminf hr (by
      simpa only [source] using
        (isBoundedUnder_of
          ⟨0, fun n => relativeRatio_nonneg D (K ∪ (F : Set ℕ)) n⟩))
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    exact herror.eventually (Iio_mem_nhds (sub_pos.mpr hyr))
  filter_upwards [hsourceEventually, herrorEventually, hcompare] with
      n hsource hsmall hle
  linarith

end
end Stage3Case025
