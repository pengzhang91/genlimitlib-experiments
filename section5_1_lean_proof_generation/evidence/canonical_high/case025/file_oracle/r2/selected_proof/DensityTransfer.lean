import PositiveEngine
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Stage3Case025
namespace DensityTransfer

open GenLimit
open GenLimit.PatientScope

noncomputable def relativeRatio (A K : Set ℕ) (n : ℕ) : ℝ :=
  (prefixCount A n : ℝ) / (prefixCount K n : ℝ)

theorem relativeRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ relativeRatio A K n := by
  exact div_nonneg (by positivity) (by positivity)

theorem relativeRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    relativeRatio A K n ≤ 1 := by
  unfold relativeRatio
  by_cases hzero : prefixCount K n = 0
  · simp [hzero]
  · have hpos : (0 : ℝ) < prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    rw [div_le_one hpos]
    exact_mod_cast prefixCount_mono hAK n

theorem liminf_le_of_eventually_le_add_vanishing
    (source output error : ℕ → ℝ)
    (hsource_nonneg : ∀ n, 0 ≤ source n)
    (houtput_nonneg : ∀ n, 0 ≤ output n)
    (houtput_le_one : ∀ n, output n ≤ 1)
    (herror : Tendsto error atTop (nhds 0))
    (hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ output n + error n) :
    liminf source atTop ≤ liminf output atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop houtput_le_one)
    (isBoundedUnder_of ⟨0, houtput_nonneg⟩)).2
  intro y hy
  obtain ⟨r, hyr, hr⟩ := exists_between hy
  have hsourceEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hr
      (isBoundedUnder_of ⟨0, hsource_nonneg⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hsourceEventually, herrorEventually, hprefix] with
      n hsource hsmall hcount
  linarith

theorem prefixCount_le_card_finite
    {F : Set ℕ} (hF : F.Finite) (n : ℕ) :
    prefixCount F n ≤ hF.toFinset.card := by
  classical
  unfold prefixCount
  apply Finset.card_le_card
  intro x hx
  exact Set.Finite.mem_toFinset hF |>.2 (mem_prefixFinset.mp hx).2

theorem prefixCount_le_add_finite_difference
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := prefixFinset A n
  let bPrefix := prefixFinset B n
  let diffPrefix := prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    have hxA := mem_prefixFinset.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ (mem_prefixFinset.mpr ⟨hxA.1, hxB⟩)
    · exact Finset.mem_union_right _
        (mem_prefixFinset.mpr ⟨hxA.1, hxA.2, hxB⟩)
  have hcard : aPrefix.card ≤ bPrefix.card + diffPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    simpa [diffPrefix, prefixCount] using prefixCount_le_card_finite hfinite n
  simpa [aPrefix, bPrefix, diffPrefix, prefixCount] using
    hcard.trans (Nat.add_le_add_left hdiff _)

theorem relativeLowerDensity_finite_extension
    {Q K R : Set ℕ}
    (hK : K.Infinite) (hKR : K ⊆ R) (hfinite : (R \ K).Finite) :
    relativeLowerDensity (Q ∩ R) R ≤
      relativeLowerDensity (Q ∩ K) K := by
  let c : ℕ := hfinite.toFinset.card
  let source := relativeRatio (Q ∩ R) R
  let target := relativeRatio (Q ∩ K) K
  let error : ℕ → ℝ := fun n => (c : ℝ) / (prefixCount K n : ℝ)
  have hcountNat : Tendsto (prefixCount K) atTop atTop :=
    tendsto_prefixCount_atTop hK
  have hcountReal : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountNat
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcountReal
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
    hcountNat.eventually (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hpositive] with n hn
    have hdenomNat : prefixCount K n ≤ prefixCount R n :=
      prefixCount_mono hKR n
    have hdenom : (prefixCount K n : ℝ) ≤ prefixCount R n := by
      exact_mod_cast hdenomNat
    have hkpos : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hrpos : (0 : ℝ) < prefixCount R n := lt_of_lt_of_le hkpos hdenom
    have hdiff : ((Q ∩ R) \ (Q ∩ K)).Finite := by
      apply hfinite.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hnumNat :
        prefixCount (Q ∩ R) n ≤ prefixCount (Q ∩ K) n + c := by
      have hdiffSubset : (Q ∩ R) \ (Q ∩ K) ⊆ R \ K := by
        intro x hx
        exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
      have hcard : hdiff.toFinset.card ≤ hfinite.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        exact Set.Finite.mem_toFinset hfinite |>.2
          (hdiffSubset (Set.Finite.mem_toFinset hdiff |>.1 hx))
      exact (prefixCount_le_add_finite_difference hdiff n).trans
        (Nat.add_le_add_left hcard _)
    have hnum :
        (prefixCount (Q ∩ R) n : ℝ) ≤
          prefixCount (Q ∩ K) n + c := by
      exact_mod_cast hnumNat
    calc
      source n =
          (prefixCount (Q ∩ R) n : ℝ) / (prefixCount R n : ℝ) := rfl
      _ ≤ (prefixCount (Q ∩ R) n : ℝ) / (prefixCount K n : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) hkpos hdenom
      _ ≤ ((prefixCount (Q ∩ K) n : ℝ) + c) /
          (prefixCount K n : ℝ) := by
        exact div_le_div_of_nonneg_right hnum hkpos.le
      _ = target n + error n := by
        rw [add_div]
        rfl
  have hlim := liminf_le_of_eventually_le_add_vanishing
    source target error
    (fun n => relativeRatio_nonneg _ _ n)
    (fun n => relativeRatio_nonneg _ _ n)
    (fun n => relativeRatio_le_one (Set.inter_subset_right) n)
    herror hprefix
  simpa [relativeLowerDensity, relativeRatio, source, target] using hlim

end DensityTransfer
end Stage3Case025
