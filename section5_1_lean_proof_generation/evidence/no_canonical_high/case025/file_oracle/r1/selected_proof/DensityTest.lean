import Stage3Model
import GenLimit.Paper17_InfiniteContamination.FiniteContaminationSufficiency

open Filter
open scoped Topology

namespace Case025

open GenLimit
open GenLimit.PatientScope

theorem ambientPrefixCount_le_add_ncard_diff
    {A B : Set ℕ} (hfinite : (A \ B).Finite) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hfinite.toFinset.card := by
  classical
  let aPrefix := prefixFinset A n
  let bPrefix := prefixFinset B n
  let diffPrefix := prefixFinset (A \ B) n
  have hsub : aPrefix ⊆ bPrefix ∪ diffPrefix := by
    intro x hx
    simp only [aPrefix, bPrefix, diffPrefix, mem_prefixFinset,
      Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hx.1, hxB⟩
    · exact Or.inr ⟨hx.1, hx.2, hxB⟩
  have hcard : aPrefix.card ≤ bPrefix.card + diffPrefix.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdiff : diffPrefix.card ≤ hfinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact Set.Finite.mem_toFinset hfinite |>.2 (mem_prefixFinset.mp hx).2
  simpa [prefixCount, aPrefix, bPrefix, diffPrefix] using
    hcard.trans (Nat.add_le_add_left hdiff _)

theorem ambientRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    (0 : ℝ) ≤ (prefixCount A n : ℝ) / (prefixCount K n : ℝ) := by
  positivity

theorem ambientRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / (prefixCount K n : ℝ) ≤ 1 := by
  by_cases hn : prefixCount K n = 0
  · simp [hn]
  · have hnpos : (0 : ℝ) < prefixCount K n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_le_one hnpos]
    exact_mod_cast prefixCount_mono hAK n

theorem relativeLowerDensity_mono_finite_extension
    {A K E : Set ℕ} (hK : K.Infinite) (hKE : K ⊆ E)
    (hfinite : (E \ K).Finite) :
    relativeLowerDensity (A ∩ E) E ≤ relativeLowerDensity (A ∩ K) K := by
  let source : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ E) n : ℝ) / (prefixCount E n : ℝ)
  let target : ℕ → ℝ := fun n =>
    (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  let error : ℕ → ℝ := fun n =>
    (hfinite.toFinset.card : ℝ) / (prefixCount K n : ℝ)
  have hcountK := tendsto_prefixCount_atTop hK
  have hcountKR : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcountK
  have herror : Tendsto error atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hcountKR
  have hKpos : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
    hcountK.eventually (eventually_gt_atTop 0)
  have hprefix : ∀ᶠ n : ℕ in atTop, source n ≤ target n + error n := by
    filter_upwards [hKpos] with n hn
    have hnK : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hnKE : prefixCount K n ≤ prefixCount E n := prefixCount_mono hKE n
    have hnE : (0 : ℝ) < prefixCount E n := by
      exact_mod_cast lt_of_lt_of_le hn hnKE
    have hdiff : ((A ∩ E) \ (A ∩ K)).Finite := by
      apply hfinite.subset
      intro x hx
      exact ⟨hx.1.2, fun hxK => hx.2 ⟨hx.1.1, hxK⟩⟩
    have hnumNat := ambientPrefixCount_le_add_ncard_diff hdiff n
    have hcard : hdiff.toFinset.card ≤ hfinite.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      exact Set.Finite.mem_toFinset hfinite |>.2
        (by
          have hxm := Set.Finite.mem_toFinset hdiff |>.1 hx
          exact ⟨hxm.1.2, fun hxK => hxm.2 ⟨hxm.1.1, hxK⟩⟩)
    have hnum : (prefixCount (A ∩ E) n : ℝ) ≤
        prefixCount (A ∩ K) n + hfinite.toFinset.card := by
      exact_mod_cast hnumNat.trans (Nat.add_le_add_left hcard _)
    calc
      source n ≤
          ((prefixCount (A ∩ K) n : ℝ) + hfinite.toFinset.card) /
            (prefixCount E n : ℝ) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt hnE)
      _ ≤ ((prefixCount (A ∩ K) n : ℝ) + hfinite.toFinset.card) /
            (prefixCount K n : ℝ) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hnK
        · exact_mod_cast hnKE
      _ = target n + error n := by rw [add_div]
  unfold relativeLowerDensity
  change liminf source atTop ≤ liminf target atTop
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le atTop
      (fun n => ambientRatio_le_one (Set.inter_subset_right) n))
    (isBoundedUnder_of
      ⟨0, fun n => ambientRatio_nonneg (A ∩ K) K n⟩)).2
  intro y hy
  obtain ⟨r, hyr, hrsource⟩ := exists_between hy
  have hrEventually : ∀ᶠ n : ℕ in atTop, r < source n :=
    eventually_lt_of_lt_liminf hrsource
      (isBoundedUnder_of
        ⟨0, fun n => ambientRatio_nonneg (A ∩ E) E n⟩)
  have herrorEventually : ∀ᶠ n : ℕ in atTop, error n < r - y := by
    have hpositive : 0 < r - y := by linarith
    exact herror.eventually (Iio_mem_nhds hpositive)
  filter_upwards [hrEventually, herrorEventually, hprefix] with n hr herr hp
  linarith

end Case025
