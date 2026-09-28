import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Archimedean.IndicatorCard

open Filter
open scoped Topology

namespace Stage3Case025

noncomputable section

private theorem prefixFinset_mono {A C : Set ℕ} (hAC : A ⊆ C) (n : ℕ) :
    GenLimit.PatientScope.prefixFinset A n ⊆
      GenLimit.PatientScope.prefixFinset C n := by
  intro x hx
  simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
    Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hAC hx.2⟩

private theorem prefixCount_mono {A C : Set ℕ} (hAC : A ⊆ C) (n : ℕ) :
    GenLimit.PatientScope.prefixCount A n ≤
      GenLimit.PatientScope.prefixCount C n := by
  exact Finset.card_le_card (prefixFinset_mono hAC n)

private theorem prefixCount_union_le (A C : Set ℕ) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∪ C) n ≤
      GenLimit.PatientScope.prefixCount A n +
        GenLimit.PatientScope.prefixCount C n := by
  rw [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixCount,
    GenLimit.PatientScope.prefixCount]
  calc
    (GenLimit.PatientScope.prefixFinset (A ∪ C) n).card ≤
        (GenLimit.PatientScope.prefixFinset A n ∪
          GenLimit.PatientScope.prefixFinset C n).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [GenLimit.PatientScope.prefixFinset, Finset.mem_filter,
        Finset.mem_range, Finset.mem_union] at hx ⊢
      rcases hx.2 with hxA | hxC
      · exact Or.inl ⟨hx.1, hxA⟩
      · exact Or.inr ⟨hx.1, hxC⟩
    _ ≤ _ := Finset.card_union_le _ _

private theorem prefixCount_finite_le (B : Set ℕ) (hB : B.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount B n ≤ hB.toFinset.card := by
  classical
  rw [GenLimit.PatientScope.prefixCount]
  apply Finset.card_le_card
  intro x hx
  simpa only [Set.Finite.mem_toFinset] using
    (show x ∈ B from (Finset.mem_filter.mp hx).2)

private theorem prefixCount_inter_union_le
    (A K B : Set ℕ) (hB : B.Finite) (n : ℕ) :
    GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n ≤
      GenLimit.PatientScope.prefixCount (A ∩ K) n + hB.toFinset.card := by
  calc
    GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n ≤
        GenLimit.PatientScope.prefixCount ((A ∩ K) ∪ B) n := by
      apply prefixCount_mono
      intro x hx
      rcases hx with ⟨hxA, hxK | hxB⟩
      · exact Or.inl ⟨hxA, hxK⟩
      · exact Or.inr hxB
    _ ≤ GenLimit.PatientScope.prefixCount (A ∩ K) n +
        GenLimit.PatientScope.prefixCount B n := prefixCount_union_le _ _ _
    _ ≤ GenLimit.PatientScope.prefixCount (A ∩ K) n + hB.toFinset.card :=
      Nat.add_le_add_left (prefixCount_finite_le B hB n) _

private theorem prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Filter.Tendsto
      (fun n => GenLimit.PatientScope.prefixCount K n)
      Filter.atTop Filter.atTop := by
  rw [show (fun n => GenLimit.PatientScope.prefixCount K n) =
      (fun n => ∑ k ∈ Finset.range n,
        K.indicator (fun _ => (1 : ℕ)) k) by
    funext n
    simp [GenLimit.PatientScope.prefixCount,
      GenLimit.PatientScope.prefixFinset, Set.indicator]]
  exact
    (Set.infinite_iff_tendsto_sum_indicator_atTop
      (R := ℕ) Nat.zero_lt_one).mp hK

private theorem eventually_prefixCount_pos {K : Set ℕ} (hK : K.Infinite) :
    ∀ᶠ n in Filter.atTop, 0 < GenLimit.PatientScope.prefixCount K n := by
  exact (prefixCount_tendsto_atTop hK).eventually (eventually_gt_atTop 0)

private theorem ratio_bounds (A K : Set ℕ) :
    (∀ n, 0 ≤ (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        GenLimit.PatientScope.prefixCount K n) ∧
    (∀ n, (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
        GenLimit.PatientScope.prefixCount K n ≤ 1) := by
  constructor
  · intro n
    positivity
  · intro n
    by_cases hzero : GenLimit.PatientScope.prefixCount K n = 0
    · simp [hzero]
    · apply (div_le_one (by positivity)).2
      exact_mod_cast prefixCount_mono Set.inter_subset_right n

theorem finite_change_relativeLowerDensity
    (A K B : Set ℕ) (hK : K.Infinite) (hB : B.Finite) :
    GenLimit.PatientScope.relativeLowerDensity (A ∩ (K ∪ B)) (K ∪ B) ≤
      GenLimit.PatientScope.relativeLowerDensity (A ∩ K) K := by
  let extendedRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n : ℝ) /
      GenLimit.PatientScope.prefixCount (K ∪ B) n
  let targetRatio : ℕ → ℝ := fun n =>
    (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
      GenLimit.PatientScope.prefixCount K n
  let error : ℕ → ℝ := fun n =>
    (hB.toFinset.card : ℝ) / GenLimit.PatientScope.prefixCount K n
  have hdenom : ∀ n,
      GenLimit.PatientScope.prefixCount K n ≤
        GenLimit.PatientScope.prefixCount (K ∪ B) n := by
    intro n
    exact prefixCount_mono Set.subset_union_left n
  have hineq : ∀ᶠ n in Filter.atTop,
      extendedRatio n - error n ≤ targetRatio n := by
    filter_upwards [eventually_prefixCount_pos hK] with n hn
    dsimp [extendedRatio, targetRatio, error]
    have hnum := prefixCount_inter_union_le A K B hB n
    have hden := hdenom n
    have hbigpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount (K ∪ B) n := by
      exact_mod_cast lt_of_lt_of_le hn hden
    have hsmallpos : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by
      exact_mod_cast hn
    have hden' : (GenLimit.PatientScope.prefixCount K n : ℝ) ≤
        GenLimit.PatientScope.prefixCount (K ∪ B) n := by exact_mod_cast hden
    have hfirst :
        (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n : ℝ) /
            GenLimit.PatientScope.prefixCount (K ∪ B) n ≤
          (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n := by
      exact div_le_div_of_nonneg_left (by positivity) hsmallpos hden'
    have hnum' :
        (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n : ℝ) ≤
          GenLimit.PatientScope.prefixCount (A ∩ K) n + hB.toFinset.card := by
      exact_mod_cast hnum
    have hsecond :
        (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n : ℝ) /
            GenLimit.PatientScope.prefixCount K n ≤
          ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) + hB.toFinset.card) /
            GenLimit.PatientScope.prefixCount K n :=
      (div_le_div_iff_of_pos_right hsmallpos).2 hnum'
    calc
      (GenLimit.PatientScope.prefixCount (A ∩ (K ∪ B)) n : ℝ) /
            GenLimit.PatientScope.prefixCount (K ∪ B) n -
          (hB.toFinset.card : ℝ) / GenLimit.PatientScope.prefixCount K n ≤
        ((GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) + hB.toFinset.card) /
            GenLimit.PatientScope.prefixCount K n -
          (hB.toFinset.card : ℝ) / GenLimit.PatientScope.prefixCount K n :=
        sub_le_sub_right (hfirst.trans hsecond) _
      _ = (GenLimit.PatientScope.prefixCount (A ∩ K) n : ℝ) /
          GenLimit.PatientScope.prefixCount K n := by ring
  have hcast : Filter.Tendsto
      (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (prefixCount_tendsto_atTop hK)
  have herr : Filter.Tendsto error Filter.atTop (𝓝 0) := by
    exact hcast.const_div_atTop (hB.toFinset.card : ℝ)
  have hnegerr : Filter.Tendsto (fun n => - error n) Filter.atTop (𝓝 0) := by
    simpa using herr.neg
  have hext_lower : Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y)
      Filter.atTop extendedRatio := by
    apply Filter.isBoundedUnder_of_eventually_ge (a := 0)
    exact Filter.Eventually.of_forall (ratio_bounds A (K ∪ B)).1
  have hext_upper : Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y)
      Filter.atTop extendedRatio := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Filter.Eventually.of_forall (ratio_bounds A (K ∪ B)).2
  have hden_large : ∀ᶠ n in Filter.atTop,
      hB.toFinset.card ≤ GenLimit.PatientScope.prefixCount K n :=
    (prefixCount_tendsto_atTop hK).eventually (eventually_ge_atTop hB.toFinset.card)
  have hneg_event : ∀ᶠ n in Filter.atTop, -1 ≤ - error n := by
    filter_upwards [eventually_prefixCount_pos hK, hden_large] with n hn hlarge
    dsimp [error]
    have hden : (0 : ℝ) < GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hn
    have hlarge' : (hB.toFinset.card : ℝ) ≤
        GenLimit.PatientScope.prefixCount K n := by exact_mod_cast hlarge
    have hquot : (hB.toFinset.card : ℝ) /
        GenLimit.PatientScope.prefixCount K n ≤ 1 :=
      (div_le_one hden).2 hlarge'
    linarith
  have hneg_lower : Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y)
      Filter.atTop (fun n => - error n) :=
    Filter.isBoundedUnder_of_eventually_ge hneg_event
  have hneg_upper : Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y)
      Filter.atTop (fun n => - error n) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 0)
    exact Filter.Eventually.of_forall (fun n => by
      dsimp [error]
      exact neg_nonpos.mpr (div_nonneg (by positivity) (by positivity)))
  rw [GenLimit.PatientScope.relativeLowerDensity,
    GenLimit.PatientScope.relativeLowerDensity]
  change Filter.liminf extendedRatio Filter.atTop ≤
    Filter.liminf targetRatio Filter.atTop
  calc
    Filter.liminf extendedRatio Filter.atTop =
        Filter.liminf extendedRatio Filter.atTop + 0 := by ring
    _ = Filter.liminf extendedRatio Filter.atTop +
        Filter.liminf (fun n => - error n) Filter.atTop := by
      rw [hnegerr.liminf_eq]
    _ ≤ Filter.liminf (extendedRatio + fun n => - error n) Filter.atTop :=
      le_liminf_add hext_lower hext_upper hneg_lower hneg_upper.isCoboundedUnder_ge
    _ ≤ Filter.liminf targetRatio Filter.atTop := by
      apply Filter.liminf_le_liminf
      · simpa only [Pi.add_apply, sub_eq_add_neg] using hineq
      · apply Filter.isBoundedUnder_of_eventually_ge (a := -1)
        filter_upwards [hneg_event] with n hn
        have hextnonneg : 0 ≤ extendedRatio n := (ratio_bounds A (K ∪ B)).1 n
        dsimp only [Pi.add_apply]
        linarith
      · have htarget_upper : Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y)
            Filter.atTop targetRatio := by
          apply Filter.isBoundedUnder_of_eventually_le (a := 1)
          exact Filter.Eventually.of_forall (ratio_bounds A K).2
        exact htarget_upper.isCoboundedUnder_ge

end

end Stage3Case025
