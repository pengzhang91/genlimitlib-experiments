import Helpers
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Archimedean.IndicatorCard

open Filter Set
open scoped Topology BigOperators

namespace Stage3Case025

lemma prefixCount_eq_sum_indicator (S : Set ℕ) (n : ℕ) :
    (GenLimit.PatientScope.prefixCount S n : ℝ) =
      ∑ k ∈ Finset.range n, S.indicator (fun _ => (1 : ℝ)) k := by
  simp [GenLimit.PatientScope.prefixCount, GenLimit.PatientScope.prefixFinset,
    Finset.sum_filter, Set.indicator]

lemma prefixCount_tendsto_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (fun n => (GenLimit.PatientScope.prefixCount K n : ℝ)) atTop atTop := by
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (R := ℝ) zero_lt_one] at hK
  exact hK.congr' (Eventually.of_forall fun n => (prefixCount_eq_sum_indicator K n).symm)

end Stage3Case025

namespace Stage3Case025

open GenLimit.PatientScope

lemma prefixCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n := by
  apply Finset.card_le_card
  intro x hx
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma prefixCount_union_le (A B : Set ℕ) (n : ℕ) :
    prefixCount (A ∪ B) n ≤ prefixCount A n + prefixCount B n := by
  unfold prefixCount
  have heq : prefixFinset (A ∪ B) n = prefixFinset A n ∪ prefixFinset B n := by
    ext x
    simp [prefixFinset, and_or_left]
  rw [heq]
  exact Finset.card_union_le _ _

lemma prefixCount_finite_le_natCard {E : Set ℕ} (hE : E.Finite) (n : ℕ) :
    prefixCount E n ≤ Nat.card E := by
  rw [Nat.card_eq_card_finite_toFinset hE]
  apply Finset.card_le_card
  intro x hx
  have hx' : x < n ∧ x ∈ E := by simpa [prefixFinset] using hx
  exact hE.mem_toFinset.2 hx'.2

lemma scored_count_le_add_finite
    (Q K R : Set ℕ) (hKR : K ⊆ R) (hfin : (R \ K).Finite) (n : ℕ) :
    prefixCount (Q ∩ R) n ≤ prefixCount (Q ∩ K) n + Nat.card ↥(R \ K) := by
  calc
    prefixCount (Q ∩ R) n ≤ prefixCount ((Q ∩ K) ∪ (R \ K)) n :=
      prefixCount_mono (by
        rintro x ⟨hxQ, hxR⟩
        by_cases hxK : x ∈ K
        · exact Or.inl ⟨hxQ, hxK⟩
        · exact Or.inr ⟨hxR, hxK⟩) n
    _ ≤ prefixCount (Q ∩ K) n + prefixCount (R \ K) n :=
      prefixCount_union_le _ _ _
    _ ≤ prefixCount (Q ∩ K) n + Nat.card ↥(R \ K) :=
      Nat.add_le_add_left (prefixCount_finite_le_natCard hfin n) _

lemma ratio_finite_extension_le
    (Q K R : Set ℕ) (hKR : K ⊆ R) (hfin : (R \ K).Finite) (n : ℕ)
    (hpos : 0 < prefixCount K n) :
    (prefixCount (Q ∩ R) n : ℝ) / prefixCount R n ≤
      (prefixCount (Q ∩ K) n : ℝ) / prefixCount K n +
        (Nat.card ↥(R \ K) : ℝ) / prefixCount K n := by
  have hden : prefixCount K n ≤ prefixCount R n := prefixCount_mono hKR n
  have hnum := scored_count_le_add_finite Q K R hKR hfin n
  have hKreal : (0 : ℝ) < prefixCount K n := by exact_mod_cast hpos
  have hRreal : (0 : ℝ) < prefixCount R n := by
    exact lt_of_lt_of_le hKreal (by exact_mod_cast hden)
  have hnumreal : (prefixCount (Q ∩ R) n : ℝ) ≤
      prefixCount (Q ∩ K) n + Nat.card ↥(R \ K) := by exact_mod_cast hnum
  have hdenreal : (prefixCount K n : ℝ) ≤ prefixCount R n := by exact_mod_cast hden
  apply (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hKreal hdenreal).trans
  rw [div_add_div_same]
  exact div_le_div_of_nonneg_right hnumreal hKreal.le


end Stage3Case025

namespace Stage3Case025

open GenLimit.PatientScope

lemma prefixRatio_nonneg (A K : Set ℕ) (n : ℕ) :
    0 ≤ (prefixCount A n : ℝ) / prefixCount K n := by positivity

lemma prefixRatio_le_one {A K : Set ℕ} (hAK : A ⊆ K) (n : ℕ) :
    (prefixCount A n : ℝ) / prefixCount K n ≤ 1 := by
  by_cases hzero : prefixCount K n = 0
  · simp [hzero]
  · apply (div_le_one (by positivity)).2
    exact_mod_cast prefixCount_mono hAK n

lemma ratio_bdd_below (A K : Set ℕ) :
    IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => (prefixCount A n : ℝ) / prefixCount K n) := by
  apply isBoundedUnder_of_eventually_ge
  exact Eventually.of_forall (prefixRatio_nonneg A K)

lemma ratio_cobdd_below {A K : Set ℕ} (hAK : A ⊆ K) :
    IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop
      (fun n => (prefixCount A n : ℝ) / prefixCount K n) := by
  apply isCoboundedUnder_ge_of_eventually_le atTop
  exact Eventually.of_forall (prefixRatio_le_one hAK)

lemma finite_extension_density_le
    (Q K R : Set ℕ) (hK : K.Infinite) (hKR : K ⊆ R) (hfin : (R \ K).Finite) :
    GenLimit.PatientScope.relativeLowerDensity (Q ∩ R) R ≤
      GenLimit.PatientScope.relativeLowerDensity (Q ∩ K) K := by
  let c : ℝ := Nat.card ↥(R \ K)
  let fR : ℕ → ℝ := fun n => (prefixCount (Q ∩ R) n : ℝ) / prefixCount R n
  let fK : ℕ → ℝ := fun n => (prefixCount (Q ∩ K) n : ℝ) / prefixCount K n
  let err : ℕ → ℝ := fun n => c / prefixCount K n
  have hcount : Tendsto (fun n => (prefixCount K n : ℝ)) atTop atTop :=
    prefixCount_tendsto_atTop hK
  have herr : Tendsto err atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcount
  have hpos : ∀ᶠ n in atTop, 0 < prefixCount K n := by
    filter_upwards [hcount.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    exact_mod_cast hn
  have hle : ∀ᶠ n in atTop, fR n ≤ fK n + err n := by
    filter_upwards [hpos] with n hn
    exact ratio_finite_extension_le Q K R hKR hfin n hn
  rw [GenLimit.PatientScope.relativeLowerDensity,
    GenLimit.PatientScope.relativeLowerDensity]
  change liminf fR atTop ≤ liminf fK atTop
  apply le_of_forall_pos_le_add
  intro ε hε
  have herrε : ∀ᶠ n in atTop, err n ≤ ε :=
    herr.eventually (Iic_mem_nhds hε)
  have hεle : ∀ᶠ n in atTop, fR n ≤ fK n + ε :=
    hle.and herrε |>.mono fun n hn => hn.1.trans (add_le_add_left hn.2 _)
  calc
    liminf fR atTop ≤ liminf (fun n => fK n + ε) atTop :=
      liminf_le_liminf hεle (ratio_bdd_below (Q ∩ R) R)
        (isCoboundedUnder_ge_of_eventually_le atTop
          (Eventually.of_forall fun n => by
            dsimp [fK]
            exact (add_le_add_right
              (prefixRatio_le_one (show Q ∩ K ⊆ K by exact inter_subset_right) n) ε)))
    _ = liminf fK atTop + ε := by
      apply liminf_add_const
      · exact ratio_cobdd_below (show Q ∩ K ⊆ K by exact inter_subset_right)
      · exact ratio_bdd_below (Q ∩ K) K

end Stage3Case025
