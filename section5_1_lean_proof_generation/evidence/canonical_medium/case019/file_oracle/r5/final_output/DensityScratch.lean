import Stage3Model
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import GenLimit.Paper39_DenseGeneration.Abstract.TargetDensity

open Set Filter
open scoped Topology

namespace TestDensity
open GenLimit.PatientScope

lemma prefixCount_le_add_of_subset_union_finite
    {A B F : Set ℕ} (hF : F.Finite) (hsub : A ⊆ B ∪ F) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n + hF.toFinset.card := by
  classical
  unfold prefixCount
  calc
    (prefixFinset A n).card ≤
        (prefixFinset B n ∪ hF.toFinset).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := mem_prefixFinset.mp hx
      rcases hsub hx'.2 with hxB | hxF
      · exact Finset.mem_union_left _ (mem_prefixFinset.mpr ⟨hx'.1, hxB⟩)
      · exact Finset.mem_union_right _ (hF.mem_toFinset.mpr hxF)
    _ ≤ (prefixFinset B n).card + hF.toFinset.card := Finset.card_union_le _ _

lemma relativeLowerDensity_finite_transfer
    {A K R : Set ℕ} (hK : K.Infinite) (hKR : K ⊆ R)
    (hfin : (R \ K).Finite) (hAR : A ⊆ R) :
    relativeLowerDensity A R ≤ relativeLowerDensity (A ∩ K) K := by
  let c := hfin.toFinset.card
  let f : ℕ → ℝ := fun n => (prefixCount A n : ℝ) / (prefixCount R n : ℝ)
  let g : ℕ → ℝ := fun n => (prefixCount (A ∩ K) n : ℝ) / (prefixCount K n : ℝ)
  let e : ℕ → ℝ := fun n => (c : ℝ) / (prefixCount R n : ℝ)
  have hR : R.Infinite := hK.mono hKR
  have hcount : ∀ n, prefixCount A n ≤ prefixCount (A ∩ K) n + c := by
    intro n
    apply prefixCount_le_add_of_subset_union_finite hfin
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx, hxK⟩
    · exact Or.inr ⟨hAR hx, hxK⟩
  have hden : ∀ n, prefixCount K n ≤ prefixCount R n :=
    fun n => prefixCount_mono hKR n
  have hcompare : ∀ᶠ n : ℕ in atTop, f n ≤ g n + e n := by
    have hkpos : ∀ᶠ n : ℕ in atTop, 0 < prefixCount K n :=
      (tendsto_prefixCount_atTop hK).eventually (eventually_gt_atTop 0)
    filter_upwards [hkpos] with n hn
    have hrpos : 0 < prefixCount R n := lt_of_lt_of_le hn (hden n)
    have hkR : (0 : ℝ) < prefixCount K n := by exact_mod_cast hn
    have hrR : (0 : ℝ) < prefixCount R n := by exact_mod_cast hrpos
    have hcR : (prefixCount A n : ℝ) ≤
        prefixCount (A ∩ K) n + c := by exact_mod_cast hcount n
    have hnumNonneg : (0 : ℝ) ≤ prefixCount (A ∩ K) n := by positivity
    have hfrac : (prefixCount (A ∩ K) n : ℝ) / prefixCount R n ≤
        (prefixCount (A ∩ K) n : ℝ) / prefixCount K n := by
      exact div_le_div_of_nonneg_left hnumNonneg hkR (by exact_mod_cast hden n)
    dsimp [f, g, e]
    calc
      (prefixCount A n : ℝ) / prefixCount R n ≤
          ((prefixCount (A ∩ K) n : ℝ) + c) / prefixCount R n :=
        div_le_div_of_nonneg_right hcR hrR.le
      _ = (prefixCount (A ∩ K) n : ℝ) / prefixCount R n +
          (c : ℝ) / prefixCount R n := by rw [add_div]
      _ ≤ (prefixCount (A ∩ K) n : ℝ) / prefixCount K n +
          (c : ℝ) / prefixCount R n := add_le_add_right hfrac _
  have he : Tendsto e atTop (𝓝 0) := by
    have hcast : Tendsto (fun n => (prefixCount R n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_prefixCount_atTop hR)
    simpa [e] using tendsto_const_nhds.div_atTop hcast
  have hf_nonneg : ∀ n, 0 ≤ f n := by intro n; positivity
  have hf_le_one : ∀ n, f n ≤ 1 := by
    intro n
    by_cases hn : prefixCount R n = 0
    · simp [f, hn]
    · have hr : (0 : ℝ) < prefixCount R n := by exact_mod_cast Nat.pos_of_ne_zero hn
      change (prefixCount A n : ℝ) / prefixCount R n ≤ 1
      rw [div_le_one hr]
      exact_mod_cast prefixCount_mono hAR n
  have hg_nonneg : ∀ n, 0 ≤ g n := by intro n; positivity
  have hg_le_one : ∀ n, g n ≤ 1 := by
    intro n
    by_cases hn : prefixCount K n = 0
    · simp [g, hn]
    · have hk : (0 : ℝ) < prefixCount K n := by exact_mod_cast Nat.pos_of_ne_zero hn
      change (prefixCount (A ∩ K) n : ℝ) / prefixCount K n ≤ 1
      rw [div_le_one hk]
      exact_mod_cast prefixCount_mono (Set.inter_subset_right) n
  have he_nonneg : ∀ n, 0 ≤ e n := by intro n; positivity
  have he_le : ∀ᶠ n : ℕ in atTop, e n ≤ 1 :=
    (he.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)).mono (by
      intro n hn
      have := abs_lt.mp hn
      linarith [he_nonneg n])
  have hlim : liminf f atTop ≤ liminf (g + e) atTop :=
    liminf_le_liminf hcompare
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hf_nonneg))
      (isCoboundedUnder_ge_of_eventually_le atTop
        ((Eventually.of_forall hg_le_one).and he_le |>.mono (by
          intro n hn
          change g n + e n ≤ 2
          linarith)))
  have hadd : liminf (g + e) atTop ≤ limsup e atTop + liminf g atTop := by
    simpa [add_comm] using
      (liminf_add_le (f := atTop) (u := e) (v := g)
        (isBoundedUnder_of_eventually_ge (Eventually.of_forall he_nonneg))
        (isBoundedUnder_of_eventually_le he_le)
        (isBoundedUnder_of_eventually_ge (Eventually.of_forall hg_nonneg))
        (isCoboundedUnder_ge_of_eventually_le atTop
          (Eventually.of_forall hg_le_one)))
  have heSup : limsup e atTop = 0 := he.limsup_eq
  change liminf f atTop ≤ liminf g atTop
  calc
    liminf f atTop ≤ liminf (g + e) atTop := hlim
    _ ≤ limsup e atTop + liminf g atTop := hadd
    _ = liminf g atTop := by rw [heSup, zero_add]

end TestDensity
